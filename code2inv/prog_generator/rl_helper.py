from __future__ import print_function

import os
import sys
import numpy as np
import torch
import json
import random
from tqdm import tqdm
from torch.autograd import Variable
from torch.nn.parameter import Parameter
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from itertools import chain
from tqdm import tqdm


from code2inv.common.ssa_graph_builder import ProgramGraph, GraphNode, ExprNode
from code2inv.common.constants import AC_CODE, NUM_EDGE_TYPES, LIST_PREDICATES, LIST_OP, MAX_DEPTH, MAX_AND, MAX_OR, INVALID_CODE, NORMAL_EXPR_CODE
from code2inv.common.cmd_args import cmd_args
from code2inv.common.checker import boogie_result, z3_precheck, z3_precheck_expensive, stat_counter


class RLEnv(object):
    def __init__(self, s2v_graph):
        self.s2v_graph = s2v_graph
        self.pg = s2v_graph.pg
        self.reset()

    def reset(self):
        self.root = None
        self.terminal = False
        self.trivial_subexpr = False
        self.expr_in_and = set()
        self.expr_in_or = set()
        self.used_core_vars = set()

    def num_vars(self):
        return len(self.pg.raw_variable_nodes)

    def num_consts(self):
        return len(self.pg.const_nodes)

    def pg_nodes(self):
        return self.pg.node_list

    def update_used_core_var(self, var_node):
        if var_node.name in self.pg.core_vars:
            self.used_core_vars.add(var_node.name)

    def constraint_satisfied(self):
        return len(self.used_core_vars) == len(self.pg.core_vars)

    def step(self, and_or, sub_expr_node):
        reward = 0.0        
        if and_or is None:
            assert sub_expr_node is None
            assert self.root is not None
            self.terminal = True
        else:
            if self.root is None:
                self.root = ExprNode('&&')
                assert and_or == '&&'
            if and_or == '&&': # a new and branch
                self.expr_in_or.clear()
                if len(self.root.children): # finished an existing and branch
                    self.expr_in_and.add( str(self.root.children[-1]) )
                self.root.children.append( ExprNode('||') )
            else:
                assert and_or == '||'
            cur_node = self.root.children[-1]
            cur_node.children.append(sub_expr_node)

            if len(self.root.children) == MAX_AND and len(self.root.children[-1].children) == MAX_OR:
                self.terminal = True
            
            self.root.state = None
            str_expr = str(sub_expr_node)
            if str_expr in self.expr_in_or: # each expr in same disjuction should be different
                self.trivial_subexpr = True 
            elif str(cur_node) in self.expr_in_and: # each and branch should be different
                self.trivial_subexpr = True 
            elif cmd_args.aggressive_check:
                if cur_node.has_trivial_pattern():
                    self.trivial_subexpr = True  
                if not self.trivial_subexpr:    
                    stat_counter.add(self.s2v_graph.sample_index, 'impl')
                    if cur_node.has_internal_implications(self.pg):
                        self.trivial_subexpr = True
                if not self.trivial_subexpr: 
                    stat_counter.add(self.s2v_graph.sample_index, 'z3_exp_pre')
                    # trivial or expr, e.g. (c <0 || c >= 0) 
                    if z3_precheck_expensive(self.pg, cur_node.to_z3()) != NORMAL_EXPR_CODE: 
                        self.trivial_subexpr = True             
            else:
                stat_counter.add(self.s2v_graph.sample_index, 'z3_pre')
                if z3_precheck(self.pg, str(sub_expr_node)) != NORMAL_EXPR_CODE: # trivial expr itself
                    self.trivial_subexpr = True             
                else:
                    reward += 0.5

            if self.trivial_subexpr:
                reward += -2.0
                self.terminal = True
                
            self.expr_in_or.add(str_expr)

        if self.terminal:
            if not self.trivial_subexpr: #self.constraint_satisfied():
                r = boogie_result(self.s2v_graph, self.root)
                reward += r
            else:
                reward += -4.0
            
        return self.terminal, reward

    def core_var_budget(self, cur_used, new_and_branch):
        subexpr_budget = 2 ** (MAX_DEPTH - 1) + 1

        if self.root is None:
            used_and = 0
            used_or = 0
        else:
            used_and = len(self.root.children)
            used_or = len(self.root.children[-1].children)

        future_and = (MAX_AND - used_and)
        if new_and_branch:
            future_and -= 1
            used_or = 0

        remain = (future_and * MAX_OR + MAX_OR - used_or) * subexpr_budget
        remain -= cur_used
        task = self.pg.core_vars - self.used_core_vars

        return remain - len(task)

    def available_var_indices(self, cur_used, new_and_branch):
        if len(self.used_core_vars) == len(self.pg.core_vars): # condition already satisfied
            return list(range(len(self.pg.raw_variable_nodes)))
        
        remain_budget = self.core_var_budget(cur_used, new_and_branch)
        assert remain_budget >= 0 # a valid solution should always be guaranteed
        
        if remain_budget:
            return list(range(len(self.pg.raw_variable_nodes)))

        task = self.pg.core_vars - self.used_core_vars
        indices = [self.pg.raw_variable_nodes[w].index for w in task]
        indices.sort()
        return indices

    def and_budget(self):
        if self.root is None:
            return MAX_AND
        return MAX_AND - len(self.root.children)
    
    def or_budget(self):
        if self.root is None:
            return MAX_OR
        return MAX_OR - len(self.root.children[-1].children)

    def is_finished(self):
        return self.terminal

def rollout(g, node_embedding, decoder, use_random, eps):
    nll_list = []
    value_list = []
    reward_list = []

    env = RLEnv(g)    
    while not env.is_finished():
        
        and_or, subexpr_node, nll, vs = decoder(env, node_embedding, use_random=use_random, eps = eps)
        nll_list.append(nll)
        value_list.append(vs)

        _, reward = env.step(and_or, subexpr_node)

        reward_list.append(reward)

    if not env.trivial_subexpr:
        if cmd_args.decoder_model == 'AssertAware':            
            assert env.constraint_satisfied()

    return nll_list, value_list, reward_list, env.root

def actor_critic_loss(nll_list, value_list, reward_list):
    r = 0.0
    rewards = []
    for t in range(len(reward_list) - 1, -1, -1):
        r = r + reward_list[t] # accumulated future reward
        rewards.insert(0, r / 10.0)
            
    policy_loss = 0.0
    targets = []
    for t in range(len(reward_list)):        
        reward = rewards[t] - value_list[t].data[0, 0]                
        policy_loss += nll_list[t] * reward
        targets.append(Variable(torch.Tensor([ [rewards[t]] ])))

    policy_loss /= len(reward_list)

    value_pred = torch.cat(value_list, dim=0)
    targets = torch.cat(targets, dim=0)    
    value_loss = F.mse_loss(value_pred, targets)

    loss = policy_loss + value_loss

    return loss
