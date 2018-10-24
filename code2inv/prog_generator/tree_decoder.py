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

from code2inv.common.ssa_graph_builder import ProgramGraph, GraphNode, ExprNode
from code2inv.common.constants import AC_CODE, NUM_EDGE_TYPES, LIST_PREDICATES, LIST_OP, MAX_DEPTH, MAX_AND, MAX_OR, INVALID_CODE, NORMAL_EXPR_CODE
from code2inv.common.cmd_args import cmd_args
from code2inv.common.pytorch_util import weights_init, to_num

from code2inv.prog_generator.prog_encoder import LogicEncoder


class IDecoder(nn.Module):
    def __init__(self, latent_dim):
        super(IDecoder, self).__init__()
        self.latent_dim = latent_dim

        self.token_w = Parameter(torch.Tensor(len(LIST_PREDICATES) + len(LIST_OP), latent_dim))
        self.decision = nn.Linear(latent_dim, 3)

        self.state_gru = nn.GRUCell(latent_dim, latent_dim)

        self.char_embedding = nn.Embedding(len(LIST_PREDICATES) + len(LIST_OP), latent_dim)
        self.and_embedding = Parameter(torch.Tensor(1, latent_dim))
        self.or_embedding = Parameter(torch.Tensor(1, latent_dim))
        
        self.value_pred_w1 = nn.Linear(self.latent_dim, self.latent_dim)
        self.value_pred_w2 = nn.Linear(self.latent_dim, 1)

        if cmd_args.attention:
            self.first_att = nn.Linear(self.latent_dim, 1)
        
        weights_init(self)     

    def choose_action(self, state, cls_w, use_random, eps):
        if type(cls_w) is Variable or type(cls_w) is Parameter or type(cls_w) is torch.Tensor:            
            logits = F.linear(state, cls_w, None)
        elif type(cls_w) is torch.nn.modules.linear.Linear:
            logits = cls_w(state)
        else:
            raise NotImplementedError()
        
        ll = F.log_softmax(logits, dim=1)        
        if use_random:
            scores = torch.exp(ll) * (1 - eps) + eps / ll.shape[1]
            picked = torch.multinomial(scores, 1)
        else:            
            _, picked = torch.max(ll, 1)

        picked = picked.view(-1)        

        self.nll += F.nll_loss(ll, picked)        
        return picked

    def update_state(self, input_embedding):
        self.latent_state = self.state_gru(input_embedding, self.latent_state)

    def recursive_decode(self, pg_node_list, lv, use_random, eps):
        if lv == 0: # subtree expression root node, decode the first symbol
            # left child, which is a variable
            picked = self.choose_action(self.latent_state, self.variable_embedding, use_random, eps)
            self.update_state(torch.index_select(self.variable_embedding, 0, picked))
            left_node = ExprNode(pg_node_list[ picked.data.cpu()[0] ])

            # recursively construct right child
            right_node = self.recursive_decode(pg_node_list, 1, use_random, eps)

            # root
            w = self.token_w[0 : len(LIST_PREDICATES), :]            
            picked = self.choose_action(self.latent_state, w, use_random, eps)
            self.update_state(self.char_embedding(picked))
            cur_node = ExprNode(LIST_PREDICATES[picked.data.cpu()[0]])            
            cur_node.children.append( left_node )
            cur_node.children.append( right_node )            
        else:
            if lv < MAX_DEPTH:
                w_op = self.token_w[len(LIST_PREDICATES) : , :]
                classifier = torch.cat((w_op, self.var_const_embedding), dim=0)
                picked = self.choose_action(self.latent_state, classifier, use_random, eps)
                self.update_state(torch.index_select(classifier, 0, picked))
                
                idx = picked.data.cpu()[0]
                if idx < len(LIST_OP): # it is an op node
                    cur_node = ExprNode(LIST_OP[idx])
                    # assert binary operator
                    cur_node.children.append( self.recursive_decode(pg_node_list, lv + 1, use_random, eps) )
                    cur_node.children.append( self.recursive_decode(pg_node_list, lv + 1, use_random, eps) )
                else:
                    cur_node = ExprNode(pg_node_list[idx - len(LIST_OP)])                
            else: # can only choose variable or const
                picked = self.choose_action(self.latent_state, self.var_const_embedding, use_random, eps)
                self.update_state(torch.index_select(self.var_const_embedding, 0, picked))

                cur_node = ExprNode(pg_node_list[ picked.data.cpu()[0] ])

        return cur_node

    def embed_tree(self, node_embedding, root):
        raise NotImplementedError()
    
    def forward(self, env, node_embedding, use_random, eps=0.05):
        state_embedding = self.embed_tree(node_embedding, env.root)
        self.latent_state = state_embedding
        est = self.value_pred_w2( F.relu( self.value_pred_w1(state_embedding) ) )

        self.nll = 0.0
        subexpr_node = None
        if env.root is None:
            act = 1
        else:
            first_decision = self.choose_action(self.latent_state, self.decision, use_random, eps)
            act = first_decision.data.cpu()[0]
            if act == 0 or (act == 1 and env.and_budget() == 0) or (act == 2 and env.or_budget() == 0):
                return None, subexpr_node, self.nll, est

        self.variable_embedding = node_embedding[0 : env.num_vars(), :]
        self.var_const_embedding = node_embedding[0 : env.num_vars() + env.num_consts(), :]                        

        if act == 1:
            self.update_state(self.and_embedding)            
            
        self.update_state(self.or_embedding)
        subexpr_node = self.recursive_decode(env.pg_nodes(), 0, use_random, eps)

        if act == 1:
            and_or = '&&'
        else:
            and_or = '||'

        return and_or, subexpr_node, self.nll, est

    def get_init_embedding(self, node_embedding, state):
        if cmd_args.attention:
            if state is None:
                logits = self.first_att(node_embedding)
            else:
                logits = torch.sum( node_embedding * self.latent_state, dim = 1, keepdim=True )
            weights = F.softmax(logits, dim = 0)
            init_embedding = torch.sum( weights * node_embedding, dim = 0, keepdim=True)
        else:
            init_embedding = torch.mean(node_embedding, dim=0, keepdim=True)
        return init_embedding

class CFGTreeDecoder(IDecoder):
    def __init__(self, latent_dim):
        super(CFGTreeDecoder, self).__init__(latent_dim)

        self.tree_embed = LogicEncoder(self.latent_dim)

    def embed_tree(self, node_embedding, root):
        init_embedding = self.get_init_embedding(node_embedding, root)
        return self.tree_embed(node_embedding, init_embedding, root)

class CFGRNNDecoder(IDecoder):
    def __init__(self, latent_dim):
        super(CFGRNNDecoder, self).__init__(latent_dim)

    def embed_tree(self, node_embedding, root):
        init_embedding = self.get_init_embedding(node_embedding, root)

        if root is None:
            return init_embedding
        else:
            return self.latent_state + init_embedding 

class AssertAwareDecoder(IDecoder):
    def __init__(self, latent_dim):
        super(AssertAwareDecoder, self).__init__(latent_dim)
        self.tree_grow_decision = nn.Linear(latent_dim, 2)
        self.top_act_w = Parameter( torch.Tensor(3, latent_dim) )

        weights_init(self)

    def count_var_leaves(self, env, expr):
        if len(expr.children) == 0:
            if expr.name in env.pg.raw_variable_nodes:
                return 1
            return 0
        cnt = 0
        for c in expr.children:
            cnt += self.count_var_leaves(env, c)
        return cnt

    def choose_operand(self, env, node_embedding, use_random, eps):
        var_list = env.available_var_indices(self.cur_token_used, self.top_act == 1)
        if len(var_list) == env.num_vars(): # can freely choose any variable
            selector = node_embedding
        else: # have to choose from core variables
            selector = node_embedding[var_list, :]

        picked = self.choose_action(self.latent_state, selector, use_random, eps)
        self.update_state(torch.index_select(selector, 0, picked))

        idx = to_num(picked)
        if idx < len(var_list): # otherwise, we have chosen a constant
            idx = var_list[idx]        
            env.update_used_core_var(env.pg_nodes()[idx])

        return ExprNode(env.pg_nodes()[ idx ])
                
    def recursive_decode(self, env, lv, use_random, eps):
        if lv == 0: # subtree expression root node, decode the first symbol
            # left child, which is a variable
            left_node = self.choose_operand(env, self.variable_embedding, use_random, eps)
            self.cur_token_used += 1 # occupy one token slot

            # recursively construct right child
            right_node = self.recursive_decode(env, 1, use_random, eps)

            assert self.cur_token_used == 2 ** (MAX_DEPTH - 1) + 1
            # root            
            w = self.token_w[0 : len(LIST_PREDICATES), :]            
            picked = self.choose_action(self.latent_state, w, use_random, eps)
            self.update_state(self.char_embedding(picked))
            cur_node = ExprNode(LIST_PREDICATES[picked.data.cpu()[0]])
            cur_node.children.append( left_node )
            cur_node.children.append( right_node )
        else:
            if lv < MAX_DEPTH:
                # can I just choose a variable, instead of an operator? 
                classifier = None
                tmp = 2 ** (MAX_DEPTH - lv)
                if env.core_var_budget(self.cur_token_used + tmp - 1, self.top_act == 1) < 0:
                    decision = 0
                else:                    
                    sp = self.choose_action(self.latent_state, self.tree_grow_decision, use_random, eps)
                    decision = to_num(sp)
                
                if decision == 0: # op node
                    classifier = self.token_w[len(LIST_PREDICATES) : , :]
                    picked = self.choose_action(self.latent_state, classifier, use_random, eps)
                    self.update_state(torch.index_select(classifier, 0, picked))                    
                    idx = to_num(picked)
                    cur_node = ExprNode(LIST_OP[idx])
                    cur_node.children.append( self.recursive_decode(env, lv + 1, use_random, eps) )
                    cur_node.children.append( self.recursive_decode(env, lv + 1, use_random, eps) )                    
                else: # leaf const/var node
                    self.cur_token_used += 2 ** (MAX_DEPTH - lv) - 1
                    cur_node = self.choose_operand(env, self.var_const_embedding, use_random, eps)
                    self.cur_token_used += 1    
            else: # can only choose variable or const
                cur_node = self.choose_operand(env, self.var_const_embedding, use_random, eps)

                self.cur_token_used += 1 # it is a leaf

        return cur_node

    def forward(self, env, node_embedding, use_random, eps=0.05):
        state_embedding = self.embed_tree(node_embedding, env.root)
        self.latent_state = state_embedding
        est = self.value_pred_w2( F.relu( self.value_pred_w1(state_embedding) ) )

        self.nll = 0.0
        self.cur_token_used = 0
        subexpr_node = None
        if env.root is None:
            act = 1
        else:            
            avail_actions = []
            if env.constraint_satisfied():
                avail_actions.append(0)
            if env.and_budget() and env.core_var_budget(0, True) >= 0:
                avail_actions.append(1)                
            if env.or_budget():
                avail_actions.append(2)
            
            if len(avail_actions) > 1:
                top_act_w = self.top_act_w[avail_actions, :]            
                first_decision = self.choose_action(self.latent_state, top_act_w, use_random, eps)
                act = avail_actions[ to_num(first_decision) ]
            else:
                act = avail_actions[0]
            if act == 0 or (act == 1 and env.and_budget() == 0) or (act == 2 and env.or_budget() == 0):
                return None, subexpr_node, self.nll, est
        
        self.variable_embedding = node_embedding[0 : env.num_vars(), :]
        self.var_const_embedding = node_embedding[0 : env.num_vars() + env.num_consts(), :]

        if act == 1:
            self.update_state(self.and_embedding)            

        self.top_act = act

        self.update_state(self.or_embedding)

        subexpr_node = self.recursive_decode(env, 0, use_random, eps)

        if act == 1:
            and_or = '&&'
        else:
            and_or = '||'

        return and_or, subexpr_node, self.nll, est

class AssertAwareTreeLSTMDecoder(AssertAwareDecoder):
    def __init__(self, latent_dim):
        super(AssertAwareTreeLSTMDecoder, self).__init__(latent_dim)

        self.tree_embed = LogicEncoder(self.latent_dim)

    def embed_tree(self, node_embedding, root):
        init_embedding = self.get_init_embedding(node_embedding, root)
        return self.tree_embed(node_embedding, init_embedding, root)

class AssertAwareRNNDecoder(AssertAwareDecoder):
    def __init__(self, latent_dim):
        super(AssertAwareRNNDecoder, self).__init__(latent_dim)

    def embed_tree(self, node_embedding, root):
        init_embedding = self.get_init_embedding(node_embedding, root)
        if root is None:
            return init_embedding
        else:
            return self.latent_state + init_embedding 
