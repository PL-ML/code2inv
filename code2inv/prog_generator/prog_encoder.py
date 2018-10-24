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


from code2inv.common.constants import NUM_EDGE_TYPES, LIST_PREDICATES, LIST_OP, MAX_DEPTH, MAX_AND, MAX_OR
from code2inv.common.cmd_args import cmd_args
from code2inv.common.pytorch_util import weights_init


class LogicEncoder(nn.Module):
    def __init__(self, latent_dim):
        super(LogicEncoder, self).__init__()
        self.latent_dim = latent_dim

        self.char_embedding = Parameter(torch.Tensor(len(LIST_PREDICATES) + len(LIST_OP), latent_dim))

        def new_gate():
            lh = nn.Linear(self.latent_dim, self.latent_dim)
            rh = nn.Linear(self.latent_dim, self.latent_dim)
            return lh, rh

        self.ilh, self.irh = new_gate()        
        self.lflh, self.lfrh = new_gate()
        self.rflh, self.rfrh = new_gate()
        self.ulh, self.urh = new_gate()

        self.ix = nn.Linear(self.latent_dim, self.latent_dim)
        self.fx = nn.Linear(self.latent_dim, self.latent_dim)
        self.ux = nn.Linear(self.latent_dim, self.latent_dim)

        self.and_transform_c, self.and_transform_h = new_gate()
        self.or_transform_c, self.or_transform_h = new_gate()

        self.cx, self.ox = new_gate()
        self.oend = nn.Linear(self.latent_dim * 3, self.latent_dim)

        weights_init(self)

    def forward(self, node_embedding, init_embedding, root):
        if root is None:
            return init_embedding

        if root.state is None:            
            if root.name == '&&' or root.name == '||':
                if root.name == '&&':
                    trans = (self.and_transform_c, self.and_transform_h)
                    pool = torch.min
                else:
                    trans = (self.or_transform_c, self.or_transform_h)
                    pool = torch.max
                    
                subtree_clist = []
                subtree_hlist = []
                for child in root.children:
                    self.forward(node_embedding, init_embedding, child)
                    c, h = child.state

                    subtree_clist.append(c)
                    subtree_hlist.append(h)
                
                c = trans[0]( torch.cat(subtree_clist, dim=0) )
                h = trans[1]( torch.cat(subtree_hlist, dim=0) )
                            
                if len(root.children) > 1:
                    c, _ = pool(c, dim=0, keepdim=True)
                    h, _ = pool(h, dim=0, keepdim=True)                
                root.state = (c, h)
            else: # embed sub expr
                self.subexpr_embed(node_embedding, root)

        if root.name == '&&':
            s = torch.cat((init_embedding, root.state[0], root.state[1]), dim=1)
            o = F.tanh(self.oend(s))
            return o

    def _get_token_embed(self, node_embedding, node):
        if node.name in LIST_PREDICATES or node.name in LIST_OP:
            
            if node.name in LIST_PREDICATES:
                idx = LIST_PREDICATES.index(node.name)
            else:
                idx = len(LIST_PREDICATES) + LIST_OP.index(node.name)
            x_embed = torch.index_select(self.char_embedding, 0, Variable(torch.LongTensor([idx])))
        else:
            assert node.pg_node is not None
            x_embed = torch.index_select(node_embedding, 0, Variable(torch.LongTensor([node.pg_node.index])))
        
        return x_embed

    def subexpr_embed(self, node_embedding, node):
        if node.state is not None:
            return node.state
        x_embed = self._get_token_embed(node_embedding, node)

        if len(node.children) == 0: # leaf node                        
            c = self.cx(x_embed)
            o = F.sigmoid(self.ox(x_embed))
            h = o * F.tanh(c)
            node.state = (c, h)
        else:
            assert len(node.children) == 2

            self.subexpr_embed(node_embedding, node.children[0])
            self.subexpr_embed(node_embedding, node.children[1])

            lc, lh = node.children[0].state
            rc, rh = node.children[1].state

            i = F.sigmoid(self.ix(x_embed) + self.ilh(lh) + self.irh(rh))
            fx = self.fx(x_embed)
            lf = F.sigmoid(fx + self.lflh(lh) + self.lfrh(rh))
            rf = F.sigmoid(fx + self.rflh(lh) + self.rfrh(rh))

            update = F.tanh(self.ux(x_embed) + self.ulh(lh) + self.urh(rh))
            c =  i* update + lf*lc + rf*rc
            h = F.tanh(c)

            node.state = (c, h)
