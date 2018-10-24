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

from code2inv.common.ssa_graph_builder import ProgramGraph, GraphNode
from code2inv.common.constants import AC_CODE, NUM_EDGE_TYPES, LIST_PREDICATES, LIST_OP, MAX_DEPTH, MAX_AND, MAX_OR, INVALID_CODE, NORMAL_EXPR_CODE
from code2inv.common.cmd_args import cmd_args, tic, toc
from code2inv.common.checker import stat_counter, boogie_result
from code2inv.common.dataset import Dataset 

from code2inv.graph_encoder.embedding import EmbedMeanField
from code2inv.prog_generator.rl_helper import rollout, actor_critic_loss
from code2inv.prog_generator import tree_decoder


if __name__ == '__main__':
    random.seed(cmd_args.seed)
    np.random.seed(cmd_args.seed)
    torch.manual_seed(cmd_args.seed)    
    tic() 
    dataset = Dataset()

    params = []

    encoder = EmbedMeanField(cmd_args.embedding_size, len(dataset.node_type_dict), max_lv=cmd_args.s2v_level)
    decoder_class = getattr(tree_decoder, cmd_args.decoder_model + 'Decoder')
    decoder = decoder_class(cmd_args.embedding_size)
    
    if cmd_args.init_model_dump is not None:
        encoder.load_state_dict(torch.load(cmd_args.init_model_dump + '.encoder'))
        decoder.load_state_dict(torch.load(cmd_args.init_model_dump + '.decoder'))
        
    params.append( encoder.parameters() )
    params.append( decoder.parameters() )
    
    optimizer = optim.Adam(chain.from_iterable(params), lr=cmd_args.learning_rate)    
    
    for epoch in range(cmd_args.num_epochs):
        best_reward = -5.0
        best_root = None
        tested_roots = []
                
        acc_reward = 0.0
        pbar = tqdm(range(100), file=sys.stdout)
        for k in pbar:
            
            g_list = dataset.sample_minibatch(cmd_args.rl_batchsize, replacement = True)
            node_embedding_batch = encoder(g_list)

            total_loss = 0.0
            embedding_offset = 0
            for b in range(cmd_args.rl_batchsize):
                if cmd_args.single_sample is None:
                    g = g_list[b]
                    node_embedding = node_embedding_batch[embedding_offset : embedding_offset + g.pg.num_nodes(), :]
                    embedding_offset += g.pg.num_nodes()
                else:
                    g = g_list[0]
                    node_embedding = node_embedding_batch
                nll_list, value_list, reward_list, root = rollout(g, node_embedding, decoder, use_random = True, eps = 0.05)  

                tested_roots.append(root)
                if reward_list[-1] > best_reward:
                    best_reward = reward_list[-1]
                    best_root = root

                acc_reward += np.sum(reward_list) / cmd_args.rl_batchsize                          
                loss = actor_critic_loss(nll_list, value_list, reward_list)      
                total_loss += loss   
            optimizer.zero_grad()                    
            loss = total_loss / cmd_args.rl_batchsize
            loss.backward()
            optimizer.step()
            pbar.set_description('avg reward: %.4f' % (acc_reward / (k + 1)))
        
        g = dataset.sample_minibatch(1, replacement = True)[0]
        node_embedding = encoder(g)
        _, _, _, root = rollout(g, node_embedding, decoder, use_random = True, eps = 0.0)
        
        print('epoch: %d, average reward: %.4f, Random: %s, result_r: %.4f' % (epoch, acc_reward / 100.0, root, boogie_result(g, root)))
        print("best_reward:", best_reward, ", best_root:", best_root)
        stat_counter.report_global()
        if cmd_args.save_dir is not None:
            torch.save(encoder.state_dict(), cmd_args.save_dir + '/epoch-%d.encoder' % epoch)
            torch.save(decoder.state_dict(), cmd_args.save_dir + '/epoch-%d.decoder' % epoch)
            torch.save(encoder.state_dict(), cmd_args.save_dir + '/epoch-latest.encoder')
            torch.save(decoder.state_dict(), cmd_args.save_dir + '/epoch-latest.decoder')
