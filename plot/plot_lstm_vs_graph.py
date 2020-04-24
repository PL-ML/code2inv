#!/usr/bin/env  python3

import numpy as np
import matplotlib.pyplot as plt

import os
import sys


def R(fpath):
    with open(fpath, "r") as fin:
        return fin.read().splitlines()

def acc(xs):
    s = 0
    r = []
    for x in xs:
        s += x
        r.append(s)
    return r


if len(sys.argv) != 3: 
    print("usage: ", sys.argv[0], "lstm_z3.txt", "graph_z3.txt")
    exit()

lb = ['LSTM','Graph Embedding']
# load data
lss = []
for f in sys.argv[1:]:
    ls = list(map(int, R(f)))
    lss.append(  sorted(ls) )
    


# plot data

colors = ['b','y','r','g']
#shapes = ['^','o','-','s']
shapes = ['-','-','-','-']

plt.xlim(1,108)
plt.yscale('log')

for i in range(len(lss)):
    ls = lss[i]
    xs = np.arange(1, len(ls)+1)
    cl = colors[i]
    sh = shapes[i]
    
    plt.plot(xs, ls, cl+sh, label=lb[i], linewidth=2)
    

x_ticks = [10 * x for x in range(11)]
plt.xticks(x_ticks)

plt.ylabel('# Z3 queries', fontsize=18)
plt.xlabel('# instances solved ', fontsize=18)
plt.grid(True)
ax = plt.gca()
for item in ([ax.xaxis.label, ax.yaxis.label] +
             ax.get_xticklabels() + ax.get_yticklabels()):
    item.set_fontsize(16)
#plt.legend(bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
plt.legend(fontsize=16)

#plt.show()
plt.savefig('lstm_vs_graph.pdf',  bbox_inches='tight')

