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


if len(sys.argv) != 4:
    print("usage: ", sys.argv[0], "baseline","neural","general") 
    exit()

baseline = list( map(int, R(sys.argv[1])) )
neural = list( map(int, R(sys.argv[2])) )
general = list( map(int, R(sys.argv[3])) )

#neural = [x * 10 for x in neural]

baseline.sort()
neural.sort()
general.sort()


acc_bs = baseline
acc_nn = neural
acc_gen = general

plt.xlim(1,110)
plt.yscale('log')

xs = np.arange(1,len(baseline)+1)
plt.plot(xs, acc_bs, 'bo', label='C2I')

xs = np.arange(1, len(neural)+1)
plt.plot(xs, acc_nn, 'g^', label='Code2Inv-S')

xs = np.arange(1, len(general)+1)
plt.plot(xs, acc_gen, 'r^', label='Code2Inv-G')

x_ticks = [10 * x for x in range(11)]

plt.xticks(x_ticks)

plt.ylabel('# trials', fontsize=18)
plt.xlabel('# instances solved', fontsize=18)
plt.grid(True)

ax = plt.gca()
for item in ([ax.xaxis.label, ax.yaxis.label] +
             ax.get_xticklabels() + ax.get_yticklabels()):
    item.set_fontsize(16)
#plt.legend(bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
plt.legend(fontsize=16)

#plt.show()
plt.savefig('nprogs.pdf', bbox_inches='tight')
