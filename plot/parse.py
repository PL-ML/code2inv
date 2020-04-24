#!/usr/bin/env python3


import os
import sys
import pickle


def R(fpath):
    with open(fpath, 'r') as fin:
        return fin.read().splitlines()

#anfp-new.sl.0.c 23287 {'z3_pre': 1135855, 'boogie_result': 209948, 'actual_z3': 35}
def parse(line):
    line = line.replace(',', '')
    line = line.replace(':', '')
    line = line.replace("'", '')
    line = line.replace('{', '')
    line = line.replace('}', '')

    rs = line.split()
    bname = rs[0]
    updates = int(rs[1])
    i = 3
    L = len(rs)
    s = {}
    while i < L:
        key = rs[i]
        # print(rs)
        val = int(rs[i+1])
        s[key] = val
        i += 2

    return (bname, updates, s)


if len(sys.argv) != 2:
    print("usage: ", sys.argv[0], "dnn-log")
    exit()

lines = R( sys.argv[1] )

stats = {}
for l in lines:
    bn,up,d = parse(l)
    stats[bn] = (up,d)
    #print(d['actual_z3'])
    print(d['actual_z3'])

#pickle.dump(stats, open("dnn_stats.pickle",'wb') )



