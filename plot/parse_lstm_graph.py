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
    tm = float(rs[2])
    i = 3
    L = len(rs)
    s = {}
    while i < L:
        key = rs[i]
        val = int(rs[i+1])
        s[key] = val
        i += 2

    return (bname, updates, tm, s)


if len(sys.argv) != 2:
    print("usage: ", sys.argv[0], "dnn-log")
    exit()

lines = R( sys.argv[1] )

s = []

stats = {}
for l in lines:
    bn,up,tm,d = parse(l)
    stats[bn] = (up,d)
    if tm > 12 * 3600.0:
        #print('more than 12 hours, skip ', bn)
        continue

    s.append( (d['actual_z3'], bn) )
    #print(d['actual_z3'])
    #print(d['boogie_result'])

#s.sort(reverse=True)
s.sort()
for z,b in s:
    #print(z,b)
    print(z)
#for key in stats:
#    print(key)
#pickle.dump(stats, open("dnn_stats.pickle",'wb') )



