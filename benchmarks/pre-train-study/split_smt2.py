#!/usr/bin/env python

import sys
import os


def R(fpath):
    with open(fpath, 'r') as fin:
        return fin.read().splitlines()

if len(sys.argv) != 2:
    print("Usage: ", sys.argv[0], "smt_file") 
    exit()


f = sys.argv[1]

if not os.path.isfile(f):
    print("cannot find smt2 file: ", f)
    exit()

rs = R(f)
smt2 = '\n'.join(rs)

cs = smt2.split('SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop')
#suffix = "\n(check-sat)\n(get-model)\n"

assert( len(cs) == 5 );

with open(f+".1", "w") as fout:
    fout.write( cs[0] )

for x in [2,3,4]:
    with open(f+ (".%d" % x), "w") as fout:
        fout.write( cs[1] + cs[x])

