#!/usr/bin/env python

import subprocess
import sys
import os
import shutil

import pickle
import gzip

def R(fpath):
    with open(fpath, 'r') as fin:
        return fin.read()

def save_zipped_pickle(obj, filename, protocol=-1):
    with gzip.open(filename, 'wb') as f:
        pickle.dump(obj, f, protocol)

def load_zipped_pickle(filename):
    with gzip.open(filename, 'rb') as f:
        loaded_object = pickle.load(f)
        return loaded_object

if len(sys.argv) != 2:
    print("usage: ", sys.argv[0], "pickle")
    exit()

pickle_f = sys.argv[1]

data = load_zipped_pickle(pickle_f)

print( len(data) )

show = True 
for x in data:
    json = x[0]
    s1,s2,s3,s4 = x[1]
    if show:
        print("json:", json)
        print("s1",s1, "s4",s4)
        show = False

