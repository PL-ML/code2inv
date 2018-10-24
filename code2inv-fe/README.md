# Code2Inv-fe


Code2Inv-fe is the front end for Code2Inv framework, which is based on the static analyzer [Sparrow](https://github.com/ropas/sparrow).

Code2Inv-fe takes a C program as input and outputs program graph in [JSON](https://www.json.org/) format and verification conditions (VC) in [SMT-LIB 2](http://smtlib.cs.uiowa.edu/) format. 

## Dependencies and Setup

1. Please refer to the set-up instructions of [Sparrow](https://github.com/ropas/sparrow).
2. Run `make`

## Extract Program Graphs
```sh
# extract program graph
./bin/code2inv-fe -ssa a.c > graph/a.json

# extract verification conditions
./bin/code2inv-fe -smt2 a.c > smt2/a.smt

# pre-process VC
./bin/split_smt2.py  smt2/a.smt

# visualize program graph
./bin/code2inv-vis2  a.json # will produce a.json.svg

# insert confounding variables 
./bin/code2inv-fe -c -junk 1 a.c > a.j1.c
```
