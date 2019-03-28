#!/bin/bash

inv=$(cat $1)
top=$(cat $2.smt.1)
pre=$(cat $2.smt.2)
loop=$(cat $2.smt.3)
post=$(cat $2.smt.4)

# for pre
echo -e "$top\n$inv\n$pre\n(check-sat)" > tmppre
z3 -smt2 tmppre

# for loop
echo -e "$top\n$inv\n$loop\n(check-sat)" > tmploop
z3 -smt2 tmploop


# for post
echo -e "$top\n$inv\n$post\n(check-sat)" > tmppost
z3 -smt2 tmppost