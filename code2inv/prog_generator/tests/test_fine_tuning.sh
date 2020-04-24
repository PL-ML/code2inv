#!/bin/bash

num=$1

# timeout 5m ./run_solver.sh $num
cd ..

if [ $? -eq 124 ]
then
    echo "Time's up"
    tput bel
    exit 1
fi

./fine_tuning.sh j1_pickle $num 0 latest specs/c_spec
