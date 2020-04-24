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

./pretraining.sh j5_pickle $num 0 specs/c_spec  
