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

file=$(cat ../../benchmarks/names.txt | head -$(($num+1)) | tail -1)
echo $file
./run_solver_file.sh ../../benchmarks/C_instances/c_graph/$file.json ../../benchmarks/C_instances/c_smt2/$file.smt specs/c_spec 
