#!/bin/bash

num=$1

# timeout 5m ./run_solver.sh $num
cd ..

./run_solver.sh $num

cd tests

if [ $? -eq 124 ]
then
    echo "Time's up"
    tput bel
    exit 1
fi

file=$(cat ../../../benchmarks/names.txt | head -$(($num+1)) | tail -1)

mkdir -p tmp-test

cp ../../../benchmarks/smt2/$file.smt tmp-test/smt2testfile_$num.smt

# slice files

cd tmp-test

orgifs=$IFS
prevline=0
body=()
for line in $(grep -n "SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop" smt2testfile_$num.smt | cut -f1 -d:)
do
    # IFS=
    # echo $line
    s=$(cat smt2testfile_$num.smt | head -$((line-1)) | tail -$((line-prevline)))
    body+=("$s")
    # echo -e "\n\nSEPERATOR\n\n"
    # echo $s
    prevline=$((line+1))
    # IFS=$orgifs
done

totalLines=$(wc -l smt2testfile_$num.smt | awk '{ print $1 }')

s=$(cat smt2testfile_$num.smt | tail -$((totalLines-line)))
body+=("$s")

# making 3 separate assert versions of the file

# top
echo "${body[0]}" > smt2testfile_$num.smt.1

# pre
echo -e "${body[1]}\n${body[2]}" > smt2testfile_$num.smt.2

# trans
echo -e "${body[1]}\n${body[3]}" > smt2testfile_$num.smt.3

# post
echo -e "${body[1]}\n${body[4]}" > smt2testfile_$num.smt.4

../check.sh ../results/result_$num smt2testfile_$num > test_$num

diff test_$num control && echo "Success" && tput bel && exit 0 || echo "Failed" && tput bel && exit 1

