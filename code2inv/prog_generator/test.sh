#!/bin/bash

num=$1

timeout 5m ./run_solver.sh $num

if [ $? -eq 124 ]
then
    echo "Time's up"
    tput bel
    exit 1
fi

file=$(cat ../../benchmarks/names.txt | head -$(($num+1)) | tail -1)

mkdir -p tmp

../../clang-fe/bin/clang-fe -smt ../../benchmarks/c/$file > tmp/smt2testfile.smt

# slice files
orgifs=$IFS
prevline=0
body=()
for line in $(grep -n "SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop" smt2testfile.smt | cut -f1 -d:)
do
    # IFS=
    # echo $line
    s=$(cat smt2testfile.smt | head -$((line-1)) | tail -$((line-prevline)))
    body+=("$s")
    # echo -e "\n\nSEPERATOR\n\n"
    # echo $s
    prevline=$((line+1))
    # IFS=$orgifs
done

totalLines=$(wc -l smt2testfile.smt | awk '{ print $1 }')

s=$(cat smt2testfile.smt | tail -$((totalLines-line)))
body+=("$s")

# making 3 separate assert versions of the file

# top
echo "${body[0]}" > tmp/smt2testfile.smt.1

# pre
echo -e "${body[1]}\n${body[2]}" > tmp/smt2testfile.smt.2

# trans
echo -e "${body[1]}\n${body[3]}" > tmp/smt2testfile.smt.3

# post
echo -e "${body[1]}\n${body[4]}" > tmp/smt2testfile.smt.4

cd tmp

../check.sh ../result smt2testfile > test

diff test control && echo "Success" && tput bel && exit 0 || echo "Failed" && tput bel && exit 1

