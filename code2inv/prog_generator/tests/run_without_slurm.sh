#!/bin/bash

if (( $# != 3 ))
then
	echo -e "Usage:- ./run_without_slurm.sh <exp> <time limit> <log directory>\n<exp> can be one of c, c_nl, chc, chc_nl, learning, fine_tuning, fine_tuning_untrained"
	echo -e "<log directory> must not exist"
	exit
fi

exp="$1"
timelim="$2"
log_dir="$3"

if [ -d "$log_dir" ]
then
	echo "Error: $log_dir directory exists"
fi

numlist="${exp}_numlist.txt"
if [[ "$exp" == "learning" || "$exp" == "fine_tuning" || "$exp" == "fine_tuning_untrained" ]]
then
	test_script="test_${exp}.sh"
else
	test_script="test_${exp}_inv.sh"
fi

log_script="get_log_$exp.sh"

mkdir -p tmp
mkdir -p $log_dir
rm $log_dir/* 2>/dev/null

while read benchnum
do
	echo "Testing benchmark $benchnum"
	timeout $timelim ./$test_script $benchnum > tmp/$benchnum.out
	if [ $? -eq 124 ]
	then
		echo "TIMEOUT"
	else
		if [ $exp != "learning" ]
		then
			./$log_script tmp/$benchnum.out > $log_dir/$benchnum-log
		fi
	fi
done < $numlist
