#!/bin/bash

if [ "$#" -ne 4 ]
then
	echo "Usage $0 exp_type timelimit -o output"
	echo "exptype can be one of c, chc, c_nl, chc_nl, learning, fine_tuning or fine_tuning_untrained. Refer to BATCH_EXPERIMENT_INSTRUCTIONS.txt for more information"
	echo "eg: $0 c 12h -o logs-c-noslurm"
	echo "eg: $0 learning 12h -o logs-learning-noslurm"
	exit
else
	if [[ "$1" == "c" || "$1" == "chc" || "$1" == "c_nl" || "$1" == "chc_nl" || "$1" == "learning" || "$1" == "fine_tuning" || "$1" == "fine_tuning_untrained" ]] && [ "$3" == -o ]
	then
		exp="$1"
		timelim="$2"
		op_dir="$4"
	else
		echo "Usage $0 exp_type timelimit -o output"
		echo "exptype can be one of c, chc, c_nl, chc_nl, learning, fine_tuning or fine_tuning_untrained. Refer to BATCH_EXPERIMENT_INSTRUCTIONS.txt for more information"
		echo "eg: $0 c 12h -o logs-c-noslurm"
		echo "eg: $0 learning 12h -o logs-learning-noslurm"
		exit
	fi
fi

cd code2inv/prog_generator/tests

rm -rf "../../../$op_dir"

./run_without_slurm.sh $exp $timelim "../../../$op_dir"
