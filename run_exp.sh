#!/bin/bash

if [ "$#" -ne 3 ]
then
	echo "Usage: $0 exptype -o output_dir"
	echo "exptype can be one of c, chc, c_nl, chc_nl, learning, fine_tuning or fine_tuning_untrained. Refer to BATCH_EXPERIMENT_INSTRUCTIONS.txt for more information"
	echo "For example: $0 c -o logs-artifact-c"
	exit
else
	if [[ "$1" == "c" || "$1" == "chc" || "$1" == "c_nl" || "$1" == "chc_nl" || "$1" == "learning" || "$1" == "fine_tuning" || "$1" == "fine_tuning_untrained" ]] && [ "$2" == "-o" ]
        then
                test_type="$1"
                op_dir="$3"
        else
                echo "Usage: $0 exptype -o output_dir"
                echo "exptype can be one of c, chc, c_nl, chc_nl, learning, fine_tuning or fine_tuning_untrained. Refer to BATCH_EXPERIMENT_INSTRUCTIONS.txt for more information"
                echo "For example: $0 c -o logs-artifact-c"
                exit
        fi
fi

cd code2inv/prog_generator/tests
rm -rf "../../../$op_dir"

python run.py cluster_$test_type.sub ${test_type}_numlist.txt "../../../$op_dir"
