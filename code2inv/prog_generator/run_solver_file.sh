#!/bin/bash

if(( $# != 3))
then
    echo "Usage- run_solver.sh <input_graph> <input_vcs> <grammar_file>"
    exit
fi

data_folder=../../benchmarks
file_list=names.txt

inv_reward_type=ordered
input_graph="$1"
input_vcs="$2"
grammar_file="$3"
rl_batchsize=10
embedding=128
s2v_level=20
model=AssertAwareTreeLSTM
att=1
ac=0
ce=1
save_dir=$HOME/scratch/results/code2inv/benchmarks/

if [ ! -e $save_dir ];
then
    mkdir -p $save_dir
fi

mkdir -p tests/results

log_file=$save_dir/log-sample-${single_sample}-model-${model}-r-${inv_reward_type}-s2v-${s2v_level}-bsize-${rl_batchsize}-att-${att}-ac-${ac}-ce-${ce}.txt

python -u file_solver.py \
    -input_graph $input_graph\
    -input_vcs $input_vcs\
    -exit_on_find 1 \
    -attention $att \
    -use_ce $ce \
    -aggressive_check $ac \
    -encoder_model "Param"\
    -decoder_model $model \
    -only_use_z3 1 \
    -s2v_level $s2v_level \
    -embedding_size $embedding \
    -rl_batchsize $rl_batchsize \
    -inv_reward_type $inv_reward_type \
    -inv_grammar $(sed "1q;d" $grammar_file)\
    -inv_checker $(sed "2q;d" $grammar_file)\
    -var_format "$(sed '3q;d' $grammar_file)"\
    -save_dir "$save_dir/$input_graph/"\
    2>&1 | tee $log_file
