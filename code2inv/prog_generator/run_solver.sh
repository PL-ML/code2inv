#!/bin/bash

data_folder=../../benchmarks
file_list=names.txt

inv_reward_type=ordered
single_sample=$1
rl_batchsize=10
embedding=128
s2v_level=20
model=AssertAwareTreeLSTM
att=1
ac=0
ce=1
save_dir=$HOME/scratch/results/code2inv/benchmarks

if [ ! -e $save_dir ];
then
    mkdir -p $save_dir
fi

mkdir -p tests/results

log_file=$save_dir/log-sample-${single_sample}-model-${model}-r-${inv_reward_type}-s2v-${s2v_level}-bsize-${rl_batchsize}-att-${att}-ac-${ac}-ce-${ce}.txt

python -u ootb_solver_main.py \
    -data_root $data_folder \
    -exit_on_find 1 \
    -attention $att \
    -use_ce $ce \
    -aggressive_check $ac \
    -decoder_model $model \
    -only_use_z3 1 \
    -max_and 3 \
    -single_sample $single_sample \
    -max_or 2 \
    -max_depth 2 \
    -list_op +,- \
    -s2v_level $s2v_level \
    -embedding_size $embedding \
    -rl_batchsize $rl_batchsize \
    -file_list $file_list \
    -inv_reward_type $inv_reward_type \
    -save_smt "tests/results/result_$1" \
    2>&1 | tee $log_file
