#!/bin/bash

dropbox=../../dropbox

dataset=$1

data_folder=$dropbox/sc_hard/py2_training_${dataset}
file_list=list.txt

inv_reward_type=ordered
single_sample=$2
rl_batchsize=10
embedding=128
s2v_level=20
att=1
agg_check=$3
ce=1
model=AssertAwareTreeLSTM

save_dir=$HOME/scratch/results/learn_loop_invariant/sc_hard-$dataset/model-${model}-r-${inv_reward_type}-s2v-${s2v_level}-sample-${single_sample}-att-${att}-ac-${agg_check}-ce-${ce}

if [ ! -e $save_dir ]; 
then
    mkdir -p $save_dir
fi

init_epoch=$4
log_file=$save_dir/test-log-e-${init_epoch}.txt

python -u train_test.py \
    -save_dir $save_dir \
    -only_use_z3 1 \
    -use_ce $ce \
    -data_root $data_folder \
    -tune_test 1 \
    -attention $att \
    -num_epochs 52 \
    -aggressive_check $agg_check \
    -init_model_dump $save_dir/epoch-${init_epoch} \
    -phase test \
    -single_sample $single_sample \
    -decoder_model $model \
    -max_and 3 \
    -max_or 2 \
    -max_depth 2 \
    -list_op +,- \
    -s2v_level $s2v_level \
    -embedding_size $embedding \
    -rl_batchsize $rl_batchsize \
    -file_list $file_list \
    -inv_reward_type $inv_reward_type \
    2>&1 | tee $log_file

