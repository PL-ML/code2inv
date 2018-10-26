

# Environment Setup

## Basic Setup
- python-2.7 
- PyTorch 0.4.0
- python library: numpy, tqdm, pyparsing
- gcc/g++ 5.4.0 (or higher)
- make, cmake

## Z3 Setup
Z3 is the theorem prover we used to verify the corrrectness of generated loop invariant. To build z3, please follow:

1. Download and unzip Z3 source code from https://github.com/Z3Prover/z3/releases/tag/z3-4.4.0
2. ```python scripts/mk_make.py --prefix /usr/local/; cd build; make -j16; make install ```

## Frontend Setup (Optional)
Frontend is used to extract program graphs and verifcation conditions from C programs. The program graphs and VCs for our benchmark are already included in `benchmarks`.  To build the frontend, please follow the README in `code2inv-fe`. 


# Experiments

## Package Install

Install the dev version of this package:

```pip install -e .```

## Run as out-of-the-box solver:

```cd code2inv/prog_generator```, then directly run the script ```./run_solver.sh```

To modify the script ```run_solver.sh```:

1. Set ```data_folder``` option to the code folder that contains folders: ```graph/``` and ```smt2/``` which are created by the front-end pre-processor
2. Set ```file_list``` option to the file that contains a list of code names. See ```code2inv/benchmarks/names.txt``` as an example.
3. Set ```single_sample``` to be the index of code where you want to find the loopinv for.
4. Adjust other parameters if necessary. Make sure to change the parameters like ```max_and, max_or, max_depth, list_op``` to make sure the loopinv space is large enough (but not too large).

## Run by pretraining and fine-tuning:

### Pretraining: 

```cd code2inv/prog_generator```
The do:
```./pretraining.sh ${dataset} ${prog_idx} ${agg_check}```
where ```dataset``` is the data name, ```prog_idx``` stands for the set of random perturbed programs, and ```agg_check``` can be 0 or 1, denotes whether more aggressive checker should be used. 

### fine-tuning:
```cd code2inv/prog_generator```
The do:
```./fine_tuning.sh ${dataset} ${prog_idx} ${agg_check} ${init_epoch}```
where the last argument ```init_epoch``` stands for the model dump of corresponding epoch. 






