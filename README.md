
# Environment Setup

## Basic Setup
- python-2.7 
- PyTorch 0.4.0
- python library: numpy, tqdm, pyparsing
- gcc/g++ 5.4.0 (or higher)
- make, cmake

## Z3 Setup
code2inv uses the Z3 theorem prover to verify the correctness of generated loop invariants. Follow these steps to build Z3:

1. Clone the source code of Z3 from https://github.com/Z3Prover/z3
2. Run ```python scripts/mk_make.py --prefix /usr/local/; cd build; make -j16; make install ```

Remember to set environment variables DYLD_LIBRARY_PATH and PYTHONPATH to contain paths for Z3 shared libraries and Z3Py, respectively.  These paths will be indicated upon successful installation of Z3.

## Frontend Setup (Optional)
The frontend is used to extract program graphs and verification conditions (VCs) from the input C programs. The program graphs and VCs for our benchmarks are already included in the `benchmarks` directory.  To build the frontend, follow the instructions in README in `clang-fe`. 


# Experiments

## Package Installation

Install the dev version of this package:

```pip install -e .```

## Running as an out-of-the-box solver

```cd code2inv/prog_generator```, then directly run the script ```./run_solver.sh```

To modify the script ```run_solver.sh```:

1. Set the ```data_folder``` option to the code folder that contains folders ```graph/``` and ```smt2/``` which are created by the front-end pre-processor
2. Set the ```file_list``` option to the file that contains a list of code names.  See ```code2inv/benchmarks/names.txt``` as an example.
3. Set the ```single_sample``` option to be the index of code where you want to find the loopinv for.
4. Adjust other parameters if necessary. Make sure to change parameters like ```max_and, max_or, max_depth, list_op``` to make sure the loopinv space is large enough (but not too large).

## Running with pretraining and fine-tuning

### Pretraining: 

```cd code2inv/prog_generator```
Then run:
```./pretraining.sh ${dataset} ${prog_idx} ${agg_check}```
where ```dataset``` is the data name, ```prog_idx``` stands for the set of random perturbed programs, and ```agg_check``` can be 0 or 1, denoting whether more aggressive checker should be used. 

### Fine-tuning:
```cd code2inv/prog_generator```
Then run:
```./fine_tuning.sh ${dataset} ${prog_idx} ${agg_check} ${init_epoch}```
where the last argument ```init_epoch``` stands for the model dump of corresponding epoch. 




# Reference

    @inproceedings{si2018nips,
        author    = {Si, Xujie and Dai, Hanjun and Raghothaman, Mukund and Naik, Mayur and Song, Le},
        title     = {Learning Loop Invariants for Program Verification.},
        year      = {2018},
        booktitle = {Advances in Neural Information Processing Systems (NeurIPS)},
    }



