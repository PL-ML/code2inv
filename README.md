
# Environment Setup

## Basic Setup
The following are needed for running the basic setup
- python-3.7 
- PyTorch 0.4.0
- python library: numpy, tqdm, pyparsing
- gcc/g++ 5.4.0 (or higher)
- clang-7
- make, cmake

## Z3 Setup
code2inv uses the Z3 theorem prover to verify the correctness of generated loop invariants. Follow these steps to build Z3:
1. Clone the source code of Z3 from https://github.com/Z3Prover/z3
2. Run ```git checkout tags/z3-4.8.7; python scripts/mk_make.py --prefix=<installation_prefix> --python --pypkgdir=<python_site_package_directory>; cd build; make; make install```

Remember to set environment variables LD_LIBRARY_PATH and PYTHONPATH to contain paths for Z3 shared libraries and Z3Py, respectively.  These paths will be indicated upon successful installation of Z3.

## Frontend Setup (Optional)
There are two frontends, one each for the C and CHC instances. The C frontend is called clang-fe and can be found in the `clang-fe/` directory. The CHC frontend is called chc-fe and is located in the `chc-fe/` directory.

The `clang-fe` frontend is used to extract program graphs and verification conditions (VCs) from the input C programs. The program graphs and VCs for our benchmarks are already included in the `benchmarks/C_instances` directory and the same for the Non Linear benchmarks are included in the `benchmarks/nl-bench/` directory.  To build the frontend, follow the instructions in README in `clang-fe`. 

The `chc-fe` frontend is used to extract program graphs from the input CHC programs (the CHC constraints themselves serve as the verification conditions (VCs)). The graphs and the VCs are already included in the `benchmarks/CHC_instances` directory. To run the CHC frontend, follow the instructions in README in `chc-fe`.

# Experiments

## Package Installation

Install the dev version of this package:

```pip install -e .```

## Running as an out-of-the-box solver

```cd code2inv/prog_generator```, then directly run the script ```./run_solver_file.sh <graph_file.json> <vc_file> <specification_file>```. 

Eg- `./run_solver_file.sh ../../benchmarks/C_instances/c_graph/101.c.json ../../benchmarks/C_instances/c_smt2/101.c.smt specs/c_spec`

Eg- `./run_solver_file.sh ../../benchmarks/CHC_instances/sygus-constraints-graphs/sygus-bench-101.c.smt.json ../../benchmarks/CHC_instances/sygus-constraints/sygus-bench-101.c.smt specs/chc_spec`

The specification file is a file as such:

```
name_of_inv_grammar
name_of_solver_script (in the format of a python package)
var_format (ssa if graph has variables in the ssa format, leave blank if not)
```

Refer to the spec files in `spec/` directory as an example

## Running with pretraining and fine-tuning

### Pretraining: 

```cd code2inv/prog_generator```
Then run:
```./pretraining.sh ${dataset} ${prog_idx} ${agg_check} ${grammar_file}```
where ```dataset``` is the data name, ```prog_idx``` stands for the set of random perturbed programs, and ```agg_check``` can be 0 or 1, denoting whether more aggressive checker should be used. 

### Fine-tuning:
```cd code2inv/prog_generator```
Then run:
```./fine_tuning.sh ${dataset} ${prog_idx} ${agg_check} ${init_epoch} ${grammar_file}```
where the penultimate argument ```init_epoch``` stands for the model dump of corresponding epoch (`latest` for the latest epoch dumped). 




<!-- # Reference

    @inproceedings{si2018nips,
        author    = {Si, Xujie and Dai, Hanjun and Raghothaman, Mukund and Naik, Mayur and Song, Le},
        title     = {Learning Loop Invariants for Program Verification.},
        year      = {2018},
        booktitle = {Advances in Neural Information Processing Systems (NeurIPS)},
    }
 -->


