
# Code2Inv

# Environment Setup

## Using the Docker Container

An easy way to get Code2Inv up and running is to build it using the Dockerfile we have provided.

You can either pull the docker image from our dockerhub repo:
```
docker pull code2inv/code2inv
```

or build the docker container yourself by running the following command in the repo's root directory:
```
$ docker build -t code2inv/code2inv docker/
```

This should create an image called `code2inv/code2inv`. To see all the docker images, run
```
$ docker images
```

Create the docker container:
```
$ docker run -it --name code2inv code2inv/code2inv
```

This should open a docker container with all code2inv setup completed.

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

Remember to set environment variables `LD_LIBRARY_PATH` and `PYTHONPATH` to contain paths for Z3 shared libraries and Z3Py, respectively.  These paths will be indicated upon successful installation of Z3.

## Frontend Setup (Optional)
There are two frontends, one each for the C and CHC instances. The C frontend is called clang-fe and can be found in the `clang-fe/` directory. The CHC frontend is called chc-fe and is located in the `chc-fe/` directory. These frontends have limited support and are tested with the benchmarks included. Primarily, they can be used with programs containing single loops.

The `clang-fe` frontend is used to extract program graphs and verification conditions (VCs) from the input C programs. This will be a necessary step if you wish to run Code2Inv on a C file which isn't in the benchmarks. The program graphs and VCs for our benchmarks are already included in the `benchmarks/C_instances` directory and the same for the Non Linear benchmarks are included in the `benchmarks/nl-bench/` directory.  To build the frontend, follow the instructions in [README](clang-fe/README.md) in `clang-fe`. 

The `chc-fe` frontend is used to extract program graphs from the input CHC programs (the CHC constraints themselves serve as the verification conditions (VCs)). This will be necessary to run Code2Inv for constraints not included in the benchmarks. The graphs and the VCs are already included in the `benchmarks/CHC_instances` directory. To run the CHC frontend, follow the instructions in [README](chc-fe/README) in `chc-fe`.

# Experiments

## Package Installation

First, install the dev version of this package. To do this, run the following in the repository root directory:

```
$ pip install -e .
```

## Running as an out-of-the-box solver

First change directory as follows:
```
$ cd code2inv/prog_generator
```

Directly run the solver script:
```
$ ./run_solver_file.sh $graph_file $vc_file $specification_file
```

To assign the output and related logs to a file, you can add the optional `-o` argument: 
```
$ ./run_solver_file.sh $graph_file $vc_file $specification_file \
-o output_file
```

### Examples

To run code2inv on one of the 133 Linear C instances:
```
$ ./run_solver_file.sh ../../benchmarks/C_instances/c_graph/101.c.json ../../benchmarks/C_instances/c_smt2/101.c.smt specs/c_spec
```

Optionally, to store the result and related logs into an output file `inv_result.txt`:
```
$ ./run_solver_file.sh ../../benchmarks/C_instances/c_graph/101.c.json ../../benchmarks/C_instances/c_smt2/101.c.smt specs/c_spec -o inv_result.txt
```

Some of other benchmarks which give an answer relatively quick include: 102.c, 53.c, 56.c, 65.c, 18.c, 98.c. Just substitute 101.c in the previous command with one of these benchmarks to get the solution for the same.

To run code2inv on one of the 120 Linear CHC instances:

```
$ ./run_solver_file.sh ../../benchmarks/CHC_instances/sygus-constraints-graphs/sygus-bench-101.c.smt.json ../../benchmarks/CHC_instances/sygus-constraints/sygus-bench-101.c.smt specs/chc_spec
```

Optionally, to store the result and related logs into an output file `inv_result.txt`: 

```
$ ./run_solver_file.sh ../../benchmarks/CHC_instances/sygus-constraints-graphs/sygus-bench-101.c.smt.json ../../benchmarks/CHC_instances/sygus-constraints/sygus-bench-101.c.smt specs/chc_spec -o inv_result.txt
```

Some of other benchmarks which give an answer relatively quick include: 78.c, 115.c, 45.c, 54.c, 71.c, 77.c. Just substitute 101.c in the previous command with one of these benchmarks to get the solution for the same.

To use a different grammar file for the invariants, refer to the grammar section in the [customization guide](customizing.md#the-grammar-file).

For general customization, check out the [customization guide](customizing.md).

To run Code2Inv on your own C programs or CHC instances, you will have to use the frontends provided to generate the program graphs and the verification conditions.

<!--### Using Pretrained weights

To lower the amount of time needed for some benchmarks which take longer, we have provided pretrained weights for these benchmarks in the `weights.tar` file in the repository root directory. To use them, first extract the weights: `tar -xvf weights.tar`. This should create a directory with all necessary weights.
Then change directory `cd code2inv/prog_generator` and run
```
$./run_solver_file_with_weights.sh $graph_file $vc_file $specification_file $path_to_weights [ -o output_file ]
```

The same optional argument from earlier to denote the output file applies here as well.

The path_to_weights argument uses the path to the .encoder weight file without the extension.

for example,
```
$ ./run_solver_file_with_weights.sh ../../benchmarks/C_instances/c_graph/6.c.json ../../benchmarks/C_instances/c_smt2/6.c.smt specs/c_spec ../../weights/benchmarks/C_instances/c_graph/6.c.json/epoch-latest
```

Another example:
```
$ ./run_solver_file_with_weights.sh ../../benchmarks/C_instances/c_graph/69.c.json ../../benchmarks/C_instances/c_smt2/69.c.smt specs/c_spec ../../weights/benchmarks/C_instances/c_graph/69.c.json/epoch-latest -o inv_result
```
-->

### Process for running Code2Inv with C files

Code2Inv only supports C files with one loop and no external function calls (refer to `benchmarks/C_instances/c/` for examples of supported C programs).

We refer to the file as `file.c`.

First, we need our input files which are the program graph json file and verification conditions SMT2 file. Follow the README in `clang-fe/` and build the front-end. Then perform the following while in the `clang-fe/` directory:
```
$ ./bin/clang-fe -ssa file.c > file.c.json 2>/dev/null
$ ./bin/clang-fe -smt file.c > file.c.smt2 2>/dev/null
```

Our graph file is now `file.c.json` and verification condition file is `file.c.smt2`. Now from the repository directory, do the following:
```
$ cd code2inv/prog_generator
$ ./run_solver_file.sh file.c.json file.c.smt2 specs/c_spec -o file_inv.txt
```

After the solution is found (if it is found), you will see the solution and its logs printed on the screen (the line begins with `Found a solution for 0...`). There will also be a file called file_inv.txt created with this information.

### Process for running Code2Inv with CHC clauses

Code2Inv has only been tested on the CHC constraints corresponding to single loop C files obtained from Seahorn (refer to `benchmarks/CHC_instances/sygus-constraints` for examples of supported CHC constraints).

We refer to our file as `file.chc`.

First, we need our input files which are the program graph json file and the verification conditions file. The CHC file itself will serve as our verification condition file, so we only need to extract a program graph from it:
```
$ cd chc-fe
$ python graph-gen.py file.chc > file.json
```

Our graph file is now `file.json` and verification condition file is `file.chc`. From the repository directory, do the following:
```
$ cd code2inv/prog_generator
$ ./run_solver_file.sh file.c.json file.c.smt2 specs/c_spec -o file_inv.txt
```

After the solution is found (if it is found), you will see the solution and its logs printed on the screen (the line begins with `Found a solution for 0...`). There will also be a file called file_inv.txt created with this information.

## Running with pretraining and fine-tuning

### Pretraining: 

Run:

```
$ cd code2inv/prog_generator
```

```
$ ./pretraining.sh ${dataset} ${prog_idx} ${agg_check} ${grammar_file}
```

where ```dataset``` is the data name, ```prog_idx``` stands for the set of random perturbed programs, and ```agg_check``` can be 0 or 1, denoting whether more aggressive checker should be used.

An easier way would be to run 
```
$ cd tests; ./test_learning.sh ${prog_idx}
```

### Fine-tuning:

Run:

```
$ cd code2inv/prog_generator
$ ./fine_tuning.sh ${dataset} ${prog_idx} ${agg_check} ${init_epoch} ${grammar_file}
```

where the penultimate argument ```init_epoch``` stands for the model dump of corresponding epoch (`latest` for the latest epoch dumped). 
An easier way would be to run 

```
$ cd tests; ./test_fine_tuning.sh ${prog_idx}
```

<!-- # Reference

    @inproceedings{si2018nips,
        author    = {Si, Xujie and Dai, Hanjun and Raghothaman, Mukund and Naik, Mayur and Song, Le},
        title     = {Learning Loop Invariants for Program Verification.},
        year      = {2018},
        booktitle = {Advances in Neural Information Processing Systems (NeurIPS)},
    }
 -->


