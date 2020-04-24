
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
$ ./run_solver_file.sh $graph_file $vc_file $specification_file -o output_file
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
### Setting up the invariant grammar

The invariant grammar is a combination of grammar productions as such:-<br>
NT `::=` production_rule_1 `|` production_rule_2 `|` ...

Restrictions:<br>
* There are fixed terminals to denote variables and constants, namely `var` and `const` respectively. These terminals must be used in the invariant grammar wherever variables and constants are expected.
* The start symbol for the grammar is always `S` and so every invariant grammar must include the `S` non terminal.
* Each invariant is considered to have an expression in terms of atomic predicates whose grammar is given by the non-terminal `p`. So every invariant grammar must include the `p` non terminal, and the non terminals `S` and `p` should relate to each other through production rules.

An example of a valid invariant grammar is:

```
S ::= ( C ) | ( C && C ) | ( C && C && C )
C ::= ( p ) | ( p  "||" p )
p ::= var cmp expr
expr ::= ( var op var ) | ( var op const ) | ( const op var ) | ( const op const ) | var | const
cmp ::= < | > | == | <= | >=
op ::= + | -
```

You can see more grammar examples in the `code2inv/prog_generator/grammar_files` directory.

### Specification Files

The specification file is a file as such:

```
name_of_inv_grammar_file
name_of_solver_script (in the format of a python package)
var_format (ssa if graph has core variables in the ssa format (for example in the C instances), leave blank if not)
```

Refer to the spec files in `spec/` directory as an example

## Running with pretraining and fine-tuning

### Pretraining: 

```
$ cd code2inv/prog_generator
```
Then run:
```
$ ./pretraining.sh ${dataset} ${prog_idx} ${agg_check} ${grammar_file}
```
where ```dataset``` is the data name, ```prog_idx``` stands for the set of random perturbed programs, and ```agg_check``` can be 0 or 1, denoting whether more aggressive checker should be used.

An easier way would be to run 
```
$ cd tests; ./test_learning.sh ${prog_idx}
```

### Fine-tuning:
```
$ cd code2inv/prog_generator
```
Then run:
```
$ ./fine_tuning.sh ${dataset} ${prog_idx} ${agg_check} ${init_epoch} ${grammar_file}
```
where the penultimate argument ```init_epoch``` stands for the model dump of corresponding epoch (`latest` for the latest epoch dumped). 
An easier way would be to run 
```
$ cd tests; ./test_fine_tuning.sh ${prog_idx}
```

## Running Batch Experiments
Read the instructions in the BATCH_EXPERIMENT_INSTRUCTIONS.txt file or the code2inv/prog_generator/tests directory

## Getting the plots
Read the instructions in the GRAPH_REPRODUCTION_INSTRUCTIONS.txt file

## Referring to existing logs
We have included the logs for experiments conducted on our servers under the logs directory in the repository root directory. Each folder stands for an experiment with each file under that including the logs for a particular sample. The csv files are the combined logs for the C and CHC linear experiments (`|` is considered the delimiter).

<!-- # Reference

    @inproceedings{si2018nips,
        author    = {Si, Xujie and Dai, Hanjun and Raghothaman, Mukund and Naik, Mayur and Song, Le},
        title     = {Learning Loop Invariants for Program Verification.},
        year      = {2018},
        booktitle = {Advances in Neural Information Processing Systems (NeurIPS)},
    }
 -->


