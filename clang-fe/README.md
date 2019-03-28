# clang-fe

A front end to code2inv responsible for transforming code into its SSA form and also generating Verification Conditions using Clang.

## Installation

Refer [INSTALL.md](INSTALL.md).

## Run the executable

To run any of the test codes inside the tests directory, cd into tests/ and run `../bin/clang-fe -ssa filename.c`. This will produce a json file of the same name with the ssa graph in it. To run all tests, run `make tests` (for no debug output) or `make test-debug` for debug output (which includes the CFG, Dominator Tree and the SSA Graph).

To generate Verification Conditions, run `./bin/clang-fe -smt ../benchmarks/c/<filename>`. Only the files under benchmarks have been tested with VC Generation. To only store the SMT graph, run `./bin/clang-fe -smt ../benchmarks/c/<filename> > smtfile.smt 2>/dev/null`.

## Notes
The renaming and phi function placement algorithms are taken from http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.100.6361&rep=rep1&type=pdf.

Clang-fe has only been tested on the programs under the tests directory taken from https://github.com/sosy-lab/sv-benchmarks/tree/master/c/loop-invgen and the benchmarks directory.

## Known Issues
<ul>
    <li> The program crashes if a non-existent file is passed as the argument.</li>
    <li> The program simply ignores any errors it encounters in the C code. </li>
</ul>