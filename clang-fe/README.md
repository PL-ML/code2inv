# clang-fe
A front end to code2inv responsible for transforming code into its SSA form using Clang.
# Installation
First get the dependencies
<ul>
    <li> LLVM </li>
    <li> The Clang API</li>
</ul>
Get them at https://clang.llvm.org

Then run `make` while inside the ssa-transform directory. This should make an executable named ssa-transform.

You may need to edit the include variables of make if llvm-config does not include the clang include directory or produces linker errors.

# Run the executable

To run any of the test codes inside the tests directory, cd into tests/ and run `../bin/ssa-transform filename.c`. This will produce a json file of the same name with the ssa graph in it. To run all tests, run `make tests` (for no debug output) or `make test-debug` for debug output (which includes the CFG, Dominator Tree and the SSA Graph).

# Notes
The renaming and phi function placement algorithms are taken from http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.100.6361&rep=rep1&type=pdf

Clang-fe has only been tested on the programs under the tests directory, taken from https://github.com/sosy-lab/sv-benchmarks/tree/master/c/loop-invgen

# Known Issues
<ul>
    <li> The program crashes if a non-existent file is passed as the argument.</li>
    <li> The program crashes if undefined keywords are used (for eg. using the assert keyword without including assert.h) </li>
</ul>