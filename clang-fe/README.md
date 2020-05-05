# clang-fe

A front end to code2inv responsible for transforming code into its SSA form and also generating Verification Conditions using Clang.

## Installation

Refer [INSTALL.md](INSTALL.md).

## Run the executable

To generate the Program Graph, run
```
./bin/clang-fe -ssa ../benchmarks/C_instances/c/<filename>
```

To generate Verification Conditions, run
```
./bin/clang-fe -smt ../benchmarks/C_instances/c/<filename>
```
Only the files under benchmarks have been tested with VC Generation and Program Graph generation.

To only store the SMT conditions, run
```
./bin/clang-fe -smt ../benchmarks/C_instances/c/<filename> > smtfile.smt 2>/dev/null
```
and similarly for storing the Program Graphs
```
./bin/clang-fe -ssa ../benchmarks/C_instances/c/<filename> > graph.json 2>/dev/null
```
To generate the Verification Conditions in the SyGuS format, replace the -smt option with -sygus.

## Notes
The renaming and phi function placement algorithms are taken from http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.100.6361&rep=rep1&type=pdf.

Clang-fe has only been tested on the programs under the tests directory taken from https://github.com/sosy-lab/sv-benchmarks/tree/master/c/loop-invgen and the benchmarks directory.

## Known Issues
<ul>
    <li> The program crashes if a non-existent file is passed as the argument.</li>
    <li> The program simply ignores any errors it encounters in the C code. </li>
</ul>