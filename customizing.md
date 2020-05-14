# Customizing Code2Inv for other inputs

Code2Inv allows you to customize the input language provided it is supplied with 3 major components-
1. The inputs (a graph file and verification condition file)
2. The specification file
3. A python module to check the invariant supplied and return the counter examples (we will call this the checker module)

We detail the specifics of each component.

## The Inputs

### The Graph File

The graph file contains one JSON object which describes the program graph.
This program graph will include nodes and control flows.

#### Nodes

Each node represents an instruction and the usage of the variable in that instruction.
For example, consider a snippet of code-
```c
...
assert(x > y);
y = y + 1;
...
```

The corresponding nodes in the JSON object would be written as-
```
{
    "nodes": {
        ...
        "17": {
            "cmd": "Assert",
            "rval": {
                "OP": ">=",
                "arg1": { "Var": "x_21" },
                "arg2": { "Var": "y_22" }
            }
        },
        "16": {
            "cmd": "assign",
            "lval": { "Var": "y_16" },
            "rval": {
                "OP": "+",
                "arg1": { "Var": "y_22" },
                "arg2": { "Const": "1" }
            }
        },
    },
    ...
}
```

There are several keys which can be used for each node object.

| Key | Stands for | Notes |
|-----|-------|--|
| `cmd` | Command | Denotes the role of the node. For example, `"cmd" : "Assert"` indicates that the node is an assertion node. Each node must have a `cmd` if it denotes an expression or an instruction.|
| `lval` | Left Value | Denotes the left value for relevant commands (like assign) |
| `rval` | Right Value | Denotes the right value for relevant commands (like assign) or any other associated value (like the assertion expression for assert commands). Compulsory if there is any associated value with the node.|
| `OP` | Operator | Denotes any associated operator |
| `Var` | Variable | Denotes that the value is a variable which must be considered in the invariant |
| `Const` | Constant | Denotes that the value is a constant which must be considered in the invariant |
| `argn` | Argument n | Denotes the nth argument |

While these are the important keys, any other key can be used.
Only the variables denoted under the `Var` key and constants in the `Const` key will be considered in the invariant generation.

#### Control Flow

The control flows are defined as an array of pairs, each pair being an array of two elements denoting the IDs of the nodes in question.
To denote a control flow from `node_1` to `node_2`, the pair will be written as `["node_1", "node_2"]`.

Once we add the control flows to the previously discussed example, we will get the final JSON object as-
```
{
    "nodes": {
        ...
        "17": {
            "cmd": "Assert",
            "rval": {
                "OP": ">=",
                "arg1": { "Var": "x_21" },
                "arg2": { "Var": "y_22" }
            }
        },
        "16": {
            "cmd": "assign",
            "lval": { "Var": "y_16" },
            "rval": {
                "OP": "+",
                "arg1": { "Var": "y_22" },
                "arg2": { "Const": "1" }
            }
        },
    },
    "control-flow": {
        ...
        ["17", "16"],
        ["ENTRY", "22"],
        ["22", "17"],
        ...
    }
}
```

Under the `benchmarks` directory, each subdirectory will have a subdirectory dedicated to the graph files for the instances. [An example graph file](benchmarks/C_instances/c_graph/101.c.json).

### The Verification Condition File

The Verification Condition file contains the verification conditions that will be used to check the correctness of the predicted invariant and get the counterexamples if any. These may be in any format, as long as the checker module is able to process them. [Here](benchmarks/C_instaances/c_smt2/101.c.smt) is an example of an SMT2 file and [here](benchmarks/CHC_instances/sygus-constraints/sygus-bench-101.c.smt) is an example of a CHC file.

The verification condition format for the C instances is the same as the one used in [SyGus 2017 Invariant Track](http://sygus.seas.upenn.edu/SyGuS-COMP2017.html). It consists of three parts: `pre-f`, `trans-f` and `post-f`, which corresponds the pre-condition, loop body and post-condition, respectively.

The CHC constraints serve as their own verification conditions.

## The Specification File

The specification file is a file as such:

```
name_of_inv_grammar_file
name_of_checker_module (in the format of a python package)
var_format (ssa if graph has core variables in the ssa format (for example in the C instances), leave blank if not)
```

Refer to the spec files in [`code2inv/prog_generator/specs/` directory](code2inv/prog_generator/specs) as an example.

### The Grammar File

The invariant grammar is a combination of grammar productions as such:-<br>
NT `::=` production_rule_1 `|` production_rule_2 `|` ...

Restrictions:<br>
* There are fixed terminals to denote variables and constants, namely `var` and `const` respectively. These terminals must be used in the invariant grammar wherever variables and constants are expected. They will be populated by some of the variables and constants denoted by `Var` and `Const` in the grammar file as discussed before.
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

You can see more grammar examples in the [`code2inv/prog_generator/grammar_files` directory](code2inv/prog_generator/grammar_files).

### The Name of the Checker Module

The name of the checker module (which we shall discuss in the next section) should be in the format of a python package relative to the `code2inv/prog_generator` directory.
For example, if the checker module is `code2inv/prog_generator/checkers/c_inv_checker.py`, the name should be given as `checkers.c_inv_checker`.

### The Variable Format

The variable format must be specified as `ssa` only if the SSA format of variables is used in the input graph, else leave it blank. For example, refer to our
[C benchmarks](benchmarks/C_instances) and our [C specification file](code2inv/prog_generator/specs/c_spec).

## The Checker Module

The checker module is the way Code2Inv verifies if the predicted invariant is correct, and if it is not, then the checker module must return the set of counter examples for that invariant.

Examples of the checker module can be found in the [`code2inv/prog_generator/checkers` directory](code2inv/prog_generator/checkers).

There are two functions that must be present in the checker- `inv_checker` and `inv_solver`. `inv_checker` will take the verification condition file name, the invariant string (as produced taking the invariant grammar into account) and a counter-example given as a list of `(variable_name, variable_value)` assignment pairs. `inv_checker` will assign the variables their values (any variable in the invariant not in the assignment pair is assigned the value of 1) and evaluate the invariant based on these values, which should either return true or false.

`inv_solver` will take the verification condition file name and the invariant string and check if the invariant is correct or not and return a list of 3 elements. The invariant will be checked over the precondition, the loop condition and the post condition in that order. For each check, if the invariant is correct and there is no counter example, the corresponding list element will be `None`. If there is a counter example, the corresponding list element will be a dictionary of counter example variables mapped to their values.

For example, in the event that an invariant raises a counterexample for the loop condition but is correct for the other conditions, the returned list will be `[ None, { "var1" : 10 }, None ]`.