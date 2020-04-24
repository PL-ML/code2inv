
# Directory Structure
- The directory `c` consists of 133 C programs we collected to evaluate Code2Inv.

- The directory `graph` consists of the corresponding 133 program graphs.

- The directory `smt2` consists of the corresponding verification conditions.

- The directory `pre-train-study` consists of generated (i.e. inserting confounding variables/statements) C programs and corresponding graphs and VCs.

# Program Graph Format
Each program graph contains two dictionaries: one to describes nodes in the graph, and the other one describes the control flow. 
Each node represents a statement/command, e.g. `assert (x > y); y = y + 1`. The corresponding JSON file might be as follows: 

```json
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
    ...
  },
  "control-flow": [
    [ "22", "4" ],
    [ "17", "EXIT" ],
    [ "ENTRY", "13" ]
    ...
  ]
}
```

# Verification Condition Format

The verification condition format is the same as the one used in [SyGus 2017 Invariant Track](http://sygus.seas.upenn.edu/SyGuS-COMP2017.html).

It consists of three parts: `pre-f`, `trans-f` and `post-f`, which corresponds the pre-condition, loop body and post-condition, respectively.