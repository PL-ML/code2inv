
# Directory Structure
- The directory `C_instances` consists of 133 C programs, their program graphs and their verification conditions we collected to evaluate Code2Inv.

- The directory `CHC_instances` consists of 120 CHC constraints and their corresponding program graphs we collected to evaluate Code2Inv.

- The directory `nl-bench` consists of the non linear programs used to evaluate Code2Inv.

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

The verification condition format for the C instances is the same as the one used in [SyGus 2017 Invariant Track](http://sygus.seas.upenn.edu/SyGuS-COMP2017.html). It consists of three parts: `pre-f`, `trans-f` and `post-f`, which corresponds the pre-condition, loop body and post-condition, respectively.

The CHC constraints serve as their own verification conditions.