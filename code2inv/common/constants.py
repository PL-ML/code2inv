AST_EDGE_TYPE = 0
CONTROL_EDGE_TYPE = 2
VAR_LINK_TYPE = 4

NUM_EDGE_TYPES = 6 # 3 edge types x 2 directions


# boogie results
AC_CODE = 0
POST_FAIL_CODE = 1
INDUCTIVE_FAIL_CODE = 2
ENTRY_FAIL_CODE = 3
INVALID_CODE = 4

# z3 pre-check
ALWAYS_TRUE_EXPR_CODE = 3
ALWAYS_FALSE_EXPR_CODE = 4
NORMAL_EXPR_CODE = 5

from code2inv.common.cmd_args import cmd_args

LIST_PREDICATES = [w for w in cmd_args.list_pred.split(',')]
LIST_OP = [w for w in cmd_args.list_op.split(',')]

MAX_DEPTH = cmd_args.max_depth

MAX_AND = cmd_args.max_and

MAX_OR = cmd_args.max_or