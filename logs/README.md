# Code2Inv Experimental Logs

This directory includes a collection of the experimental logs of code2inv.
We include the logs for all experiments in their corresponding subdirectories `logs-<exp_type>`.
For example, `logs-c` consist of the logs for the solved instances from the linear C instances, while `logs-chc` will have the logs of the solved instances from the linear CHC instances.

Each subdirectory has a collection of files.
Each file will contain the file name, the invariant found, number of iterations,
wallclock time and other general logs (like z3 count, counter example counts, etc).

The linear C logs and linear CHC logs have been compiled into the csv files called `c_logs.csv` and `chc_logs.csv` respectively.
The CSV files include the headers for each column and contain the same information in the individual files from the `logs-c` and `logs-chc` subdirectories respectively.

The files `code2inv-general-all-chc-logs`, `LinearArbitrary-all-chc-logs` and `z3-all-chc-logs` files have all the CHC logs and walclock times for the linear CHC intances as solved by Code2Inv, LinearArbitrary and Z3 respectively.

As for logs for the other baseline solvers for the linear C benchmarks, refer to the SyGuS 2017 competition (https://sygus.org/comp/2017/).
The solver executables are available at https://www.starexec.org/starexec/secure/index.jsp and instructions for the same can be found at https://sygus.org/artifacts/.