#!/bin/bash

cd ../code2inv/code2inv/prog_generator

./run_solver_file.sh ../../naturalness_study/sygus-bench-84.c.smt/sygus-bench-84.c.smt.json ../../naturalness_study/sygus-bench-84.c.smt/sygus-bench-84.c.smt specs/chc_spec
