

# Environment Setup

## Basic Setup
- python-2.7 
- PyTorch 0.4.0
- python library: numpy, tqdm, pyparsing
- gcc/g++ 5.4.0 (or higher)
- make, cmake

## Z3 Setup
Z3 is the theorem prover we used to verify the corrrectness of generated loop invariant. To build z3, please follow:

1. Download and unzip Z3 source code from https://github.com/Z3Prover/z3/releases/tag/z3-4.4.0
2. ```python scripts/mk_make.py --prefix /usr/local/; cd build; make -j16; make install ```

## Frontend Setup (Optional)
Frontend is used to extract program graphs and verifcation conditions from C programs. The program graphs and VCs for our benchmark are already included in `benchmarks`.  To build the frontend, please follow the README in `code2inv-fe`. 


# Experiments
TODO
