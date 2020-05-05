FROM ubuntu:18.04

RUN apt-get update && apt-get install -y \
    python3 g++ gcc make cmake git llvm-7 libllvm7 clang-7 wget unzip python3-pip vim libclang-7-dev libclang-common-7-dev

RUN ln -sf $(which python3) /usr/bin/python; ln -sf $(which pip3) /usr/bin/pip

RUN git clone https://github.com/Z3Prover/z3
RUN cd /z3; git checkout tags/z3-4.8.7; python scripts/mk_make.py --prefix=/ --python --pypkgdir=/usr/lib/python3/dist-packages; cd build; make; make install

# RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.7/z3-4.8.7-x64-ubuntu-16.04.zip
# RUN unzip z3-4.8.7-x64-ubuntu-16.04.zip
# RUN mv z3-4.8.7-x64-ubuntu-16.04 z3

ENV Z3_DIR="/z3"
ENV LD_LIBRARY_PATH="/z3/build"
ENV PYTHON_PATH="/z3/build/python"

ARG CACHEBUST=1

RUN git clone https://github.com/PL-ML/code2inv.git
RUN cd /code2inv; pip install -e .
RUN cd /code2inv/clang-fe; make
WORKDIR code2inv
