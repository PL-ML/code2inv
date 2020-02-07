# Installation

First get the dependencies

* LLVM 7
* The Clang API

On Ubuntu, run `sudo apt-get install llvm-7 libllvm7 clang-7`

Get them at http://clang.llvm.org/get_started.html

Then run `make` while inside the clang-fe directory. This should make an executable named ssa-transform.

You may need to edit the include variables of `make` if llvm-config-7 does not include the clang include directory or produces linker errors.