# Introduction

This module is made for enarx runtime that runs the confidential computing. To make enarx run, you need to set up the rust target for `wasm32-wasi`, which can be done by

```sh
$ rustup target add wasm32-wasi
```

Also, make sure that you have tvm installed and all the environment variables set. Specifically, you should set `TVM_HOME` and `PYTHONPATH`. 

Finally, follow the instruction [here](https://github.com/apache/tvm/tree/main/apps/wasm-standalone) for building the WASM module of ResNet152 model.

**Warning:** The instruction "Build wasm-graph package" is somehow not correct. You may need to run the following command:

```sh
$ cd wasm-graph
$ export TVM_HOME=...
$ export PYTHONPATH=...
$ LLVM_AR=llvm-ar-10 python3 ./build_graph_lib.py -O3
$ cargo +nightly build --target wasm32-wasi --release
$ cp ./target/wasm32-wasi/release/wasm_graph.wasm ./lib/wasm_graph_resnet172.wasm
```

Enarx needs to link against `wasm-runtime` for creating a runtime for TVM graph executor.

## Problems

1. Cannot build `wasm-runtime` for `wasi`. Caused by `cranelift-codegen`:
```sh
thread 'main' panicked at 'error when identifying target: "no supported isa found for arch `wasm32`"'.
```

This is because wastime needs a JIT backend but WASI does not support this. You need to instead compile wasi target from barebone Rust programs.
