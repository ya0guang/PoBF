#!/bin/bash
# This bash script is expected to run inside the docker container provided by Occlum.

# Install Pip3 dependencies.
pip3 install -r ../../requirements.txt
# Build TVM for the Rust program.
pushd ../evaluation_tvm/model_deploy > /dev/null
make clean && make -j
popd > /dev/null

# Build the Rust program.
pushd ./rust_app > /dev/null
occlum-cargo build --release 
popd > /dev/null
