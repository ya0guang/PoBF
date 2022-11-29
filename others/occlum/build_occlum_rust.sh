#!/bin/bash
# This bash script is expected to run inside the docker container provided by Occlum.

MAGENTA="\033[0;35m"
NC="\033[0m"

# Add musl target.
rustup target add x86_64-unknown-linux-musl

declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")

mkdir -p "eval"
# Install Pip3 dependencies.
pip3 install -r ../../requirements.txt
# Build TVM for the Rust program.
pushd ../evaluation_tvm/model_deploy > /dev/null
make clean && make -j
popd > /dev/null

# Build the Rust program.
pushd ./rust_app > /dev/null

for task in "${tasks[@]}"; do
    occlum-cargo build --release --features=$task
    cp target/x86_64-unknown-linux-musl/release/rust_app ../eval/rust_app_$task
done

popd > /dev/null

copy_bom -f ./rust_config.yaml --root image --include-dir /opt/occlum/etc/template
rm -rf build
occlum build

for task in "${tasks[@]}"; do
    echo -e "$MAGENTA[+] Testing Occlum program for $task...$NC"
    occlum run /bin/rust_app_$task
    echo -e "$MAGENTA[+] Finished!$NC"
done
