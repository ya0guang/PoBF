#!/bin/bash
# This script performs evaluations on different computation tasks for PoBF library.

# TODO: Split this script according to the type of the target platform?
# E.g., evaluation_pobf.sh, evaluation_native.sh, evaluation_rust.sh

MAGENTA="\033[0;35m"
NC="\033[0m"
ADDRESS=127.0.0.1
PORT=1234

pushd .. > /dev/null
declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")

# Create some directories
for task in "${tasks[@]}"; do
    mkdir -p eval/"$task"/pobf
    mkdir -p eval/"$task"/native_enclave
    mkdir -p eval/"$task"/rust
    mkdir -p eval/"$task"/gramine
done

# Build data provider first.
pushd data_provider > /dev/null
cargo build --release
popd > /dev/null

echo -e "$MAGENTA[+] Building TVM runtime for native Rust program...$NC"
pushd others/rust/evaluation_tvm/model_deploy > /dev/null
make -j
popd > /dev/null

# Build different Rust programs for different tasks.
for task in "${tasks[@]}"; do
    if [[ ! -f eval/$task/rust/app ]]; then
        echo -e "$MAGENTA[+] Building Rust binary for $task...$NC"
        echo $(pwd)
        pushd others/rust > /dev/null
        cargo build --release --features="$task"
        cp target/release/rust ../../eval/"$task"/rust/app
        popd > /dev/null
        
        echo -e "$MAGENTA[+] Finished!$NC"
    fi
done

# Build different native enclaves for different tasks.
for task in "${tasks[@]}"; do
    if [[ ! -f eval/$task/native_enclave/app ||
        ! -f eval/$task/native_enclave/enclave.signed.so ]]; then
        echo -e "$MAGENTA[+] Building native enclave for $task...$NC"
        SGX_MODE=HW TASK=$task NATIVE_ENCLAVE=1 make -j
        cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/native_enclave
        echo -e "$MAGENTA[+] Finished!$NC"
    else
        echo -e "$MAGENTA[+] File exists. Skipped!$NC"
    fi
done

# Build different PoBF enclaves for different tasks.
for task in "${tasks[@]}"; do

    if [[ ! -f eval/$task/pobf/app || ! -f eval/$task/pobf/enclave.signed.so ]]; then
        echo -e "$MAGENTA[+] Building enclave for $task...$NC"
        SGX_MODE=HW TASK=$task NATIVE_ENCLAVE=0 make -j
        cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/pobf
        echo -e "$MAGENTA[+] Finished!$NC"
    else
        echo -e "$MAGENTA[+] File exists. Skipped!$NC"
    fi
done

# Build Gramine backbone.
pushd others/gramine > /dev/null
make clean
make app dcap RA_TYPE=dcap -j$((`nproc`+1)) > /tmp/meta.txt
# Get config keys.
mr_enclave=$(awk '/mr_enclave/ { print $2 }' /tmp/meta.txt | head -1)
mr_signer=$(awk '/mr_signer/ { print $2 }' /tmp/meta.txt | head -1)
isv_prod_id=$(awk '/isv_prod_id/ { print $2 }' /tmp/meta.txt | head -1)
isv_svn=$(awk '/isv_svn/ { print $2 }' /tmp/meta.txt | head -1)
rm -r /tmp/meta.txt

# Build its Rust tasks.

popd > /dev/null

# Doing evaluations on Rust programs.
for task in "${tasks[@]}"; do
    echo -e "$MAGENTA[-] Testing Rust program for $task...$NC"

    pushd eval/"$task"/rust > /dev/null
    { time ./app; } > ../../../data/"$task"/output_enclave_rust.txt 2>&1
    popd > /dev/null
    
    echo -e "$MAGENTA  [+] Finished!$NC"
done

# Doing evaluations on PoBF.
for task in "${tasks[@]}"; do
    echo -e "$MAGENTA[-] Testing PoBF enclave for $task...$NC"
    
    # Start the enclave.
    pushd eval/"$task"/pobf > /dev/null
    { time ./app $ADDRESS $PORT; } > ../../../data/"$task"/output_enclave_pobf.txt 2>&1 &
    sleep 1
    popd > /dev/null
    
    # Start the data provider.
    pushd ./data_provider/bin > /dev/null
    { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/output_data_provider_pobf.txt 2>&1
    cp ./output.txt ../../data/"$task"/result_pobf.txt
    popd > /dev/null
    
    killall app
    wait
    echo -e "$MAGENTA  [+] Finished!$NC"
done

# Doing evaluations on the native enclave.
for task in "${tasks[@]}"; do
    echo -e "$MAGENTA[-] Testing native enclave for $task...$NC"
    
    # Start the enclave.
    pushd eval/"$task"/native_enclave > /dev/null
    { time ./app $ADDRESS $PORT; } > ../../../data/"$task"/output_enclave_native_enclave.txt 2>&1 &
    sleep 1
    popd > /dev/null
    
    # Start the data provider.
    pushd ./data_provider/bin > /dev/null
    { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/output_data_provider_native_enclave.txt 2>&1
    cp ./output.txt ../../data/"$task"/result_native_enclave.txt
    popd > /dev/null
    
    killall app
    wait
    echo -e "$MAGENTA  [+] Finished!$NC"
done

popd > /dev/null
