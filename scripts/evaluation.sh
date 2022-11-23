#!/bin/bash
# This script performs evaluations on different computation tasks for PoBF library.
# To evaluate on other platforms, use a standalone repository instead. => TODO.

MAGENTA="\033[0;35m"
NC="\033[0m"
ADDRESS=127.0.0.1
PORT=1234

pushd .. > /dev/null
declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")
# Create some directories for PoBF evaluations.
for task in "${tasks[@]}"; do
    mkdir -p eval/"$task"
done

# Build different PoBF enclaves for different tasks.
for task in "${tasks[@]}"; do
    if [[ ! -f eval/$task/app || ! -f eval/$task/enclave.signed.so ]]; then
        echo -e "$MAGENTA[+] Building enclave for $task...$NC"
        SGX_MODE=HW TASK=$task make -j
        cp platform_sgx/bin/{app,enclave.signed.so} eval/$task
        echo -e "$MAGENTA[+] Finished!$NC"
    else
        echo -e "$MAGENTA[+] File exists. Skipped!$NC"
    fi
done

# Doing evaluations.
for task in "${tasks[@]}"; do
    echo -e "$MAGENTA[-] Testing enclave for $task...$NC"
    
    # Start the enclave.
    pushd eval/"$task" > /dev/null
    { time ./app $ADDRESS $PORT; } > ../../data/"$task"/output_enclave.txt 2>&1 &
    sleep 1
    popd > /dev/null
    
    # Start the data provider.
    pushd ./data_provider/bin > /dev/null
    { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/output_data_provider.txt 2>&1
    popd > /dev/null
    
    killall app
    wait
    echo -e "$MAGENTA  [+] Finished!$NC"
done

popd > /dev/null
