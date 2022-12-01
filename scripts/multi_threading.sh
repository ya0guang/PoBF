#!/bin/bash

MAGENTA="\033[0;35m"
RED="\033[0;31m"
YELLOW="\033[0;33m"
NC="\033[0m"

function install_package {
    while true; do
        read -p $'\t    Install it? (y/n) ' yn
        case $yn in
            [Yy]* ) sudo apt install $1; break;;
            [Nn]* ) exit;;
            * ) echo "Please answer yes or no.";;
        esac
    done
}

echo -e "\t[+] Multi-threading config: tcs_num = $1, target = $2"
if ! command -v parallel &> /dev/null; then
    echo -e "${RED}\t[!] The command 'parallel' does not exist.$NC"
    echo -e "${YELLOW}\t    You can install it by 'sudo apt -y install parallel'.$NC"
    install_package "parallel"
fi

declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")

pushd .. > /dev/null

# Test multi-threading for Rust program.
if [[ $2 = "rust" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA\t[-] Testing multi-threading on Rust program for $task...$NC"
        
        pushd eval/"$task"/rust > /dev/null
        { time ./server; } > ../../../data/"$task"/mt_output_enclave_rust.txt 2>&1 &
        while true ; do
            if grep -q "Server started" ../../../data/$task/mt_output_enclave_rust.txt; then
                break
            fi
            
            sleep 1
        done

        { time eval 'parallel -j0 -N0 ./client ../../../data/"$task"/data.bin ::: '{1..$1}''; } \
             > ../../../data/$task/mt_output_data_provider_rust.txt 2>&1
        fuser -k 7788/tcp > /dev/null 2>&1
        wait
        popd > /dev/null
    done
fi

popd > /dev/null
