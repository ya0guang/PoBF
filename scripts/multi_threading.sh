#!/bin/bash

MAGENTA="\033[0;35m"
RED="\033[0;31m"
YELLOW="\033[0;33m"
NC="\033[0m"
ADDRESS=127.0.0.1
PORT=1234

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

echo -e "[-] Multi-threading config:"
echo -e "\t[+] tcs_num = $1, target = $2"
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
        
        { time eval 'parallel -j0 -N0 ./client ../../../data/'$task'/data.bin ::: '{1..$1}''; } \
        > ../../../data/$task/mt_output_data_provider_rust.txt 2>&1
        fuser -k 7788/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t\t[+] Finished!$NC"
        popd > /dev/null
    done
fi

# Test multi-threading for Occlum program.
if [[ $2 = "occlum" || $2 = "all" ]]; then
    pushd others/occlum > /dev/null
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA\t[-] Testing multi-threading on Occlum for $task...$NC"
        { time occlum run /bin/server_$task; } > ../../data/$task/mt_output_enclave_occlum.txt 2>&1 &
        # Wait for the server.
        while true ; do
            if grep -q "Server started" ../../data/$task/mt_output_enclave_occlum.txt; then
                break
            fi
            
            sleep 1
        done
        
        { time eval 'parallel -j0 -N0 ./eval/client ../../data/'$task'/data.bin ::: '{1..$1}''; } \
        > ../../data/$task/mt_output_data_provider_occlum.txt 2>&1
        fuser -k 7788/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t\t[+] Finished!$NC"
    done
    popd > /dev/null
fi

# Test multi-threading for Gramine program.
if [[ $2 = "gramine" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA\t[+] Testing multi-threading on Gramine for $task...$NC"
        
        pushd eval/$task/gramine > /dev/null
        
        { time gramine-sgx ./server; } > ../../../data/$task/mt_output_enclave_gramine.txt 2>&1 &
        # Wait for the server.
        while true ; do
            if grep -q "Waiting for a remote connection" \
            ../../../data/$task/mt_output_enclave_gramine.txt; then
                break
            fi
            
            sleep 1
        done
        
        export RA_TLS_ALLOW_DEBUG_ENCLAVE_INSECURE=1
        export RA_TLS_ALLOW_OUTDATED_TCB_INSECURE=1
        export RA_TLS_MRENCLAVE=$(awk '/mr_enclave/ { print $2 }' ../../../data/$task/gramine_meta.txt | head -1)
        export RA_TLS_MRSIGNER=$(awk '/mr_signer/ { print $2 }' ../../../data/$task/gramine_meta.txt | head -1)
        export RA_TLS_ISV_PROD_ID=0
        export RA_TLS_ISV_SVN=0
        export DATA_PATH="../../../data/$task/data.bin"
        
        { time eval 'parallel -j0 -N0 ./client dcap ::: '{1..$1}''; } \
        > ../../../data/$task/mt_output_data_provider_gramine.txt 2>&1
        unset DATA_PATH
        unset RA_TLS_MRENCLAVE
        unset RA_TLS_MRSIGNER
        
        fuser -k 2333/tcp > /dev/null 2>&1
        wait
        
        popd > /dev/null
        
        echo -e "$MAGENTA\t\t[+] Finished!$NC"
    done
fi

# Test multi-threading for PoBF program.
if [[ $2 = "pobf" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA\t[+] Testing multi-threading on PoBF for $task...$NC"
        
        pushd eval/$task/pobf > /dev/null
        { time ./app $ADDRESS $PORT; } > ../../../data/$task/mt_output_enclave_pobf.txt 2>&1 &
        sleep 1
        popd > /dev/null
        
        pushd ./data_provider/bin > /dev/null
        { time eval 'parallel -j0 -N0 ./data_provider run ../../data/$task/manifest.json ::: '{1..$1}''; } \
        > ../../data/$task/mt_output_data_provider_pobf.txt 2>&1
        popd > /dev/null
        
        fuser -k $PORT/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t\t[+] Finished!$NC"
    done
fi

# Test multi-threading for native enclave.
if [[ $2 = "native" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA\t[+] Testing multi-threading on native enclave for $task...$NC"
        
        pushd eval/$task/native_enclave > /dev/null
        { time ./app $ADDRESS $PORT; } > ../../../data/$task/mt_output_enclave_native.txt 2>&1 &
        sleep 1
        popd > /dev/null
        
        pushd ./data_provider/bin > /dev/null
        { time eval 'parallel -j0 -N0 ./data_provider run ../../data/$task/manifest.json ::: '{1..$1}''; } \
        > ../../data/$task/mt_output_data_provider_native.txt 2>&1
        popd > /dev/null
        
        fuser -k $PORT/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t\t[+] Finished!$NC"
    done
fi

# Test multi-threading for enarx.
if [[ $2 = "enarx" || $2 = "all" ]]; then
    echo -e "$RED[!] Enarx does not support multi-threading!$NC"
fi

popd > /dev/null

echo -e "$MAGENTA[+] Multi-threading finished!$NC"
