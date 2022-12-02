#!/bin/bash
# This script performs evaluations on different computation tasks for PoBF library.

# TODO: Split this script according to the type of the target platform?
# E.g., evaluation_pobf.sh, evaluation_native.sh, evaluation_rust.sh

MAGENTA="\033[0;35m"
RED="\033[0;31m"
YELLOW="\033[0;33m"
NC="\033[0m"
ADDRESS=127.0.0.1
PORT=1234

if [ ! $# -eq 2 ]; then
    echo -e "${RED}Error: Argument number mismatch! Got $#.$NC"
    echo -e "  Usage: ./evaluation.sh ${YELLOW}[thread_num] [rust|native|pobf|occlum|gramine|all|none]$NC"
    exit 1
fi

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

echo -e "$MAGENTA[+] Building TVM runtime for PoBF and others...$NC"
make -C others/evaluation_tvm/model_deploy -j
make -C cctasks/evaluation_tvm/model_deploy -j

# Build different Rust programs for different tasks.
if [[ $2 = "rust" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        if [[ ! -f eval/$task/rust/server || ! -f eval/$task/rust/client ]]; then
            echo -e "$MAGENTA[-] Building Rust binary for $task...$NC"
            pushd others/rust_app > /dev/null
            cargo build --release --features=server/$task
            cp target/release/server ../../eval/"$task"/rust/server
            cp target/release/client ../../eval/"$task"/rust/client
            popd > /dev/null
            
            echo -e "$MAGENTA\t[+] Finished!$NC"
        else
            echo -e "$MAGENTA\t[+] File exists. Skipped!$NC"
        fi
    done
fi

# Build Occlum Rust.
if [[ $2 = "occlum" || $2 = "all" ]]; then
    pushd others/occlum > /dev/null
    mkdir -p "eval"
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA[-] Building Occlum LibOS for $task...$NC"
        pushd ../rust_app > /dev/null
        occlum-cargo build --release --features=server/$task,libos
        cp target/x86_64-unknown-linux-musl/release/server ../occlum/eval/server_$task
        cp target/x86_64-unknown-linux-musl/release/client ../occlum/eval/client
        popd > /dev/null
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
    rm -rf build
    copy_bom -f ./rust_config.yaml --root image --include-dir /opt/occlum/etc/template
    occlum build
    popd > /dev/null
fi

# Build Gramine backbone.
if [[ $2 = "gramine" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        if [[ ! -f eval/$task/gramine/server || ! -f eval/$task/gramine/client ||
            ! -d eval/$task/gramine/ssl ]]; then
            echo -e "$MAGENTA[-] Building Gramine server and client for $task...$NC"
            pushd others/gramine > /dev/null
            make clean
            make app dcap TASK=$task RA_TYPE=dcap -j$((`nproc`+1)) > ../../data/$task/gramine_meta.txt
            cp ./server* ../../eval/$task/gramine
            cp ./client* ../../eval/$task/gramine
            cp -r ./ssl  ../../eval/$task/gramine
            popd > /dev/null
            echo -e "$MAGENTA\t[+] Finished!$NC"
        else
            echo -e "$MAGENTA\t[+] File exists. Skipped!$NC"
        fi
    done
fi

# Build different native enclaves for different tasks.
if [[ $2 = "native" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        if [[ ! -f eval/$task/native_enclave/app ||
            ! -f eval/$task/native_enclave/enclave.signed.so ]]; then
            echo -e "$MAGENTA[-] Building native enclave for $task...$NC"
            make -j SGX_MODE=HW TASK=$task NATIVE_ENCLAVE=1
            cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/native_enclave
            echo -e "$MAGENTA\t[+] Finished!$NC"
        else
            echo -e "$MAGENTA\t[+] File exists. Skipped!$NC"
        fi
    done
fi

# Build different PoBF enclaves for different tasks.
if [[ $2 = "pobf" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        if [[ ! -f eval/$task/pobf/app || ! -f eval/$task/pobf/enclave.signed.so ]]; then
            echo -e "$MAGENTA[-] Building enclave for $task...$NC"
            make -j SGX_MODE=HW TASK=$task NATIVE_ENCLAVE=0
            cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/pobf
            echo -e "$MAGENTA\t[+] Finished!$NC"
        else
            echo -e "$MAGENTA\t[+] File exists. Skipped!$NC"
        fi
    done
fi

# Doing evaluations on Rust programs.
if [[ $2 = "rust" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA[-] Testing Rust program for $task...$NC"
        
        pushd eval/"$task"/rust > /dev/null
        { time ./server; } > ../../../data/"$task"/output_enclave_rust.txt 2>&1 &
        while true ; do
            if grep -q "Server started" ../../../data/$task/output_enclave_rust.txt; then
                break
            fi
            
            sleep 1
        done
        
        ./client ../../../data/"$task"/data.bin > ../../../data/"$task"/output_data_provider_rust.txt 2>&1
        popd > /dev/null
        
        fuser -k 7788/tcp > /dev/null 2>&1
        wait
        
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
fi

# Doing evaluations on Occlum.
if [[ $2 = "occlum" || $2 = "all" ]]; then
    pushd others/occlum > /dev/null
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA[-] Testing Occlum for $task...$NC"
        { time occlum run /bin/server_$task; } > ../../data/$task/output_enclave_occlum.txt 2>&1 &
        # Wait for the server.
        while true ; do
            if grep -q "Server started" ../../data/$task/output_enclave_occlum.txt; then
                break
            fi
            
            sleep 1
        done
        
        ./eval/client ../../data/$task/data.bin > ../../data/$task/output_data_provider_occlum.txt 2>&1
        fuser -k 7788/tcp > /dev/null 2>&1
        wait
        
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
    popd > /dev/null
fi

# Doing evaluations on Gramine.
if [[ $2 = "gramine" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA[-] Testing Gramine for $task...$NC"
        
        pushd eval/"$task"/gramine > /dev/null
        
        { time gramine-sgx ./server; } > ../../../data/"$task"/output_enclave_gramine.txt 2>&1 &
        # Wait for the server.
        while true ; do
            if grep -q "Waiting for a remote connection" \
            ../../../data/"$task"/output_enclave_gramine.txt; then
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
        ./client dcap > ../../../data/"$task"/output_data_provider_gramine.txt 2>&1
        unset DATA_PATH
        unset RA_TLS_MRENCLAVE
        unset RA_TLS_MRSIGNER
        
        popd > /dev/null
        
        fuser -k 2333/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
fi

# Doing evaluations on PoBF.
if [[ $2 = "pobf" || $2 = "all" ]]; then
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
        
        fuser -k $PORT/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENT\t[+] Finished!$NC"
    done
fi

# Doing evaluations on the native enclave.
if [[ $2 = "native" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA[-] Testing native enclave for $task...$NC"
        
        # Start the enclave.
        pushd eval/"$task"/native_enclave > /dev/null
        { time ./app $ADDRESS $PORT; } > ../../../data/"$task"/output_enclave_native.txt 2>&1 &
        sleep 1
        popd > /dev/null
        
        # Start the data provider.
        pushd ./data_provider/bin > /dev/null
        { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/output_data_provider_native_enclave.txt 2>&1
        cp ./output.txt ../../data/"$task"/result_native_enclave.txt
        popd > /dev/null
        
        fuser -k $PORT/tcp > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
fi

popd > /dev/null

# Test multi-threading.
echo -e "$MAGENTA[+] Testing multi-threading...$NC"
./multi_threading.sh $1 $2
