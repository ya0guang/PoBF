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
TIMES=10

function build_tvm_wasm {
    # Build wasm32-wasi targeted TVM model for ResNet152.
    pushd others/enarx/tvm-wasm/tools
    # Remember to set `TVM_HOME` and `PYTHONPATH`.
    if [[ -z $TVM_HOME ]]; then
        echo -e "${RED} TVM_HOME is not set.${NC}"
        exit 1
    fi
    export PYTHONPATH=$TVM_HOME/python:$PYTHONPATH
    export LLVM_AR=llvm-ar-10
    echo -e "${MAGENTA} Building TVM model for wasm32-wasi target...${NC}"
    python3 ./build_graph_lib.py -O3
    echo -e "${MAGENTA} Finished!${NC}"
    
    popd > /dev/null
}

if [ ! $# -eq 2 ]; then
    echo -e "${RED}Error: Argument number mismatch! Got $#.$NC"
    echo -e "  Usage: ./evaluation.sh ${YELLOW}[thread_num] [rust|native|pobf|occlum|gramine|enarx|sev|all|none]$NC"
    exit 1
fi

pushd .. > /dev/null
# declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")
declare -a tasks=("task_fasta" )

declare -a polybench_tasks=("_2mm" "_3mm" "atax" "bicg" "cholesky" "correlation" "covariance" "deriche" "doitgen" "durbin" "fdtd_2d" "floyd_warshall" "gemm" "gemver" "gesummv" "gramschmidt" "heat_3d" "jacobi_1d" "jacobi_2d" "lu" "ludcmp" "mvt" "nussinov" "seidel_2d" "symm" "syr2k" "syrk" "trisolv" "trmm" "adi")
# declare -a polybench_tasks=("_2mm" "_3mm" "atax" "bicg" "cholesky")

# Create some directories
for task in "${tasks[@]}"; do
    mkdir -p eval/"$task"/pobf
    mkdir -p eval/"$task"/native
    mkdir -p eval/"$task"/rust
    mkdir -p eval/"$task"/gramine
    mkdir -p eval/"$task"/enarx
    mkdir -p eval/"$task"/sev
done

# Build data provider first.
if [[ $2 = "sev" ]]; then
    pushd data_provider_sev > /dev/null
    cargo build --release
    popd > /dev/null
    # Build the shared library.
    pushd platform_sev/attestation_lib > /dev/null
    make -j && cp ./libsev_attestation.so ../../eval
    popd > /dev/null
else
    pushd data_provider > /dev/null
    cargo build --release
    popd > /dev/null
fi 

echo -e "$MAGENTA[+] Building TVM runtime for PoBF and others...$NC"
make -C others/evaluation_tvm/model_deploy -j

if [[ $2 != "sev" ]]; then
    make -C cctasks/evaluation_tvm/model_deploy -j
fi

# Build different SEV enclaves for different tasks.
if [[ $2 = "sev" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        if [[ ! -f eval/$task/sev/app ]]; then
            echo -e "$MAGENTA[-] Building SEV program for $task...$NC"
            if [[ $task = "task_polybench" ]]; then
                for subtask in "${polybench_tasks[@]}"; do
                    mkdir -p eval/$task/sev/$subtask
                    pushd ./platform_sev > /dev/null
                    cargo build --features=$task,$subtask
                    cp target/debug/platform_sev ../eval/$task/sev/$subtask/app
                    popd > /dev/null
                done
            else
                pushd ./platform_sev > /dev/null
                cargo build --features=$task
                cp target/debug/platform_sev ../eval/$task/sev/app
                popd > /dev/null
            fi
            echo -e "$MAGENTA\t[+] Finished!$NC"
        else
            echo -e "$MAGENTA\t[+] File exists. Skipped!$NC"
        fi
    done
fi

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
        occlum-cargo build --release --features=server/$task,occlum
        cp target/x86_64-unknown-linux-musl/release/server ../occlum/eval/server_$task
        cp target/x86_64-unknown-linux-musl/release/client ../occlum/eval/client
        popd > /dev/null
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
    rm -rf build
    occlum init
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

# Build Enarx backbone.
if [[ $2 = "enarx" || $2 = "all" ]]; then
    if [[ ! -f others/enarx/tvm-wasm/lib/libgraph_wasm32.a ]]; then
        build_tvm_wasm
    fi
    
    for task in "${tasks[@]}"; do
        if [[ ! -f eval/$task/enarx/server.wasm || ! -f eval/$task/enarx/client ]]; then
            echo -e "$MAGENTA[-] Building Enarx server and client for $task...$NC"
            pushd others/enarx > /dev/null
            cargo +nightly build --release --target=wasm32-wasi --features=server/$task
            
            pushd client > /dev/null
            cargo build --release
            popd > /dev/null
            
            cp target/wasm32-wasi/release/server.wasm ../../eval/"$task"/enarx/server.wasm
            cp target/release/client ../../eval/"$task"/enarx/client
            cp Enarx.toml ../../eval/"$task"/enarx/Enarx.toml
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
        if [[ ! -f eval/$task/native/app || ! -f eval/$task/native/enclave.signed.so ]]; then
            echo -e "$MAGENTA[-] Building enclave for $task...$NC"
            if [[ $task = "task_polybench" ]]; then
                for subtask in "${polybench_tasks[@]}"; do
                    make -j SGX_MODE=HW TASK=$task,$subtask, NATIVE_ENCLAVE=1
                    mkdir -p eval/$task/native/$subtask
                    cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/native/$subtask
                done
            else
                make -j SGX_MODE=HW TASK=$task NATIVE_ENCLAVE=1
                cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/native
            fi
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
            if [[ $task = "task_polybench" ]]; then
                for subtask in "${polybench_tasks[@]}"; do
                    make -j SGX_MODE=HW TASK=$task,$subtask, NATIVE_ENCLAVE=0
                    mkdir -p eval/$task/pobf/$subtask
                    cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/pobf/$subtask
                done
            else
                make -j SGX_MODE=HW TASK=$task NATIVE_ENCLAVE=0
                cp platform_sgx/bin/{app,enclave.signed.so} eval/$task/pobf
            fi
            echo -e "$MAGENTA\t[+] Finished!$NC"
        else
            echo -e "$MAGENTA\t[+] File exists. Skipped!$NC"
        fi
    done
fi


# Doing evaluations on SEV.
if [[ $2 = "sev" || $2 = "all" ]]; then
    export LD_LIBRARY_PATH=$(realpath eval)
    for i in $(seq 1 $TIMES); do
        for task in "${tasks[@]}"; do
            echo -e "$MAGENTA[-] Testing SEV for $task...$NC"

            if [[ $task = "task_polybench" ]]; then
                for subtask in "${polybench_tasks[@]}"; do
                    echo -e "$MAGENTA\t[-] Testing SEV for $task/$subtask...$NC"
                    # Start the enclave.
                    pushd eval/"$task"/sev/"$subtask" > /dev/null
                    mkdir -p ../../../../data/"$task"/"$subtask"
                    sudo LD_LIBRARY_PATH=$LD_LIBRARY_PATH ADDRESS=$ADDRESS PORT=$PORT \
                        sh -c 'time ./app $ADDRESS $PORT;' > ../../../../data/"$task"/"$subtask"/"$i"output_enclave_sev.txt 2>&1 &
                    sleep 1
                    popd > /dev/null

                    # Start the data provider.
                    pushd ./data_provider_sev > /dev/null
                    { time cargo run -r -- run ../data/"$task"/manifest_sev.json; } > ../data/"$task"/"$subtask"/"$i"output_data_provider_sev.txt 2>&1
                    cp ./output.txt ../data/"$task"/"$subtask"/"$i"result_sev.txt
                    popd > /dev/null

                    sudo fuser -k $PORT/tcp > /dev/null 2>&1
                    wait
                    echo -e "$MAGENT\t[+] Finished!$NC"
                done
            else
                # Start the program.
                pushd eval/"$task"/sev > /dev/null
                sudo LD_LIBRARY_PATH=$LD_LIBRARY_PATH ADDRESS=$ADDRESS PORT=$PORT \
                        sh -c 'time ./app $ADDRESS $PORT;' > ../../../data/"$task"/"$i"output_enclave_sev.txt 2>&1 &
                sleep 1
                popd > /dev/null

                # Start the data provider.
                pushd ./data_provider_sev > /dev/null
                { time cargo run -r -- run ../data/"$task"/manifest_sev.json; } > ../data/"$task"/output_data_provider_sev.txt 2>&1
                cp ./output.txt ../data/"$task"/"$subtask"/"$i"result_sev.txt
                popd > /dev/null

            fi
            sudo fuser -k $PORT/tcp > /dev/null 2>&1
            wait
            echo -e "$MAGENT\t[+] Finished!$NC"
        done
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
    for i in $(seq 1 $TIMES); do
        for task in "${tasks[@]}"; do
            echo -e "$MAGENTA[-] Testing PoBF enclave for $task...$NC"

            if [[ $task = "task_polybench" ]]; then
                for subtask in "${polybench_tasks[@]}"; do
                    echo -e "$MAGENTA\t[-] Testing PoBF enclave for $task/$subtask...$NC"
                    # Start the enclave.
                    pushd eval/"$task"/pobf/"$subtask" > /dev/null
                    mkdir -p ../../../../data/"$task"/"$subtask"
                    { time ./app $ADDRESS $PORT; } > ../../../../data/"$task"/"$subtask"/"$i"output_enclave_pobf.txt 2>&1 &
                    sleep 1
                    popd > /dev/null
                    
                    # Start the data provider.
                    pushd ./data_provider/bin > /dev/null
                    { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/"$subtask"/"$i"output_data_provider_pobf.txt 2>&1
                    cp ./output.txt ../../data/"$task"/"$subtask"/"$i"result_pobf.txt
                    popd > /dev/null
                    
                    fuser -k $PORT/tcp > /dev/null 2>&1
                    wait
                    echo -e "$MAGENT\t[+] Finished!$NC"
                done
            else
                # Start the enclave.
                pushd eval/"$task"/pobf > /dev/null
                { time ./app $ADDRESS $PORT; } > ../../../data/"$task"/output_enclave_pobf.txt 2>&1 &
                sleep 1
                popd > /dev/null
                
                # Start the data provider.
                pushd ./data_provider/bin > /dev/null
                { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/output_data_provider_pobf.txt 2>&1
                cp ./output.txt ../../data/"$task"/"$subtask"/"$i"result_pobf.txt
                popd > /dev/null

            fi
            fuser -k $PORT/tcp > /dev/null 2>&1
            wait
            echo -e "$MAGENT\t[+] Finished!$NC"
        done
    done
fi

# Doing evaluations on the native enclave.
if [[ $2 = "native" || $2 = "all" ]]; then
    for i in $(seq 1 $TIMES); do
        for task in "${tasks[@]}"; do
            echo -e "$MAGENTA[-] Testing native enclave for $task...$NC"

            if [[ $task = "task_polybench" ]]; then
                for subtask in "${polybench_tasks[@]}"; do
                    echo -e "$MAGENTA\t[-] Testing Native enclave for $task/$subtask...$NC"
                    # Start the enclave.
                    pushd eval/"$task"/native/$subtask > /dev/null
                    mkdir -p ../../../../data/"$task"/"$subtask"
                    { time ./app $ADDRESS $PORT; } > ../../../../data/"$task"/"$subtask"/"$i"output_enclave_native.txt 2>&1 &
                    sleep 1
                    popd > /dev/null
                    
                    # Start the data provider.
                    pushd ./data_provider/bin > /dev/null
                    { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/"$subtask"/"$i"output_data_provider_native.txt 2>&1
                    cp ./output.txt ../../data/"$task"/"$subtask"/"$i"result_native.txt
                    popd > /dev/null

                    fuser -k $PORT/tcp > /dev/null 2>&1
                    wait
                    echo -e "$MAGENT\t[+] Finished!$NC"
                done
            else
                # Start the enclave.
                pushd eval/"$task"/native > /dev/null
                { time ./app $ADDRESS $PORT; } > ../../../data/"$task"/output_enclave_native.txt 2>&1 &
                sleep 1
                popd > /dev/null
                
                # Start the data provider.
                pushd ./data_provider/bin > /dev/null
                { time ./data_provider run ../../data/"$task"/manifest.json; } > ../../data/"$task"/output_data_provider_native.txt 2>&1
                cp ./output.txt ../../data/"$task"/result_native.txt
                popd > /dev/null
            fi
            
            fuser -k $PORT/tcp > /dev/null 2>&1
            wait
            echo -e "$MAGENTA\t[+] Finished!$NC"
        done
    done
fi

# Doing evaluations on the Enarx.
if [[ $2 = "enarx" || $2 = "all" ]]; then
    for task in "${tasks[@]}"; do
        echo -e "$MAGENTA[-] Testing Enarx enclave for $task...$NC"
        
        backend=nil
        if [[ ! -z $BACKEND ]]; then
            backend=$BACKEND
        fi
        
        # Start the enclave.
        pushd eval/"$task"/enarx > /dev/null
        { time enarx run --backend=$backend ./server.wasm --wasmcfgfile ./Enarx.toml; } > \
        ../../../data/"$task"/output_enclave_enarx.txt 2>&1 &
        sleep 1
        # Wait for the server.
        while true ; do
            if grep -q "Server started" \
            ../../../data/"$task"/output_enclave_enarx.txt; then
                break
            fi
            
            sleep 1
        done
        
        # Start the client.
        if [[ $task = "task_tvm" ]]; then
            ./client ../../../data/"$task"/cat.png > ../../../data/"$task"/output_data_provider_enarx.txt 2>&1
        else
            ./client ../../../data/"$task"/data.bin > ../../../data/"$task"/output_data_provider_enarx.txt 2>&1
        fi
        popd > /dev/null
        
        pkill enarx > /dev/null 2>&1
        wait
        echo -e "$MAGENTA\t[+] Finished!$NC"
    done
fi

popd > /dev/null

# Test multi-threading.
echo -e "$MAGENTA[+] Testing multi-threading...$NC"
# ./multi_threading.sh $1 $2
