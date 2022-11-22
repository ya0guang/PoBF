#!/bin/bash
# This script performs evaluations on different computation tasks for PoBF library.
# To evaluate on other platforms, use a standalone repository instead. => TODO.

MAGENTA="\033[0;35m"
NC="\033[0m"

pushd ..
declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")
# Create some directories for PoBF evaluations.
for task in "${tasks[@]}"; do
  mkdir -p eval/"$task"
done

# Build different PoBF enclaves for different tasks.
for task in "${tasks[@]}";do
  echo -e "$MAGENTA[+] Building enclave for $task...$NC"
  SGX_MODE=HW TASK=$task make -j
  cp platform_sgx/bin/* eval/$task
  echo -e "$MAGENTA[+] Finished!$NC"
done

# Doing evaluations.

popd
