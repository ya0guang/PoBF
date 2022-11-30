#!/bin/bash

MAGENTA="\033[0;35m"
NC="\033[0m"

pushd .. > /dev/null
declare -a tasks=("task_tvm" "task_fann" "task_fasta" "task_polybench" "task_sample")
# Clean outputs.
for task in "${tasks[@]}"; do
    rm -r ./eval > /dev/null 2>&1
    rm -r others/occlum/eval > /dev/null 2>&1
    rm -r data/"$task"/output* > /dev/null 2>&1
    rm -r data/"$task"/result* > /dev/null 2>&1
done

popd > /dev/null
