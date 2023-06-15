#!/bin/bash

MAGENTA="\033[0;35m"
NC="\033[0m"

allow_unsafe="lib.rs ocall.rs networking_utils.rs db_persistent.rs"
features="sgx,leak_log,task_sample"

export PATH="$(pwd)/../pobf_verifier/:$HOME/.local/prusti/:$PATH"
export SGX_MODE=HW
export PRUSTI_LOG=ERROR
export TASK=mirai_sample
export MIRAI_FLAGS="--single_func pobfref.pobf.pobf_workflow"

printf "${MAGENTA}- Check if Prusti is intalled.${NC}\n"
if [ ! -d $HOME/.local/prusti ]; then
  printf "${MAGENTA}  + Prusti is not installed, start to install Prusti.${NC}\n"
  . $(pwd)/prepare_prusti.sh
else
  printf "${MAGENTA}  + Found Prusti.${NC}\n"
fi

printf "${MAGENTA}- Verify the PoBF framework...${NC}\n\n"
pushd $(pwd)/../platform_sgx/enclave
cargo pobf-verify \
      --allowed-unsafe $allow_unsafe \
      --log-level INFO -- --features=$features
popd
