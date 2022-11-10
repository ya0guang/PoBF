 #!/bin/bash

MAGENTA="\033[0;35m"
NC="\033[0m"

export PATH="$(pwd)/verifier/:$HOME/.local/prusti/:$PATH"
export SGX_MODE=HW
export PRUSTI_LOG=ERROR

printf "${MAGENTA}- Check if Prusti is intalled.${NC}\n"
if [ ! -d $HOME/.local/prusti ]; then
  printf "${MAGENTA}  + Prusti is not installed, start to install Prusti.${NC}\n"
  exec $(pwd)/prepare_prusti.sh
else
  printf "${MAGENTA}  + Found Prusti.${NC}\n"
fi

printf "${MAGENTA}- Verify the PoBF framework...${NC}\n\n"
cd $(pwd)/platform_sgx/enclave && cargo pobf-verify --allowed-unsafe lib.rs ocall.rs networking_utils.rs --log-level INFO -- --features=sgx,leak_log
