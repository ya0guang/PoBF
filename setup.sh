#!/usr/bin/bash

# A simple script that prepares the environment at once, a modified script from docker build script.

echo "Installing necessary packages from apt..."
sudo apt install -y \
  build-essential \
  libtool \
  autoconf \
  python \
  curl \
  git \
  wget \
  python3 \
  python3-pip \
  libclang-dev \
  default-jdk \
  llvm-10
# cmake
wget -O - https://apt.kitware.com/keys/kitware-archive-latest.asc 2> /dev/null | gpg --dearmor - | sudo tee /etc/apt/trusted.gpg.d/kitware.gpg > /dev/null
sudo apt-add-repository 'deb https://apt.kitware.com/ubuntu/ focal main' 
sudo apt update
sudo apt install -y cmake 
echo "Done"

echo "Installing Rust"
if ! [ -x "$(command -v rustup)" ]; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
  source "$HOME/.cargo/env"
fi
# Install nightly toolchain
rustup -V
echo "Done"

if ! [ -x "$(command -v coqc)" ]; then
  echo "Installing Coq"
  # opam
  bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
  opam init
  opam switch default
  eval $(opam env)

  # coq
  opam pin add coq 8.13.2
  opam repo add coq-released https://coq.inria.fr/opam/released
  echo "Done"
fi

echo "Preparing MIRAI and Prusti"
pushd scripts > /dev/null
bash -c ./prepare_mirai.sh
bash -c ./prepare_prusti.sh
popd > /dev/null
echo "Done"

echo "Installing SGX SDK and libraries"
echo 'deb [arch=amd64] https://download.01.org/intel-sgx/sgx_repo/ubuntu focal main' | sudo tee /etc/apt/sources.list.d/intel-sgx.list
wget -qO - https://download.01.org/intel-sgx/sgx_repo/ubuntu/intel-sgx-deb.key | sudo apt-key add
sudo apt update && sudo apt install -y \
  libsgx-epid \
  libsgx-quote-ex \
  libsgx-dcap-ql \
  libsgx-dcap-default-qpl \
  libsgx-uae-service \
  libsgx-urts-dbgsym \
  libsgx-enclave-common-dbgsym \
  libsgx-uae-service-dbgsym \
  libsgx-dcap-ql-dbgsym \
  libsgx-dcap-default-qpl-dbgsym
wget https://download.01.org/intel-sgx/sgx-linux/2.17.1/distro/ubuntu20.04-server/sgx_linux_x64_sdk_2.17.101.1.bin \
  -O sgx_linux_x64_sdk_2.17.101.1.bin
chmod +x ./sgx_linux_x64_sdk_2.17.101.1.bin
sudo ./sgx_linux_x64_sdk_2.17.101.1.bin
echo "Done. Please remember to do 'echo source /opt/intel/sgxsdk/environment >> ~/.bashrc' to update \$PATH."

# Install TVM.
echo "Installing Apache-TVM"
git clone https://github.com/apache/tvm.git $HOME/tvm
pushd $HOME/tvm > /dev/null
git checkout v0.12.0
git submodule update --init
mkdir build && cp ./cmake/config.cmake ./build
pushd build > /dev/null
sed -i 's/set(USE_MICRO_STANDALONE_RUNTIME OFF)/set(USE_MICRO_STANDALONE_RUNTIME ON)/g' config.cmake
sed -i 's/set(USE_LLVM OFF)/set(USE_LLVM ON)/g' config.cmake
sed -i 's/set(USE_MICRO OFF)/set(USE_MICRO ON)/g' config.cmake
cmake .. && make -j8
export TVM_HOME=$HOME/tvm
export PYTHONPATH=$TVM_HOME/python:$TVM_HOME/topi/python:$TVM_HOME/nnvm/python:${PYTHONPATH}
popd > /dev/null
popd > /dev/null
echo "Done"
