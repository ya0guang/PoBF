FROM ubuntu:20.04

ARG SGX_SDK_VERSION_MAJOR=2.17.1
ARG SGX_SDK_VERSION_MINOR=2.17.101.1
ARG DEV_PRUSTI_GIT_REPO=https://github.com/viperproject/prusti-dev.git
ARG DEV_PRUSTI_COMMIT=734426eb50e6de7454b40694d5a8e843c05d9ee8
ARG RUST_COMP="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
ARG RUST_TOOLCHAIN=nightly-2022-10-22
ARG SSH_KEY

SHELL ["/bin/bash", "-c"] 

RUN apt update && apt install -y \
  build-essential \
  libtool \
  autoconf \
  python \
  curl \
  git \
  wget \
  python3

RUN echo 'deb [arch=amd64] https://download.01.org/intel-sgx/sgx_repo/ubuntu focal main' | tee /etc/apt/sources.list.d/intel-sgx.list

RUN wget -qO - https://download.01.org/intel-sgx/sgx_repo/ubuntu/intel-sgx-deb.key | apt-key add

RUN apt update && apt install -y \
  libsgx-epid \
  libsgx-quote-ex \
  libsgx-dcap-ql \
  libsgx-uae-service \
  libsgx-urts-dbgsym \
  libsgx-enclave-common-dbgsym \
  libsgx-uae-service-dbgsym \
  libsgx-dcap-ql-dbgsym \
  libsgx-dcap-default-qpl-dbgsym

WORKDIR /root/Downloads

RUN wget https://download.01.org/intel-sgx/sgx-linux/${SGX_SDK_VERSION_MAJOR}/distro/ubuntu20.04-server/sgx_linux_x64_sdk_${SGX_SDK_VERSION_MINOR}.bin
RUN chmod +x sgx_linux_x64_sdk_${SGX_SDK_VERSION_MINOR}.bin
RUN printf "no\n/opt/intel\n" | ./sgx_linux_x64_sdk_${SGX_SDK_VERSION_MINOR}.bin
RUN echo 'source /opt/intel/sgxsdk/environment' >> /root/.bashrc

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN echo 'source "$HOME/.cargo/env"' >> /root/.bashrc
RUN source "$HOME/.cargo/env" && rustup toolchain install ${RUST_TOOLCHAIN}

RUN echo "[+] Configuring Prusti..."
RUN git clone ${DEV_PRUSTI_GIT_REPO}

WORKDIR /root/Downloads/prusti-dev
RUN git checkout ${DEV_PRUSTI_COMMIT}

RUN source "$HOME/.cargo/env" && rustup component add --toolchain ${RUST_TOOLCHAIN} ${RUST_COMP}
RUN apt update && DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC \ 
  apt install -y \
  unzip \
  default-jre \
  openssl \
  libssl-dev \
  pkg-config \
  sudo

# Override the toolchain.
RUN printf '[toolchain]\nchannel = "nightly-2022-10-22"\ncomponents = [ "rustc-dev", "llvm-tools-preview", "rust-std", "rustfmt", "clippy" ]\nprofile = "minimal"' \
  > rust-toolchain
RUN source "$HOME/.cargo/env" && rustup override set ${RUST_TOOLCHAIN} && ./x.py setup && ./x.py build --release
RUN source "$HOME/.cargo/env" && ./x.py package release $HOME/.cargo/prusti
RUN echo "[-] Prusti successfully compiled and installed!"

ENTRYPOINT ["bash", "-l", "-c"]