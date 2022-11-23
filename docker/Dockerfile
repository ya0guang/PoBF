FROM ubuntu:20.04

ARG SGX_SDK_VERSION_MAJOR=2.17.1
ARG SGX_SDK_VERSION_MINOR=2.17.101.1
ARG DEV_PRUSTI_GIT_REPO=https://github.com/viperproject/prusti-dev.git
ARG DEV_PRUSTI_COMMIT=ee91e7772e764c910b1e6638f609ad5da0a791a7
ARG MIRAI_GIT_REPO=https://github.com/facebookexperimental/MIRAI.git
ARG MIRAI_COMMIT=5ca2f1ebe1b057ba74438782e2bef91ec87834c4
ARG RUST_COMP="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
ARG RUST_TOOLCHAIN=nightly-2022-11-01

SHELL ["/bin/bash", "-c"] 

RUN apt update && DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC apt install -y \
  build-essential \
  libtool \
  autoconf \
  python \
  curl \
  git \
  wget \
  python3 \
  python3-pip \
  cmake
RUN pip3 install coloredlogs

RUN echo 'deb [arch=amd64] https://download.01.org/intel-sgx/sgx_repo/ubuntu focal main' | tee /etc/apt/sources.list.d/intel-sgx.list

RUN wget -qO - https://download.01.org/intel-sgx/sgx_repo/ubuntu/intel-sgx-deb.key | apt-key add

RUN apt update && apt install -y \
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
  sudo \
  libclang-dev

RUN source "$HOME/.cargo/env" && rustup override set ${RUST_TOOLCHAIN} && ./x.py setup && ./x.py build --release
RUN source "$HOME/.cargo/env" && ./x.py package release $HOME/.local/prusti
RUN echo "[-] Prusti successfully compiled and installed!"

RUN ln -s /usr/lib/x86_64-linux-gnu/libsgx_dcap_quoteverify.so.1 /usr/lib/x86_64-linux-gnu/libsgx_dcap_quoteverify.so
RUN ln -s /usr/lib/x86_64-linux-gnu/libsgx_dcap_ql.so.1 /usr/lib/x86_64-linux-gnu/libsgx_dcap_ql.so

WORKDIR /root
RUN git clone ${MIRAI_GIT_REPO}
WORKDIR /root/MIRAI
RUN git checkout ${MIRAI_COMMIT}
RUN source "$HOME/.cargo/env" && rustup override set ${RUST_TOOLCHAIN}
RUN source "$HOME/.cargo/env" && cargo install --locked --path ./checker

ENTRYPOINT ["bash", "-l", "-c"]
