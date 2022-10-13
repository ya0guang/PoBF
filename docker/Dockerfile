FROM ubuntu:20.04

ARG SGX_SDK_VERSION=2.17.100.3
ARG PRUSTI_GIT_REPO=https://github.com/viperproject/prusti-dev.git
ARG PRUSTI_COMMIT=b74ed28a0d8b946c67fb85f56edbeb81346aabd9
ARG RUST_COMP="rust-src rustc-dev llvm-tools-preview rustfmt rust-analysis"
ARG RUST_TOOLCHAIN

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

RUN wget https://download.01.org/intel-sgx/latest/linux-latest/distro/ubuntu20.04-server/sgx_linux_x64_sdk_${SGX_SDK_VERSION}.bin
RUN chmod +x sgx_linux_x64_sdk_2.17.100.3.bin 
RUN printf "no\n/opt/intel\n" | ./sgx_linux_x64_sdk_2.17.100.3.bin
RUN echo 'source /opt/intel/sgxsdk/environment' >> /root/.bashrc

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN echo 'source "$HOME/.cargo/env"' >> /root/.bashrc
RUN source "$HOME/.cargo/env" && rustup toolchain install ${RUST_TOOLCHAIN}

RUN echo "[+] Configuring Prusti..."
RUN git clone ${PRUSTI_GIT_REPO}

WORKDIR /root/Downloads/prusti-dev
RUN git checkout ${PRUSTI_COMMIT}
RUN source "$HOME/.cargo/env" && rustup override set ${RUST_TOOLCHAIN}
RUN source "$HOME/.cargo/env" && rustup component add --toolchain ${RUST_TOOLCHAIN} ${RUST_COMP}
RUN apt update && DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC \ 
    apt install -y \
    unzip \
    default-jre \
    openssl \
    libssl-dev \
    pkg-config

RUN source "$HOME/.cargo/env" && ./x.py setup && ./x.py build --release

RUN echo "[-] Prusti successfully configured and installed!"

ENTRYPOINT ["bash", "-l", "-c"]
