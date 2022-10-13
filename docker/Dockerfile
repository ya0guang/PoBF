FROM ubuntu:20.04

ARG SGX_SDK_VERSION=2.17.100.3
ARG RUST_TOOLCHAIN

SHELL ["/bin/bash", "-c"] 

RUN apt update && apt install -y \
    build-essential \
    libtool \
    autoconf \
    python \
    curl \
    git \
    wget

RUN echo 'deb [arch=amd64] https://download.01.org/intel-sgx/sgx_repo/ubuntu focal main' | tee /etc/apt/sources.list.d/intel-sgx.list

RUN wget -qO - https://download.01.org/intel-sgx/sgx_repo/ubuntu/intel-sgx-deb.key | apt-key add

RUN apt update && apt install -y \
    libsgx-epid \
    libsgx-quote-ex \
    libsgx-dcap-ql \
    libsgx-urts-dbgsym \
    libsgx-enclave-common-dbgsym \
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

ENTRYPOINT ["bash", "-l", "-c"]
