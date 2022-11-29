#!/bin/bash

docker run -it --privileged -v /dev/sgx_enclave:/dev/sgx/enclave -v /dev/sgx_provision:/dev/sgx/provision -v ~/PoBF:/root/PoBF -v ~/tvm:/root/tvm --net="host" occlum/occlum:occulum-latest-ubuntu20.04
