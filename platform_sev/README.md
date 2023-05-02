# PoBF on AMD-SEV

This folder contains the code base for running our Proof-of-Concept implementation of PoBF on VM-based TEEs (i.e., SEV). We utilize the implementation of Microsoft Azure's attestation library, so you must need to run the code on an Azure EPYC-3rd instance to ensure that works as expected.

Before that, make sure the client library is properly installed. You can install the library by:

```sh
sudo apt install -y libcurl4-openssl-dev libjsoncpp-dev libboost-all-dev nlohman-json3-dev
wget https://packages.microsoft.com/repos/azurecore/pool/main/a/azguestattestation1/azguestattestation1_1.0.5_amd64.deb
sudo dpkg -i ./azguestattestation1_1.0.5_amd64.deb
```

## Some Minor Issues

* Using an old nightly Rust toolchain will cause the program to panic due to `segmentation fault` in `clear_on_drop`.
