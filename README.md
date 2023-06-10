# PoBF-Compliant Framework (PoCF) Reference Implementation

This repository contains all the codebase of the reference implementation of a PoBF-Compliant Framework (PoCF) where the term "PoBF" refers to *Proof of Being Forgotten*, a novel security and privacy properties for ensuring that in-TEE programs would not cause any leakage and secret residue.

## Citing the Paper

You can use the following bibtex code to cite our work.

```tex
@inproceedings{chen2023verified,
  title={A Verified Confidential Computing as a Service Framework for Privacy Preservation},
  author={Chen, Hongbo and Chen, Haobin Hiroki and Sun, Mingshen and Li, Kang and Chen, Zhaofeng and Wang, Xiaofeng},
  booktitle={32nd USENIX Security Symposium (USENIX Security 23)},
  year={2023}
}
```

## Prerequisites

### Hardware
To properly configure, install, and run the confidential computing task using the PoCF library, you need to have one of the following machines:

* A PC that supports SGX (we recommend that you use SGX2 for the best performance).
* A virtual machine that runs on a SEV host (such VMs can be rented from Azure).

### System Requirements

We have only tested PoCF on the following system. By its design, it is able to run on any Linux distribution, but due to some platform-specific designs, the compatilibty issue may occur.

* Ubuntu 20.04 (tested) /22.04 (may not work)

### Packages and Toolchains

0. Prepare

1. Install requires packages:

```sh
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
  cmake \
  libclang-dev \
  default-jdk \
  llvm-10
```

Note that if you want to plot correctly, please install tex-live by `sudo apt install -y texlive-full`. For a successful compilation of TVM, please install cmake >= 3.18:

```sh
wget -O - https://apt.kitware.com/keys/kitware-archive-latest.asc 2> /dev/null | gpg --dearmor - | sudo tee /etc/apt/trusted.gpg.d/kitware.gpg > /dev/null
sudo apt-add-repository 'deb https://apt.kitware.com/ubuntu/ focal main' 
sudo apt update
sudo apt install -y cmake 
```

2. Install Rust:

```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

In the root directory of this repository, run

```sh
rustup -V
```

which automatically reads the nightly toolchain version and installs the required toolchain version and components.

3. Prepare Python dependencies:

```sh
pip3 install -r ./requirements.txt
```

It is recommended that you manage the dependencies using Anaconda or pyenv.

### Verifiers

#### Coq

Please install `opam` first and install `coq` with opam:

```sh
# opam
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
opam init
opam switch default
eval $(opam env)

# coq
opam pin add coq 8.13.2
opam repo add coq-released https://coq.inria.fr/opam/released
```

#### Mirai and Prusti

Please run the scripts at `./scripts`:

```sh
./prepare_mirai.sh
./prepare_prusti.sh
```

### TEE-specific Configurations

*If you are using SGX:* Please first install the required SGX SDK and libraries before building Rust library:

```sh
sudo echo 'deb [arch=amd64] https://download.01.org/intel-sgx/sgx_repo/ubuntu focal main' | tee /etc/apt/sources.list.d/intel-sgx.list
sudo wget -qO - https://download.01.org/intel-sgx/sgx_repo/ubuntu/intel-sgx-deb.key | apt-key add
sudo apt update && apt install -y \
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

# Install SDK.
wget https://download.01.org/intel-sgx/sgx-linux/2.17.1/distro/ubuntu20.04-server/sgx_linux_x64_sdk_2.17.101.1.bin
chmod +x ./sgx_linux_x64_sdk_2.17.101.1.bin
sudo ./sgx_linux_x64_sdk_2.17.101.1.bin
```

The installation path of the SGX SDK is expected to be set to `/opt/intel`. Do *not* change it as doing so would break the build script of PoCF. Also do *not* install SDK other than the 2.17.1 version.

A one-shot installation and configuration script is located at the root directory:

```sh
./setup.sh
```

*If you want to use DCAP-baed remote attestation:*

1. Add yourself to `sgx_prv` group (if you do not do this, you need to execute the enclave program with sudo privilege):

```sh
sudo adduser `id -un` sgx_prv
```

You may need to re-login to allow the operation to take effect.

2. Register yourself as an Intel developer at [this portal](https://api.portal.trustedservices.intel.com/provisioning-certification) and subscribe to the Product Intel® Software Guard Extensions Provisioning Certification Service.

Finally, follow the instructions in [DCAP Quick Installation Guide](https://software.intel.com/content/www/us/en/develop/articles/intel-software-guard-extensions-data-center-attestation-primitives-quick-install-guide.html). You will be requested with a working key.

*If you are using SEV:* there is nothing to be configured.

## Verification towards PoCF

We provide a simple Python script under `pobf_verifier` that can verify:

- Whether `unsafe` is forbidden in the source code files.
- Whether OCALL(s) leak sensitive data.
- Whether Rust compiler can compile the code.
- Whether the implementation of the typestate is consistent with the abstract model.


Sample verification:

```sh
$ cd scripts && ./demo-verify.sh
- Check if Prusti is intalled.
  + Found Prusti.
- Verify the PoBF framework...

~/PoBF/platform_sgx/enclave ~/PoBF/scripts
INFO checking if the source code forbids `unsafe` ...

INFO checking unsafe code...
INFO - analyzing file: ./src/mirai_types/task.rs...
INFO   + unsafe code fobidden in ./src/mirai_types/task.rs, clear.
INFO - analyzing file: ./src/mirai_types/mirai_comp.rs...
INFO   + unsafe code fobidden in ./src/mirai_types/mirai_comp.rs, clear.
INFO - analyzing file: ./src/mirai_types/mod.rs...
INFO   + unsafe code fobidden in ./src/mirai_types/mod.rs, clear.
INFO - analyzing file: ./src/vecaes.rs...
INFO   + unsafe code fobidden in ./src/vecaes.rs, clear.
INFO - analyzing file: ./src/pobf.rs...
INFO   + unsafe code fobidden in ./src/pobf.rs, clear.
INFO - analyzing file: ./src/dh.rs...
INFO   + unsafe code fobidden in ./src/dh.rs, clear.
INFO - analyzing file: ./src/bogus.rs...
INFO   + unsafe code fobidden in ./src/bogus.rs, clear.
INFO - analyzing file: ./src/ocall.rs...
WARNING   + unsafe code not forbidden in ./src/ocall.rs, and this is allowed.
INFO - analyzing file: ./src/userfunc.rs...
INFO   + unsafe code fobidden in ./src/userfunc.rs, clear.
INFO - analyzing file: ./src/db_persistent.rs...
ERROR   + unsafe code not forbidden in ./src/db_persistent.rs, please add `#![forbid(unsafe_code)]` in this file!
INFO - analyzing file: ./src/pobf_verifier.rs...
INFO   + unsafe code fobidden in ./src/pobf_verifier.rs, clear.
INFO - analyzing file: ./src/networking_utils.rs...
WARNING   + unsafe code not forbidden in ./src/networking_utils.rs, and this is allowed.
INFO - analyzing file: ./src/utils.rs...
INFO   + unsafe code fobidden in ./src/utils.rs, clear.
INFO - analyzing file: ./src/lib.rs...
WARNING   + unsafe code not forbidden in ./src/lib.rs, and this is allowed.
INFO checking if type state is consistent with the abstract model using Prusti...

INFO Prusti verification passed.

/home/panda/PoBF/platform_sgx/entopclave
INFO Building PoBF binary...
INFO Trying to test run the PoBF binary...
INFO Finished!
INFO checking possible leakage through OCALLs...

INFO Checking leakage of the PoBF framework by MIRAI. The userfunc is not checked at this time.
INFO The PoBF framework does not leak any secret according to MIRAI!
INFO Checking leakage of the PoBF framework by MIRAI when userfunc is being executed.
ERROR PoBF only allows printing non-secret-tainted values from within the enclave. Consider removing it?
WARNING The detailed explaination of this error type [vio-ocall] can be found in the document.
warning: possible false verification condition
  --> src/userfunc.rs:21:9
   |
21 |         verified_log!(SecretTaint, "The 0-th item is {} in sample_add", input[0]);
   |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


ERROR `no_leakage` verification failed: leakage(s) found by MIRAI.

INFO checking possible secret residue...

INFO Compiler verification started.
INFO running [['cargo', 'build', '--message-format=json', '--features=sgx,leak_log,task_sample']]
```

Indeed, the function source code of `sample_add` indeed has some potential leakage.

```rust
/// See `platform_sgx/enclave/src/userfunc.rs`.
pub fn sample_add(input: Vec<u8>) -> Vec<u8> {
    let step = 1;

    // MIRAI can detect this bug.
    #[cfg(feature = "leak_log")]
    {
        // Try remove this verified_log! Then MIRAI verifies.
        #[cfg(mirai)]
        verified_log!(SecretTaint, "The 0-th item is {} in sample_add", input[0]);
    }

    let mut output = Vec::new();
    for i in 0..input.len() {
        output.push(step + input[i]);
    }

    #[cfg(mirai)]
    add_tag!(&output, SecretTaint);

    output
}
```

> **Warning**
>
> Do not directly run the scripts under `pobf_verifier/pobf-verify` as the path is the incorrect.

Z3 will consume a lot of memory, and we are working on this issue.

## Build and Run on SGX

Currently we have the following CC tasks available (located under `cctasks`):

* `db`: The in-memory KV store build atop the `hashbrown` crate.
* `evaluation_tvm`: The ResNet-152 model deployed by Apache TVM.
* `fann`: The FANN task.
* `fasta`: The genomic sequence generator.
* `polybench`: A series of matrix algorithms for microbenchmarks.
* `sample_add`: A simple task that increments each element in a vector.

All these tasks are `no_std` and can be easily integrated in any environment.

> **Note**
>
> For the TVM task, please install TVM properly. The instruction can be found in [README.md](cctasks/evaluation_tvm/README.md).

All these tasks are optional dependencies of the PoCF application which can be selected using the Rust feature in the form of `task_*` (where `*` is the task name). For example, one runs the following command to compile the enclave program that executes the `fasta` task:

```sh
SGX_MODE=HW TASK=task_fasta make -j
```

The compiled binaries and libraries are located under `platform_sgx/{bin,lib}`. Then you can run the binary by

```sh
$ cd platform_sgx/bin
$ ls
app  enclave.signed.so  enclave.so
$ ./app 127.0.0.1 1234 # address and port
[2023-06-08T06:59:34Z INFO  app] [+] Listening to 127.0.0.1:1234
[2023-06-08T06:59:34Z INFO  app] [+] Initializing the enclave. May take a while...
[2023-06-08T07:00:03Z INFO  app] [+] Init Enclave Successful, eid: 2!
```

To connect to the remote enclave, you need to run the data provider. We provide with a sample data provider that can be found under `data_provider`. The following command build and run it with a custom manifest as its input.

```sh
cd data_provider && make -j
cd bin && ./data_provider run ../manifest.json
```

The manifest specifies the behavior of the data provider:

```json
{
  "address": "127.0.0.1",
  "port": 1234,
  // DCAP-based remote attestation does not require this field.
  "spid": "",
  // DCAP-based remote attestation does not require this field.
  "ias_key": "",
  "linkable": true,
  "data_path": "some/path/to/the/data",
  // 0 => EPID-based remote attestation.
  // 1 => DCAP-based remote attestation.
  "ra_type": 1
}
```

Some pre-generated data is located under `data/task_name/data.bin` along with the corresponding manifest file.

