# Source Files for Other Platforms

## Tasks for `Occlum`
You can install `Occlum` on the host machine by package manager.
```sh
$ echo 'deb [arch=amd64] https://occlum.io/occlum-package-repos/debian focal main' | tee /etc/apt/sources.list.d/occlum.list
$ wget -qO - https://occlum.io/occlum-package-repos/debian/public.key | sudo apt-key add -
$ sudo apt update
$ sudo apt install -y --no-install-recommends occlum ca-certificates gnupg2 jq make gdb wget libfuse-dev libtool tzdata
$ echo 'source /etc/profile' >> ~/.bashrc # or ~/.zshrc
```

Next, you will need to set up a the Occlum rust toolchain for Occlum.
```sh
$ wget https://raw.githubusercontent.com/occlum/occlum/master/tools/toolchains/rust/build.sh
$ chmod +x ./build.sh
$ sudo -E PATH="$HOME/.cargo/bin:$PATH" bash -c ./build.sh
$ echo 'export PATH="/opt/occlum/toolchains/rust/bin:/opt/occlum/build/bin:$PATH"' >> ~/.bashrc # or ~/.zshrc
```

## Tasks for `Gramine`
The networking interface and remove attestation are integrated with `mbedtls` ported in shared libraries in the `Gramine` LibOS package. This project uses the RA-TLS libraries `ra_tls_attest.so` for server and `ra_tls_verify_epid.so`/ `ra_tls_verify_dcap.so` for client. These libraries are
installed together with Gramine. For DCAP attestation, the DCAP software infrastructure must be installed and work correctly on the host by the corresponding kernel driver `/dev/isgx` or `/dev/sgx/enclave`.

`Gramine` provides quick installation by package manager. You can install it quickly on your machine by the following steps.

```sh
$ sudo curl -fsSLo /usr/share/keyrings/gramine-keyring.gpg https://packages.gramineproject.io/gramine-keyring.gpg
$ echo 'deb [arch=amd64 signed-by=/usr/share/keyrings/gramine-keyring.gpg] https://packages.gramineproject.io/ focal main' | sudo tee /etc/apt/sources.list.d/gramine.list
$ sudo apt update
$ sudo apt install -y gramine-dcap
```

Then you can build and run this project by
```sh
$ TASK=[task_tvm | task_sample | task_fann | task_faste | task_polybench] \
  make app dcap RA_TYPE=dcap -j$((`nproc` + 1)) > /tmp/meta.txt
$ gramine-sgx ./server &
$ RA_TLS_ALLOW_DEBUG_ENCLAVE_INSECURE=1 \
  RA_TLS_ALLOW_OUTDATED_TCB_INSECURE=1 \
  RA_TLS_MRENCLAVE=$(awk '/mr_enclave/ { print $2 }' /tmp/meta.txt | head -1) \
  RA_TLS_MRSIGNER=$(awk '/mr_signer/ { print $2 }' /tmp/meta.txt | head -1) \
  RA_TLS_ISV_PROD_ID=0 \
  RA_TLS_ISV_SVN=0 \
  DATA_PATH=[The path to data.bin]
  ./client dcap
```

We write the core functionalities in Rust (in `rustlib` and `cctasks`) and utilize the attestation framework offered by `Gramine`. The layout is illustrated below.
```txt
server --------> Rust library interfaces (private_computation) --------> Rust cctasks package
                                                                                  |
                                                                                  |
                                          (Links to TVM C runtime)       <--------+
```

## Bare Rust Programs

`rust` folder contains the unmodified code that contains tasks running in native host machine for baseline benchmarking. Compile by

```sh
$ cargo build --release --features=[task_tvm | task_sample | task_fann | task_faste | task_polybench]
```

## Evaluation TVM
`evaluation_tvm` is a shared package that compiles into a static library (self-contained) and can be linked by `Gramine` or the bare Rust programs for ResNet152 predictions. The static library `libevaluation_tvm.a` must be linked against a working libc runtime (whereas PoBF enclave links it against `libsgx_tstdc.a`), which is automatically done by `Gramine` and Rust linker.

## Native Enclave

This is implemented using the same framework of PoBF where the previous `pobf_workflow` is disabled by conditional compilation `#[cfg(feature = "native_enclave")]`. The modified `pobf_workflow` of this enclave is just a series of function calls and does not involve the type state.
