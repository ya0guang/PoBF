# Problems
* [**SOLVED**] The enclave.so cannot be properly signed because of mismatched version information when building the enclave?? 
  * SDK version for building: 2.12 (should be <= 2.9)
  * GNU C Compiler: `g++ (Debian 11.3.0-3) 11.3.0`
  * Rust Compiler: `rustc 1.61.0-nightly (68369a041 2022-02-22)`
  * OS (Should not be the problem): `Linux kali 5.16.0-kali7-amd64 #1 SMP PREEMPT Debian 5.16.18-1kali1 (2022-04-01) x86_64 GNU/Linux`
```
SDK version is not correct. The same SDK should be used for enclave building and signing.
The SDK version for building enclave could be obtained by below command:

           $ strings {Enclave.so} | grep SGX_TSTDC_VERSION 

Error happened while signing the enclave.

$ strings {Enclave.so} | grep SGX_TSTDC_VERSION gives empty information.
```
**When SDK version reaches 2.9.1 or higher**, the sign tool will check if `enclave.so` contains the symbol `SGX_TSTDC_VERSION`.
The third-party repo for incubator-teaclave-sgx-sdk is just too old so that it will not produce this symbol when building the 
enclave... [**Update**] This is due to old version of Rust SDK and incompatibility of (not fully uninstalled) Intel SGX SDK.

<s>However, when I run the script `./enclave/demo_verify.sh` (which later invokes `./verfier/pobf-verify.py`),
everything goes very well except that the enclave is not signed either.</s> <- Simply because output is directed
to `/dev/null`...

* [**SOLVED**] (Due to a bug in `Makefile`.) If I invoke the app directly in the terminal by (SIMULATION MODE)
```shell
$ ./app cal ../key.bin ../data.enc
```
, it will report the shared object file missing error:
```shell
./app: error while loading shared libraries: libsgx_urts.so: cannot open shared object file: No such file or directory
```

It seems that the binary needs the `libsgx_urts.so` library but this library is nowhere to be found.

Solution:
```makefile
app:
    @cd app && SGX_SDK=$(SGX_SDK) SGX_MODE=$(SGX_MODE) cargo build $(App_Rust_Flags) # Add SGX_MODE env var; otherwise build.rs cannot read it and will link to so for hardware.
```

* `incubator-teaclave-sgx-sdk/sgx_crypto/sgx_crypto_sys/tcrypto/ipp/sgx_sm2.cpp` (commit sha256: 7e1b671cbad5cb8f62d628f562fad32dbfdb2a40)
contains a bug in line 527, 
which should be:
```cpp
    if (hash_drg == NULL || hash_drg_len <= 0 ||
        sgx_sm2_order == NULL || sgx_sm2_order_len <=0 ||
        out_key == NULL || out_key_len <= 0) {
        return SGX_ERROR_INVALID_PARAMETER;
    }
```
Otherwise, the project won't compile.

* [**SOLVED**] The binary cannot be executed if built in simulation mode.
```shell
$ export SGX_MODE=SIM && make -C .. run && ./app
  zsh: illegal hardware instruction ./app
```
If we build the enclave without environment variable `SGX_MODE`, the Rust teaclave SDK will be build in HW mode. So the 
final binary will report the `ModeIncompatible` error.
```shell
===== Run Enclave =====

[+] Trying to init enclave...
[-] Init Enclave Failed, reason: "ModeIncompatible"!
```
<s>Not sure if this is due to OS incompatibility (I am using Kali Linux) or incorrect Intel SDK version?</s>

I have written sample enclave in C++ to test if the SDK works, and it correctly outputs expected results.

Solution: Although the Rust SGX SDK won't produce the string `SGX_TSTDC_VERSION`, we can use the new version of `sgx_sign`
but with slight modification to bypass version check (I think the SDK *should* produce the symbol, though).

* Modification on global heap allocator for Rust `collections` and `Box` types. When the crate `sgx_no_tstd` is imported
to the project, it will override the global allocator to `System` which binds to enclave `libc`'s API for memory allocation. We
cannot implement a custom allocator once this crate is imported. <u>I applied `system.patch` on `sgx_alloc/src/system.rs`.</u>

* Stack and register cleanups: maybe we need to manually perform LLVM pass on functions at Machine Code level to ensure all 
sensitive data on the stack can be erased (like some `X86StackZeroizePass.cpp`). However, if there is IR optimization, some unexpected results may occur (do we
need to consider this?):

  * Assembler will temporarily spill register onto stacks due to register pressure (very likely). <- cannot be avoided at
    a high level. This also happens when calling a function (caller-saved or callee-saved registers on stack).
  * Extended registers.
  
  Maybe useful external crates:
    * `llvm-ir` for IR parsing and modification.
    * `llvm-sys` for C API binding to LLVM.
  
  Possible solution: obtain the stack pointer and then calculate the size of current stack frame. Finally, pad zeros to
  with the pointer (e.g., `memset_s`), but can be optimized away accidentally by the compiler...
  
  Consider writing a pass on code generation and rebuild LLVM for specific usage(?