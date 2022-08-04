# Problems
* The enclave.so cannot be properly signed because of mismatched version information when building the enclave?? SDK version
for building is 2.12.
```
SDK version is not correct. The same SDK should be used for enclave building and signing.
The SDK version for building enclave could be obtained by below command:

           $ strings {Enclave.so} | grep SGX_TSTDC_VERSION 

Error happened while signing the enclave.

$ strings {Enclave.so} | grep SGX_TSTDC_VERSION gives empty information.
```

* `incubator-teaclave-sgx-sdk/sgx_crypto/sgx_crypto_sys/tcrypto/ipp/sgx_sm2.cpp` contains a bug in line 527, 
which should be:
```cpp
    if (hash_drg == NULL || hash_drg_len <= 0 ||
        sgx_sm2_order == NULL || sgx_sm2_order_len <=0 ||
        out_key == NULL || out_key_len <= 0) {
        return SGX_ERROR_INVALID_PARAMETER;
    }
```