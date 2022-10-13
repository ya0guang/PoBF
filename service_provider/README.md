# The Rust Implementation of the Service Provider (SP)

The service provider  will need to attest to the user that the target enclaving is indeed running on a genuine Intel SGX-enabled platform. This is done by the remote attestation which involved three entities: the platform (application enclave and its quoting enclave), the Service Provider (SP), which, of course, could also run on the same platform where the application runs, and the Intel Attestation Service (IAS) as the arbitrator.

Basically, remote attestation is a process of verifying an enclave’s `REPORT` by transforming `REPORT` to `QUOTE` using the attestation key. The quoting enclave is built by Intel and is available if the CPU supports SGX.

Since we will rely on the IAS to complete the attestation, we will use the EPID-based remote attestation.

## Run SP.

```shell
$ cargo run -- run [app_addr] [add_port] [spid] [primary or secondary key]
```

The SPID and keys can be found in the Intel Developer Zone.