# The Rust Implementation of the Data Provider (a.k.a., the Service Provider)

The service provider will need to attest to the user that the target enclaving is indeed running on a genuine Intel SGX-enabled platform. This is done by the remote attestation which involved three entities: the platform (application enclave and its quoting enclave), the Service Provider (SP), which, of course, could also run on the same platform where the application runs, and the Intel Attestation Service (IAS) as the arbitrator. In out Proof-of-Being-Forgotten framework, this is also served as a intermediate entity that transfers the user data to the application enclave.

Basically, remote attestation is a process of verifying an enclave’s `REPORT` by transforming `REPORT` to `QUOTE` using the attestation key. The quoting enclave is built by Intel and is available if the CPU supports SGX.

Since we will rely on the IAS to complete the attestation, we will use the EPID-based remote attestation.

## Run The Data Provider

To run the compiled binary, you will need to provide with a valid manifest file located in the root directory of the data provider as follows.

```json
{
  // Can be found at https://api.portal.trustedservices.intel.com/developer
  "spid": "1234567890ABCDEF1234567890ABCDEF",
  "ias_key": "1234567890abcdef1234567890abcdef",
  "linkable": true
}
```

You can also change the path in the `Makefile`:

```makefile
DataProvider_Manifest_Path ?= ../path/to/manifest
```

Or run the binary by

```shell
$ DataProvider_Manifest_Path="some_path" make run
```