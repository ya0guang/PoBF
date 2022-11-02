# The Rust Implementation of the Data Provider (a.k.a., the Service Provider)

The service provider will need to attest to the user that the target enclaving is indeed running on a genuine Intel SGX-enabled platform. This is done by the remote attestation which involved three entities: the platform (application enclave and its quoting enclave), the Service Provider (SP), which, of course, could also run on the same platform where the application runs, and the Intel Attestation Service (IAS) as the arbitrator. In out Proof-of-Being-Forgotten framework, this is also served as a intermediate entity that transfers the user data to the application enclave.

Basically, remote attestation is a process of verifying an enclave’s `REPORT` by transforming `REPORT` to `QUOTE` using the attestation key. The quoting enclave is built by Intel and is available if the CPU supports SGX.

## EPID-based Attestation

### Run The Data Provider

To run the compiled binary, you will need to provide with a valid manifest file located in the root directory of the data provider as follows.

```json
{
  // Can be found at https://api.portal.trustedservices.intel.com/developer
  "spid": "1234567890ABCDEF1234567890ABCDEF",
  "ias_key": "1234567890abcdef1234567890abcdef",
  "linkable": true,
  "data_path": "../../data/data.bin"
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

## DCAP based Attestation

You will need to first install the required libraries (if you deploy the data provider on another machine, you will also need to install the Intel SGX-SDK):

```shell
$ deb [arch=amd64] https://download.01.org/intel-sgx/sgx_repo/ubuntu focal main | tee /etc/apt/sources.list.d/intel-sgx.list
$ sudo apt update && sudo apt -y install libsgx-dcap-quote-verify libsgx-dcap-quote-verify-dev
```

Then you need to configure the Provisioning Certificate Caching Service (PCCS). It retrieves PCK Certificates and other collaterals on-demand using the internet at runtime, and then caches them in local database. The PCCS exposes similar HTTPS interfaces as Intel's Provisioning Certificate Service.

* Install node.js (Version 12.22 or later)
  ```shell
  $ curl -sL https://deb.nodesource.com/setup_16.x | sudo -E bash -
  $ sudo apt install -y nodejs
  ```
* Install dependencies (python3, cracklib-runtime) if they are not installed. Also make sure "python" is linked to "python3":
  ```shell
  $ sudo apt-get install python3 cracklib-runtime
  ```
* Install PCCS.
  ```shell
  $ sudo apt install -y sgx-dcap-pccs
  ```
  Note that reinstalling PCCS will remove the cache.

  The installation will run the PCCS setup script, which will ask you several questions.

  `Do you want to configure PCCS now? (Y/N)`
  Answer "Y" to this question.

  `Set HTTPS listening port [8081] (1024-65535)`
  Accept the default listening port of 8081, or select a non-privileged port number.

  `Set the PCCS service to accept local connections only? [Y] (Y/N)`
  Answer "N" to this question. We want the PCCS service to accept connections from other systems.

  `Set your Intel PCS API key (Press ENTER to skip)`
  Enter either your primary or secondary key.

  `Choose caching fill method : [LAZY] (LAZY/OFFLINE/REQ)`
  Answer "REQ" to this question. This places the caching service in the "on request" mode, which means it will fetch the attestation collateral for hosts as provisioning requests are received. For more information on the PCCS caching modes, see the white paper titled Design Guide for Intel® SGX Provisioning Certificate Caching Service (Intel® SGX PCCS) .

* Install the PCK id retriver.
  ```shell
  $ sudo apt install sgx-pck-id-retrieval-tool
  ```
  Now the provisioning tool needs to be configured so that it knows how to contact the caching service. Edit the configuration file `/opt/intel/sgx-pck-id-retrieval-tool/network_setting.conf` and make the following changes:

  1. Change the `PCCS_URL` to match your caching service’s location.
  Uncomment the user_token parameter, and set it to the user password you created when configuring the PCCS
  2. Set the `proxy_type` to fit your environment (most likely this will be “direct”)
  3. Ensure `USE_SECURE_CERT` is set to “FALSE” since we’re using a self-signed certificate for testing purposes. In a production environment, this should be set to “TRUE”.
  4. Set the `user_token` to the password configured when PCCS was installed.

### Provisioning
Run the following command under the root directory `./PoBF`.
  ```shell
  $ sudo PCKIDRetrievalTool

  Intel(R) Software Guard Extensions PCK Cert ID Retrieval Tool Version 1.14.100.3

  Warning: platform manifest is not available or current platform is not multi-package platform.
  the data has been sent to cache server successfully and pckid_retrieval.csv has been generated successfully!
  ```

### Verification

Although we do not require the relying party (a.k.a., the data provider) to have an SGX-enabled platform, the QvE's identity should be verified via another enclave on the platform of data provider. Untrusted QVL when the QvE information is set to null. Quote verification would be done inside untrusted QVL library, and the verifier can use this way on a non-SGX capable system, but the result *cannot* be cryptographically authenticated in this mode.

### High-level Workflow

1. Data provider sends the attestation request to the application enclave.
2. The application enclave asks the quoting enclave to generate a quote along with the current platform target information.
3. The quote and target information are forwarded to data provider.
4. The data provider applies either QvE- or QVL-based verification of the quote. The Verify Quote API will verify that the application’s enclave `REPORT` was generated by an SGX enclave running with SGX protections but it does not identify whose enclave it is.
5. (QvE-based only) The data provider verifies the identity of the QvE. Intel (R) SGX SDK provides a library named `sgx_dcap_tvl` to help the verifier to verify QvE's identity, and this requires a working SGX hardware. Since the QvE on the platform is not verified as a genuine Intel signed enclave, so we need to verify it so that we can trust it.

### Glossary

* Quoting Enclave (QE): Intel signed enclave that is used to issue quotes on the SGX-capable platform which may be controlled by a malicious owner. E.g., the AWS, Azure cloud provider.
* Quoting Verification Enclave (QvE): Intel signed enclave that is trusted by the attestation infrastructure owner to *verify* QE generated quotes.
* Quoting Verfiication Library (QVL): An auxiliray library that performs the same verification steps as a QvE except that it is not crypographically trusted. Used when the data provider does not support SGX.