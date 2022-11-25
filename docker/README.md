# Build the image

```sh
docker build -t ya0guang/pobf --build-arg RUST_TOOLCHAIN=$(cat ../rust-toolchain) .
```

# Run the image WITH SGX support

## Interactive Shell

```sh
docker run -it --entrypoint /bin/bash -v /var/run/aesmd:/var/run/aesmd --device=/dev/sgx/enclave --device=/dev/sgx/provision -v $(pwd)/..:/Code/PoBF -v ya0guang/pobf
```

## Simple Commands

```sh
docker run -it --entrypoint /bin/bash -v /var/run/aesmd:/var/run/aesmd --device=/dev/sgx/enclave --device=/dev/sgx/provision -v $(pwd)/..:/Code/PoBF -v ya0guang/pobf "COMMAND_TO_RUN"
```

e.g., `make` and `make clean`.
