.PHONY: all
all: PlatformSGX DataProvider

######## Platform SGX ########

.PHONY: PlatformSGX
PlatformSGX: platform_sgx
	$(MAKE) -C platform_sgx

######## Verification ########
# TODO

.PHONY: verify

######## Run Service ########
# TODO

.PHONY: run
run: $(App_Name) $(RustEnclave_Signed_Name)
	@echo -e '\n===== Run Enclave =====\n'
	@cd bin && ./app

####### Data Owner #######
DataProvider_Rust_Flags := --release

.PHONY: DataProvider
DataProvider:
	@cd data_provider && cargo build $(DataProvider_Rust_Flags)
	@cd data_provider && cp target/release/data_provider ../bin

.PHONY: clean
clean:
	@cd platform_sgx && $(MAKE) clean
	@cd data_provider && cargo clean
