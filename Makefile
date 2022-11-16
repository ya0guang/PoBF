.PHONY: all
all: PlatformSGX DataProvider

######## Platform SGX ########

.PHONY: TVM PlatformSGX
TVM:
	$(MAKE) -C cctasks/evaluation_tvm/model_deploy

PlatformSGX: TVM platform_sgx
	@pkill app || true
	$(MAKE) -C platform_sgx

######## Verification ########
# TODO

.PHONY: verify

######## Run Service ########
DataProvider_Manifest_Path ?= ../manifest.json
# Bind address and port.
Server_Address := 127.0.0.1
Server_Port := 1234
# CI arguments for the enclave.
Enclave_App_Arguments := $(Server_Address) $(Server_Port)
# CI arguments for data provider.
DataProvider_Arguments := run $(DataProvider_Manifest_Path)

.PHONY: run
run: $(App_Name) $(RustEnclave_Signed_Name)
	@pkill app || true
	@printf '\n\e[0;36m===== Run Enclave =====\e[0m\n'
	@cd ./platform_sgx/bin && ./app $(Enclave_App_Arguments) &
	@sleep 1
	@printf '\n\e[0;36m===== Run Data Provider =====\e[0m\n'
# TODO: Run in parallel.
	@cd ./data_provider/bin && ./data_provider $(DataProvider_Arguments)
	@pkill app

####### Data Owner #######
.PHONY: DataProvider
DataProvider: data_provider
	$(MAKE) -C data_provider

.PHONY: clean
clean:
	@cd platform_sgx && $(MAKE) clean
	@cd data_provider && $(MAKE) clean
	@cd cctasks/evaluation_tvm/model_deploy && $(MAKE) clean
	@cd pobf_state && cargo clean
