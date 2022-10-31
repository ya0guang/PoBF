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
RA_TYPE ?= 1

DataProvider_Manifest_Path ?= ../manifest.json
# Bind address and port.
Server_Address := 127.0.0.1
Server_Port := 1234
# CI arguments for the enclave.
Enclave_App_Arguments := cal $(Server_Address) $(Server_Port)
# CI arguments for data provider.
DataProvider_Arguments := run $(Server_Address) $(Server_Port) $(DataProvider_Manifest_Path) $(RA_TYPE)

.PHONY: run
run: $(App_Name) $(RustEnclave_Signed_Name)
	@printf '\n\e[0;36m===== Run Enclave =====\e[0m\n'
	@cd ./platform_sgx/bin && ./app $(Enclave_App_Arguments) &
	@sleep 1
	@printf '\n\e[0;36m===== Run Data Provider =====\e[0m\n'
	@cd ./data_provider/bin && ./data_provider $(DataProvider_Arguments)

####### Data Owner #######
.PHONY: DataProvider
DataProvider: data_provider
	$(MAKE) -C data_provider

.PHONY: clean
clean:
	@cd platform_sgx && $(MAKE) clean
	@cd data_provider && $(MAKE) clean
