DataProvider_Rust_Flags ?= --release
DataProvider_Rust_Files := $(wildcard ./src/*.rs)
DataProvider_Enclave_Objects := ./lib/libenclave_u.a

.PHONY: all clean

all: tvl_enclave app

tvl_enclave: 
	@mkdir -p bin
	@mkdir -p lib
	@$(MAKE) -C ./tvl
	@cp ./tvl/enclave.signed.so ./lib
	$(AR) rcsD $(DataProvider_Enclave_Objects) ./tvl/App/Enclave_u.o

app: $(DataProvider_Rust_Files)
	@cargo build $(DataProvider_Rust_Flags)
	@cp target/release/data_provider ./bin
	
clean:
	@cargo clean
	@rm -rf bin 
	@rm -rf lib
	@cd ./tvl && $(MAKE) clean