DataProvider_Rust_Flags ?= --release
DataProvider_Rust_Files := $(wildcard ./src/*.rs)

.PHONY: all clean

all: bin

bin: $(DataProvider_Rust_Files)
	@mkdir -p bin
	@cargo build $(DataProvider_Rust_Flags)
	@cp target/release/data_provider ./bin

clean:
	@cargo clean
	@rm -r bin