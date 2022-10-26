DataProvider_Rust_Flags ?= --release

.PHONY: all clean

all:
	@mkdir bin
	@cargo build $(DataProvider_Rust_Flags)
	@cp target/release/data_provider ./bin

clean:
	@cargo clean
	@rm -r bin