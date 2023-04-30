.phony: all clean

all: ./attestation_lib/libsev_attestation.so
	@cargo build -r

./attestation_lib/libsev_attestation.so:
	@$(MAKE) -C ./attestation_lib

clean:
	@cargo clean
	@$(MAKE) -C ./attestation_lib clean
