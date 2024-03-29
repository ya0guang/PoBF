ARCH_LIBDIR ?= /lib/$(shell $(CC) -dumpmachine)

ifeq ($(DEBUG),1)
GRAMINE_LOG_LEVEL = debug
CFLAGS += -O0 -ggdb3
else
GRAMINE_LOG_LEVEL = error
CFLAGS += -O2
endif

CFLAGS += -fPIE
LDFLAGS += -pie

RA_TYPE ?= none
RA_CLIENT_SPID ?=
RA_CLIENT_LINKABLE ?= 0
TASK ?= task_sample

.PHONY: all
all: app epid  # by default, only build EPID because it doesn't rely on additional (DCAP) libs

.PHONY: app
app: ssl/server.crt mbedtls/.mbedtls_configured server.manifest.sgx server.sig server.token client

.PHONY: epid
epid: client_epid.manifest.sgx client_epid.sig client_epid.token

.PHONY: dcap
dcap: client_dcap.manifest.sgx client_dcap.sig client_dcap.token

############################# SSL DATA DEPENDENCY #############################

# SSL data: key and x.509 self-signed certificate
ssl/server.crt: ssl/ca_config.conf
	openssl genrsa -out ssl/ca.key 2048
	openssl req -x509 -new -nodes -key ssl/ca.key -sha256 -days 1024 -out ssl/ca.crt -config ssl/ca_config.conf
	openssl genrsa -out ssl/server.key 2048
	openssl req -new -key ssl/server.key -out ssl/server.csr -config ssl/ca_config.conf
	openssl x509 -req -days 360 -in ssl/server.csr -CA ssl/ca.crt -CAkey ssl/ca.key -CAcreateserial -out ssl/server.crt

############################# MBEDTLS DEPENDENCY ##############################

# This download is done to get headers in include/, because we currently fail to provide the headers
# (`pkg-config --cflags mbedtls_gramine` in the below CFLAGS line returns a non-existing directory).
# TODO: install mbedtls_gramine headers during Gramine install, and use them in below CFLAGS line.

MBEDTLS_VERSION ?= 3.2.1
MBEDTLS_SRC ?= mbedtls-$(MBEDTLS_VERSION).tar.gz
MBEDTLS_URI ?= \
	https://github.com/ARMmbed/mbedtls/archive \
	https://packages.gramineproject.io/distfiles
MBEDTLS_HASH ?= 5850089672560eeaca03dc36678ee8573bb48ef6e38c94f5ce349af60c16da33

ifeq ($(DEBUG),1)
MBED_BUILD_TYPE=Debug
else
MBED_BUILD_TYPE=Release
endif

$(MBEDTLS_SRC):
	./download --output $@ $(foreach mirror,$(MBEDTLS_URI),--url $(mirror)/$(MBEDTLS_SRC)) --sha256 $(MBEDTLS_HASH)

.SECONDARY: mbedtls/.mbedtls_downloaded
mbedtls/.mbedtls_downloaded: $(MBEDTLS_SRC)
	tar --touch -xzf $(MBEDTLS_SRC) > /dev/null 2>&1
	mv mbedtls-mbedtls-$(MBEDTLS_VERSION) mbedtls
	touch $@

.SECONDARY: mbedtls/.mbedtls_configured
mbedtls/.mbedtls_configured: mbedtls/.mbedtls_downloaded
	cd mbedtls && ./scripts/config.pl set MBEDTLS_CMAC_C MBEDTLS_ERROR_C
	touch $@

######################### CLIENT/SERVER EXECUTABLES ###########################
RUST_LIB_DIR := ./rustlib/target/release
# TODO: use `$(shell pkg-config --cflags mbedtls_gramine)` instead of local mbedtls includes
CFLAGS += -I./mbedtls/include
CXXFLAGS := $(CFLAGS) -std=c++11
LDFLAGS += -ldl -Wl,--enable-new-dtags $(shell pkg-config --libs mbedtls_gramine)
SERVER_LDFLAGS = $(LDFLAGS) -L$(RUST_LIB_DIR) -lgramine_task -lpthread

ifeq ($(TASK), task_tvm)
	SERVER_LDFLAGS += -L../evaluation_tvm/target/release -levaluation_tvm
endif

libgramine_task.a: ./rustlib/src/lib.rs ./rustlib/Cargo.toml
	@cd rustlib && RUSTFLAGS="-C link-args=-pie" cargo build --release --features=$(TASK)

libevaluation_tvm.a: ../evaluation_tvm/src/lib.rs ../evaluation_tvm/build.rs ../evaluation_tvm/Cargo.toml
	@cd ../evaluation_tvm && RUSTFLAGS="-C link-args=-pie" cargo build --release

server: src/server.cc mbedtls/.mbedtls_configured libgramine_task.a libevaluation_tvm.a
	@$(CXX) src/server.cc mbedtls/.mbedtls_configured $(CXXFLAGS) $(SERVER_LDFLAGS) -o $@

client: server src/client.cc mbedtls/.mbedtls_configured
	@$(CXX) src/client.cc mbedtls/.mbedtls_configured $(CXXFLAGS) $(LDFLAGS) -o $@

############################### SERVER MANIFEST ###############################

server.manifest: server.manifest.template
	gramine-manifest \
		-Dlog_level=$(GRAMINE_LOG_LEVEL) \
		-Darch_libdir=$(ARCH_LIBDIR) \
		-Dra_type=$(RA_TYPE) \
		-Dra_client_spid=$(RA_CLIENT_SPID) \
		-Dra_client_linkable=$(RA_CLIENT_LINKABLE) \
		$< > $@

# Make on Ubuntu <= 20.04 doesn't support "Rules with Grouped Targets" (`&:`),
# see the helloworld example for details on this workaround.
server.manifest.sgx server.sig: sgx_sign_server
	@:

.INTERMEDIATE: sgx_sign_server
sgx_sign_server: server.manifest server
	gramine-sgx-sign \
		--manifest $< \
		--output $<.sgx

server.token: server.sig
	gramine-sgx-get-token --output $@ --sig $<

########################### CLIENT (DCAP) MANIFEST ############################

client_dcap.manifest: client.manifest.template
	gramine-manifest \
		-Dlog_level=$(GRAMINE_LOG_LEVEL) \
		-Darch_libdir=$(ARCH_LIBDIR) \
		$< >$@

client_dcap.manifest.sgx client_dcap.sig: sgx_sign_client_dcap
	@:

.INTERMEDIATE: sgx_sign_client_dcap
sgx_sign_client_dcap: client_dcap.manifest client
	gramine-sgx-sign \
		--manifest $< \
		--output $<.sgx

client_dcap.token: client_dcap.sig
	gramine-sgx-get-token --output $@ --sig $<

########################### CLIENT (EPID) MANIFEST ############################

client_epid.manifest: client.manifest.template
	gramine-manifest \
		-Dlog_level=$(GRAMINE_LOG_LEVEL) \
		-Darch_libdir=$(ARCH_LIBDIR) \
		$< >$@

client_epid.manifest.sgx client_epid.sig: sgx_sign_client_epid
	@:

.INTERMEDIATE: sgx_sign_client_epid
sgx_sign_client_epid: client_epid.manifest client
	gramine-sgx-sign \
		--manifest $< \
		--output $<.sgx

client_epid.token: client_epid.sig
	gramine-sgx-get-token --output $@ --sig $<

################################## CLEANUP ####################################

.PHONY: clean
clean:
	$(RM) -r \
		*.token *.sig *.manifest.sgx *.manifest server client *.so *.so.* OUTPUT
	cd ./rustlib && cargo clean

.PHONY: distclean
distclean: clean
	$(RM) -r mbedtls/ *.tar.gz ssl/ca.* ssl/server.*
