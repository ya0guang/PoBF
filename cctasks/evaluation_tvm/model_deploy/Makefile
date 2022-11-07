# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.

MAGENTA := \e[0;35m
NC := \e[0m

# Setup build environment
SGX_SDK ?= /opt/intel/sgxsdk
TVM_HOME ?= $(HOME)/tvm
CRT_ROOT ?= $(TVM_HOME)/build/standalone_crt
ifeq ($(shell ls -lhd $(CRT_ROOT)),)
$(error "CRT not found. Ensure you have built the standalone_crt target and try again")
endif

CRT_SRCS := $(shell find $(CRT_ROOT))

# Set python path.
export PYTHONPATH = $(TVM_HOME)/python:$(shell echo $PYTHONPATH)

DMLC_CORE=${TVM_HOME}/3rdparty/dmlc-core
PKG_COMPILE_OPTS = -g -Wall -O2 -fPIC

PKG_CFLAGS = ${PKG_COMPILE_OPTS} \
	-I${TVM_HOME}/include \
	-I${DMLC_CORE}/include \
	-I${TVM_HOME}/3rdparty/dlpack/include \
	-I. \
	-DDMLC_USE_LOGGING_LIBRARY=\<tvm/runtime/logging.h\>

PKG_LDFLAGS = -pthread -lm

OUT_DIR := ../outlib
BUNDLE := $(OUT_DIR)/libbundle.a
MODEL_ENTRY_SRC := model_entry.c
MODEL_ENTRY := $(OUT_DIR)/libmodel_entry.a
PYTHON_MODEL := $(OUT_DIR)/devc.o $(OUT_DIR)/lib0.o $(OUT_DIR)/lib1.o
LIB_COMMON := $(OUT_DIR)/libcommon.a
LIB_MEMORY := $(OUT_DIR)/libmemory.a
LIB_GRAPH_EXECUTOR := $(OUT_DIR)/libgraph_executor.a

.phony: all clean

all: $(OUT_DIR) $(MODEL_ENTRY)

$(OUT_DIR):
	@mkdir -p $@

$(PYTHON_MODEL): build_model.py
	@printf "$(MAGENTA)+ Building ML Model with TVM$(NC)\n"
	@python3 ./build_model.py -o $(OUT_DIR) 1> /dev/null
	@tar -xvf $(OUT_DIR)/model.tar -C $(OUT_DIR) 
	@rm -rf $(OUT_DIR)/model.tar
	@printf "$(MAGENTA)+ Finished! \n"

$(LIB_MEMORY): $(CRT_SRCS)
	@printf "$(MAGENTA)+ Building TVM CRT static library libmemory.a:$(NC)\n"
	@cd $(CRT_ROOT) && make BUILD_DIR=$(abspath $(OUT_DIR))/crt CRT_CONFIG=$(abspath ./crt_config.h) "EXTRA_CFLAGS=$(PKG_COMPILE_OPTS)" memory
	@cp $(OUT_DIR)/crt/libmemory.a $(OUT_DIR)

$(LIB_GRAPH_EXECUTOR): $(CRT_SRCS)
	@printf "$(MAGENTA)+ Building TVM CRT static library libgraph_executor.a:$(NC)\n"
	@cd $(CRT_ROOT) && make BUILD_DIR=$(abspath $(OUT_DIR))/crt CRT_CONFIG=$(abspath ./crt_config.h) "EXTRA_CFLAGS=$(PKG_COMPILE_OPTS)" graph_executor
	@cp $(OUT_DIR)/crt/libgraph_executor.a $(OUT_DIR)
	@printf "$(MAGENTA)+ Finished! \n"

$(LIB_COMMON): $(CRT_SRCS)
	@printf "$(MAGENTA)+ Building TVM CRT static library libcommon.a:$(NC)\n"
	@cd $(CRT_ROOT) && make BUILD_DIR=$(abspath $(OUT_DIR))/crt CRT_CONFIG=$(abspath ./crt_config.h) "EXTRA_CFLAGS=$(PKG_COMPILE_OPTS)" common
	@cp $(OUT_DIR)/crt/libcommon.a $(OUT_DIR)
	@printf "$(MAGENTA)+ Finished! \n"

$(BUNDLE): bundle.c
	@gcc -c -o $(OUT_DIR)/bundle.o $^ $(PKG_CFLAGS) $(PKG_LDFLAGS)
	@ar rcs $@ $(OUT_DIR)/bundle.o
	@rm -f $(OUT_DIR)/bundle.o

# Extract all the object files and pack them into a single library.
# This is a must. We have to make the whole bundle standalone.
$(MODEL_ENTRY): $(MODEL_ENTRY_SRC) $(BUNDLE) $(PYTHON_MODEL) $(LIB_COMMON) $(LIB_GRAPH_EXECUTOR) $(LIB_MEMORY)
	@printf "$(MAGENTA)+ Packing the runtime into single static library:$(NC)\n"
	@mkdir -p $(OUT_DIR)/../tmp
	@gcc -c $(MODEL_ENTRY_SRC) -o $(OUT_DIR)/../tmp/model_entry.o $(PKG_CFLAGS)
	@cd $(OUT_DIR)/../tmp && ar -x $(BUNDLE) && ar -x $(LIB_COMMON) && ar -x $(LIB_GRAPH_EXECUTOR) && ar -x $(LIB_MEMORY) && ar -x $(SGX_SDK)/lib64/libsgx_tstdc.a
	@cd $(OUT_DIR)/../tmp && ar -crs $(MODEL_ENTRY) *.o $(PYTHON_MODEL)
	@rm -rf $(OUT_DIR)/../tmp
	@rm -rf $(OUT_DIR)/crt
	@cp $@ ../../../platform_sgx/lib
	@printf "$(MAGENTA)+ Finished! \n"

clean:
	@rm -rf $(OUT_DIR)