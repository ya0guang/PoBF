/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#include <stdarg.h>
#include <stdlib.h>
#include <tvm/runtime/crt/crt.h>
#include <tvm/runtime/crt/graph_executor.h>
#include <tvm/runtime/crt/packed_func.h>
#include <tvm/runtime/crt/page_allocator.h>

#include "bundle.h"

// We create an arena sized 4 GiB.
#define CRT_MEMORY_NUM_PAGES 1048576
#define CRT_MEMORY_PAGE_SIZE_LOG2 10

// Serves as an arena for memory allocation.
static uint8_t* g_crt_memory;
static MemoryManagerInterface* g_memory_manager;

/*! \brief macro to do C API call */
#define TVM_CCALL(func)            \
  do {                             \
    tvm_crt_error_t ret = (func);  \
    if (ret != kTvmErrorNoError) { \
      abort();                     \
    }                              \
  } while (0)

TVM_DLL void* tvm_runtime_create(const char* json_data, const char* params_data,
                                 const uint64_t params_size) {
  int64_t device_type = kDLCPU;
  int64_t device_id = 0;

  TVMByteArray params;
  params.data = params_data;
  params.size = params_size;

  DLDevice dev;
  dev.device_type = (DLDeviceType)device_type;
  dev.device_id = device_id;

  // get pointers
  const size_t crt_memory_size =
      CRT_MEMORY_NUM_PAGES * (1 << CRT_MEMORY_PAGE_SIZE_LOG2);
  g_crt_memory = (uint8_t*)(malloc(crt_memory_size));

  TVM_CCALL(PageMemoryManagerCreate(&g_memory_manager, g_crt_memory,
                                    crt_memory_size,
                                    CRT_MEMORY_PAGE_SIZE_LOG2));
  TVM_CCALL(TVMInitializeRuntime());
  TVMPackedFunc pf;
  TVMArgs args = TVMArgs_Create(NULL, NULL, 0);
  TVM_CCALL(TVMPackedFunc_InitGlobalFunc(&pf, "runtime.SystemLib", &args));
  TVM_CCALL(TVMPackedFunc_Call(&pf));

  TVMModuleHandle mod_syslib = TVMArgs_AsModuleHandle(&pf.ret_value, 0);

  // run modules
  TVMGraphExecutor* graph_executor = NULL;
  TVM_CCALL(
      TVMGraphExecutor_Create(json_data, mod_syslib, &dev, &graph_executor));
  TVM_CCALL(
      TVMGraphExecutor_LoadParams(graph_executor, params.data, params.size));

  return graph_executor;
}

TVM_DLL void tvm_runtime_destroy(void* executor) {
  TVMGraphExecutor* graph_executor = (TVMGraphExecutor*)executor;
  TVMGraphExecutor_Release(&graph_executor);

  free(g_crt_memory);
}

TVM_DLL void tvm_runtime_set_input(void* executor, const char* name,
                                   DLTensor* tensor) {
  TVMGraphExecutor* graph_executor = (TVMGraphExecutor*)executor;
  TVMGraphExecutor_SetInput(graph_executor, name, tensor);
}

TVM_DLL void tvm_runtime_run(void* executor) {
  TVMGraphExecutor* graph_executor = (TVMGraphExecutor*)executor;
  TVMGraphExecutor_Run(graph_executor);
}

TVM_DLL void tvm_runtime_get_output(void* executor, int32_t index,
                                    DLTensor* tensor) {
  TVMGraphExecutor* graph_executor = (TVMGraphExecutor*)executor;
  TVMGraphExecutor_GetOutput(graph_executor, index, tensor);
}

void TVMLogf(const char* msg, ...) {
  // Does nothing
}

void __attribute__((noreturn)) TVMPlatformAbort(tvm_crt_error_t error_code) {
  abort();
}

tvm_crt_error_t TVMPlatformMemoryAllocate(size_t num_bytes, DLDevice dev,
                                          void** out_ptr) {
  return g_memory_manager->Allocate(g_memory_manager, num_bytes, dev, out_ptr);
}

tvm_crt_error_t TVMPlatformMemoryFree(void* ptr, DLDevice dev) {
  return g_memory_manager->Free(g_memory_manager, ptr, dev);
}

tvm_crt_error_t TVMPlatformTimerStart() {
  return kTvmErrorFunctionCallNotImplemented;
}

tvm_crt_error_t TVMPlatformTimerStop(double* elapsed_time_seconds) {
  return kTvmErrorFunctionCallNotImplemented;
}