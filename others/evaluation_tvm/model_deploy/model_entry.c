/*
 Copyright (c) 2022 Haobin Chen and Hongbo Chen

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#include <tvm/runtime/c_runtime_api.h>

#include "bundle.h"

#define OUTPUT_LEN 1000
#define INPUT_LEN 1 * 3 * 224 * 224

/* Fix musl. */
int __fprintf_chk(void* stream, int flag, const char* format, ...) { return 0; }

/* Fix musl. */
int __vsnprintf_chk(char* s, size_t maxlen, int flag, size_t slen,
                    const char* format, va_list args) {
  return 0;
}
// Main entry for the Rust enclave to invoke the model.
// The model is statically linked by the enclave, so everything is secret.
int32_t tvm_resnet152_run(const uint8_t* json, size_t json_size,
                          const uint8_t* param, size_t param_size,
                          const uint8_t* input_buf, size_t input_size,
                          uint8_t* output_buf, size_t output_buf_size) {
  char* json_data = (char*)(json);
  char* params_data = (char*)(param);

  // Create a handle to TVM runtime modules including the
  // tvm::runtime::GraphExecutor.
  void* handle = tvm_runtime_create(json_data, params_data, param_size);

  // Check input length.
  if (input_size < INPUT_LEN * sizeof(float)) {
    return 1;
  }

  // Convert to the input tensor for storing the image.
  DLTensor input;
  input.data = (float*)(input_buf);
  DLDevice dev = {kDLCPU, 0};
  input.device = dev;
  input.ndim = 4;
  DLDataType dtype = {kDLFloat, 32, 1};
  input.dtype = dtype;
  int64_t shape[4] = {1, 3, 224, 224};
  input.shape = shape;
  input.strides = NULL;
  input.byte_offset = 0;

  // Prepare the output tensor.
  float output_storage[OUTPUT_LEN];
  DLTensor output;
  output.data = output_storage;
  DLDevice out_dev = {kDLCPU, 0};
  output.device = out_dev;
  output.ndim = 2;
  DLDataType out_dtype = {kDLFloat, 32, 1};
  output.dtype = out_dtype;
  int64_t out_shape[2] = {1, OUTPUT_LEN};
  output.shape = out_shape;
  output.strides = NULL;
  output.byte_offset = 0;

  // Set the input.
  tvm_runtime_set_input(handle, "data", &input);
  // Run the model and get the result.
  tvm_runtime_run(handle);
  // Get the output. The result is a 1001-element vector of logits, rating the
  // probability of each class for the image. You need to check ImageNet for
  // more details.
  tvm_runtime_get_output(handle, 0, &output);
  // Dectroy the handle.
  tvm_runtime_destroy(handle);
  // Copy back.
  memcpy(output_buf, output.data, output_buf_size);

  return 0;
}
