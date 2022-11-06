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

#include <tvm/runtime/c_runtime_api.h>

#include "bundle.h"

#define OUTPUT_LEN 1000

// Main entry
int32_t tvm_mxnet_run(const uint8_t* json, size_t json_size,
                      const uint8_t* param, size_t param_size,
                      const uint8_t* input_buf, size_t input_size,
                      uint8_t* output_buf, size_t output_buf_size,
                      size_t* output_size) {
  char* json_data = (char*)(json);
  char* params_data = (char*)(param);

  return 0;
}
