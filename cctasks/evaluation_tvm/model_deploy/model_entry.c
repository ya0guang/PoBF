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

#include <tvm/runtime/c_runtime_api.h>

#include "bundle.h"

#define OUTPUT_LEN 1000
#define INPUT_LEN 1 * 3 * 224 * 224

// Force override I/O.
int stderr = -1;
int stdout = -1;
int stdin = -1;

size_t fwrite(ptr, size, nmemb, stream) const void* ptr;
size_t size;
size_t nmemb;
register void* stream;
{ return size; }

int puts(const char* s) { return 0; }

#if __BYTE_ORDER == __BIG_ENDIAN
#define X(x) x
#else
#define X(x) (((x) / 256 | (x)*256) % 65536)
#endif

static const unsigned short table[] = {
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        X(0x200), X(0x200), X(0x200), X(0x200), X(0x200),
    X(0x200), X(0x200), X(0x200), X(0x200), X(0x320), X(0x220), X(0x220),
    X(0x220), X(0x220), X(0x200), X(0x200), X(0x200), X(0x200), X(0x200),
    X(0x200), X(0x200), X(0x200), X(0x200), X(0x200), X(0x200), X(0x200),
    X(0x200), X(0x200), X(0x200), X(0x200), X(0x200), X(0x200), X(0x160),
    X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0),
    X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0),
    X(0x4c0), X(0x8d8), X(0x8d8), X(0x8d8), X(0x8d8), X(0x8d8), X(0x8d8),
    X(0x8d8), X(0x8d8), X(0x8d8), X(0x8d8), X(0x4c0), X(0x4c0), X(0x4c0),
    X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x8d5), X(0x8d5), X(0x8d5),
    X(0x8d5), X(0x8d5), X(0x8d5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5),
    X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5),
    X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5), X(0x8c5),
    X(0x8c5), X(0x8c5), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0), X(0x4c0),
    X(0x4c0), X(0x8d6), X(0x8d6), X(0x8d6), X(0x8d6), X(0x8d6), X(0x8d6),
    X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6),
    X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6),
    X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x8c6), X(0x4c0),
    X(0x4c0), X(0x4c0), X(0x4c0), X(0x200), 0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,
};

static const unsigned short* const ptable = table + 128;
/* Compare S1 and S2, returning less than, equal to or
   greater than zero if S1 is lexicographically less than,
   equal to or greater than S2.  */
int _strcmp(const char* p1, const char* p2) {
  const unsigned char* s1 = (const unsigned char*)p1;
  const unsigned char* s2 = (const unsigned char*)p2;
  unsigned char c1, c2;
  do {
    c1 = (unsigned char)*s1++;
    c2 = (unsigned char)*s2++;
    if (c1 == '\0') return c1 - c2;
  } while (c1 == c2);
  return c1 - c2;
}

void* _memchr(void const* s, int c_in, size_t n) {
  /* On 32-bit hardware, choosing longword to be a 32-bit unsigned
     long instead of a 64-bit uintmax_t tends to give better
     performance.  On 64-bit hardware, unsigned long is generally 64
     bits already.  Change this typedef to experiment with
     performance.  */
  typedef unsigned long int longword;
  const unsigned char* char_ptr;
  const longword* longword_ptr;
  longword repeated_one;
  longword repeated_c;
  unsigned char c;
  c = (unsigned char)c_in;
  /* Handle the first few bytes by reading one byte at a time.
     Do this until CHAR_PTR is aligned on a longword boundary.  */
  for (char_ptr = (const unsigned char*)s;
       n > 0 && (size_t)char_ptr % sizeof(longword) != 0; --n, ++char_ptr)
    if (*char_ptr == c) return (void*)char_ptr;
  longword_ptr = (const longword*)char_ptr;
  /* All these elucidatory comments refer to 4-byte longwords,
     but the theory applies equally well to any size longwords.  */
  /* Compute auxiliary longword values:
     repeated_one is a value which has a 1 in every byte.
     repeated_c has c in every byte.  */
  repeated_one = 0x01010101;
  repeated_c = c | (c << 8);
  repeated_c |= repeated_c << 16;
  if (0xffffffffU < (longword)-1) {
    repeated_one |= repeated_one << 31 << 1;
    repeated_c |= repeated_c << 31 << 1;
    if (8 < sizeof(longword)) {
      size_t i;
      for (i = 64; i < sizeof(longword) * 8; i *= 2) {
        repeated_one |= repeated_one << i;
        repeated_c |= repeated_c << i;
      }
    }
  }
  /* Instead of the traditional loop which tests each byte, we will test a
     longword at a time.  The tricky part is testing if *any of the four*
     bytes in the longword in question are equal to c.  We first use an xor
     with repeated_c.  This reduces the task to testing whether *any of the
     four* bytes in longword1 is zero.
     We compute tmp =
       ((longword1 - repeated_one) & ~longword1) & (repeated_one << 7).
     That is, we perform the following operations:
       1. Subtract repeated_one.
       2. & ~longword1.
       3. & a mask consisting of 0x80 in every byte.
     Consider what happens in each byte:
       - If a byte of longword1 is zero, step 1 and 2 transform it into 0xff,
         and step 3 transforms it into 0x80.  A carry can also be propagated
         to more significant bytes.
       - If a byte of longword1 is nonzero, let its lowest 1 bit be at
         position k (0 <= k <= 7); so the lowest k bits are 0.  After step 1,
         the byte ends in a single bit of value 0 and k bits of value 1.
         After step 2, the result is just k bits of value 1: 2^k - 1.  After
         step 3, the result is 0.  And no carry is produced.
     So, if longword1 has only non-zero bytes, tmp is zero.
     Whereas if longword1 has a zero byte, call j the position of the least
     significant zero byte.  Then the result has a zero at positions 0, ...,
     j-1 and a 0x80 at position j.  We cannot predict the result at the more
     significant bytes (positions j+1..3), but it does not matter since we
     already have a non-zero bit at position 8*j+7.
     So, the test whether any byte in longword1 is zero is equivalent to
     testing whether tmp is nonzero.  */
  while (n >= sizeof(longword)) {
    longword longword1 = *longword_ptr ^ repeated_c;
    if ((((longword1 - repeated_one) & ~longword1) & (repeated_one << 7)) != 0)
      break;
    longword_ptr++;
    n -= sizeof(longword);
  }
  char_ptr = (const unsigned char*)longword_ptr;
  /* At this point, we know that either n < sizeof (longword), or one of the
     sizeof (longword) bytes starting at char_ptr is == c.  On little-endian
     machines, we could determine the first such byte without any further
     memory accesses, just by looking at the tmp result from the last loop
     iteration.  But this does not work on big-endian machines.  Choose code
     that works in both cases.  */
  for (; n > 0; --n, ++char_ptr) {
    if (*char_ptr == c) return (void*)char_ptr;
  }
  return NULL;
}

const unsigned short** __ctype_b_loc(void) { return (void*)&ptable; }

int __fprintf_chk(void* stream, int flag, const char* format, ...) { return 0; }
int usleep(int64_t useconds) { return 0; }
void __assert_fail(const char* assertion, const char* file, unsigned int line,
                   const char* function) {
  abort();
}

// Main entry for the Rust enclave to invoke the model.
// The model is statically linked by the enclave, so everything is secret.
int32_t tvm_mxnet_run(const uint8_t* json, size_t json_size,
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
  // Get the output. The result is a 1001-element vector of logits, rating the probability of 
  // each class for the image. You need to check ImageNet for more details.
  tvm_runtime_get_output(handle, 0, &output);
  // Dectroy the handle.
  tvm_runtime_destroy(handle);
  // Copy back.
  memcpy(output_buf, output.data, output_buf_size);

  return 0;
}
