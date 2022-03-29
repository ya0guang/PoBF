#ifndef ENCLAVE_T_H__
#define ENCLAVE_T_H__

#include <stdint.h>
#include <wchar.h>
#include <stddef.h>
#include "sgx_edger8r.h" /* for sgx_ocall etc. */

#include "time.h"
#include "time.h"
#include "inc/stat.h"

#include <stdlib.h> /* for size_t */

#define SGX_CAST(type, item) ((type)(item))

#ifdef __cplusplus
extern "C" {
#endif

sgx_status_t generate_sealed_key(uint8_t* sealed_key_ptr, uint32_t sealed_key_buffer_size, uint32_t* sealed_key_size);
sgx_status_t private_computing_entry(uint8_t* sealed_key_ptr, uint32_t sealed_key_size, uint8_t* encrypted_input_ptr, uint32_t encrypted_input_size, uint8_t* encrypted_output_buffer_ptr, uint32_t encrypted_output_buffer_size, uint32_t* encrypted_output_size);

sgx_status_t SGX_CDECL u_env_ocall(size_t* retval, int* error, uint8_t* buf, size_t bufsz);
sgx_status_t SGX_CDECL u_args_ocall(size_t* retval, int* error, uint8_t* buf, size_t bufsz);
sgx_status_t SGX_CDECL u_chdir_ocall(int* retval, int* error, const char* dir);
sgx_status_t SGX_CDECL u_getcwd_ocall(int* retval, int* error, char* buf, size_t bufsz);
sgx_status_t SGX_CDECL u_getuid_ocall(unsigned int* retval);
sgx_status_t SGX_CDECL u_getgid_ocall(unsigned int* retval);
sgx_status_t SGX_CDECL u_thread_set_event_ocall(int* retval, int* error, size_t tcs);
sgx_status_t SGX_CDECL u_thread_wait_event_ocall(int* retval, int* error, size_t tcs, const struct timespec* timeout);
sgx_status_t SGX_CDECL u_thread_set_multiple_events_ocall(int* retval, int* error, size_t* tcss, size_t total);
sgx_status_t SGX_CDECL u_thread_setwait_events_ocall(int* retval, int* error, size_t waiter_tcs, size_t self_tcs, const struct timespec* timeout);
sgx_status_t SGX_CDECL u_clock_gettime_ocall(int* retval, int* error, int clk_id, struct timespec* tp);
sgx_status_t SGX_CDECL u_getpid_ocall(int* retval);
sgx_status_t SGX_CDECL u_read_ocall(size_t* retval, int* error, int fd, void* buf, size_t count);
sgx_status_t SGX_CDECL u_pread64_ocall(size_t* retval, int* error, int fd, void* buf, size_t count, int64_t offset);
sgx_status_t SGX_CDECL u_write_ocall(size_t* retval, int* error, int fd, const void* buf, size_t count);
sgx_status_t SGX_CDECL u_pwrite64_ocall(size_t* retval, int* error, int fd, const void* buf, size_t count, int64_t offset);
sgx_status_t SGX_CDECL u_sendfile_ocall(size_t* retval, int* error, int out_fd, int in_fd, int64_t* offset, size_t count);
sgx_status_t SGX_CDECL u_copy_file_range_ocall(size_t* retval, int* error, int fd_in, int64_t* off_in, int fd_out, int64_t* off_out, size_t len, unsigned int flags);
sgx_status_t SGX_CDECL u_splice_ocall(size_t* retval, int* error, int fd_in, int64_t* off_in, int fd_out, int64_t* off_out, size_t len, unsigned int flags);
sgx_status_t SGX_CDECL u_fcntl_arg0_ocall(int* retval, int* error, int fd, int cmd);
sgx_status_t SGX_CDECL u_fcntl_arg1_ocall(int* retval, int* error, int fd, int cmd, int arg);
sgx_status_t SGX_CDECL u_ioctl_arg0_ocall(int* retval, int* error, int fd, unsigned long int request);
sgx_status_t SGX_CDECL u_ioctl_arg1_ocall(int* retval, int* error, int fd, unsigned long int request, int* arg);
sgx_status_t SGX_CDECL u_close_ocall(int* retval, int* error, int fd);
sgx_status_t SGX_CDECL u_isatty_ocall(int* retval, int* error, int fd);
sgx_status_t SGX_CDECL u_dup_ocall(int* retval, int* error, int oldfd);
sgx_status_t SGX_CDECL u_eventfd_ocall(int* retval, int* error, unsigned int initval, int flags);
sgx_status_t SGX_CDECL u_malloc_ocall(void** retval, int* error, size_t size, size_t align, int zeroed);
sgx_status_t SGX_CDECL u_free_ocall(void* p);
sgx_status_t SGX_CDECL u_mmap_ocall(void** retval, int* error, void* start, size_t length, int prot, int flags, int fd, int64_t offset);
sgx_status_t SGX_CDECL u_munmap_ocall(int* retval, int* error, void* start, size_t length);
sgx_status_t SGX_CDECL u_msync_ocall(int* retval, int* error, void* addr, size_t length, int flags);
sgx_status_t SGX_CDECL u_mprotect_ocall(int* retval, int* error, void* addr, size_t length, int prot);
sgx_status_t SGX_CDECL u_read_hostbuf_ocall(size_t* retval, int* error, const void* host_buf, void* encl_buf, size_t count);
sgx_status_t SGX_CDECL u_write_hostbuf_ocall(size_t* retval, int* error, void* host_buf, const void* encl_buf, size_t count);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif
