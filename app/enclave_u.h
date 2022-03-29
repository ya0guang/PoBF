#ifndef ENCLAVE_U_H__
#define ENCLAVE_U_H__

#include <stdint.h>
#include <wchar.h>
#include <stddef.h>
#include <string.h>
#include "sgx_edger8r.h" /* for sgx_status_t etc. */

#include "time.h"
#include "time.h"
#include "inc/stat.h"

#include <stdlib.h> /* for size_t */

#define SGX_CAST(type, item) ((type)(item))

#ifdef __cplusplus
extern "C" {
#endif

#ifndef U_ENV_OCALL_DEFINED__
#define U_ENV_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_env_ocall, (int* error, uint8_t* buf, size_t bufsz));
#endif
#ifndef U_ARGS_OCALL_DEFINED__
#define U_ARGS_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_args_ocall, (int* error, uint8_t* buf, size_t bufsz));
#endif
#ifndef U_CHDIR_OCALL_DEFINED__
#define U_CHDIR_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_chdir_ocall, (int* error, const char* dir));
#endif
#ifndef U_GETCWD_OCALL_DEFINED__
#define U_GETCWD_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_getcwd_ocall, (int* error, char* buf, size_t bufsz));
#endif
#ifndef U_GETUID_OCALL_DEFINED__
#define U_GETUID_OCALL_DEFINED__
unsigned int SGX_UBRIDGE(SGX_NOCONVENTION, u_getuid_ocall, (void));
#endif
#ifndef U_GETGID_OCALL_DEFINED__
#define U_GETGID_OCALL_DEFINED__
unsigned int SGX_UBRIDGE(SGX_NOCONVENTION, u_getgid_ocall, (void));
#endif
#ifndef U_THREAD_SET_EVENT_OCALL_DEFINED__
#define U_THREAD_SET_EVENT_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_thread_set_event_ocall, (int* error, size_t tcs));
#endif
#ifndef U_THREAD_WAIT_EVENT_OCALL_DEFINED__
#define U_THREAD_WAIT_EVENT_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_thread_wait_event_ocall, (int* error, size_t tcs, const struct timespec* timeout));
#endif
#ifndef U_THREAD_SET_MULTIPLE_EVENTS_OCALL_DEFINED__
#define U_THREAD_SET_MULTIPLE_EVENTS_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_thread_set_multiple_events_ocall, (int* error, size_t* tcss, size_t total));
#endif
#ifndef U_THREAD_SETWAIT_EVENTS_OCALL_DEFINED__
#define U_THREAD_SETWAIT_EVENTS_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_thread_setwait_events_ocall, (int* error, size_t waiter_tcs, size_t self_tcs, const struct timespec* timeout));
#endif
#ifndef U_CLOCK_GETTIME_OCALL_DEFINED__
#define U_CLOCK_GETTIME_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_clock_gettime_ocall, (int* error, int clk_id, struct timespec* tp));
#endif
#ifndef U_GETPID_OCALL_DEFINED__
#define U_GETPID_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_getpid_ocall, (void));
#endif
#ifndef U_READ_OCALL_DEFINED__
#define U_READ_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_read_ocall, (int* error, int fd, void* buf, size_t count));
#endif
#ifndef U_PREAD64_OCALL_DEFINED__
#define U_PREAD64_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_pread64_ocall, (int* error, int fd, void* buf, size_t count, int64_t offset));
#endif
#ifndef U_WRITE_OCALL_DEFINED__
#define U_WRITE_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_write_ocall, (int* error, int fd, const void* buf, size_t count));
#endif
#ifndef U_PWRITE64_OCALL_DEFINED__
#define U_PWRITE64_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_pwrite64_ocall, (int* error, int fd, const void* buf, size_t count, int64_t offset));
#endif
#ifndef U_SENDFILE_OCALL_DEFINED__
#define U_SENDFILE_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_sendfile_ocall, (int* error, int out_fd, int in_fd, int64_t* offset, size_t count));
#endif
#ifndef U_COPY_FILE_RANGE_OCALL_DEFINED__
#define U_COPY_FILE_RANGE_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_copy_file_range_ocall, (int* error, int fd_in, int64_t* off_in, int fd_out, int64_t* off_out, size_t len, unsigned int flags));
#endif
#ifndef U_SPLICE_OCALL_DEFINED__
#define U_SPLICE_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_splice_ocall, (int* error, int fd_in, int64_t* off_in, int fd_out, int64_t* off_out, size_t len, unsigned int flags));
#endif
#ifndef U_FCNTL_ARG0_OCALL_DEFINED__
#define U_FCNTL_ARG0_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_fcntl_arg0_ocall, (int* error, int fd, int cmd));
#endif
#ifndef U_FCNTL_ARG1_OCALL_DEFINED__
#define U_FCNTL_ARG1_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_fcntl_arg1_ocall, (int* error, int fd, int cmd, int arg));
#endif
#ifndef U_IOCTL_ARG0_OCALL_DEFINED__
#define U_IOCTL_ARG0_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_ioctl_arg0_ocall, (int* error, int fd, unsigned long int request));
#endif
#ifndef U_IOCTL_ARG1_OCALL_DEFINED__
#define U_IOCTL_ARG1_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_ioctl_arg1_ocall, (int* error, int fd, unsigned long int request, int* arg));
#endif
#ifndef U_CLOSE_OCALL_DEFINED__
#define U_CLOSE_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_close_ocall, (int* error, int fd));
#endif
#ifndef U_ISATTY_OCALL_DEFINED__
#define U_ISATTY_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_isatty_ocall, (int* error, int fd));
#endif
#ifndef U_DUP_OCALL_DEFINED__
#define U_DUP_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_dup_ocall, (int* error, int oldfd));
#endif
#ifndef U_EVENTFD_OCALL_DEFINED__
#define U_EVENTFD_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_eventfd_ocall, (int* error, unsigned int initval, int flags));
#endif
#ifndef U_MALLOC_OCALL_DEFINED__
#define U_MALLOC_OCALL_DEFINED__
void* SGX_UBRIDGE(SGX_NOCONVENTION, u_malloc_ocall, (int* error, size_t size, size_t align, int zeroed));
#endif
#ifndef U_FREE_OCALL_DEFINED__
#define U_FREE_OCALL_DEFINED__
void SGX_UBRIDGE(SGX_NOCONVENTION, u_free_ocall, (void* p));
#endif
#ifndef U_MMAP_OCALL_DEFINED__
#define U_MMAP_OCALL_DEFINED__
void* SGX_UBRIDGE(SGX_NOCONVENTION, u_mmap_ocall, (int* error, void* start, size_t length, int prot, int flags, int fd, int64_t offset));
#endif
#ifndef U_MUNMAP_OCALL_DEFINED__
#define U_MUNMAP_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_munmap_ocall, (int* error, void* start, size_t length));
#endif
#ifndef U_MSYNC_OCALL_DEFINED__
#define U_MSYNC_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_msync_ocall, (int* error, void* addr, size_t length, int flags));
#endif
#ifndef U_MPROTECT_OCALL_DEFINED__
#define U_MPROTECT_OCALL_DEFINED__
int SGX_UBRIDGE(SGX_NOCONVENTION, u_mprotect_ocall, (int* error, void* addr, size_t length, int prot));
#endif
#ifndef U_READ_HOSTBUF_OCALL_DEFINED__
#define U_READ_HOSTBUF_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_read_hostbuf_ocall, (int* error, const void* host_buf, void* encl_buf, size_t count));
#endif
#ifndef U_WRITE_HOSTBUF_OCALL_DEFINED__
#define U_WRITE_HOSTBUF_OCALL_DEFINED__
size_t SGX_UBRIDGE(SGX_NOCONVENTION, u_write_hostbuf_ocall, (int* error, void* host_buf, const void* encl_buf, size_t count));
#endif

sgx_status_t generate_sealed_key(sgx_enclave_id_t eid, sgx_status_t* retval, uint8_t* sealed_key_ptr, uint32_t sealed_key_buffer_size, uint32_t* sealed_key_size);
sgx_status_t private_computing_entry(sgx_enclave_id_t eid, sgx_status_t* retval, uint8_t* sealed_key_ptr, uint32_t sealed_key_size, uint8_t* encrypted_input_ptr, uint32_t encrypted_input_size, uint8_t* encrypted_output_buffer_ptr, uint32_t encrypted_output_buffer_size, uint32_t* encrypted_output_size);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif
