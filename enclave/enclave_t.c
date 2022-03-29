#include "enclave_t.h"

#include "sgx_trts.h" /* for sgx_ocalloc, sgx_is_outside_enclave */
#include "sgx_lfence.h" /* for sgx_lfence */

#include <errno.h>
#include <mbusafecrt.h> /* for memcpy_s etc */
#include <stdlib.h> /* for malloc/free etc */

#define CHECK_REF_POINTER(ptr, siz) do {	\
	if (!(ptr) || ! sgx_is_outside_enclave((ptr), (siz)))	\
		return SGX_ERROR_INVALID_PARAMETER;\
} while (0)

#define CHECK_UNIQUE_POINTER(ptr, siz) do {	\
	if ((ptr) && ! sgx_is_outside_enclave((ptr), (siz)))	\
		return SGX_ERROR_INVALID_PARAMETER;\
} while (0)

#define CHECK_ENCLAVE_POINTER(ptr, siz) do {	\
	if ((ptr) && ! sgx_is_within_enclave((ptr), (siz)))	\
		return SGX_ERROR_INVALID_PARAMETER;\
} while (0)

#define ADD_ASSIGN_OVERFLOW(a, b) (	\
	((a) += (b)) < (b)	\
)


typedef struct ms_generate_sealed_key_t {
	sgx_status_t ms_retval;
	uint8_t* ms_sealed_key_ptr;
	uint32_t ms_sealed_key_buffer_size;
	uint32_t* ms_sealed_key_size;
} ms_generate_sealed_key_t;

typedef struct ms_private_computing_entry_t {
	sgx_status_t ms_retval;
	uint8_t* ms_sealed_key_ptr;
	uint32_t ms_sealed_key_size;
	uint8_t* ms_encrypted_input_ptr;
	uint32_t ms_encrypted_input_size;
	uint8_t* ms_encrypted_output_buffer_ptr;
	uint32_t ms_encrypted_output_buffer_size;
	uint32_t* ms_encrypted_output_size;
} ms_private_computing_entry_t;

typedef struct ms_u_env_ocall_t {
	size_t ms_retval;
	int* ms_error;
	uint8_t* ms_buf;
	size_t ms_bufsz;
} ms_u_env_ocall_t;

typedef struct ms_u_args_ocall_t {
	size_t ms_retval;
	int* ms_error;
	uint8_t* ms_buf;
	size_t ms_bufsz;
} ms_u_args_ocall_t;

typedef struct ms_u_chdir_ocall_t {
	int ms_retval;
	int* ms_error;
	const char* ms_dir;
} ms_u_chdir_ocall_t;

typedef struct ms_u_getcwd_ocall_t {
	int ms_retval;
	int* ms_error;
	char* ms_buf;
	size_t ms_bufsz;
} ms_u_getcwd_ocall_t;

typedef struct ms_u_getuid_ocall_t {
	unsigned int ms_retval;
} ms_u_getuid_ocall_t;

typedef struct ms_u_getgid_ocall_t {
	unsigned int ms_retval;
} ms_u_getgid_ocall_t;

typedef struct ms_u_thread_set_event_ocall_t {
	int ms_retval;
	int* ms_error;
	size_t ms_tcs;
} ms_u_thread_set_event_ocall_t;

typedef struct ms_u_thread_wait_event_ocall_t {
	int ms_retval;
	int* ms_error;
	size_t ms_tcs;
	const struct timespec* ms_timeout;
} ms_u_thread_wait_event_ocall_t;

typedef struct ms_u_thread_set_multiple_events_ocall_t {
	int ms_retval;
	int* ms_error;
	size_t* ms_tcss;
	size_t ms_total;
} ms_u_thread_set_multiple_events_ocall_t;

typedef struct ms_u_thread_setwait_events_ocall_t {
	int ms_retval;
	int* ms_error;
	size_t ms_waiter_tcs;
	size_t ms_self_tcs;
	const struct timespec* ms_timeout;
} ms_u_thread_setwait_events_ocall_t;

typedef struct ms_u_clock_gettime_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_clk_id;
	struct timespec* ms_tp;
} ms_u_clock_gettime_ocall_t;

typedef struct ms_u_getpid_ocall_t {
	int ms_retval;
} ms_u_getpid_ocall_t;

typedef struct ms_u_read_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_fd;
	void* ms_buf;
	size_t ms_count;
} ms_u_read_ocall_t;

typedef struct ms_u_pread64_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_fd;
	void* ms_buf;
	size_t ms_count;
	int64_t ms_offset;
} ms_u_pread64_ocall_t;

typedef struct ms_u_write_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_fd;
	const void* ms_buf;
	size_t ms_count;
} ms_u_write_ocall_t;

typedef struct ms_u_pwrite64_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_fd;
	const void* ms_buf;
	size_t ms_count;
	int64_t ms_offset;
} ms_u_pwrite64_ocall_t;

typedef struct ms_u_sendfile_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_out_fd;
	int ms_in_fd;
	int64_t* ms_offset;
	size_t ms_count;
} ms_u_sendfile_ocall_t;

typedef struct ms_u_copy_file_range_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_fd_in;
	int64_t* ms_off_in;
	int ms_fd_out;
	int64_t* ms_off_out;
	size_t ms_len;
	unsigned int ms_flags;
} ms_u_copy_file_range_ocall_t;

typedef struct ms_u_splice_ocall_t {
	size_t ms_retval;
	int* ms_error;
	int ms_fd_in;
	int64_t* ms_off_in;
	int ms_fd_out;
	int64_t* ms_off_out;
	size_t ms_len;
	unsigned int ms_flags;
} ms_u_splice_ocall_t;

typedef struct ms_u_fcntl_arg0_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_fd;
	int ms_cmd;
} ms_u_fcntl_arg0_ocall_t;

typedef struct ms_u_fcntl_arg1_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_fd;
	int ms_cmd;
	int ms_arg;
} ms_u_fcntl_arg1_ocall_t;

typedef struct ms_u_ioctl_arg0_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_fd;
	unsigned long int ms_request;
} ms_u_ioctl_arg0_ocall_t;

typedef struct ms_u_ioctl_arg1_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_fd;
	unsigned long int ms_request;
	int* ms_arg;
} ms_u_ioctl_arg1_ocall_t;

typedef struct ms_u_close_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_fd;
} ms_u_close_ocall_t;

typedef struct ms_u_isatty_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_fd;
} ms_u_isatty_ocall_t;

typedef struct ms_u_dup_ocall_t {
	int ms_retval;
	int* ms_error;
	int ms_oldfd;
} ms_u_dup_ocall_t;

typedef struct ms_u_eventfd_ocall_t {
	int ms_retval;
	int* ms_error;
	unsigned int ms_initval;
	int ms_flags;
} ms_u_eventfd_ocall_t;

typedef struct ms_u_malloc_ocall_t {
	void* ms_retval;
	int* ms_error;
	size_t ms_size;
	size_t ms_align;
	int ms_zeroed;
} ms_u_malloc_ocall_t;

typedef struct ms_u_free_ocall_t {
	void* ms_p;
} ms_u_free_ocall_t;

typedef struct ms_u_mmap_ocall_t {
	void* ms_retval;
	int* ms_error;
	void* ms_start;
	size_t ms_length;
	int ms_prot;
	int ms_flags;
	int ms_fd;
	int64_t ms_offset;
} ms_u_mmap_ocall_t;

typedef struct ms_u_munmap_ocall_t {
	int ms_retval;
	int* ms_error;
	void* ms_start;
	size_t ms_length;
} ms_u_munmap_ocall_t;

typedef struct ms_u_msync_ocall_t {
	int ms_retval;
	int* ms_error;
	void* ms_addr;
	size_t ms_length;
	int ms_flags;
} ms_u_msync_ocall_t;

typedef struct ms_u_mprotect_ocall_t {
	int ms_retval;
	int* ms_error;
	void* ms_addr;
	size_t ms_length;
	int ms_prot;
} ms_u_mprotect_ocall_t;

typedef struct ms_u_read_hostbuf_ocall_t {
	size_t ms_retval;
	int* ms_error;
	const void* ms_host_buf;
	void* ms_encl_buf;
	size_t ms_count;
} ms_u_read_hostbuf_ocall_t;

typedef struct ms_u_write_hostbuf_ocall_t {
	size_t ms_retval;
	int* ms_error;
	void* ms_host_buf;
	const void* ms_encl_buf;
	size_t ms_count;
} ms_u_write_hostbuf_ocall_t;

static sgx_status_t SGX_CDECL sgx_generate_sealed_key(void* pms)
{
	CHECK_REF_POINTER(pms, sizeof(ms_generate_sealed_key_t));
	//
	// fence after pointer checks
	//
	sgx_lfence();
	ms_generate_sealed_key_t* ms = SGX_CAST(ms_generate_sealed_key_t*, pms);
	sgx_status_t status = SGX_SUCCESS;
	uint8_t* _tmp_sealed_key_ptr = ms->ms_sealed_key_ptr;
	uint32_t _tmp_sealed_key_buffer_size = ms->ms_sealed_key_buffer_size;
	size_t _len_sealed_key_ptr = _tmp_sealed_key_buffer_size;
	uint8_t* _in_sealed_key_ptr = NULL;
	uint32_t* _tmp_sealed_key_size = ms->ms_sealed_key_size;
	size_t _len_sealed_key_size = sizeof(uint32_t);
	uint32_t* _in_sealed_key_size = NULL;

	CHECK_UNIQUE_POINTER(_tmp_sealed_key_ptr, _len_sealed_key_ptr);
	CHECK_UNIQUE_POINTER(_tmp_sealed_key_size, _len_sealed_key_size);

	//
	// fence after pointer checks
	//
	sgx_lfence();

	if (_tmp_sealed_key_ptr != NULL && _len_sealed_key_ptr != 0) {
		if ( _len_sealed_key_ptr % sizeof(*_tmp_sealed_key_ptr) != 0)
		{
			status = SGX_ERROR_INVALID_PARAMETER;
			goto err;
		}
		if ((_in_sealed_key_ptr = (uint8_t*)malloc(_len_sealed_key_ptr)) == NULL) {
			status = SGX_ERROR_OUT_OF_MEMORY;
			goto err;
		}

		memset((void*)_in_sealed_key_ptr, 0, _len_sealed_key_ptr);
	}
	if (_tmp_sealed_key_size != NULL && _len_sealed_key_size != 0) {
		if ( _len_sealed_key_size % sizeof(*_tmp_sealed_key_size) != 0)
		{
			status = SGX_ERROR_INVALID_PARAMETER;
			goto err;
		}
		if ((_in_sealed_key_size = (uint32_t*)malloc(_len_sealed_key_size)) == NULL) {
			status = SGX_ERROR_OUT_OF_MEMORY;
			goto err;
		}

		memset((void*)_in_sealed_key_size, 0, _len_sealed_key_size);
	}

	ms->ms_retval = generate_sealed_key(_in_sealed_key_ptr, _tmp_sealed_key_buffer_size, _in_sealed_key_size);
	if (_in_sealed_key_ptr) {
		if (memcpy_s(_tmp_sealed_key_ptr, _len_sealed_key_ptr, _in_sealed_key_ptr, _len_sealed_key_ptr)) {
			status = SGX_ERROR_UNEXPECTED;
			goto err;
		}
	}
	if (_in_sealed_key_size) {
		if (memcpy_s(_tmp_sealed_key_size, _len_sealed_key_size, _in_sealed_key_size, _len_sealed_key_size)) {
			status = SGX_ERROR_UNEXPECTED;
			goto err;
		}
	}

err:
	if (_in_sealed_key_ptr) free(_in_sealed_key_ptr);
	if (_in_sealed_key_size) free(_in_sealed_key_size);
	return status;
}

static sgx_status_t SGX_CDECL sgx_private_computing_entry(void* pms)
{
	CHECK_REF_POINTER(pms, sizeof(ms_private_computing_entry_t));
	//
	// fence after pointer checks
	//
	sgx_lfence();
	ms_private_computing_entry_t* ms = SGX_CAST(ms_private_computing_entry_t*, pms);
	sgx_status_t status = SGX_SUCCESS;
	uint8_t* _tmp_sealed_key_ptr = ms->ms_sealed_key_ptr;
	uint32_t _tmp_sealed_key_size = ms->ms_sealed_key_size;
	size_t _len_sealed_key_ptr = _tmp_sealed_key_size;
	uint8_t* _in_sealed_key_ptr = NULL;
	uint8_t* _tmp_encrypted_input_ptr = ms->ms_encrypted_input_ptr;
	uint32_t _tmp_encrypted_input_size = ms->ms_encrypted_input_size;
	size_t _len_encrypted_input_ptr = _tmp_encrypted_input_size;
	uint8_t* _in_encrypted_input_ptr = NULL;
	uint8_t* _tmp_encrypted_output_buffer_ptr = ms->ms_encrypted_output_buffer_ptr;
	uint32_t _tmp_encrypted_output_buffer_size = ms->ms_encrypted_output_buffer_size;
	size_t _len_encrypted_output_buffer_ptr = _tmp_encrypted_output_buffer_size;
	uint8_t* _in_encrypted_output_buffer_ptr = NULL;
	uint32_t* _tmp_encrypted_output_size = ms->ms_encrypted_output_size;
	size_t _len_encrypted_output_size = sizeof(uint32_t);
	uint32_t* _in_encrypted_output_size = NULL;

	CHECK_UNIQUE_POINTER(_tmp_sealed_key_ptr, _len_sealed_key_ptr);
	CHECK_UNIQUE_POINTER(_tmp_encrypted_input_ptr, _len_encrypted_input_ptr);
	CHECK_UNIQUE_POINTER(_tmp_encrypted_output_buffer_ptr, _len_encrypted_output_buffer_ptr);
	CHECK_UNIQUE_POINTER(_tmp_encrypted_output_size, _len_encrypted_output_size);

	//
	// fence after pointer checks
	//
	sgx_lfence();

	if (_tmp_sealed_key_ptr != NULL && _len_sealed_key_ptr != 0) {
		if ( _len_sealed_key_ptr % sizeof(*_tmp_sealed_key_ptr) != 0)
		{
			status = SGX_ERROR_INVALID_PARAMETER;
			goto err;
		}
		_in_sealed_key_ptr = (uint8_t*)malloc(_len_sealed_key_ptr);
		if (_in_sealed_key_ptr == NULL) {
			status = SGX_ERROR_OUT_OF_MEMORY;
			goto err;
		}

		if (memcpy_s(_in_sealed_key_ptr, _len_sealed_key_ptr, _tmp_sealed_key_ptr, _len_sealed_key_ptr)) {
			status = SGX_ERROR_UNEXPECTED;
			goto err;
		}

	}
	if (_tmp_encrypted_input_ptr != NULL && _len_encrypted_input_ptr != 0) {
		if ( _len_encrypted_input_ptr % sizeof(*_tmp_encrypted_input_ptr) != 0)
		{
			status = SGX_ERROR_INVALID_PARAMETER;
			goto err;
		}
		_in_encrypted_input_ptr = (uint8_t*)malloc(_len_encrypted_input_ptr);
		if (_in_encrypted_input_ptr == NULL) {
			status = SGX_ERROR_OUT_OF_MEMORY;
			goto err;
		}

		if (memcpy_s(_in_encrypted_input_ptr, _len_encrypted_input_ptr, _tmp_encrypted_input_ptr, _len_encrypted_input_ptr)) {
			status = SGX_ERROR_UNEXPECTED;
			goto err;
		}

	}
	if (_tmp_encrypted_output_buffer_ptr != NULL && _len_encrypted_output_buffer_ptr != 0) {
		if ( _len_encrypted_output_buffer_ptr % sizeof(*_tmp_encrypted_output_buffer_ptr) != 0)
		{
			status = SGX_ERROR_INVALID_PARAMETER;
			goto err;
		}
		if ((_in_encrypted_output_buffer_ptr = (uint8_t*)malloc(_len_encrypted_output_buffer_ptr)) == NULL) {
			status = SGX_ERROR_OUT_OF_MEMORY;
			goto err;
		}

		memset((void*)_in_encrypted_output_buffer_ptr, 0, _len_encrypted_output_buffer_ptr);
	}
	if (_tmp_encrypted_output_size != NULL && _len_encrypted_output_size != 0) {
		if ( _len_encrypted_output_size % sizeof(*_tmp_encrypted_output_size) != 0)
		{
			status = SGX_ERROR_INVALID_PARAMETER;
			goto err;
		}
		if ((_in_encrypted_output_size = (uint32_t*)malloc(_len_encrypted_output_size)) == NULL) {
			status = SGX_ERROR_OUT_OF_MEMORY;
			goto err;
		}

		memset((void*)_in_encrypted_output_size, 0, _len_encrypted_output_size);
	}

	ms->ms_retval = private_computing_entry(_in_sealed_key_ptr, _tmp_sealed_key_size, _in_encrypted_input_ptr, _tmp_encrypted_input_size, _in_encrypted_output_buffer_ptr, _tmp_encrypted_output_buffer_size, _in_encrypted_output_size);
	if (_in_encrypted_output_buffer_ptr) {
		if (memcpy_s(_tmp_encrypted_output_buffer_ptr, _len_encrypted_output_buffer_ptr, _in_encrypted_output_buffer_ptr, _len_encrypted_output_buffer_ptr)) {
			status = SGX_ERROR_UNEXPECTED;
			goto err;
		}
	}
	if (_in_encrypted_output_size) {
		if (memcpy_s(_tmp_encrypted_output_size, _len_encrypted_output_size, _in_encrypted_output_size, _len_encrypted_output_size)) {
			status = SGX_ERROR_UNEXPECTED;
			goto err;
		}
	}

err:
	if (_in_sealed_key_ptr) free(_in_sealed_key_ptr);
	if (_in_encrypted_input_ptr) free(_in_encrypted_input_ptr);
	if (_in_encrypted_output_buffer_ptr) free(_in_encrypted_output_buffer_ptr);
	if (_in_encrypted_output_size) free(_in_encrypted_output_size);
	return status;
}

SGX_EXTERNC const struct {
	size_t nr_ecall;
	struct {void* ecall_addr; uint8_t is_priv; uint8_t is_switchless;} ecall_table[2];
} g_ecall_table = {
	2,
	{
		{(void*)(uintptr_t)sgx_generate_sealed_key, 0, 0},
		{(void*)(uintptr_t)sgx_private_computing_entry, 0, 0},
	}
};

SGX_EXTERNC const struct {
	size_t nr_ocall;
	uint8_t entry_table[35][2];
} g_dyn_entry_table = {
	35,
	{
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
		{0, 0, },
	}
};


sgx_status_t SGX_CDECL u_env_ocall(size_t* retval, int* error, uint8_t* buf, size_t bufsz)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_buf = bufsz;

	ms_u_env_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_env_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_buf = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(buf, _len_buf);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (buf != NULL) ? _len_buf : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_env_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_env_ocall_t));
	ocalloc_size -= sizeof(ms_u_env_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	if (buf != NULL) {
		ms->ms_buf = (uint8_t*)__tmp;
		__tmp_buf = __tmp;
		if (_len_buf % sizeof(*buf) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_buf, 0, _len_buf);
		__tmp = (void *)((size_t)__tmp + _len_buf);
		ocalloc_size -= _len_buf;
	} else {
		ms->ms_buf = NULL;
	}
	
	ms->ms_bufsz = bufsz;
	status = sgx_ocall(0, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (buf) {
			if (memcpy_s((void*)buf, _len_buf, __tmp_buf, _len_buf)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_args_ocall(size_t* retval, int* error, uint8_t* buf, size_t bufsz)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_buf = bufsz;

	ms_u_args_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_args_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_buf = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(buf, _len_buf);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (buf != NULL) ? _len_buf : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_args_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_args_ocall_t));
	ocalloc_size -= sizeof(ms_u_args_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	if (buf != NULL) {
		ms->ms_buf = (uint8_t*)__tmp;
		__tmp_buf = __tmp;
		if (_len_buf % sizeof(*buf) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_buf, 0, _len_buf);
		__tmp = (void *)((size_t)__tmp + _len_buf);
		ocalloc_size -= _len_buf;
	} else {
		ms->ms_buf = NULL;
	}
	
	ms->ms_bufsz = bufsz;
	status = sgx_ocall(1, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (buf) {
			if (memcpy_s((void*)buf, _len_buf, __tmp_buf, _len_buf)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_chdir_ocall(int* retval, int* error, const char* dir)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_dir = dir ? strlen(dir) + 1 : 0;

	ms_u_chdir_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_chdir_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(dir, _len_dir);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (dir != NULL) ? _len_dir : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_chdir_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_chdir_ocall_t));
	ocalloc_size -= sizeof(ms_u_chdir_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	if (dir != NULL) {
		ms->ms_dir = (const char*)__tmp;
		if (_len_dir % sizeof(*dir) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, dir, _len_dir)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_dir);
		ocalloc_size -= _len_dir;
	} else {
		ms->ms_dir = NULL;
	}
	
	status = sgx_ocall(2, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_getcwd_ocall(int* retval, int* error, char* buf, size_t bufsz)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_buf = bufsz;

	ms_u_getcwd_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_getcwd_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_buf = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(buf, _len_buf);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (buf != NULL) ? _len_buf : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_getcwd_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_getcwd_ocall_t));
	ocalloc_size -= sizeof(ms_u_getcwd_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	if (buf != NULL) {
		ms->ms_buf = (char*)__tmp;
		__tmp_buf = __tmp;
		if (_len_buf % sizeof(*buf) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_buf, 0, _len_buf);
		__tmp = (void *)((size_t)__tmp + _len_buf);
		ocalloc_size -= _len_buf;
	} else {
		ms->ms_buf = NULL;
	}
	
	ms->ms_bufsz = bufsz;
	status = sgx_ocall(3, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (buf) {
			if (memcpy_s((void*)buf, _len_buf, __tmp_buf, _len_buf)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_getuid_ocall(unsigned int* retval)
{
	sgx_status_t status = SGX_SUCCESS;

	ms_u_getuid_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_getuid_ocall_t);
	void *__tmp = NULL;


	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_getuid_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_getuid_ocall_t));
	ocalloc_size -= sizeof(ms_u_getuid_ocall_t);

	status = sgx_ocall(4, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_getgid_ocall(unsigned int* retval)
{
	sgx_status_t status = SGX_SUCCESS;

	ms_u_getgid_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_getgid_ocall_t);
	void *__tmp = NULL;


	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_getgid_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_getgid_ocall_t));
	ocalloc_size -= sizeof(ms_u_getgid_ocall_t);

	status = sgx_ocall(5, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_thread_set_event_ocall(int* retval, int* error, size_t tcs)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_thread_set_event_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_thread_set_event_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_thread_set_event_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_thread_set_event_ocall_t));
	ocalloc_size -= sizeof(ms_u_thread_set_event_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_tcs = tcs;
	status = sgx_ocall(6, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_thread_wait_event_ocall(int* retval, int* error, size_t tcs, const struct timespec* timeout)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_timeout = sizeof(struct timespec);

	ms_u_thread_wait_event_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_thread_wait_event_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(timeout, _len_timeout);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (timeout != NULL) ? _len_timeout : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_thread_wait_event_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_thread_wait_event_ocall_t));
	ocalloc_size -= sizeof(ms_u_thread_wait_event_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_tcs = tcs;
	if (timeout != NULL) {
		ms->ms_timeout = (const struct timespec*)__tmp;
		if (memcpy_s(__tmp, ocalloc_size, timeout, _len_timeout)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_timeout);
		ocalloc_size -= _len_timeout;
	} else {
		ms->ms_timeout = NULL;
	}
	
	status = sgx_ocall(7, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_thread_set_multiple_events_ocall(int* retval, int* error, size_t* tcss, size_t total)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_tcss = total * sizeof(size_t);

	ms_u_thread_set_multiple_events_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_thread_set_multiple_events_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(tcss, _len_tcss);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (tcss != NULL) ? _len_tcss : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_thread_set_multiple_events_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_thread_set_multiple_events_ocall_t));
	ocalloc_size -= sizeof(ms_u_thread_set_multiple_events_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	if (tcss != NULL) {
		ms->ms_tcss = (size_t*)__tmp;
		if (_len_tcss % sizeof(*tcss) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, tcss, _len_tcss)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_tcss);
		ocalloc_size -= _len_tcss;
	} else {
		ms->ms_tcss = NULL;
	}
	
	ms->ms_total = total;
	status = sgx_ocall(8, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_thread_setwait_events_ocall(int* retval, int* error, size_t waiter_tcs, size_t self_tcs, const struct timespec* timeout)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_timeout = sizeof(struct timespec);

	ms_u_thread_setwait_events_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_thread_setwait_events_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(timeout, _len_timeout);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (timeout != NULL) ? _len_timeout : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_thread_setwait_events_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_thread_setwait_events_ocall_t));
	ocalloc_size -= sizeof(ms_u_thread_setwait_events_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_waiter_tcs = waiter_tcs;
	ms->ms_self_tcs = self_tcs;
	if (timeout != NULL) {
		ms->ms_timeout = (const struct timespec*)__tmp;
		if (memcpy_s(__tmp, ocalloc_size, timeout, _len_timeout)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_timeout);
		ocalloc_size -= _len_timeout;
	} else {
		ms->ms_timeout = NULL;
	}
	
	status = sgx_ocall(9, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_clock_gettime_ocall(int* retval, int* error, int clk_id, struct timespec* tp)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_tp = sizeof(struct timespec);

	ms_u_clock_gettime_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_clock_gettime_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_tp = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(tp, _len_tp);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (tp != NULL) ? _len_tp : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_clock_gettime_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_clock_gettime_ocall_t));
	ocalloc_size -= sizeof(ms_u_clock_gettime_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_clk_id = clk_id;
	if (tp != NULL) {
		ms->ms_tp = (struct timespec*)__tmp;
		__tmp_tp = __tmp;
		memset(__tmp_tp, 0, _len_tp);
		__tmp = (void *)((size_t)__tmp + _len_tp);
		ocalloc_size -= _len_tp;
	} else {
		ms->ms_tp = NULL;
	}
	
	status = sgx_ocall(10, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (tp) {
			if (memcpy_s((void*)tp, _len_tp, __tmp_tp, _len_tp)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_getpid_ocall(int* retval)
{
	sgx_status_t status = SGX_SUCCESS;

	ms_u_getpid_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_getpid_ocall_t);
	void *__tmp = NULL;


	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_getpid_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_getpid_ocall_t));
	ocalloc_size -= sizeof(ms_u_getpid_ocall_t);

	status = sgx_ocall(11, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_read_ocall(size_t* retval, int* error, int fd, void* buf, size_t count)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_read_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_read_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_read_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_read_ocall_t));
	ocalloc_size -= sizeof(ms_u_read_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_buf = buf;
	ms->ms_count = count;
	status = sgx_ocall(12, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_pread64_ocall(size_t* retval, int* error, int fd, void* buf, size_t count, int64_t offset)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_pread64_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_pread64_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_pread64_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_pread64_ocall_t));
	ocalloc_size -= sizeof(ms_u_pread64_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_buf = buf;
	ms->ms_count = count;
	ms->ms_offset = offset;
	status = sgx_ocall(13, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_write_ocall(size_t* retval, int* error, int fd, const void* buf, size_t count)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_write_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_write_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_write_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_write_ocall_t));
	ocalloc_size -= sizeof(ms_u_write_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_buf = buf;
	ms->ms_count = count;
	status = sgx_ocall(14, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_pwrite64_ocall(size_t* retval, int* error, int fd, const void* buf, size_t count, int64_t offset)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_pwrite64_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_pwrite64_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_pwrite64_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_pwrite64_ocall_t));
	ocalloc_size -= sizeof(ms_u_pwrite64_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_buf = buf;
	ms->ms_count = count;
	ms->ms_offset = offset;
	status = sgx_ocall(15, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_sendfile_ocall(size_t* retval, int* error, int out_fd, int in_fd, int64_t* offset, size_t count)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_offset = sizeof(int64_t);

	ms_u_sendfile_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_sendfile_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_offset = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(offset, _len_offset);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (offset != NULL) ? _len_offset : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_sendfile_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_sendfile_ocall_t));
	ocalloc_size -= sizeof(ms_u_sendfile_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_out_fd = out_fd;
	ms->ms_in_fd = in_fd;
	if (offset != NULL) {
		ms->ms_offset = (int64_t*)__tmp;
		__tmp_offset = __tmp;
		if (_len_offset % sizeof(*offset) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, offset, _len_offset)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_offset);
		ocalloc_size -= _len_offset;
	} else {
		ms->ms_offset = NULL;
	}
	
	ms->ms_count = count;
	status = sgx_ocall(16, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (offset) {
			if (memcpy_s((void*)offset, _len_offset, __tmp_offset, _len_offset)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_copy_file_range_ocall(size_t* retval, int* error, int fd_in, int64_t* off_in, int fd_out, int64_t* off_out, size_t len, unsigned int flags)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_off_in = sizeof(int64_t);
	size_t _len_off_out = sizeof(int64_t);

	ms_u_copy_file_range_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_copy_file_range_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_off_in = NULL;
	void *__tmp_off_out = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(off_in, _len_off_in);
	CHECK_ENCLAVE_POINTER(off_out, _len_off_out);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (off_in != NULL) ? _len_off_in : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (off_out != NULL) ? _len_off_out : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_copy_file_range_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_copy_file_range_ocall_t));
	ocalloc_size -= sizeof(ms_u_copy_file_range_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd_in = fd_in;
	if (off_in != NULL) {
		ms->ms_off_in = (int64_t*)__tmp;
		__tmp_off_in = __tmp;
		if (_len_off_in % sizeof(*off_in) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, off_in, _len_off_in)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_off_in);
		ocalloc_size -= _len_off_in;
	} else {
		ms->ms_off_in = NULL;
	}
	
	ms->ms_fd_out = fd_out;
	if (off_out != NULL) {
		ms->ms_off_out = (int64_t*)__tmp;
		__tmp_off_out = __tmp;
		if (_len_off_out % sizeof(*off_out) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, off_out, _len_off_out)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_off_out);
		ocalloc_size -= _len_off_out;
	} else {
		ms->ms_off_out = NULL;
	}
	
	ms->ms_len = len;
	ms->ms_flags = flags;
	status = sgx_ocall(17, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (off_in) {
			if (memcpy_s((void*)off_in, _len_off_in, __tmp_off_in, _len_off_in)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (off_out) {
			if (memcpy_s((void*)off_out, _len_off_out, __tmp_off_out, _len_off_out)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_splice_ocall(size_t* retval, int* error, int fd_in, int64_t* off_in, int fd_out, int64_t* off_out, size_t len, unsigned int flags)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_off_in = sizeof(int64_t);
	size_t _len_off_out = sizeof(int64_t);

	ms_u_splice_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_splice_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_off_in = NULL;
	void *__tmp_off_out = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(off_in, _len_off_in);
	CHECK_ENCLAVE_POINTER(off_out, _len_off_out);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (off_in != NULL) ? _len_off_in : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (off_out != NULL) ? _len_off_out : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_splice_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_splice_ocall_t));
	ocalloc_size -= sizeof(ms_u_splice_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd_in = fd_in;
	if (off_in != NULL) {
		ms->ms_off_in = (int64_t*)__tmp;
		__tmp_off_in = __tmp;
		if (_len_off_in % sizeof(*off_in) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, off_in, _len_off_in)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_off_in);
		ocalloc_size -= _len_off_in;
	} else {
		ms->ms_off_in = NULL;
	}
	
	ms->ms_fd_out = fd_out;
	if (off_out != NULL) {
		ms->ms_off_out = (int64_t*)__tmp;
		__tmp_off_out = __tmp;
		if (_len_off_out % sizeof(*off_out) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, off_out, _len_off_out)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_off_out);
		ocalloc_size -= _len_off_out;
	} else {
		ms->ms_off_out = NULL;
	}
	
	ms->ms_len = len;
	ms->ms_flags = flags;
	status = sgx_ocall(18, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (off_in) {
			if (memcpy_s((void*)off_in, _len_off_in, __tmp_off_in, _len_off_in)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (off_out) {
			if (memcpy_s((void*)off_out, _len_off_out, __tmp_off_out, _len_off_out)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_fcntl_arg0_ocall(int* retval, int* error, int fd, int cmd)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_fcntl_arg0_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_fcntl_arg0_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_fcntl_arg0_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_fcntl_arg0_ocall_t));
	ocalloc_size -= sizeof(ms_u_fcntl_arg0_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_cmd = cmd;
	status = sgx_ocall(19, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_fcntl_arg1_ocall(int* retval, int* error, int fd, int cmd, int arg)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_fcntl_arg1_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_fcntl_arg1_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_fcntl_arg1_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_fcntl_arg1_ocall_t));
	ocalloc_size -= sizeof(ms_u_fcntl_arg1_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_cmd = cmd;
	ms->ms_arg = arg;
	status = sgx_ocall(20, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_ioctl_arg0_ocall(int* retval, int* error, int fd, unsigned long int request)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_ioctl_arg0_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_ioctl_arg0_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_ioctl_arg0_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_ioctl_arg0_ocall_t));
	ocalloc_size -= sizeof(ms_u_ioctl_arg0_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_request = request;
	status = sgx_ocall(21, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_ioctl_arg1_ocall(int* retval, int* error, int fd, unsigned long int request, int* arg)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_arg = sizeof(int);

	ms_u_ioctl_arg1_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_ioctl_arg1_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_arg = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(arg, _len_arg);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (arg != NULL) ? _len_arg : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_ioctl_arg1_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_ioctl_arg1_ocall_t));
	ocalloc_size -= sizeof(ms_u_ioctl_arg1_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	ms->ms_request = request;
	if (arg != NULL) {
		ms->ms_arg = (int*)__tmp;
		__tmp_arg = __tmp;
		if (_len_arg % sizeof(*arg) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		if (memcpy_s(__tmp, ocalloc_size, arg, _len_arg)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_arg);
		ocalloc_size -= _len_arg;
	} else {
		ms->ms_arg = NULL;
	}
	
	status = sgx_ocall(22, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (arg) {
			if (memcpy_s((void*)arg, _len_arg, __tmp_arg, _len_arg)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_close_ocall(int* retval, int* error, int fd)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_close_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_close_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_close_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_close_ocall_t));
	ocalloc_size -= sizeof(ms_u_close_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	status = sgx_ocall(23, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_isatty_ocall(int* retval, int* error, int fd)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_isatty_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_isatty_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_isatty_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_isatty_ocall_t));
	ocalloc_size -= sizeof(ms_u_isatty_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_fd = fd;
	status = sgx_ocall(24, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_dup_ocall(int* retval, int* error, int oldfd)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_dup_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_dup_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_dup_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_dup_ocall_t));
	ocalloc_size -= sizeof(ms_u_dup_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_oldfd = oldfd;
	status = sgx_ocall(25, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_eventfd_ocall(int* retval, int* error, unsigned int initval, int flags)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_eventfd_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_eventfd_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_eventfd_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_eventfd_ocall_t));
	ocalloc_size -= sizeof(ms_u_eventfd_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_initval = initval;
	ms->ms_flags = flags;
	status = sgx_ocall(26, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_malloc_ocall(void** retval, int* error, size_t size, size_t align, int zeroed)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_malloc_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_malloc_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_malloc_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_malloc_ocall_t));
	ocalloc_size -= sizeof(ms_u_malloc_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_size = size;
	ms->ms_align = align;
	ms->ms_zeroed = zeroed;
	status = sgx_ocall(27, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_free_ocall(void* p)
{
	sgx_status_t status = SGX_SUCCESS;

	ms_u_free_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_free_ocall_t);
	void *__tmp = NULL;


	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_free_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_free_ocall_t));
	ocalloc_size -= sizeof(ms_u_free_ocall_t);

	ms->ms_p = p;
	status = sgx_ocall(28, ms);

	if (status == SGX_SUCCESS) {
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_mmap_ocall(void** retval, int* error, void* start, size_t length, int prot, int flags, int fd, int64_t offset)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_mmap_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_mmap_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_mmap_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_mmap_ocall_t));
	ocalloc_size -= sizeof(ms_u_mmap_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_start = start;
	ms->ms_length = length;
	ms->ms_prot = prot;
	ms->ms_flags = flags;
	ms->ms_fd = fd;
	ms->ms_offset = offset;
	status = sgx_ocall(29, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_munmap_ocall(int* retval, int* error, void* start, size_t length)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_munmap_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_munmap_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_munmap_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_munmap_ocall_t));
	ocalloc_size -= sizeof(ms_u_munmap_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_start = start;
	ms->ms_length = length;
	status = sgx_ocall(30, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_msync_ocall(int* retval, int* error, void* addr, size_t length, int flags)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_msync_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_msync_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_msync_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_msync_ocall_t));
	ocalloc_size -= sizeof(ms_u_msync_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_addr = addr;
	ms->ms_length = length;
	ms->ms_flags = flags;
	status = sgx_ocall(31, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_mprotect_ocall(int* retval, int* error, void* addr, size_t length, int prot)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);

	ms_u_mprotect_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_mprotect_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_mprotect_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_mprotect_ocall_t));
	ocalloc_size -= sizeof(ms_u_mprotect_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_addr = addr;
	ms->ms_length = length;
	ms->ms_prot = prot;
	status = sgx_ocall(32, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_read_hostbuf_ocall(size_t* retval, int* error, const void* host_buf, void* encl_buf, size_t count)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_encl_buf = count;

	ms_u_read_hostbuf_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_read_hostbuf_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;
	void *__tmp_encl_buf = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(encl_buf, _len_encl_buf);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (encl_buf != NULL) ? _len_encl_buf : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_read_hostbuf_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_read_hostbuf_ocall_t));
	ocalloc_size -= sizeof(ms_u_read_hostbuf_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_host_buf = host_buf;
	if (encl_buf != NULL) {
		ms->ms_encl_buf = (void*)__tmp;
		__tmp_encl_buf = __tmp;
		memset(__tmp_encl_buf, 0, _len_encl_buf);
		__tmp = (void *)((size_t)__tmp + _len_encl_buf);
		ocalloc_size -= _len_encl_buf;
	} else {
		ms->ms_encl_buf = NULL;
	}
	
	ms->ms_count = count;
	status = sgx_ocall(33, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
		if (encl_buf) {
			if (memcpy_s((void*)encl_buf, _len_encl_buf, __tmp_encl_buf, _len_encl_buf)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

sgx_status_t SGX_CDECL u_write_hostbuf_ocall(size_t* retval, int* error, void* host_buf, const void* encl_buf, size_t count)
{
	sgx_status_t status = SGX_SUCCESS;
	size_t _len_error = sizeof(int);
	size_t _len_encl_buf = count;

	ms_u_write_hostbuf_ocall_t* ms = NULL;
	size_t ocalloc_size = sizeof(ms_u_write_hostbuf_ocall_t);
	void *__tmp = NULL;

	void *__tmp_error = NULL;

	CHECK_ENCLAVE_POINTER(error, _len_error);
	CHECK_ENCLAVE_POINTER(encl_buf, _len_encl_buf);

	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (error != NULL) ? _len_error : 0))
		return SGX_ERROR_INVALID_PARAMETER;
	if (ADD_ASSIGN_OVERFLOW(ocalloc_size, (encl_buf != NULL) ? _len_encl_buf : 0))
		return SGX_ERROR_INVALID_PARAMETER;

	__tmp = sgx_ocalloc(ocalloc_size);
	if (__tmp == NULL) {
		sgx_ocfree();
		return SGX_ERROR_UNEXPECTED;
	}
	ms = (ms_u_write_hostbuf_ocall_t*)__tmp;
	__tmp = (void *)((size_t)__tmp + sizeof(ms_u_write_hostbuf_ocall_t));
	ocalloc_size -= sizeof(ms_u_write_hostbuf_ocall_t);

	if (error != NULL) {
		ms->ms_error = (int*)__tmp;
		__tmp_error = __tmp;
		if (_len_error % sizeof(*error) != 0) {
			sgx_ocfree();
			return SGX_ERROR_INVALID_PARAMETER;
		}
		memset(__tmp_error, 0, _len_error);
		__tmp = (void *)((size_t)__tmp + _len_error);
		ocalloc_size -= _len_error;
	} else {
		ms->ms_error = NULL;
	}
	
	ms->ms_host_buf = host_buf;
	if (encl_buf != NULL) {
		ms->ms_encl_buf = (const void*)__tmp;
		if (memcpy_s(__tmp, ocalloc_size, encl_buf, _len_encl_buf)) {
			sgx_ocfree();
			return SGX_ERROR_UNEXPECTED;
		}
		__tmp = (void *)((size_t)__tmp + _len_encl_buf);
		ocalloc_size -= _len_encl_buf;
	} else {
		ms->ms_encl_buf = NULL;
	}
	
	ms->ms_count = count;
	status = sgx_ocall(34, ms);

	if (status == SGX_SUCCESS) {
		if (retval) *retval = ms->ms_retval;
		if (error) {
			if (memcpy_s((void*)error, _len_error, __tmp_error, _len_error)) {
				sgx_ocfree();
				return SGX_ERROR_UNEXPECTED;
			}
		}
	}
	sgx_ocfree();
	return status;
}

