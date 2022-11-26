/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *               2020, Intel Labs
 */

/*
 * SSL server demonstration program (with RA-TLS)
 * This program is originally based on an mbedTLS example ssl_server.c but uses
 * RA-TLS flows (SGX Remote Attestation flows) if RA-TLS library is required by
 * user. Note that this program builds against mbedTLS 3.x.
 */

#define _GNU_SOURCE
#include "mbedtls/build_info.h"

#include <assert.h>
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <thread>

#define mbedtls_fprintf fprintf
#define mbedtls_printf printf

#include "mbedtls/ctr_drbg.h"
#include "mbedtls/debug.h"
#include "mbedtls/entropy.h"
#include "mbedtls/error.h"
#include "mbedtls/net_sockets.h"
#include "mbedtls/ssl.h"
#include "mbedtls/x509.h"

/* RA-TLS: on server, only need ra_tls_create_key_and_crt_der() to create
 * keypair and X.509 cert */
int (*ra_tls_create_key_and_crt_der_f)(uint8_t** der_key, size_t* der_key_size,
                                       uint8_t** der_crt, size_t* der_crt_size);
typedef int (*ra_tls_func_ptr)(uint8_t**, size_t*, uint8_t**, size_t*);

/* The external function in Rust. */
extern "C" int gramine_rust_entry(const uint8_t* input, uint32_t input_len,
                                  uint8_t* output, uint32_t output_buf_len,
                                  uint32_t* output_len);

#define DEBUG_LEVEL 0

#define MALICIOUS_STR "MALICIOUS DATA"

#define CA_CRT_PATH "ssl/ca.crt"
#define SRV_CRT_PATH "ssl/server.crt"
#define SRV_KEY_PATH "ssl/server.key"

static ssize_t file_read(const char* path, char* buf, size_t count) {
  FILE* f = fopen(path, "r");
  if (!f) return -errno;

  ssize_t bytes = fread(buf, 1, count, f);
  if (bytes <= 0) {
    int errsv = errno;
    fclose(f);
    return -errsv;
  }

  int close_ret = fclose(f);
  if (close_ret < 0) return -errno;

  return bytes;
}

static int handler(mbedtls_net_context* listen_fd, mbedtls_ssl_context ssl) {
  int ret = 0;
  mbedtls_printf("  . Performing the SSL/TLS handshake...");

  while ((ret = mbedtls_ssl_handshake(&ssl)) != 0) {
    if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
      mbedtls_printf(" failed\n  ! mbedtls_ssl_handshake returned %d\n\n", ret);
      fflush(stdout);

      char error_buf[100];
      mbedtls_strerror(ret, error_buf, sizeof(error_buf));
      mbedtls_printf("Last error was: %d - %s\n\n", ret, error_buf);
      fflush(stdout);

      return ret;
    }
  }

  mbedtls_printf(" ok\n");
  fflush(stdout);
  mbedtls_printf("  < Read from client:");
  fflush(stdout);

  uint8_t buf[1024];
  size_t len = 0;
  uint32_t round = 0;
  uint32_t input_len = 0;
  uint8_t* input_data = NULL;
  uint8_t* output = (uint8_t*)(malloc(262144));
  uint32_t output_len = 0;
  do {
    if (round == 0) {
      /* The client first sends the length of the data, then sends the data. */
      /* Always allocating data on the stack would cause stack overflow. */
      len = sizeof(buf) - 1;
      memset(buf, 0, sizeof(buf));
      ret = mbedtls_ssl_read(&ssl, buf, len);
    } else if (round == 1) {
      input_data = (uint8_t*)(malloc(input_len));
      memset(input_data, 0, input_len);
      ret = mbedtls_ssl_read(&ssl, input_data, input_len);
    }

    if (ret == MBEDTLS_ERR_SSL_WANT_READ || ret == MBEDTLS_ERR_SSL_WANT_WRITE)
      continue;

    if (ret <= 0) {
      switch (ret) {
        case MBEDTLS_ERR_SSL_PEER_CLOSE_NOTIFY:
          mbedtls_printf(" connection was closed gracefully\n");
          break;

        case MBEDTLS_ERR_NET_CONN_RESET:
          mbedtls_printf(" connection was reset by peer\n");
          break;

        default:
          mbedtls_printf(" mbedtls_ssl_read returned -0x%x\n", -ret);
          break;
      }

      break;
    }

    len = ret;
    mbedtls_printf(" %lu bytes read.", len);

    if (round == 0) {
      input_len = atol((char*)buf);
      mbedtls_printf(" the input length is %u.\n", input_len);
      fflush(stdout);

      round++;
    } else if (round == 1) {
      ret = gramine_rust_entry(input_data, input_len, output, 262144,
                               &output_len);
      if (ret != 0) {
        mbedtls_printf(" error calling `gramine_rust_entry`!");
        fflush(stdout);
      }

      free(input_data);
      free(output);
      break;
    }
  } while (1);

  mbedtls_printf("  > Write to client:");
  fflush(stdout);

  while ((ret = mbedtls_ssl_write(&ssl, output, output_len)) <= 0) {
    if (ret == MBEDTLS_ERR_NET_CONN_RESET) {
      mbedtls_printf(" failed\n  ! peer closed the connection\n\n");
      return ret;
    }

    if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
      mbedtls_printf(" failed\n  ! mbedtls_ssl_write returned %d\n\n", ret);
      return ret;
    }
  }

  mbedtls_printf(" ok\n");

  // Do cleanups.
  mbedtls_ssl_session_reset(&ssl);
  return 0;
}

int main(int argc, char** argv) {
  int ret = 0;
  mbedtls_net_context listen_fd;
  const char* pers = "ssl_server";
  void* ra_tls_attest_lib;

  uint8_t* der_key = NULL;
  uint8_t* der_crt = NULL;

  mbedtls_entropy_context entropy;
  mbedtls_ctr_drbg_context ctr_drbg;
  mbedtls_ssl_config conf;
  mbedtls_x509_crt srvcert;
  mbedtls_pk_context pkey;

  mbedtls_net_init(&listen_fd);
  mbedtls_ssl_config_init(&conf);
  mbedtls_x509_crt_init(&srvcert);
  mbedtls_pk_init(&pkey);
  mbedtls_entropy_init(&entropy);
  mbedtls_ctr_drbg_init(&ctr_drbg);

  char attestation_type_str[32] = {0};
  ret = file_read("/dev/attestation/attestation_type", attestation_type_str,
                  sizeof(attestation_type_str) - 1);
  if (ret < 0 && ret != -ENOENT) {
    mbedtls_printf(
        "User requested RA-TLS attestation but cannot read SGX-specific file "
        "/dev/attestation/attestation_type\n");
    return 1;
  }

  if (ret == -ENOENT || !strcmp(attestation_type_str, "none")) {
    ra_tls_attest_lib = NULL;
    ra_tls_create_key_and_crt_der_f = NULL;
  } else if (!strcmp(attestation_type_str, "epid") ||
             !strcmp(attestation_type_str, "dcap")) {
    ra_tls_attest_lib = dlopen("libra_tls_attest.so", RTLD_LAZY);
    if (!ra_tls_attest_lib) {
      mbedtls_printf("User requested RA-TLS attestation but cannot find lib\n");
      return 1;
    }

    char* error;
    ra_tls_create_key_and_crt_der_f = reinterpret_cast<ra_tls_func_ptr>(
        dlsym(ra_tls_attest_lib, "ra_tls_create_key_and_crt_der"));
    if ((error = dlerror()) != NULL) {
      mbedtls_printf("%s\n", error);
      return 1;
    }
  } else {
    mbedtls_printf("Unrecognized remote attestation type: %s\n",
                   attestation_type_str);
    return 1;
  }

  mbedtls_printf("  . Seeding the random number generator...");
  fflush(stdout);

  ret = mbedtls_ctr_drbg_seed(&ctr_drbg, mbedtls_entropy_func, &entropy,
                              (const unsigned char*)pers, strlen(pers));
  if (ret != 0) {
    mbedtls_printf(" failed\n  ! mbedtls_ctr_drbg_seed returned %d\n", ret);
    goto exit;
  }

  mbedtls_printf(" ok\n");

  if (ra_tls_attest_lib) {
    mbedtls_printf(
        "\n  . Creating the RA-TLS server cert and key (using \"%s\" as "
        "attestation type)...",
        attestation_type_str);
    fflush(stdout);

    size_t der_key_size;
    size_t der_crt_size;

    ret = (*ra_tls_create_key_and_crt_der_f)(&der_key, &der_key_size, &der_crt,
                                             &der_crt_size);
    if (ret != 0) {
      mbedtls_printf(
          " failed\n  !  ra_tls_create_key_and_crt_der returned %d\n\n", ret);
      goto exit;
    }

    ret =
        mbedtls_x509_crt_parse(&srvcert, (unsigned char*)der_crt, der_crt_size);
    if (ret != 0) {
      mbedtls_printf(" failed\n  !  mbedtls_x509_crt_parse returned %d\n\n",
                     ret);
      goto exit;
    }

    ret = mbedtls_pk_parse_key(&pkey, (unsigned char*)der_key, der_key_size,
                               /*pwd=*/NULL, 0, mbedtls_ctr_drbg_random,
                               &ctr_drbg);
    if (ret != 0) {
      mbedtls_printf(" failed\n  !  mbedtls_pk_parse_key returned %d\n\n", ret);
      goto exit;
    }

    mbedtls_printf(" ok\n");

    if (argc > 1) {
      // TODO. Add file path.
    }
  } else {
    mbedtls_printf("\n  . Creating normal server cert and key...");
    fflush(stdout);

    ret = mbedtls_x509_crt_parse_file(&srvcert, SRV_CRT_PATH);
    if (ret != 0) {
      mbedtls_printf(
          " failed\n  !  mbedtls_x509_crt_parse_file returned %d\n\n", ret);
      goto exit;
    }

    ret = mbedtls_x509_crt_parse_file(&srvcert, CA_CRT_PATH);
    if (ret != 0) {
      mbedtls_printf(
          " failed\n  !  mbedtls_x509_crt_parse_file returned %d\n\n", ret);
      goto exit;
    }

    ret = mbedtls_pk_parse_keyfile(&pkey, SRV_KEY_PATH, /*password=*/NULL,
                                   mbedtls_ctr_drbg_random, &ctr_drbg);
    if (ret != 0) {
      mbedtls_printf(" failed\n  !  mbedtls_pk_parse_keyfile returned %d\n\n",
                     ret);
      goto exit;
    }

    mbedtls_printf(" ok\n");
  }

  mbedtls_printf("  . Bind on https://localhost:2333/ ...");
  fflush(stdout);

  ret = mbedtls_net_bind(&listen_fd, NULL, "2333", MBEDTLS_NET_PROTO_TCP);
  if (ret != 0) {
    mbedtls_printf(" failed\n  ! mbedtls_net_bind returned %d\n\n", ret);
    goto exit;
  }

  mbedtls_printf(" ok\n");

  mbedtls_printf("  . Setting up the SSL configuration....");
  fflush(stdout);

  ret = mbedtls_ssl_config_defaults(&conf, MBEDTLS_SSL_IS_SERVER,
                                    MBEDTLS_SSL_TRANSPORT_STREAM,
                                    MBEDTLS_SSL_PRESET_DEFAULT);
  if (ret != 0) {
    mbedtls_printf(" failed\n  ! mbedtls_ssl_config_defaults returned %d\n\n",
                   ret);
    goto exit;
  }

  mbedtls_ssl_conf_rng(&conf, mbedtls_ctr_drbg_random, &ctr_drbg);

  if (!ra_tls_attest_lib) {
    /* no RA-TLS attest library present, use embedded CA chain */
    mbedtls_ssl_conf_ca_chain(&conf, srvcert.next, NULL);
  }

  ret = mbedtls_ssl_conf_own_cert(&conf, &srvcert, &pkey);
  if (ret != 0) {
    mbedtls_printf(" failed\n  ! mbedtls_ssl_conf_own_cert returned %d\n\n",
                   ret);
    goto exit;
  }

  mbedtls_printf(" ok\n");
  fflush(stdout);

reset:
  // Create a thread pool for handling different connections.
  while (true) {
    mbedtls_printf("  . Waiting for a remote connection ...\n");
    fflush(stdout);

    mbedtls_ssl_context ssl;
    mbedtls_net_context client;
    mbedtls_ssl_init(&ssl);
    // Setup the SSL tunnel.
    ret = mbedtls_ssl_setup(&ssl, &conf);
    if (ret != 0) {
      mbedtls_printf(" failed\n  ! mbedtls_ssl_setup returned %d\n\n", ret);
      fflush(stdout);
    }

    ret = mbedtls_net_accept(&listen_fd, &client, NULL, 0, NULL);
    if (ret != 0) {
      mbedtls_printf(" failed\n  ! mbedtls_net_accept returned %d\n\n", ret);
    } else {
      mbedtls_ssl_set_bio(&ssl, &client, mbedtls_net_send, mbedtls_net_recv,
                          NULL);
      mbedtls_printf(" ok\n");
      fflush(stdout);

      std::thread t(handler, &listen_fd, ssl);
      t.detach();
    }
  }

exit:
  if (ra_tls_attest_lib) dlclose(ra_tls_attest_lib);

  mbedtls_net_free(&listen_fd);

  mbedtls_x509_crt_free(&srvcert);
  mbedtls_pk_free(&pkey);
  mbedtls_ssl_config_free(&conf);
  mbedtls_ctr_drbg_free(&ctr_drbg);
  mbedtls_entropy_free(&entropy);

  free(der_key);
  free(der_crt);

  return ret;
}
