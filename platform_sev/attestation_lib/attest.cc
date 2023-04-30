#include <iostream>
#include <stdarg.h>
#include <vector>
#include <iostream>
#include <string>
#include <algorithm>
#include <thread>

#include <azguestattestation1/AttestationClient.h>
#include <boost/algorithm/string.hpp>
#include <nlohmann/json.hpp>

#include "utils.h"
#include "logger.h"

using json = nlohmann::json;

#define OUTPUT_TYPE_JWT "token"
#define OUTPUT_TYPE_BOOL "bool"

// default guest attestation url
std::string default_attestation_url =
    "https://sharedeus2.eus2.attest.azure.net/";

extern "C" int get_attestation_report(unsigned char* buf, const size_t len) {
  std::string attestation_url;
  std::string nonce;
  std::string output_type;
  if (attestation_url.empty()) {
    // use the default attestation url
    attestation_url.assign(default_attestation_url);
  }

  if (output_type.empty()) {
    // set the default output type to boolean
    output_type = OUTPUT_TYPE_BOOL;
  }

  AttestationClient* attestation_client = nullptr;
  Logger* log_handle = new Logger();

  // Initialize attestation client
  if (!Initialize(log_handle, &attestation_client)) {
    printf("Failed to create attestation client object\n");
    Uninitialize();
    exit(1);
  }

  // parameters for the Attest call
  attest::ClientParameters params = {};
  params.attestation_endpoint_url = (unsigned char*)attestation_url.c_str();
  std::string client_payload_str =
      "{\"nonce\":\"" + nonce + "\"}";  // nonce is optional
  params.client_payload = (unsigned char*)client_payload_str.c_str();
  params.version = CLIENT_PARAMS_VERSION;
  unsigned char* jwt = nullptr;
  attest::AttestationResult result;

  bool is_cvm = false;
  bool attestation_success = true;
  std::string jwt_str;
  // call attest
  if ((result = attestation_client->Attest(params, &jwt)).code_ !=
      attest::AttestationResult::ErrorCode::SUCCESS) {
    attestation_success = false;
  }

  if (attestation_success) {
    jwt_str = reinterpret_cast<char*>(jwt);
    attestation_client->Free(jwt);
    // Prase attestation token to extract isolation tee details
    std::vector<std::string> tokens;
    boost::split(tokens, jwt_str, [](char c) { return c == '.'; });
    if (tokens.size() < 3) {
      printf("Invalid JWT token");
      exit(1);
    }

    std::string jwt_response = base64_decode(tokens[1]);
    Uninitialize();

    // Copy back to Rust.
    if (jwt_response.size() >= len) {
      printf("the given buffer is too small!");
      return -1;
    }

    memcpy(buf, jwt_response.c_str(), jwt_response.size());
    return 0;
  } else {
    Uninitialize();
    return -1;
  }
}
