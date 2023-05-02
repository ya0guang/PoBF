#pragma once
#include <iostream>
#include <stdarg.h>
#include <vector>
#include <iostream>
#include <stdio.h>
#include <stdarg.h>
#include <memory>
#include <mutex>
#include <fstream>

#include <azguestattestation1/AttestationClient.h>

class Logger : public attest::AttestationLogger {
 public:
  void Log(const char* log_tag, LogLevel level, const char* function,
           const int line, const char* fmt, ...);
};