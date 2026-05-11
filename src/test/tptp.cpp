#include <cstdio>
#include <sstream>
#include <string>
#include <vector>
#include <cctype>
#include <iostream>
#include "util/debug.h"

#ifdef _WINDOWS
#define Z3_POPEN  _popen
#define Z3_PCLOSE _pclose
static char const* z3_bin_name = "z3.exe";
#else
#include <sys/wait.h>
#define Z3_POPEN  popen
#define Z3_PCLOSE pclose
static char const* z3_bin_name = "z3";
#endif

struct tptp_case {
    char const* file;
    char const* expected_status;
};

constexpr unsigned command_output_buffer_size = 4096;

static bool is_safe_file_name(char const* s) {
    if (!s || !*s)
        return false;
    if (s[0] == '-' || s[0] == '.')
        return false;
    if (std::string(s).find('/') != std::string::npos || std::string(s).find('\\') != std::string::npos)
        return false;
    if (std::string(s).find("..") != std::string::npos)
        return false;
    while (*s) {
        unsigned char c = static_cast<unsigned char>(*s);
        if (!(std::isalnum(c) || c == '.' || c == '-' || c == '_'))
            return false;
        ++s;
    }
    return true;
}

static std::string run_tptp(char const* file) {
    if (!is_safe_file_name(file)) {
        std::cerr << "Unsafe TPTP test filename: " << file << "\n";
        ENSURE(false);
    }
    std::ostringstream cmd;
    cmd << "\"" << Z3_TEST_BIN_DIR << "/" << z3_bin_name << "\" -tptp "
        << "\"" << Z3_TEST_SRC_DIR << "/tptp/" << file << "\" 2>&1";
    FILE* pipe = Z3_POPEN(cmd.str().c_str(), "r");
    if (!pipe) {
        std::cerr << "Failed to execute command: " << cmd.str() << "\n";
        ENSURE(false);
    }
    std::string out;
    char buffer[command_output_buffer_size];
    while (fgets(buffer, sizeof(buffer), pipe))
        out += buffer;
    int code = Z3_PCLOSE(pipe);
#ifndef _WINDOWS
    if (WIFEXITED(code))
        code = WEXITSTATUS(code);
#endif
    if (code != 0) {
        std::cerr << "TPTP command failed for file '" << file << "' with exit code " << code << "\n";
        std::cerr << out << "\n";
        ENSURE(false);
    }
    return out;
}

void tst_tptp() {
    std::vector<tptp_case> cases = {
        {"agatha-butler.p", "% SZS status Theorem"},
        {"socrates-theorem.p", "% SZS status Theorem"},
        {"simple-sat.p", "% SZS status Satisfiable"}
    };
    for (auto const& c : cases) {
        std::string out = run_tptp(c.file);
        ENSURE(out.find(c.expected_status) != std::string::npos);
    }
}
