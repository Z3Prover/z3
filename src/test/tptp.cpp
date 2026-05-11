#include <cstdio>
#include <sstream>
#include <string>
#include <vector>
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

constexpr unsigned tptp_buf_sz = 4096;

static std::string run_tptp(char const* file) {
    std::ostringstream cmd;
    cmd << "\"" << Z3_TEST_BIN_DIR << "/" << z3_bin_name << "\" -tptp "
        << "\"" << Z3_TEST_SRC_DIR << "/tptp/" << file << "\" 2>&1";
    FILE* pipe = Z3_POPEN(cmd.str().c_str(), "r");
    ENSURE(pipe != nullptr);
    std::string out;
    char buffer[tptp_buf_sz];
    while (fgets(buffer, sizeof(buffer), pipe))
        out += buffer;
    int code = Z3_PCLOSE(pipe);
#ifndef _WINDOWS
    if (WIFEXITED(code))
        code = WEXITSTATUS(code);
#endif
    ENSURE(code == 0);
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
