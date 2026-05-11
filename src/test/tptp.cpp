#include <string>
#include <vector>
#include <iostream>
#include <sstream>
#include "util/debug.h"
#include "shell/tptp_frontend.h"

struct tptp_case {
    char const* file;
    char const* expected_status;
};

static std::string run_tptp(char const* file) {
    std::string path = std::string(Z3_TEST_SRC_DIR) + "/tptp/" + file;
    std::streambuf* old_out = std::cout.rdbuf();
    std::ostringstream out;
    std::cout.rdbuf(out.rdbuf());
    unsigned code = read_tptp(path.c_str());
    std::cout.rdbuf(old_out);
    ENSURE(code == 0);
    return out.str();
}

bool g_display_statistics = false;
bool g_display_model = false;

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
