#include <atomic>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>
#include <iostream>
#include <sstream>
#include "util/debug.h"
#include "util/error_codes.h"
#include "cmd_context/tptp_frontend.h"

struct tptp_case {
    char const* name;
    char const* input;
    char const* expected_status;
};

static unsigned run_tptp(char const* input, std::string& out, std::string& err) {
    std::streambuf* old_out = std::cout.rdbuf();
    std::streambuf* old_err = std::cerr.rdbuf();
    std::ostringstream out_buf;
    std::ostringstream err_buf;
    std::cout.rdbuf(out_buf.rdbuf());
    std::cerr.rdbuf(err_buf.rdbuf());
    unsigned code = read_tptp_string(input);
    std::cout.rdbuf(old_out);
    std::cerr.rdbuf(old_err);
    out = out_buf.str();
    err = err_buf.str();
    return code;
}

static std::string run_tptp(char const* input) {
    std::string out, err;
    unsigned code = run_tptp(input, out, err);
    ENSURE(code == 0);
    return out;
}

static void write_file(char const* path, char const* contents) {
    std::ofstream out(path);
    ENSURE(out.good());
    out << contents;
    ENSURE(out.good());
}

class scoped_temp_file {
    std::string m_path;
public:
    scoped_temp_file(scoped_temp_file const&) = delete;
    scoped_temp_file& operator=(scoped_temp_file const&) = delete;
    scoped_temp_file(scoped_temp_file&&) = delete;
    scoped_temp_file& operator=(scoped_temp_file&&) = delete;

    scoped_temp_file(char const* contents) {
        static std::atomic<unsigned> counter(0);
        auto stamp = std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
        m_path = (std::filesystem::temp_directory_path() /
            ("z3-tptp-" + std::to_string(stamp) + "-" + std::to_string(counter.fetch_add(1)) + ".p")).string();
        write_file(m_path.c_str(), contents);
    }
    ~scoped_temp_file() {
        if (!m_path.empty() && std::remove(m_path.c_str()) != 0)
            std::cerr << "failed to remove temporary file '" << m_path << "': " << std::strerror(errno) << "\n";
    }
    std::string const& path() const { return m_path; }
};

extern bool g_display_statistics;
extern bool g_display_model;

void tst_tptp() {
    g_display_statistics = false;
    g_display_model = false;
    std::vector<tptp_case> cases = {
        {"agatha-butler",
R"(fof(ax1,axiom, lives(agatha)).
fof(ax2,axiom, lives(butler)).
fof(ax3,axiom, lives(charles)).
fof(ax4,axiom, ! [X] : (lives(X) => (X = agatha | X = butler | X = charles))).
fof(ax5,axiom, ! [X,Y] : (killed(X,Y) => hates(X,Y))).
fof(ax6,axiom, ! [X,Y] : (killed(X,Y) => ~ richer(X,Y))).
fof(ax7,axiom, ! [X] : (hates(agatha,X) => ~ hates(charles,X))).
fof(ax8,axiom, ! [X] : (X != butler => hates(agatha,X))).
fof(ax9,axiom, ! [X] : (~ richer(X,agatha) => hates(butler,X))).
fof(ax10,axiom, ! [X] : (hates(agatha,X) => hates(butler,X))).
fof(ax11,axiom, ! [X] : (? [Y] : ~ hates(X,Y))).
fof(ax12,axiom, agatha != butler).
fof(ax13,axiom, ? [X] : killed(X,agatha)).
fof(conj,conjecture, ~ killed(butler,agatha)).)",
         "% SZS status Theorem"},
        {"socrates-theorem",
R"(fof(a1,axiom, ! [X] : (human(X) => mortal(X))).
fof(a2,axiom, human(socrates)).
fof(c1,conjecture, mortal(socrates)).)",
         "% SZS status Theorem"},
        {"simple-sat",
R"(fof(a1,axiom, p(a)).)",
         "% SZS status Satisfiable"},
        {"fof-implicit-forall",
R"(fof(a1,axiom, p(X)).
fof(c1,conjecture, p(a)).)",
         "% SZS status Theorem"},
        {"cnf-implicit-forall",
R"(cnf(c1,axiom, p(X)).
cnf(c2,axiom, ~ p(a)).)",
         "% SZS status Unsatisfiable"},
        {"fof-bare-constant-equality",
R"(fof(a1,axiom, ! [X] : (X = a)).
fof(c1,conjecture, b = a).)",
         "% SZS status Theorem"},
        {"tff-negative-literal",
R"(tff(c1,conjecture, $less(-2,2)).)",
         "% SZS status Theorem"},
        {"tff-rational-literal",
R"(tff(c1,conjecture, $less(1/2,2/3)).)",
         "% SZS status Theorem"},
        {"tff-type-decl-arrow",
R"(tff(p_type,type, p: $int > $o ).
tff(a1,axiom, p(1)).
tff(c1,conjecture, p(1)).)",
         "% SZS status Theorem"},
        {"tff-typed-int-quantifier",
R"(tff(c1,conjecture, ? [X: $int] : $less(12,X)).)",
         "% SZS status Theorem"},
        {"tff-lesseq-built-in",
R"(tff(c1,conjecture, $lesseq(2,2)).)",
         "% SZS status Theorem"},
        {"tff-bare-integer-equality",
R"(tff(c1,conjecture, 31 != 12).)",
         "% SZS status Theorem"},
        {"tff-decimal-literal",
R"(tff(c1,conjecture, ~ $less(-3.25,-8.69)).)",
         "% SZS status Theorem"},
        {"tff-uminus-built-in",
R"(tff(c1,conjecture, $less($uminus(2),0)).)",
         "% SZS status Theorem"}
    };
    for (auto const& c : cases) {
        std::string out = run_tptp(c.input);
        ENSURE(out.find(c.expected_status) != std::string::npos);
    }

    std::string out, err;
    unsigned code = run_tptp("tff(c1,conjecture, $less(1/0,1)).", out, err);
    ENSURE(code == ERR_PARSER);
    ENSURE(err.find("denominator of rational literal cannot be zero") != std::string::npos);

    scoped_temp_file included(
R"(fof(keep,axiom,p).
fof(poison,axiom,~ p).)");
    std::string selected_include =
        std::string("include('") + included.path() + R"(',[keep]).
fof(a1,axiom,q).)";
    code = run_tptp(selected_include.c_str(), out, err);
    ENSURE(code == 0);
    ENSURE(out.find("% SZS status Satisfiable") != std::string::npos);

    code = run_tptp("fof(a1,axiom,[p(a),q(a)]).", out, err);
    ENSURE(code == ERR_PARSER);
    ENSURE(err.find("tuple/list formulas are not supported") != std::string::npos);

    code = run_tptp("fof(a1,axiom,$let([X: $i, Y: $i], [X,Y] := a, X = Y)).", out, err);
    ENSURE(code == ERR_PARSER);
    ENSURE(err.find("tuple $let destructuring is not supported") != std::string::npos);
}
