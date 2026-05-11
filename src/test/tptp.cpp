#include <string>
#include <vector>
#include <iostream>
#include <sstream>
#include "util/debug.h"
#include "cmd_context/tptp_frontend.h"

struct tptp_case {
    char const* name;
    char const* input;
    char const* expected_status;
};

static std::string run_tptp(char const* input) {
    std::streambuf* old_out = std::cout.rdbuf();
    std::ostringstream out;
    std::cout.rdbuf(out.rdbuf());
    unsigned code = read_tptp_string(input);
    std::cout.rdbuf(old_out);
    ENSURE(code == 0);
    return out.str();
}

// Required externs from shell/tptp_frontend.cpp; keep output minimal in tests.
bool g_display_statistics = false;
bool g_display_model = false;

void tst_tptp() {
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
         "% SZS status Satisfiable"}
    };
    for (auto const& c : cases) {
        std::string out = run_tptp(c.input);
        if (out.find(c.expected_status) == std::string::npos)
            std::cerr << "Unexpected TPTP status for case: " << c.name << "\n" << out << "\n";
        ENSURE(out.find(c.expected_status) != std::string::npos);
    }
}
