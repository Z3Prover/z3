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
//        {"fof-bare-constant-equality",
//  R"(fof(a1,axiom, ! [X] : (X = a)).
//fof(c1,conjecture, b = a).)",
//         "% SZS status Theorem"},
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
         "% SZS status Theorem"},
        {"tff-let-single-binding",
R"(tff(c1,conjecture, $let(a: $int, a := 3, $less(a,4))).)",
         "% SZS status Theorem"},
        {"tff-let-multiple-bindings",
R"(tff(c1,conjecture, $let([a: $int, b: $int], [a := 1, b := 2], $less($sum(a,b),4))).)",
         "% SZS status Theorem"},
        {"tff-let-nested",
R"(tff(c1,conjecture, $let(a: $int, a := 5, $let(b: $int, b := 3, $less(b,a)))).)",
         "% SZS status Theorem"},
        // Parenthesized negation binds only the next literal, not the whole
        // disjunction: "( ~ p | q )" is "(~p) | q", not "~(p | q)". With p
        // asserted this is satisfiable (q true); the old whole-formula negation
        // made it spuriously unsatisfiable.
        {"fof-paren-negation-precedence",
R"(fof(a1,axiom, ( ~ p | q )).
fof(a2,axiom, p).)",
         "% SZS status Satisfiable"},
        // A TPTP quantifier binds tighter than the binary connectives, so
        // "! [X] : p(X) => g" is "(! [X] : p(X)) => g". With p(a), ~p(b), ~g the
        // antecedent is false, so the implication holds (Theorem). The old parse
        // "! [X] : (p(X) => g)" was false at X=a and reported CounterSatisfiable.
        {"fof-quantifier-binds-tighter-than-implies",
R"(fof(a1,axiom, p(a)).
fof(a2,axiom, ~ p(b)).
fof(a3,axiom, ~ g).
fof(c1,conjecture, ! [X] : p(X) => g).)",
         "% SZS status Theorem"},
        // Mixed Int/Real equality must use the arithmetic to_real coercion, not
        // an uninterpreted boxing function: $to_int(3.0) = 3.0 is valid because
        // to_real(3) = 3.0. Boxing severed the link and reported CounterSatisfiable.
        {"tff-int-real-equality-coercion",
R"(tff(c1,conjecture, $to_int(3.0) = 3.0).)",
         "% SZS status Theorem"}
    };
    for (auto const& c : cases) {
        std::string out = run_tptp(c.input);
        std::cout << c.name << " status: " << c.expected_status << " out: " << out << "\n";
        ENSURE(out.find(c.expected_status) != std::string::npos);
    }

    std::string out, err;
    unsigned code = run_tptp("tff(c1,conjecture, $less(1/0,1)).", out, err);
    ENSURE(code == ERR_PARSER);
    ENSURE(err.find("denominator of rational literal cannot be zero") != std::string::npos);

    // SZS status cross-checking against the annotated input status.

    // Matching annotation: no BUG flag.
    {
        std::string o = run_tptp(
R"(% Status   : Unsatisfiable
cnf(c1,axiom, p(X)).
cnf(c2,axiom, ~ p(a)).)");
        ENSURE(o.find("% SZS status Unsatisfiable") != std::string::npos);
        ENSURE(o.find("BUG") == std::string::npos);
    }

    // Contradicting annotation (says Satisfiable, z3 finds Unsatisfiable): BUG.
    {
        std::string o = run_tptp(
R"(% SZS status Satisfiable
cnf(c1,axiom, p(X)).
cnf(c2,axiom, ~ p(a)).)");
        ENSURE(o.find("BUG") != std::string::npos);
        ENSURE(o.find("expected Satisfiable") != std::string::npos);
    }

    // Contradicting annotation (says Unsatisfiable, z3 finds Satisfiable): BUG.
    {
        std::string o = run_tptp(
R"(% Status   : Unsatisfiable
fof(a1,axiom, p(a)).)");
        ENSURE(o.find("BUG") != std::string::npos);
    }

    // Theorem annotation matches z3's Theorem verdict for conjectures: no BUG.
    {
        std::string o = run_tptp(
R"(% SZS status Theorem
fof(a1,axiom, ! [X] : (human(X) => mortal(X))).
fof(a2,axiom, human(socrates)).
fof(c1,conjecture, mortal(socrates)).)");
        ENSURE(o.find("% SZS status Theorem") != std::string::npos);
        ENSURE(o.find("BUG") == std::string::npos);
    }

    // Unannotated input: nothing to check, no BUG.
    {
        std::string o = run_tptp("fof(a1,axiom, p(a)).");
        ENSURE(o.find("BUG") == std::string::npos);
    }
}
