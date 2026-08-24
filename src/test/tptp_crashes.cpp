/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "cmd_context/tptp_frontend.h"
#include "util/debug.h"
#include <iostream>
#include <sstream>
#include <string>

extern bool g_display_model;
extern bool g_display_statistics;

static std::string run_tptp_crash_regression(char const* input) {
    std::streambuf* old_out = std::cout.rdbuf();
    std::ostringstream out;
    std::cout.rdbuf(out.rdbuf());
    unsigned code = read_tptp_string(input);
    std::cout.rdbuf(old_out);
    ENSURE(code == 0);
    return out.str();
}

void tst_tptp_crashes() {
    g_display_statistics = false;
    g_display_model = false;

    // Lambda beta axioms must be queued during array propagation. Immediate
    // internalization recursively grows the native stack.
    std::string out = run_tptp_crash_regression(
R"(thf(c,conjecture,
    ! [P: $i > $o] :
    ? [M: ( $i > $i ) > $o] :
    ! [G: $i > $i,H: $i > $i] :
      ( ( ( M @ G ) & ( M @ H ) )
     => ( ( M @ ^ [Z: $i] : ( G @ ( H @ Z ) ) )
        & ! [Y: $i] : ( ( P @ Y ) => ( P @ ( G @ Y ) ) ) ) )).)");
    ENSURE(out.find("% SZS status GaveUp") != std::string::npos);

    // A choice axiom can simplify dynamically asserted formulas to false.
    // Conflict analysis still needs an installed Boolean justification.
    out = run_tptp_crash_regression(
R"(thf(nat_type,type,nat: $tType).
thf(zer_type,type,zer: nat).
thf(suc_type,type,suc: nat > nat).
thf(fin_type,type,fin: nat > $tType).
thf(zerf_type,type,zerf: !>[N: nat] : ( fin @ ( suc @ N ) )).
thf(sucf_type,type,sucf: !>[N: nat] : ( ( fin @ N ) > ( fin @ ( suc @ N ) ) )).
thf(c,conjecture,
    ( ( @+[X: fin @ ( suc @ zer )] : ( X = ( zerf @ zer ) ) )
    = ( zerf @ zer ) )).)");
    ENSURE(out.find("% SZS status GaveUp") != std::string::npos);
}
