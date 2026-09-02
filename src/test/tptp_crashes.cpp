/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "cmd_context/tptp_frontend.h"
#include "util/debug.h"
#include "util/gparams.h"
#include "util/timeout.h"
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

    // HO refinement can expose a lambda with free outer variables to the
    // legacy array solver. Its beta axiom must use a proxy enode.
    gparams::set("smt.ho_matching", "true");
    out = run_tptp_crash_regression(
R"(thf(a_type,type,a: $tType).
thf(c,conjecture,
    ! [T: ( a > $o ) > $o] :
      ( ! [K: ( a > $o ) > $o,R: a > $o] :
          ( ( ! [X: a > $o] : ( ( K @ X ) => ( T @ X ) )
            & ( R = ( ^ [X: a] : ? [S: a > $o] : ( ( K @ S ) & ( S @ X ) ) ) ) )
         => ( T @ R ) )
     => ! [S: a > $o] :
          ( ( T @ S )
        <=> ! [X: a] :
              ( ( S @ X )
             => ? [R: a > $o] :
                  ( ? [N: a > $o] :
                      ( ( T @ N )
                      & ! [Y: a] : ( ( N @ Y ) => ( R @ Y ) )
                      & ( N @ X ) )
                  & ! [Y: a] : ( ( R @ Y ) => ( S @ Y ) ) ) ) ) )).)");
    ENSURE(out.find("% SZS status GaveUp") != std::string::npos);
    gparams::set("smt.ho_matching", "false");

    // Array term internalization must not assume that arguments already
    // internalized as booleans (e.g., in a gate context) have an enode.
    // theory_array::internalize_term_core previously indexed app2enode for
    // such arguments and dereferenced a null enode, causing an access
    // violation (SYO555^1.p from TPTP with smt.ho_matching=true).
    gparams::set("smt.ho_matching", "true");
    set_timeout(5000);
    out = run_tptp_crash_regression(
R"(thf(eps1,type,
    eps1: ( $i > $o ) > $i ).
thf(choiceax1,axiom,
    ! [P: $i > $o] :
      ( ? [X: $i] : ( P @ X )
     => ( P @ ( eps1 @ P ) ) ) ).
thf(if1,type,
    if1: $o > $i > $i > $i ).
thf(if1d,definition,
    ( if1
    = ( ^ [B: $o,X: $i,Y: $i] :
          ( eps1
          @ ^ [Z: $i] :
              ( ( B
                & ( Z = X ) )
              | ( ~ B
                & ( Z = Y ) ) ) ) ) ) ).
thf(eps2,type,
    eps2: ( $i > $o ) > $i ).
thf(choiceax2,axiom,
    ! [P: $i > $o] :
      ( ? [X: $i] : ( P @ X )
     => ( P @ ( eps2 @ P ) ) ) ).
thf(if2,type,
    if2: $o > $i > $i > $i ).
thf(if2d,definition,
    ( if2
    = ( ^ [B: $o,X: $i,Y: $i] :
          ( eps2
          @ ^ [Z: $i] :
              ( ( B
                & ( Z = X ) )
              | ( ~ B
                & ( Z = Y ) ) ) ) ) ) ).
thf(conj,conjecture,
    if1 = if2 ).)");
    ENSURE(out.find("% SZS status") != std::string::npos);
    gparams::set("smt.ho_matching", "false");
    disable_timeout();
}
