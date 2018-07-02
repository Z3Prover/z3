/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    smt_logics.cpp

Abstract:

    Module for recognizing SMT logics.

Author:

    Nikolaj Bjorner (nbjorner) 2016-11-4

Revision History:

--*/
#include "util/symbol.h"
#include "solver/smt_logics.h"



bool smt_logics::supported_logic(symbol const & s) {
    return logic_has_uf(s) || logic_is_all(s) || logic_has_fd(s) ||
        logic_has_arith(s) || logic_has_bv(s) ||
        logic_has_array(s) || logic_has_seq(s) || logic_has_str(s) ||
        logic_has_horn(s) || logic_has_fpa(s);
}

bool smt_logics::logic_has_reals_only(symbol const& s) {
    return
        s == "QF_RDL" ||
        s == "QF_LRA" ||
        s == "UFLRA" ||
        s == "LRA" ||
        s == "RDL" ||
        s == "QF_NRA" ||
        s == "QF_UFNRA" ||
        s == "QF_UFLRA";
}

bool smt_logics::logic_has_arith(symbol const & s) {
    return
        s == "QF_LRA" ||
        s == "QF_LIA" ||
        s == "QF_RDL" ||
        s == "QF_IDL" ||
        s == "QF_AUFLIA" ||
        s == "QF_ALIA" ||
        s == "QF_AUFLIRA" ||
        s == "QF_AUFNIA" ||
        s == "QF_AUFNIRA" ||
        s == "QF_ANIA" ||
        s == "QF_LIRA" ||
        s == "QF_UFLIA" ||
        s == "QF_UFLRA" ||
        s == "QF_UFIDL" ||
        s == "QF_UFRDL" ||
        s == "QF_NIA" ||
        s == "QF_NRA" ||
        s == "QF_NIRA" ||
        s == "QF_UFNRA" ||
        s == "QF_UFNIA" ||
        s == "QF_UFNIRA" ||
        s == "QF_BVRE" ||
        s == "ALIA" ||
        s == "AUFLIA" ||
        s == "AUFLIRA" ||
        s == "AUFNIA" ||
        s == "AUFNIRA" ||
        s == "UFLIA" ||
        s == "UFLRA" ||
        s == "UFNRA" ||
        s == "UFNIRA" ||
        s == "NIA" ||
        s == "NRA" ||
        s == "UFNIA" ||
        s == "LIA" ||
        s == "LRA" ||
        s == "UFIDL" ||
        s == "QF_FP" ||
        s == "QF_FPBV" ||
        s == "QF_BVFP" ||
        s == "QF_S" ||
        s == "ALL" ||
        s == "QF_FD" ||
        s == "HORN" ||
        s == "QF_FPLRA";
}

bool smt_logics::logic_has_bv(symbol const & s) {
    return
        s == "UFBV" ||
        s == "AUFBV" ||
        s == "ABV" ||
        s == "BV" ||
        s == "QF_BV" ||
        s == "QF_UFBV" ||
        s == "QF_ABV" ||
        s == "QF_AUFBV" ||
        s == "QF_BVRE" ||
        s == "QF_FPBV" ||
        s == "QF_BVFP" ||
        s == "ALL" ||
        s == "QF_FD" ||
        s == "HORN";
}

bool smt_logics::logic_has_array(symbol const & s) {
    return
        s == "QF_AX" ||
        s == "QF_AUFLIA" ||
        s == "QF_ANIA" ||
        s == "QF_ALIA" ||
        s == "QF_AUFLIRA" ||
        s == "QF_AUFNIA" ||
        s == "QF_AUFNIRA" ||
        s == "ALIA" ||
        s == "AUFLIA" ||
        s == "AUFLIRA" ||
        s == "AUFNIA" ||
        s == "AUFNIRA" ||
        s == "AUFBV" ||
        s == "ABV" ||
        s == "ALL" ||
        s == "QF_ABV" ||
        s == "QF_AUFBV" ||
        s == "HORN";
}

bool smt_logics::logic_has_seq(symbol const & s) {
    return s == "QF_BVRE" || s == "QF_S" || s == "ALL";
}

bool smt_logics::logic_has_str(symbol const & s) {
    return s == "QF_S" || s == "ALL";
}

bool smt_logics::logic_has_fpa(symbol const & s) {
    return s == "QF_FP" || s == "QF_FPBV" || s == "QF_BVFP" || s == "QF_FPLRA"  || s == "ALL";
}

bool smt_logics::logic_has_uf(symbol const & s) {
    return s == "QF_UF" || s == "UF" || s == "QF_DT";
}

bool smt_logics::logic_has_horn(symbol const& s) {
    return s == "HORN";
}

bool smt_logics::logic_has_pb(symbol const& s) {
    return s == "QF_FD" || s == "ALL" || logic_has_horn(s);
}

bool smt_logics::logic_has_datatype(symbol const& s) {
    return s == "QF_FD" || s == "ALL" || s == "QF_DT";
}
