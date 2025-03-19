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
        logic_has_horn(s) || logic_has_fpa(s) || logic_has_datatype(s);
}

bool smt_logics::logic_has_reals_only(symbol const& s) {
    return
        s.str().find("LRA") != std::string::npos ||
        s.str().find("LRA") != std::string::npos ||
        s.str().find("NRA") != std::string::npos ||
        s.str().find("RDL") != std::string::npos;
}

bool smt_logics::logic_has_arith(symbol const & s) {
    return
        s.str().find("LRA") != std::string::npos ||
        s.str().find("LIRA") != std::string::npos ||
        s.str().find("LIA") != std::string::npos ||
        s.str().find("LRA") != std::string::npos ||
        s.str().find("NRA") != std::string::npos ||
        s.str().find("NIRA") != std::string::npos ||
        s.str().find("NIA") != std::string::npos ||
        s.str().find("IDL") != std::string::npos ||
        s.str().find("RDL") != std::string::npos ||
        s == "QF_BVRE" ||
        s == "QF_FP" ||
        s == "FP" ||
        s == "QF_FPBV" ||
        s == "QF_BVFP" ||
        s == "QF_S" ||
        logic_is_all(s) ||
        s == "QF_FD" ||
        s == "HORN";
}

bool smt_logics::logic_has_bv(symbol const & s) {
    return
        s.str().find("BV") != std::string::npos ||
        s == "FP" ||
        logic_is_all(s) ||
        s == "QF_FD" ||
        s == "SMTFD" ||
        s == "HORN";
}

bool smt_logics::logic_has_array(symbol const & s) {
    return
        s.str().starts_with("QF_A") ||   
        s.str().starts_with("A") ||   
        logic_is_all(s) ||
        s == "SMTFD" ||
        s == "HORN";
}

bool smt_logics::logic_has_seq(symbol const & s) {
    return s == "QF_BVRE" || logic_has_str(s);
}

bool smt_logics::logic_has_str(symbol const & s) {
    return s == "QF_S" || s == "QF_SLIA" || s == "QF_SNIA" || logic_is_all(s);
}

bool smt_logics::logic_has_fpa(symbol const & s) {
    return s == "FP" || s == "QF_FP" || s == "QF_FPBV" || s == "QF_BVFP" || s == "QF_FPLRA"  || logic_is_all(s);
}

bool smt_logics::logic_has_uf(symbol const & s) {
    return 
        s.str().find("UF") != std::string::npos ||
        s == "SMTFD";
}

bool smt_logics::logic_has_horn(symbol const& s) {
    return s == "HORN";
}

bool smt_logics::logic_has_pb(symbol const& s) {
    return s == "QF_FD" || logic_is_all(s) || logic_has_horn(s);
}

bool smt_logics::logic_has_datatype(symbol const& s) {
    return 
        s.str().find("DT") != std::string::npos ||
        s == "QF_FD" ||
        logic_is_all(s) ||
        logic_has_horn(s);
}

