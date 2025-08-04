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
    auto str = s.str();
    return
        str.find("LRA") != std::string::npos ||
        str.find("LRA") != std::string::npos ||
        str.find("NRA") != std::string::npos ||
        str.find("RDL") != std::string::npos;
}

bool smt_logics::logic_has_arith(symbol const & s) {
    auto str = s.str();
    return
        str.find("LRA") != std::string::npos ||
        str.find("LIRA") != std::string::npos ||
        str.find("LIA") != std::string::npos ||
        str.find("LRA") != std::string::npos ||
        str.find("NRA") != std::string::npos ||
        str.find("NIRA") != std::string::npos ||
        str.find("NIA") != std::string::npos ||
        str.find("IDL") != std::string::npos ||
        str.find("RDL") != std::string::npos ||
        str == "QF_BVRE" ||
        str == "QF_FP" ||
        str == "FP" ||
        str == "QF_FPBV" ||
        str == "QF_BVFP" ||
        str == "QF_S" ||
        logic_is_all(s) ||
        str == "QF_FD" ||
        str == "HORN";
}

bool smt_logics::logic_has_bv(symbol const & s) {
    auto str = s.str();
    return
        str.find("BV") != std::string::npos ||
        str == "FP" ||
        logic_is_all(s) ||
        str == "QF_FD" ||
        str == "SMTFD" ||
        str == "HORN";
}

bool smt_logics::logic_has_array(symbol const & s) {
    auto str = s.str();
    return
        str.starts_with("QF_A") ||
        str.starts_with("A") ||
        logic_is_all(s) ||
        str == "SMTFD" ||
        str == "HORN";
}

bool smt_logics::logic_has_seq(symbol const & s) {
    return s == "QF_BVRE" || logic_has_str(s);
}

bool smt_logics::logic_has_str(symbol const & s) {
    auto str = s.str();
    return str == "QF_S" ||
           str == "QF_SLIA" ||
           str == "QF_SNIA" ||
           logic_is_all(s);
}

bool smt_logics::logic_has_fpa(symbol const & s) {
    auto str = s.str();
    return str == "FP" ||
           str == "QF_FP" ||
           str == "QF_FPBV" ||
           str == "QF_BVFP" ||
           str == "QF_FPLRA"  ||
           logic_is_all(s);
}

bool smt_logics::logic_has_uf(symbol const & s) {
    auto str = s.str();
    return 
        str.find("UF") != std::string::npos ||
        str == "SMTFD";
}

bool smt_logics::logic_has_horn(symbol const& s) {
    return s == "HORN";
}

bool smt_logics::logic_has_pb(symbol const& s) {
    return s == "QF_FD" || logic_is_all(s) || logic_has_horn(s);
}

bool smt_logics::logic_has_datatype(symbol const& s) {
    auto str = s.str();
    return 
        str.find("DT") != std::string::npos ||
        str == "QF_FD" ||
        logic_is_all(s) ||
        logic_has_horn(s);
}

