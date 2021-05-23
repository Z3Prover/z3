/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    smt_logics.h

Abstract:

    Module for recognizing SMT logics.

Author:

    Nikolaj Bjorner (nbjorner) 2016-11-4

Revision History:

--*/
#pragma once

class smt_logics {
public:
    static bool supported_logic(symbol const & s);
    static bool logic_has_reals_only(symbol const& l);       
    static bool logic_is_all(symbol const& s) { return s == "ALL"; }
    static bool logic_has_uf(symbol const& s);
    static bool logic_has_arith(symbol const & s);
    static bool logic_has_bv(symbol const & s);
    static bool logic_has_array(symbol const & s);
    static bool logic_has_seq(symbol const & s);
    static bool logic_has_str(symbol const & s);
    static bool logic_has_fpa(symbol const & s);
    static bool logic_has_horn(symbol const& s);
    static bool logic_has_pb(symbol const& s);
    static bool logic_has_fd(symbol const& s) { return s == "QF_FD"; }
    static bool logic_has_datatype(symbol const& s);
};
