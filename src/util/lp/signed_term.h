/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
     Nikolaj Bjorner(nbjorner), Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "util/lp/lar_term.h"
namespace lp {
struct signed_term {
    const lar_term*  m_term;
    bool             m_is_plus;
    mpq              m_rs;
    constraint_index m_ci;
};

}
