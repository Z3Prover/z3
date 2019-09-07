/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackr_helper.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "ackermannization/ackr_helper.h"

double ackr_helper::calculate_lemma_bound(fun2terms_map const& occs1, sel2terms_map const& occs2) {
    double total = 0;
    for (auto const& kv : occs1) {
        total += n_choose_2_chk(kv.m_value->var_args.size());
        total += kv.m_value->const_args.size() * kv.m_value->var_args.size();
    }
    for (auto const& kv : occs2) {
        total += n_choose_2_chk(kv.m_value->var_args.size());
        total += kv.m_value->const_args.size() * kv.m_value->var_args.size();
    }
    return total;
}
