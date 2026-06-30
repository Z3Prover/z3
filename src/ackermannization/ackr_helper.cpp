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
    for (auto const &[k, v] : occs1) {
        total += n_choose_2_chk(v->var_args.size());
        total += v->const_args.size() * v->var_args.size();
    }
    for (auto const &[k, v] : occs2) {
        total += n_choose_2_chk(v->var_args.size());
        total += v->const_args.size() * v->var_args.size();
    }
    return total;
}
