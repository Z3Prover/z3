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

double ackr_helper::calculate_lemma_bound(ackr_helper::fun2terms_map& occurrences) {
    fun2terms_map::iterator it = occurrences.begin();
    const fun2terms_map::iterator end = occurrences.end();
    double total = 0;
    for (; it != end; ++it) {
        const unsigned fsz = it->m_value->size();
        const double n2 = n_choose_2_chk(fsz);
        total += n2;
    }
    return total;
}
