/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)

  --*/
#include "math/lp/nla_throttle.h"
#include "util/trace.h"

namespace nla {

bool nla_throttle::insert_new_impl(const signature& sig) {
    if (m_seen.contains(sig)) {
        TRACE(nla_solver, tout << "throttled lemma generation\n";);
        return true;  // Already seen, throttle
    }
    
    m_seen.insert(sig);
    m_trail.push(insert_map(m_seen, sig));
    return false;     // New, don't throttle
}

} // namespace nla
