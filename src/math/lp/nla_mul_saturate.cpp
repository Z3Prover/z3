/*++
  Copyright (c) 2025 Microsoft Corporation

  given a monic m = x * y * z ... with evaluation val(m) != val(x) * val(y) * val(z) ...

  saturate constraints with respect to m
  in other words, if a constraint contains x*y + p >= 0, 
  then include the constraint z >= 0 => x*y*z + z*p >= 0
  assuming current value of z is non-negative.
  Check if the system with new constraints is LP feasible.
  If it is not, then produce a lemma that explains the infeasibility.

  --*/

#include "math/lp/nla_mul_saturate.h"
#include "math/lp/nla_core.h"

namespace nla {

    mul_saturate::mul_saturate(core* core) : common(core) {}

}
