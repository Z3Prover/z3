#ifndef MSS_SOLVER_H_
#define MSS_SOLVER_H_

#include "opt/maxsmt.h"

namespace opt {

    maxsmt_solver_base* mk_mss_solver(maxsat_context& c, unsigned id, weights_t& ws, expr_ref_vector const& soft);

}

#endif
