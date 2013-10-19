
#ifndef __QE_ARITH_H_
#define __QE_ARITH_H_

#include "model.h"

namespace qe {
    /**
       Loos-Weispfenning model-based projection for a basic conjunction.
       Lits is a vector of literals.
       return vector of variables that could not be projected.
     */
    expr_ref arith_project(model& model, app_ref_vector& vars, expr_ref_vector const& lits);

    expr_ref arith_project(model& model, app_ref_vector& vars, expr* fml);
};

#endif
