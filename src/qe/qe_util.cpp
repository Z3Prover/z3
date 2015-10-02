
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "qe_util.h"
#include "bool_rewriter.h"

namespace qe {

    expr_ref mk_and(expr_ref_vector const& fmls) {
        ast_manager& m = fmls.get_manager();
        expr_ref result(m);
        bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(), result);
        return result;
    }

    expr_ref mk_or(expr_ref_vector const& fmls) {
        ast_manager& m = fmls.get_manager();
        expr_ref result(m);
        bool_rewriter(m).mk_or(fmls.size(), fmls.c_ptr(), result);
        return result;
    }

}
