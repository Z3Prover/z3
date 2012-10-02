/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_instgen.h

Abstract:

    InstGen (iProver) style theory solver.
    It provides an instantiation based engine
    based on InstGen methods together with
    unit propagation.


Author:

    Krystof Hoder (t-khoder) 
    Nikolaj Bjorner (nbjorner) 2011-10-6

Revision History:

--*/
#ifndef _THEORY_INST_GEN_H_
#define _THEORY_INST_GEN_H_

#include "smt_theory.h"
#include "front_end_params.h"

namespace smt {

    class theory_instgen : public theory {
    public:
        theory_instgen(family_id fid) : theory(fid) {}
        virtual ~theory_instgen() {}
        virtual void internalize_quantifier(quantifier* q) = 0;
        virtual char const * get_name() const { return "instgen"; }
    };

    theory_instgen* mk_theory_instgen(ast_manager& m, front_end_params& p);

};

#endif /* _THEORY_INST_GEN_H_ */

