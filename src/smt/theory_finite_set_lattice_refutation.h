#pragma once

#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"

namespace smt {
    class context;
    class theory_finite_set;

    class theory_finite_set_lattice_refutation {
        ast_manager          &m;
        context             &ctx;
        theory_finite_set   &th;
        finite_set_util u;
        expr_ref_vector bs;
        expr_ref m_assumption;

        svector<std::pair<expr*, expr*>> relations;
        public:
            theory_finite_set_lattice_refutation(theory_finite_set &th);
            void add_equality(theory_var v1, theory_var v2);
            void add_disequality(theory_var v1, theory_var v2);
    };
}
