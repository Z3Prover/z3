/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_prover.h

Abstract:

    Stand-alone SPC prover (it is mainly for debugging purposes).

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#ifndef _SPC_PROVER_H_
#define _SPC_PROVER_H_

#include"spc_context.h"
#include"front_end_params.h"
#include"kbo.h"
#include"lpo.h"
#include"basic_simplifier_plugin.h"
#include"arith_simplifier_plugin.h"
#include"preprocessor.h"
#include"defined_names.h"
#include"lbool.h"

namespace spc {
    class prover {
        ast_manager &           m_manager;
        front_end_params &      m_params;
        simplifier              m_simplifier;
        defined_names           m_defined_names;
        preprocessor            m_preprocessor;
        order *                 m_order;
        clause_selection *      m_cls_sel;
        literal_selection *     m_lit_sel;
        context *               m_context;
        expr_ref_vector         m_exprs;
        proof_ref_vector        m_expr_proofs;
        bool                    m_has_theories;

        void init();

    public:
        prover(ast_manager & m, front_end_params & params);
        ~prover();
        void assert_expr(expr * e);
        lbool check();
        void display_statistics(std::ostream & out) const { if (m_context) m_context->display_statistics(out); }
    };
};

#endif /* _SPC_PROVER_H_ */

