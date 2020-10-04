/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_fixer.cpp

Abstract:

    Model-based quantifier instantiation model-finder plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-10-02

Notes:
   
    Derives from smt/smt_model_finder.cpp

--*/

#include "util/backtrackable_set.h"
#include "util/obj_pair_hashtable.h"
#include "ast/macros/cond_macro.h"
#include "ast/macros/macro_util.h"
#include "ast/macros/quantifier_macro_info.h"
#include "ast/func_decl_dependencies.h"
#include "ast/for_each_expr.h"
#include "model/model_macro_solver.h"
#include "sat/smt/q_model_fixer.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"


namespace q {

    typedef obj_hashtable<func_decl> func_decl_set;

    model_fixer::model_fixer(euf::solver& ctx, q::solver& qs) :
        ctx(ctx), qs(qs), m(ctx.get_manager()), m_dependencies(m) {}

    void model_fixer::operator()(model& mdl) {
        ptr_vector<quantifier> univ;
        for (sat::literal lit : qs.universal()) {
            quantifier* q = to_quantifier(ctx.bool_var2expr(lit.var()));
            if (ctx.is_relevant(q))
                univ.push_back(q);
        }
        if (univ.empty())
            return;

        // cleanup_quantifier_infos(qs);
        m_dependencies.reset();

        ptr_vector<quantifier> residue;               
        
        simple_macro_solver sms(m, *this);
        sms(mdl, univ, residue);

        hint_macro_solver hms(m, *this);
        hms(mdl, univ, residue);

        non_auf_macro_solver nas(m, *this, m_dependencies);
        nas.set_mbqi_force_template(ctx.get_config().m_mbqi_force_template);
        nas(mdl, univ, residue);
        univ.append(residue);

        // process-auf
    }

    quantifier_macro_info* model_fixer::operator()(quantifier* q) {
        quantifier_macro_info* info = nullptr;
        if (!m_q2info.find(q, info)) {
            info = alloc(quantifier_macro_info, m, qs.flatten(q));
            m_q2info.insert(q, info);
            ctx.push(new_obj_trail<euf::solver, quantifier_macro_info>(info));
            ctx.push(insert_obj_map<euf::solver, quantifier, quantifier_macro_info*>(m_q2info, q));
        }
        return info;
    }

#if 0

    void process_auf() {
        // depends on egraph

        // else-projections:
        //  - adds constraints
        //  - 
        // freeze universe on uninterpreted sorts
        // create projection functions
        // complete partial functions
    }

#endif
}
