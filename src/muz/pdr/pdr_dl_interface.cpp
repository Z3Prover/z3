/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_dl.cpp

Abstract:

    SMT2 interface for the datalog PDR

Author:

    Krystof Hoder (t-khoder) 2011-9-22.

Revision History:

--*/

#include "muz/base/dl_context.h"
#include "muz/transforms/dl_mk_coi_filter.h"
#include "muz/base/dl_rule.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/pdr/pdr_context.h"
#include "muz/pdr/pdr_dl_interface.h"
#include "muz/base/dl_rule_set.h"
#include "muz/transforms/dl_mk_slice.h"
#include "muz/transforms/dl_mk_unfold.h"
#include "muz/transforms/dl_mk_coalesce.h"
#include "muz/transforms/dl_transforms.h"
#include "ast/scoped_proof.h"
#include "model/model_smt2_pp.h"

using namespace pdr;

dl_interface::dl_interface(datalog::context& ctx) : 
    engine_base(ctx.get_manager(), "pdr"),
    m_ctx(ctx), 
    m_pdr_rules(ctx), 
    m_old_rules(ctx),
    m_context(nullptr),
    m_refs(ctx.get_manager()) {
    m_context = alloc(pdr::context, ctx.get_fparams(), ctx.get_params(), ctx.get_manager());
}


dl_interface::~dl_interface() {
    dealloc(m_context);
}


//
// Check if the new rules are weaker so that we can 
// re-use existing context.
// 
void dl_interface::check_reset() {
    datalog::rule_set const& new_rules = m_ctx.get_rules();
    datalog::rule_ref_vector const& old_rules = m_old_rules.get_rules();  
    bool is_subsumed = !old_rules.empty();
    for (unsigned i = 0; is_subsumed && i < new_rules.get_num_rules(); ++i) {
        is_subsumed = false;
        for (unsigned j = 0; !is_subsumed && j < old_rules.size(); ++j) {
            if (m_ctx.check_subsumes(*old_rules[j], *new_rules.get_rule(i))) {
                is_subsumed = true;
            }
        }
        if (!is_subsumed) {
            TRACE("pdr", new_rules.get_rule(i)->display(m_ctx, tout << "Fresh rule "););
            m_context->reset();
        }
    }
    m_old_rules.replace_rules(new_rules);
}


lbool dl_interface::query(expr * query) {
    //we restore the initial state in the datalog context
    m_ctx.ensure_opened();
    m_refs.reset();
    m_pred2slice.reset();
    ast_manager& m =                      m_ctx.get_manager();
    datalog::rule_manager& rm = m_ctx.get_rule_manager();
    datalog::rule_set& rules0 = m_ctx.get_rules();

    datalog::rule_set        old_rules(rules0);
    func_decl_ref            query_pred(m);
    rm.mk_query(query, rules0);
    expr_ref bg_assertion = m_ctx.get_background_assertion();

    check_reset();

    TRACE("pdr",
          if (!m.is_true(bg_assertion)) {
              tout << "axioms:\n";
              tout << mk_pp(bg_assertion, m) << "\n";
          }
          tout << "query: " << mk_pp(query, m) << "\n";
          tout << "rules:\n";
          m_ctx.display_rules(tout);
          );


    apply_default_transformation(m_ctx);

    if (m_ctx.get_params().xform_slice()) {
        datalog::rule_transformer transformer(m_ctx);
        datalog::mk_slice* slice = alloc(datalog::mk_slice, m_ctx);
        transformer.register_plugin(slice);
        m_ctx.transform_rules(transformer);
        
        // track sliced predicates.
        obj_map<func_decl, func_decl*> const& preds = slice->get_predicates();
        obj_map<func_decl, func_decl*>::iterator it  = preds.begin();
        obj_map<func_decl, func_decl*>::iterator end = preds.end();
        for (; it != end; ++it) {
            m_pred2slice.insert(it->m_key, it->m_value);
            m_refs.push_back(it->m_key);
            m_refs.push_back(it->m_value);
        }
    }

    if (m_ctx.get_params().xform_unfold_rules() > 0) {
        unsigned num_unfolds = m_ctx.get_params().xform_unfold_rules();
        datalog::rule_transformer transf1(m_ctx), transf2(m_ctx);        
        transf1.register_plugin(alloc(datalog::mk_coalesce, m_ctx));
        transf2.register_plugin(alloc(datalog::mk_unfold, m_ctx));
        if (m_ctx.get_params().xform_coalesce_rules()) {
            m_ctx.transform_rules(transf1);
        }
        while (num_unfolds > 0) {
            m_ctx.transform_rules(transf2);
            --num_unfolds;
        }
    }

    const datalog::rule_set& rules = m_ctx.get_rules();
    if (rules.get_output_predicates().empty()) {
        m_context->set_unsat();
        return l_false;
    }

    query_pred = rules.get_output_predicate();

    TRACE("pdr",
          tout << "rules:\n";
          m_ctx.display_rules(tout);
          m_ctx.display_smt2(0, 0, tout);
          );

    IF_VERBOSE(2, m_ctx.display_rules(verbose_stream()););
    m_pdr_rules.replace_rules(rules);
    m_pdr_rules.close();
    m_ctx.record_transformed_rules();
    m_ctx.reopen();
    m_ctx.replace_rules(old_rules);
    

    scoped_restore_proof _sc(m); // update_rules may overwrite the proof mode.

    m_context->set_proof_converter(m_ctx.get_proof_converter());
    m_context->set_model_converter(m_ctx.get_model_converter());
    m_context->set_query(query_pred);
    m_context->set_axioms(bg_assertion);    
    m_context->update_rules(m_pdr_rules);
    
    if (m_pdr_rules.get_rules().empty()) {
        m_context->set_unsat();
        IF_VERBOSE(1, model_smt2_pp(verbose_stream(), m, *m_context->get_model(),0););
        return l_false;
    }
        
    return m_context->solve();

}

expr_ref dl_interface::get_cover_delta(int level, func_decl* pred_orig) {
    func_decl* pred = pred_orig;
    m_pred2slice.find(pred_orig, pred);
    SASSERT(pred);
    return m_context->get_cover_delta(level, pred_orig, pred);
}

void dl_interface::add_cover(int level, func_decl* pred, expr* property) {
    if (m_ctx.get_params().xform_slice()) {
        throw default_exception("Covers are incompatible with slicing. Disable slicing before using covers");
    }
    m_context->add_cover(level, pred, property);
}

unsigned dl_interface::get_num_levels(func_decl* pred) {
    m_pred2slice.find(pred, pred);
    SASSERT(pred);
    return m_context->get_num_levels(pred);
}

void dl_interface::collect_statistics(statistics& st) const {
    m_context->collect_statistics(st);
}

void dl_interface::reset_statistics() {
    m_context->reset_statistics();
}

void dl_interface::display_certificate(std::ostream& out) const {
    m_context->display_certificate(out);
}

expr_ref dl_interface::get_answer() {
    return m_context->get_answer();
}



void dl_interface::updt_params() {
    dealloc(m_context);
    m_context = alloc(pdr::context, m_ctx.get_fparams(), m_ctx.get_params(), m_ctx.get_manager());
}

model_ref dl_interface::get_model() {
    return m_context->get_model();
}

proof_ref dl_interface::get_proof() {
    return m_context->get_proof();
}
