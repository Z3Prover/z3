/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_smt_context_manager.cpp

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.

Revision History:

--*/

#include "pdr_smt_context_manager.h"
#include "has_free_vars.h"
#include "ast_pp.h"
#include <sstream>
#include "front_end_params.h"

namespace pdr {

    smt_context::smt_context(smt_context_manager& p, ast_manager& m, app* pred):
        m_pred(pred, m),
        m_parent(p),
        m_in_delay_scope(false),
        m_pushed(false)
    {}

    bool smt_context::is_aux_predicate(func_decl* p) {
        return m_parent.is_aux_predicate(p);
    }
    
    smt_context::scoped::scoped(smt_context& ctx): m_ctx(ctx) {
        SASSERT(!m_ctx.m_in_delay_scope);
        SASSERT(!m_ctx.m_pushed);
        m_ctx.m_in_delay_scope = true;
    }

    smt_context::scoped::~scoped() {
        SASSERT(m_ctx.m_in_delay_scope);
        if (m_ctx.m_pushed) {
            m_ctx.pop(); 
            m_ctx.m_pushed = false;
        }
        m_ctx.m_in_delay_scope = false;        
    }


    _smt_context::_smt_context(smt::kernel & ctx, smt_context_manager& p, app* pred):
        smt_context(p, ctx.m(), pred),
        m_context(ctx)
    {}

    void _smt_context::assert_expr(expr* e) {
        ast_manager& m = m_context.m();
        if (m.is_true(e)) {
            return;
        }
        CTRACE("pdr", has_free_vars(e), tout << mk_pp(e, m) << "\n";);
        SASSERT(!has_free_vars(e));
        if (m_in_delay_scope && !m_pushed) {
            m_context.push();
            m_pushed = true;
        }
        expr_ref fml(m);
        fml = m_pushed?e:m.mk_implies(m_pred, e);
        m_context.assert_expr(fml);
    }

    lbool _smt_context::check(expr_ref_vector& assumptions) {
        ast_manager& m = m_pred.get_manager();
        if (!m.is_true(m_pred)) {
            assumptions.push_back(m_pred);
        }
        lbool result = m_context.check(assumptions.size(), assumptions.c_ptr());
        if (!m.is_true(m_pred)) {
            assumptions.pop_back();
        }
        return result;
    }

    void _smt_context::get_model(model_ref& model) {
        m_context.get_model(model);
    }

    proof* _smt_context::get_proof() {
        return m_context.get_proof();
    }

    smt_context_manager::smt_context_manager(front_end_params& fp, params_ref const& p, ast_manager& m):
        m_fparams(fp), 
        m(m), 
        m_max_num_contexts(p.get_uint(":max-num-contexts", 500)), 
        m_num_contexts(0), 
        m_predicate_list(m) {
    }
    
    
    smt_context_manager::~smt_context_manager() {
        TRACE("pdr",tout << "\n";);
        std::for_each(m_contexts.begin(), m_contexts.end(), delete_proc<smt::kernel>());
    }

    smt_context* smt_context_manager::mk_fresh() {        
        ++m_num_contexts;
        app_ref pred(m);
        smt::kernel * ctx = 0;
        if (m_max_num_contexts == 0) {
            m_contexts.push_back(alloc(smt::kernel, m, m_fparams));
            pred = m.mk_true();
            ctx = m_contexts[m_num_contexts-1];
        }
        else {
            if (m_contexts.size() < m_max_num_contexts) {
                m_contexts.push_back(alloc(smt::kernel, m, m_fparams));
            }
            std::stringstream name;
            name << "#context" << m_num_contexts;
            pred = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());    
            m_predicate_list.push_back(pred);
            m_predicate_set.insert(pred->get_decl());
            ctx = m_contexts[(m_num_contexts-1)%m_max_num_contexts];
        }        
        return  alloc(_smt_context, *ctx, *this, pred);   
    }

    void smt_context_manager::collect_statistics(statistics& st) const {
        for (unsigned i = 0; i < m_contexts.size(); ++i) {
            m_contexts[i]->collect_statistics(st);
        }
    }


};

