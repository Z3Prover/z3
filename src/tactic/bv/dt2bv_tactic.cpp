/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    dt2bv_tactic.cpp

Abstract:

    Tactic that eliminates finite domain data-types.

Author:

    nbjorner 2016-07-22

Revision History:

    Possible extension is to handle tuple types over finite domains.

--*/

#include "tactic/bv/dt2bv_tactic.h"
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_util.h"
#include "ast/rewriter/enum2bv_rewriter.h"
#include "ast/ast_pp.h"


class dt2bv_tactic : public tactic {

    ast_manager&  m;
    params_ref    m_params;
    datatype_util m_dt;
    bv_util       m_bv;
    obj_hashtable<sort> m_fd_sorts;
    obj_hashtable<sort> m_non_fd_sorts;
    

    bool is_fd(expr* a) { return is_fd(get_sort(a)); }
    bool is_fd(sort* a) { return m_dt.is_enum_sort(a); }

    struct check_fd {        
        dt2bv_tactic& m_t;
        ast_manager&  m;

        check_fd(dt2bv_tactic& t): m_t(t), m(t.m) {}

        void operator()(app* a) {
            if (m.is_eq(a)) {
                // no-op
            }
            else if (m.is_distinct(a)) {
                // no-op
            }
            else if (m_t.m_dt.is_recognizer(a->get_decl()) &&
                m_t.is_fd(a->get_arg(0))) {
                m_t.m_fd_sorts.insert(get_sort(a->get_arg(0)));
            }
            else if (m_t.is_fd(a) && a->get_num_args() > 0) {
                m_t.m_non_fd_sorts.insert(get_sort(a));
                args_cannot_be_fd(a);
            }
            else if (m_t.is_fd(a)) {
                m_t.m_fd_sorts.insert(get_sort(a));
            }
            else {
                args_cannot_be_fd(a);
            }
        }

        void args_cannot_be_fd(app* a) {
            for (expr* arg : *a) {
                if (m_t.is_fd(arg)) {
                    m_t.m_non_fd_sorts.insert(get_sort(arg));
                }                    
            }
        }

        void operator()(var * v) {
            if (m_t.is_fd(v)) {
                m_t.m_fd_sorts.insert(get_sort(v));
            }
        }

        void operator()(quantifier* q) {}
    };

    struct sort_pred : public i_sort_pred {
        dt2bv_tactic& m_t;
        sort_pred(dt2bv_tactic& t): m_t(t) {}
        ~sort_pred() override {}
        bool operator()(sort* s) override {
            return m_t.m_fd_sorts.contains(s);
        }
    };

    sort_pred m_is_fd;
public:

    dt2bv_tactic(ast_manager& m, params_ref const& p): 
        m(m), m_params(p), m_dt(m), m_bv(m), m_is_fd(*this) {}
    
    tactic * translate(ast_manager & m) override {
        return alloc(dt2bv_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
    }

    void collect_param_descrs(param_descrs & r) override {
    }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        bool produce_proofs = g->proofs_enabled();
        tactic_report report("dt2bv", *g);
        unsigned   size = g->size();
        expr_fast_mark1 visited;
        check_fd proc(*this);
        for (unsigned i = 0; i < size; ++i) {
            quick_for_each_expr(proc, visited, g->form(i));
        }
        for (sort* s : m_non_fd_sorts) 
            m_fd_sorts.remove(s);
        if (!m_fd_sorts.empty()) {
            ref<generic_model_converter> filter = alloc(generic_model_converter, m, "dt2bv");
            enum2bv_rewriter rw(m, m_params);
            rw.set_is_fd(&m_is_fd);            
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            for (unsigned idx = 0; idx < size; idx++) {
                rw(g->form(idx), new_curr, new_pr);
                if (produce_proofs) {
                    proof * pr = g->pr(idx);
                    new_pr = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }
            expr_ref_vector bounds(m);
            rw.flush_side_constraints(bounds);
            for (expr* b : bounds) 
                g->assert_expr(b);
            for (auto const& kv : rw.enum2bv()) 
                filter->hide(kv.m_value);
            for (auto const& kv : rw.enum2def()) 
                filter->add(kv.m_key, kv.m_value);
            
            g->add(filter.get());
            report_tactic_progress(":fd-num-translated", rw.num_translated());
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("dt2bv", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    void cleanup() override {
        m_fd_sorts.reset();
        m_non_fd_sorts.reset();
    }

};

tactic * mk_dt2bv_tactic(ast_manager & m, params_ref const & p) {
    return alloc(dt2bv_tactic, m, p);
}
