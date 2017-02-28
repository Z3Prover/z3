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

#include "dt2bv_tactic.h"
#include "tactical.h"
#include "filter_model_converter.h"
#include "datatype_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "rewriter_def.h"
#include "filter_model_converter.h"
#include "extension_model_converter.h"
#include "var_subst.h"
#include "ast_util.h"
#include "enum2bv_rewriter.h"


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
                return;
            }
            if (m.is_distinct(a)) {
                return;
            }
            if (m_t.m_dt.is_recognizer(a->get_decl()) &&
                m_t.is_fd(a->get_arg(0))) {
                m_t.m_fd_sorts.insert(get_sort(a->get_arg(0)));
                return;
            }

            if (m_t.is_fd(a) && a->get_num_args() > 0) {
                m_t.m_non_fd_sorts.insert(get_sort(a));
            }
            else if (m_t.is_fd(a)) {
                m_t.m_fd_sorts.insert(get_sort(a));
            }
            else {
                unsigned sz = a->get_num_args();
                for (unsigned i = 0; i < sz; ++i) {
                    if (m_t.is_fd(a->get_arg(i))) {
                        m_t.m_non_fd_sorts.insert(get_sort(a->get_arg(i)));
                    }
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
        virtual ~sort_pred() {}
        virtual bool operator()(sort* s) {
            return m_t.m_fd_sorts.contains(s);
        }
    };

    sort_pred m_is_fd;
public:

    dt2bv_tactic(ast_manager& m, params_ref const& p): 
        m(m), m_params(p), m_dt(m), m_bv(m), m_is_fd(*this) {}
    
    virtual tactic * translate(ast_manager & m) {
        return alloc(dt2bv_tactic, m, m_params);
    }

    virtual void updt_params(params_ref const & p) {
    }

    virtual void collect_param_descrs(param_descrs & r) {
    }

    virtual void operator()(goal_ref const & g,
                            goal_ref_buffer & result,
                            model_converter_ref & mc,
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0;
        bool produce_proofs = g->proofs_enabled();
        tactic_report report("dt2bv", *g);
        unsigned   size = g->size();
        expr_fast_mark1 visited;
        check_fd proc(*this);
        for (unsigned i = 0; i < size; ++i) {
            quick_for_each_expr(proc, visited, g->form(i));
        }
        obj_hashtable<sort>::iterator it = m_non_fd_sorts.begin(), end = m_non_fd_sorts.end();
        for (; it != end; ++it) {
            m_fd_sorts.remove(*it);
        }
        if (!m_fd_sorts.empty()) {
            ref<extension_model_converter> ext = alloc(extension_model_converter, m);
            ref<filter_model_converter> filter = alloc(filter_model_converter, m);
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
            for (unsigned i = 0; i < bounds.size(); ++i) {
                g->assert_expr(bounds[i].get());
            }
            {
                obj_map<func_decl, func_decl*>::iterator it = rw.enum2bv().begin(), end = rw.enum2bv().end();
                for (; it != end; ++it) {
                    filter->insert(it->m_value);
                }
            }
            {
                obj_map<func_decl, expr*>::iterator it = rw.enum2def().begin(), end = rw.enum2def().end();
                for (; it != end; ++it) {
                    ext->insert(it->m_key, it->m_value);
                }
            }
            
            mc = concat(filter.get(), ext.get());
            report_tactic_progress(":fd-num-translated", rw.num_translated());
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("dt2bv", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
        m_fd_sorts.reset();
        m_non_fd_sorts.reset();
    }

};

tactic * mk_dt2bv_tactic(ast_manager & m, params_ref const & p) {
    return alloc(dt2bv_tactic, m, p);
}
