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


class dt2bv_tactic : public tactic {

    ast_manager&  m;
    params_ref    m_params;
    datatype_util m_dt;
    bv_util       m_bv;
    obj_hashtable<sort> m_fd_sorts;
    obj_hashtable<sort> m_non_fd_sorts;
    expr_ref_vector     m_bounds;
    ref<extension_model_converter> m_ext;
    ref<filter_model_converter>    m_filter;
    unsigned                       m_num_translated;

    struct rw_cfg : public default_rewriter_cfg {
        dt2bv_tactic& m_t;
        ast_manager& m;        
        params_ref   m_params;
        obj_map<expr, expr*> m_cache;
        expr_ref_vector m_trail;

        rw_cfg(dt2bv_tactic& t, ast_manager & m, params_ref const & p) :
            m_t(t),
            m(m),
            m_params(p),
            m_trail(m)
        {}

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            expr_ref a0(m), a1(m);
            expr_ref_vector _args(m);
            if (m.is_eq(f) && reduce_arg(args[0], a0) && reduce_arg(args[1], a1)) {
                result = m.mk_eq(a0, a1);
                return BR_DONE;
            }
            else if (m.is_distinct(f) && reduce_args(num, args, _args)) {
                result = m.mk_distinct(_args.size(), _args.c_ptr());
                return BR_DONE;
            }
            else if (m_t.m_dt.is_recognizer(f) && reduce_arg(args[0], a0)) {
                unsigned idx = m_t.m_dt.get_recognizer_constructor_idx(f);
                a1 = m_t.m_bv.mk_numeral(rational(idx), get_sort(a0));
                result = m.mk_eq(a0, a1);
                return BR_DONE;
            }
            else {
                return BR_FAILED;
            }
        }

        bool reduce_args(unsigned sz, expr*const* as, expr_ref_vector& result) {
            expr_ref tmp(m);
            for (unsigned i = 0; i < sz; ++i) {
                if (!reduce_arg(as[i], tmp)) return false;
                result.push_back(tmp);
            }
            return true;
        }

        bool reduce_arg(expr* a, expr_ref& result) {
            expr* b;
            if (m_cache.find(a, b)) {
                result = b;
                return true;
            }

            sort* s = get_sort(a);
            if (!m_t.m_fd_sorts.contains(s)) {
                return false;
            }
            unsigned bv_size = get_bv_size(s);

            if (is_var(a)) {
                result = m.mk_var(to_var(a)->get_idx(), m_t.m_bv.mk_sort(bv_size));
                return true;
            }
            SASSERT(is_app(a));
            func_decl* f = to_app(a)->get_decl();
            if (m_t.m_dt.is_constructor(f)) {
                unsigned idx = m_t.m_dt.get_constructor_idx(f);
                result = m_t.m_bv.mk_numeral(idx, bv_size);
            }
            else if (is_uninterp_const(a)) {
                // create a fresh variable, add bounds constraints for it.
                unsigned nc = m_t.m_dt.get_datatype_num_constructors(s);
                result = m.mk_fresh_const(f->get_name().str().c_str(), m_t.m_bv.mk_sort(bv_size));
                if (!is_power_of_two(nc)) {
                    m_t.m_bounds.push_back(m_t.m_bv.mk_ule(result, m_t.m_bv.mk_numeral(nc, bv_size)));
                }                
                expr_ref f_def(m);
                ptr_vector<func_decl> const& cs = *m_t.m_dt.get_datatype_constructors(s);
                f_def = m.mk_const(cs[nc-1]);
                for (unsigned i = nc - 1; i > 0; ) {
                    --i;
                    f_def = m.mk_ite(m.mk_eq(result, m_t.m_bv.mk_numeral(i,bv_size)), m.mk_const(cs[i]), f_def);
                }
                // update model converters.
                m_t.m_ext->insert(f, f_def);
                m_t.m_filter->insert(to_app(result)->get_decl());
            }
            else {
                return false;
            }
            m_cache.insert(a, result);
            ++m_t.m_num_translated;
            return true;
        }

        ptr_buffer<sort> m_sorts;

        bool reduce_quantifier(
            quantifier * q,
            expr * old_body,
            expr * const * new_patterns,
            expr * const * new_no_patterns,
            expr_ref & result,
            proof_ref & result_pr) {
            m_sorts.reset();
            expr_ref_vector bounds(m);
            bool found = false;
            for (unsigned i = 0; i < q->get_num_decls(); ++i) {
                sort* s = q->get_decl_sort(i);
                if (m_t.m_fd_sorts.contains(s)) {
                    unsigned bv_size = get_bv_size(s);
                    m_sorts.push_back(m_t.m_bv.mk_sort(bv_size));
                    unsigned nc = m_t.m_dt.get_datatype_num_constructors(s);
                    if (!is_power_of_two(nc)) {
                        bounds.push_back(m_t.m_bv.mk_ule(m.mk_var(q->get_num_decls()-i-1, m_sorts[i]), m_t.m_bv.mk_numeral(nc, bv_size)));
                    }                
                    found = true;
                }
                else {
                    m_sorts.push_back(s);
                }
            }
            if (!found) {
                return false;
            }
            expr_ref new_body_ref(old_body, m), tmp(m);
            if (!bounds.empty()) {
                if (q->is_forall()) {
                    new_body_ref = m.mk_implies(mk_and(bounds), new_body_ref);
                }
                else {
                    bounds.push_back(new_body_ref);
                    new_body_ref = mk_and(bounds);
                }
            }
            result = m.mk_quantifier(q->is_forall(), q->get_num_decls(), m_sorts.c_ptr(), q->get_decl_names(), new_body_ref, 
                                     q->get_weight(), q->get_qid(), q->get_skid(), 
                                     q->get_num_patterns(), new_patterns,
                                     q->get_num_no_patterns(), new_no_patterns);
            result_pr = 0;
            return true;
        }

        unsigned get_bv_size(sort* s) {
            unsigned nc = m_t.m_dt.get_datatype_num_constructors(s);
            unsigned bv_size = 1;
            while ((unsigned)(1 << bv_size) < nc) {
                ++bv_size;
            }
            return bv_size;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(dt2bv_tactic& t, ast_manager & m, params_ref const & p) :
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(t, m, p) {
        }
    };



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

            if (m_t.is_fd(a)) {
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

public:

    dt2bv_tactic(ast_manager& m, params_ref const& p): 
        m(m), m_params(p), m_dt(m), m_bv(m), m_bounds(m) {}
    
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
            m_bounds.reset();
            m_num_translated = 0;
            m_ext = alloc(extension_model_converter, m);
            m_filter = alloc(filter_model_converter, m);
            scoped_ptr<rw> r = alloc(rw, *this, m, m_params);
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            for (unsigned idx = 0; idx < size; idx++) {
                (*r)(g->form(idx), new_curr, new_pr);
                if (produce_proofs) {
                    proof * pr = g->pr(idx);
                    new_pr = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }
            for (unsigned i = 0; i < m_bounds.size(); ++i) {
                g->assert_expr(m_bounds[i].get());
            }
            mc = concat(m_filter.get(), m_ext.get());
            report_tactic_progress(":fd-num-translated", m_num_translated);
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("dt2bv", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
        m_fd_sorts.reset();
        m_non_fd_sorts.reset();
        m_bounds.reset();
    }

};

tactic * mk_dt2bv_tactic(ast_manager & m, params_ref const & p) {
    return alloc(dt2bv_tactic, m, p);
}
