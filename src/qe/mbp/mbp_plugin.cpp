/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:


    mpb_plugin.cpp

Abstract:

    Model-based projection plugin utilities


Author:

    Nikolaj Bjorner (nbjorner) 2015-5-29

--*/

#include "ast/rewriter/expr_safe_replace.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/occurs.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_functors.h"
#include "ast/for_each_expr.h"
#include "ast/scoped_proof.h"
#include "qe/mbp/mbp_plugin.h"
#include "model/model_pp.h"
#include "model/model_evaluator.h"


namespace mbp {

    struct noop_op_proc {
        void operator()(expr*) {}
    };

    void project_plugin::mark_rec(expr_mark& visited, expr* e) {
        for_each_expr_proc<noop_op_proc> fe;
        for_each_expr(fe, visited, e);
    }

    void project_plugin::mark_rec(expr_mark& visited, expr_ref_vector const& es) {
        for (expr* e : es)
            mark_rec(visited, e);
    }

    /**
       \brief return two terms that are equal in the model.
       The distinct term t is false in model, so there
       are at least two arguments of t that are equal in the model.
    */
    expr_ref project_plugin::pick_equality(ast_manager& m, model& model, expr* t) {
        SASSERT(m.is_distinct(t));
        expr_ref val(m);
        expr_ref_vector vals(m);
        obj_map<expr, expr*> val2expr;
        app* alit = to_app(t);
        SASSERT(alit->get_num_args() > 1);
        if (alit->get_num_args() == 2) 
            return expr_ref(m.mk_eq(alit->get_arg(0), alit->get_arg(1)), m);        
        for (expr* e1 : *alit) {
            expr* e2;
            val = model(e1);
            TRACE("qe", tout << mk_pp(e1, m) << " |-> " << val << "\n";);
            if (val2expr.find(val, e2)) {
                return expr_ref(m.mk_eq(e1, e2), m);
            }
            val2expr.insert(val, e1);
            vals.push_back(val);
        }
        for (unsigned i = 0; i < alit->get_num_args(); ++i) {
            for (unsigned j = i + 1; j < alit->get_num_args(); ++j) {
                expr* e1 = alit->get_arg(i);
                expr* e2 = alit->get_arg(j);
                val = m.mk_eq(e1, e2);
                if (!model.is_false(val))
                    return expr_ref(m.mk_eq(e1, e2), m);
            }
        }
        UNREACHABLE();
        return expr_ref(nullptr, m);
    }


    void project_plugin::erase(expr_ref_vector& lits, unsigned& i) {
        lits[i] = lits.back();
        lits.pop_back();
        --i;
    }

    void project_plugin::push_back(expr_ref_vector& lits, expr* e) {
        if (!m.is_true(e))
            lits.push_back(e);
    }

    void project_plugin::extract_literals(model& model, app_ref_vector const& vars, expr_ref_vector& fmls) {
        m_cache.reset();
        m_bool_visited.reset();
        expr_ref val(m);
        model_evaluator eval(model);
        eval.set_expand_array_equalities(true);
        TRACE("qe", tout << fmls << "\n";);
        DEBUG_CODE(for (expr* fml : fmls) { CTRACE("qe", m.is_false(eval(fml)), tout << mk_pp(fml, m) << " is false\n" << model;); SASSERT(!m.is_false(eval(fml))); });

        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls.get(i), * nfml, * f1, * f2, * f3;
            SASSERT(m.is_bool(fml));
            if (m.is_not(fml, nfml) && m.is_distinct(nfml))
                fmls[i--] = pick_equality(m, model, nfml);
            else if (m.is_or(fml)) {
                for (expr* arg : *to_app(fml)) {
                    val = eval(arg);
                    if (m.is_true(val)) {
                        fmls[i] = arg;
                        --i;
                        break;
                    }
                }
            }
            else if (m.is_and(fml)) {
                fmls.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
                erase(fmls, i);
            }
            else if (m.is_iff(fml, f1, f2) || (m.is_not(fml, nfml) && m.is_xor(nfml, f1, f2))) {
                val = eval(f1);
                if (m.is_false(val)) {
                    f1 = mk_not(m, f1);
                    f2 = mk_not(m, f2);
                }
                fmls[i--] = f1;
                push_back(fmls, f2);
            }
            else if (m.is_implies(fml, f1, f2)) {
                val = eval(f2);
                if (m.is_true(val)) {
                    fmls[i] = f2;
                }
                else {
                    fmls[i] = mk_not(m, f1);
                }
                --i;
            }
            else if (m.is_ite(fml, f1, f2, f3)) {
                val = eval(f1);
                if (m.is_true(val)) {
                    push_back(fmls, f1);
                    push_back(fmls, f2);
                }
                else {
                    push_back(fmls, mk_not(m, f1));
                    push_back(fmls, f3);
                }
                erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_not(nfml, nfml)) {
                push_back(fmls, nfml);
                erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_and(nfml)) {
                for (expr* arg : *to_app(nfml)) {
                    val = eval(arg);
                    if (m.is_false(val)) {
                        fmls[i--] = mk_not(m, arg);
                        break;
                    }
                }
            }
            else if (m.is_not(fml, nfml) && m.is_or(nfml)) {
                for (expr* arg : *to_app(nfml))
                    push_back(fmls, mk_not(m, arg));
                erase(fmls, i);
            }
            else if ((m.is_not(fml, nfml) && m.is_iff(nfml, f1, f2)) || m.is_xor(fml, f1, f2)) {
                val = eval(f1);
                if (m.is_true(val)) 
                    f2 = mk_not(m, f2);                
                else 
                    f1 = mk_not(m, f1);                
                push_back(fmls, f1);
                push_back(fmls, f2);
                erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_implies(nfml, f1, f2)) {
                push_back(fmls, f1);
                push_back(fmls, mk_not(m, f2));
                erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_ite(nfml, f1, f2, f3)) {
                val = eval(f1);
                if (m.is_true(val)) {
                    push_back(fmls, f1);
                    push_back(fmls, mk_not(m, f2));
                }
                else {
                    push_back(fmls, mk_not(m, f1));
                    push_back(fmls, mk_not(m, f3));
                }
                erase(fmls, i);
            }
            else if (m.is_not(fml, nfml))
                extract_bools(eval, fmls, i, nfml, false);
            else
                extract_bools(eval, fmls, i, fml, true);
        }
        TRACE("qe", tout << fmls << "\n";);
    }

    void project_plugin::extract_bools(model_evaluator& eval, expr_ref_vector& fmls, unsigned idx, expr* fml, bool is_true) {
        TRACE("qe", tout << "extract bools: " << mk_pp(fml, m) << "\n";);
        if (!is_app(fml))
            return;
        m_to_visit.reset();
        m_to_visit.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());        
        while (!m_to_visit.empty()) {
            if (!m.inc())
                return;
            expr* e = m_to_visit.back();
            if (m_cache.get(e->get_id(), nullptr)) {
                m_to_visit.pop_back();
            }
            else if (!is_app(e)) {
                m_cache.setx(e->get_id(), e);
                m_to_visit.pop_back();
            }
            else if (visit_ite(eval, e, fmls))
                continue;
            else if (visit_bool(eval, e, fmls))
                continue;
            else 
                visit_app(e);            
        }

        SASSERT(m_to_visit.empty());
        m_to_visit.push_back(fml);
        visit_app(fml);
        SASSERT(m_to_visit.empty());
        expr* new_fml = m_cache.get(fml->get_id(), nullptr);
        SASSERT(new_fml);
        if (new_fml != fml) 
            fmls[idx] = is_true ? new_fml : mk_not(m, new_fml);        
    }

    bool project_plugin::is_true(model_evaluator& eval, expr* e) {
        expr_ref val = eval(e);
        bool tt = m.is_true(val);
        if (!tt && !m.is_false(val) && contains_uninterpreted(val))
            throw default_exception("could not evaluate Boolean in model");
        SASSERT(tt || m.is_false(val));
        return tt;
    }

    bool project_plugin::visit_ite(model_evaluator& eval, expr* e, expr_ref_vector& fmls) {
        expr* c = nullptr, * th = nullptr, * el = nullptr;
        if (m.is_ite(e, c, th, el)) {
            bool tt = is_true(eval, c);
            if (!m_bool_visited.is_marked(c))
                fmls.push_back(tt ? c : mk_not(m, c));
            m_bool_visited.mark(c);
            expr* s = tt ? th : el;
            expr* t = m_cache.get(s->get_id(), nullptr);
            if (t) {
                m_to_visit.pop_back();
                m_cache.setx(e->get_id(), t);
            }
            else
                m_to_visit.push_back(s);
            return true;
        }
        else 
            return false;
    }

    bool project_plugin::visit_bool(model_evaluator& eval, expr* e, expr_ref_vector& fmls) {
        if (m.is_bool(e) && !m.is_true(e) && !m.is_false(e)) {
            bool tt = is_true(eval, e);
            if (!m_bool_visited.is_marked(e))
                fmls.push_back(tt ? e : mk_not(m, e));
            m_bool_visited.mark(e);
            m_cache.setx(e->get_id(), m.mk_bool_val(tt));
            m_to_visit.pop_back();
            return true;
        }
        else
            return false;
    }

    void project_plugin::visit_app(expr* e) {
        unsigned sz = m_to_visit.size();
        m_args.reset();
        bool diff = false;
        for (expr* arg : *to_app(e)) {
            expr* new_arg = m_cache.get(arg->get_id(), nullptr);
            diff |= new_arg != arg;
            if (new_arg == nullptr)
                m_to_visit.push_back(arg);
            else
                m_args.push_back(new_arg);
        }
        if (sz == m_to_visit.size()) {
            m_cache.setx(e->get_id(), diff ? m.mk_app(to_app(e)->get_decl(), m_args) : e);
            m_to_visit.pop_back();
        }
    }

    void project_plugin::mark_non_ground(expr* e) {
        m_to_visit.push_back(e);
        while (!m_to_visit.empty()) {
            expr* e = m_to_visit.back();
            if (!is_app(e)) {
                m_visited.mark(e);
                m_to_visit.pop_back();
                continue;
            }
            unsigned n = m_to_visit.size();
            for (expr* arg : *to_app(e)) {
                if (!m_visited.is_marked(arg))
                    m_to_visit.push_back(arg);
                else if (m_non_ground.is_marked(arg))
                    m_non_ground.mark(e);
            }
            if (m_to_visit.size() == n) {
                m_visited.mark(e);
                m_to_visit.pop_back();
            }
        }
    }

}
