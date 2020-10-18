/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.cpp

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-29

Revision History:


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
        if (alit->get_num_args() == 2) {
            return expr_ref(m.mk_eq(alit->get_arg(0), alit->get_arg(1)), m);
        }
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
        m_bool_visited.reset();
        expr_ref val(m);
        model_evaluator eval(model);
        eval.set_expand_array_equalities(true);
        TRACE("qe", tout << fmls << "\n";);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls.get(i), * nfml, * f1, * f2, * f3;
            SASSERT(m.is_bool(fml));
            if (m.is_not(fml, nfml) && m.is_distinct(nfml))
                fmls[i--] = mbp::project_plugin::pick_equality(m, model, nfml);
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
                mbp::project_plugin::erase(fmls, i);
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
                mbp::project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_not(nfml, nfml)) {
                push_back(fmls, nfml);
                mbp::project_plugin::erase(fmls, i);
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
                mbp::project_plugin::erase(fmls, i);
            }
            else if ((m.is_not(fml, nfml) && m.is_iff(nfml, f1, f2)) || m.is_xor(fml, f1, f2)) {
                val = eval(f1);
                if (m.is_true(val)) {
                    f2 = mk_not(m, f2);
                }
                else {
                    f1 = mk_not(m, f1);
                }
                push_back(fmls, f1);
                push_back(fmls, f2);
                mbp::project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_implies(nfml, f1, f2)) {
                push_back(fmls, f1);
                push_back(fmls, mk_not(m, f2));
                mbp::project_plugin::erase(fmls, i);
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
                mbp::project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml)) {
                if (extract_bools(eval, fmls, nfml)) {
                    mbp::project_plugin::erase(fmls, i);
                }
            }
            else if (extract_bools(eval, fmls, fml))
                mbp::project_plugin::erase(fmls, i);
        }
        TRACE("qe", tout << fmls << "\n";);
    }

    bool project_plugin::extract_bools(model_evaluator& eval, expr_ref_vector& fmls, expr* fml) {
        TRACE("qe", tout << "extract bools: " << mk_pp(fml, m) << "\n";);
        ptr_vector<expr> todo;
        expr_safe_replace sub(m);
        m_visited.reset();
        bool found_bool = false;
        if (is_app(fml)) {
            todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        }
        while (!todo.empty() && m.inc()) {
            expr* e = todo.back();
            todo.pop_back();
            if (m_visited.is_marked(e)) {
                continue;
            }
            m_visited.mark(e);
            if (m.is_bool(e) && !m.is_true(e) && !m.is_false(e)) {
                expr_ref val = eval(e);
                TRACE("qe", tout << "found: " << mk_pp(e, m) << " " << val << "\n";);
                if (!m.inc())
                    continue;
                if (!m.is_true(val) && !m.is_false(val) && contains_uninterpreted(val)) 
                    throw default_exception("could not evaluate Boolean in model");
                SASSERT(m.is_true(val) || m.is_false(val));

                if (!m_bool_visited.is_marked(e)) 
                    fmls.push_back(m.is_true(val) ? e : mk_not(m, e));
                sub.insert(e, val);
                m_bool_visited.mark(e);
                found_bool = true;
            }
            else if (is_app(e)) {
                todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else {
                TRACE("qe", tout << "expression not handled " << mk_pp(e, m) << "\n";);
            }
        }
        if (found_bool) {
            expr_ref tmp(m);
            sub(fml, tmp);
            expr_ref val = eval(tmp);
            if (!m.is_true(val) && !m.is_false(val))
                return false;
            fmls.push_back(m.is_true(val) ? tmp : mk_not(m, tmp));
        }
        return found_bool;
    }

}
