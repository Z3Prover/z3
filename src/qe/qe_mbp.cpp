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

#include "qe_mbp.h"
#include "qe_arith.h"
#include "qe_arrays.h"
#include "qe_datatypes.h"
#include "expr_safe_replace.h"
#include "ast_pp.h"
#include "ast_util.h"
#include "th_rewriter.h"
#include "model_v2_pp.h"
#include "expr_functors.h"


using namespace qe;


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
    for (unsigned i = 0; i < alit->get_num_args(); ++i) {
        expr* e1 = alit->get_arg(i), *e2;
        VERIFY(model.eval(e1, val));
        if (val2expr.find(val, e2)) {
            return expr_ref(m.mk_eq(e1, e2), m);
        }
        val2expr.insert(val, e1);
        vals.push_back(val);
    }
    UNREACHABLE();
    return expr_ref(0, m);
}

void project_plugin::partition_values(model& model, expr_ref_vector const& vals, expr_ref_vector& lits) {
    ast_manager& m = vals.get_manager();
    expr_ref val(m);
    expr_ref_vector trail(m), reps(m);
    obj_map<expr, expr*> roots;
    for (unsigned i = 0; i < vals.size(); ++i) {
        expr* v = vals[i], *root;
        VERIFY (model.eval(v, val));
        if (roots.find(val, root)) {
            lits.push_back(m.mk_eq(v, root));
        }
        else {
            roots.insert(val, v);
            trail.push_back(val);
            reps.push_back(v);
        }
    }
    if (reps.size() > 1) {                
        lits.push_back(mk_distinct(reps));
    }
}

void project_plugin::partition_args(model& model, app_ref_vector const& selects, expr_ref_vector& lits) {
    ast_manager& m = selects.get_manager();
    if (selects.empty()) return;
    unsigned num_args = selects[0]->get_decl()->get_arity();
    for (unsigned j = 1; j < num_args; ++j) {
        expr_ref_vector args(m);            
        for (unsigned i = 0; i < selects.size(); ++i) {
            args.push_back(selects[i]->get_arg(j));
        }
        project_plugin::partition_values(model, args, lits);
    }
}

void project_plugin::erase(expr_ref_vector& lits, unsigned& i) {
    lits[i] = lits.back();
    lits.pop_back();
    --i;
}

void project_plugin::push_back(expr_ref_vector& lits, expr* e) {
    if (lits.get_manager().is_true(e)) return;
    lits.push_back(e);
}


class mbp::impl {
    ast_manager& m;
    ptr_vector<project_plugin> m_plugins;

    void add_plugin(project_plugin* p) {
        family_id fid = p->get_family_id();
        SASSERT(!m_plugins.get(fid, 0));
        m_plugins.setx(fid, p, 0);
    }

    project_plugin* get_plugin(app* var) {
        family_id fid = m.get_sort(var)->get_family_id();
        return m_plugins.get(fid, 0);
    }

    bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        expr_mark is_var, is_rem;
        if (vars.empty()) {
            return false;
        }
        bool reduced = false;
        for (unsigned i = 0; i < vars.size(); ++i) { 
            is_var.mark(vars[i].get());
        }
        expr_ref tmp(m), t(m), v(m);            
        th_rewriter rw(m);
        for (unsigned i = 0; i < lits.size(); ++i) {
            expr* e = lits[i].get(), *l, *r;
            if (m.is_eq(e, l, r) && reduce_eq(is_var, l, r, v, t)) {
                reduced = true;
                lits[i] = lits.back();
                lits.pop_back();
                --i;
                expr_safe_replace sub(m);
                sub.insert(v, t);
                is_rem.mark(v);
                for (unsigned j = 0; j < lits.size(); ++j) {
                    sub(lits[j].get(), tmp);
                    rw(tmp);
                    lits[j] = tmp;
                }
            }
        }
        if (reduced) {
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (is_rem.is_marked(vars[i].get())) {
                    vars[i] = vars.back();
                    vars.pop_back();
                }
            }
        }
        return reduced;
    }

    bool reduce_eq(expr_mark& is_var, expr* l, expr* r, expr_ref& v, expr_ref& t) {
        if (is_var.is_marked(r)) {
            std::swap(l, r);
        }
        if (is_var.is_marked(l)) {
            contains_app cont(m, to_app(l));
            if (!cont(r)) {
                v = to_app(l);
                t = r;
                return true;
            }
        }
        return false;
    }

public:

    void extract_literals(model& model, expr_ref_vector& fmls) {
        expr_ref val(m);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls[i].get(), *nfml, *f1, *f2, *f3;
            if (m.is_not(fml, nfml) && m.is_distinct(nfml)) {
                fmls[i] = project_plugin::pick_equality(m, model, nfml);
                --i;
            }
            else if (m.is_or(fml)) {
                for (unsigned j = 0; j < to_app(fml)->get_num_args(); ++j) {
                    VERIFY (model.eval(to_app(fml)->get_arg(j), val));
                    if (m.is_true(val)) {
                        fmls[i] = to_app(fml)->get_arg(j);
                        --i;
                        break;
                    }
                }
            }
            else if (m.is_and(fml)) {
                fmls.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
                project_plugin::erase(fmls, i);
            }
            else if (m.is_iff(fml, f1, f2) || (m.is_not(fml, nfml) && m.is_xor(nfml, f1, f2))) {
                VERIFY (model.eval(f1, val));
                if (m.is_false(val)) {
                    f1 = mk_not(m, f1);
                    f2 = mk_not(m, f2);
                }
                project_plugin::push_back(fmls, f1);
                project_plugin::push_back(fmls, f2);
                project_plugin::erase(fmls, i);
            }
            else if (m.is_implies(fml, f1, f2)) {
                VERIFY (model.eval(f2, val));
                if (m.is_true(val)) {
                    project_plugin::push_back(fmls, f2);
                }
                else {
                    project_plugin::push_back(fmls, mk_not(m, f1));
                }
                project_plugin::erase(fmls, i);
            }
            else if (m.is_ite(fml, f1, f2, f3)) {
                VERIFY (model.eval(f1, val));                
                if (m.is_true(val)) {
                    project_plugin::push_back(fmls, f2);
                }
                else {
                    project_plugin::push_back(fmls, f3);
                }
                project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_not(nfml, nfml)) {
                project_plugin::push_back(fmls, nfml);
                project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_and(nfml)) {
                for (unsigned j = 0; j < to_app(nfml)->get_num_args(); ++j) {
                    VERIFY (model.eval(to_app(nfml)->get_arg(j), val));
                    if (m.is_false(val)) {
                        fmls[i] = mk_not(m, to_app(nfml)->get_arg(j));
                        --i;
                        break;
                    }
                }
            }
            else if (m.is_not(fml, nfml) && m.is_or(nfml)) {
                for (unsigned j = 0; j < to_app(nfml)->get_num_args(); ++j) {
                    project_plugin::push_back(fmls, mk_not(m, to_app(nfml)->get_arg(j)));
                }
                project_plugin::erase(fmls, i);                
            }
            else if ((m.is_not(fml, nfml) && m.is_iff(nfml, f1, f2)) || m.is_xor(fml, f1, f2)) {
                VERIFY (model.eval(f1, val));
                if (m.is_true(val)) {
                    f2 = mk_not(m, f2);
                }
                else {
                    f1 = mk_not(m, f1);
                }
                project_plugin::push_back(fmls, f1);
                project_plugin::push_back(fmls, f2);
                project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_implies(nfml, f1, f2)) {
                project_plugin::push_back(fmls, f1);
                project_plugin::push_back(fmls, mk_not(m, f2));
                project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml) && m.is_ite(nfml, f1, f2, f3)) {
                VERIFY (model.eval(f1, val));                
                if (m.is_true(val)) {
                    project_plugin::push_back(fmls, mk_not(m, f2));
                }
                else {
                    project_plugin::push_back(fmls, mk_not(m, f3));
                }
                project_plugin::erase(fmls, i);
            }
            else {
                // TBD other Boolean operations.
            }
        }
    }

    impl(ast_manager& m):m(m) {
        add_plugin(alloc(arith_project_plugin, m));
        add_plugin(alloc(datatype_project_plugin, m));
        add_plugin(alloc(array_project_plugin, m));
    }

    ~impl() {
        std::for_each(m_plugins.begin(), m_plugins.end(), delete_proc<project_plugin>());
    }

    void preprocess_solve(model& model, app_ref_vector& vars, expr_ref_vector& fmls) {
        extract_literals(model, fmls);
        bool change = true;
        while (change && !vars.empty()) {
            change = solve(model, vars, fmls);
            for (unsigned i = 0; i < m_plugins.size(); ++i) {
                if (m_plugins[i] && m_plugins[i]->solve(model, vars, fmls)) {
                    change = true;
                }
            }
        }        
    }

    void operator()(bool force_elim, app_ref_vector& vars, model& model, expr_ref_vector& fmls) {
        expr_ref val(m), tmp(m);
        app_ref var(m);
        th_rewriter rw(m);
        bool progress = true;
        while (progress && !vars.empty()) {
            preprocess_solve(model, vars, fmls);
            app_ref_vector new_vars(m);
            progress = false;
            while (!vars.empty()) {
                var = vars.back();
                vars.pop_back();
                project_plugin* p = get_plugin(var);
                if (p && (*p)(model, var, vars, fmls)) {
                    progress = true;
                }
                else {
                    new_vars.push_back(var);
                }
            }
            if (!progress && !new_vars.empty() && force_elim) {
                var = new_vars.back();
                new_vars.pop_back();
                expr_safe_replace sub(m);
                VERIFY(model.eval(var, val));
                sub.insert(var, val);
                for (unsigned i = 0; i < fmls.size(); ++i) {
                    sub(fmls[i].get(), tmp);
                    rw(tmp);
                    if (m.is_true(tmp)) {
                        fmls[i] = fmls.back();
                        fmls.pop_back();
                        --i;
                    }
                    else {
                        fmls[i] = tmp;
                    }
                }            
                progress = true;
            }
            vars.append(new_vars);
        }
    }
};
    
mbp::mbp(ast_manager& m) {
    m_impl = alloc(impl, m);
}
        
mbp::~mbp() {
    dealloc(m_impl);
}
        
void mbp::operator()(bool force_elim, app_ref_vector& vars, model& mdl, expr_ref_vector& fmls) {
    (*m_impl)(force_elim, vars, mdl, fmls);
}

void mbp::solve(model& model, app_ref_vector& vars, expr_ref_vector& fmls) {
    m_impl->preprocess_solve(model, vars, fmls);
}
        
void mbp::extract_literals(model& model, expr_ref_vector& lits) {
    m_impl->extract_literals(model, lits);
}
