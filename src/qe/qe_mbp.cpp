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
#include "for_each_expr.h"


using namespace qe;

struct noop_op_proc {
    void operator()(expr*) {}
};


void project_plugin::mark_rec(expr_mark& visited, expr* e) {
    for_each_expr_proc<noop_op_proc> fe;    
    for_each_expr(fe, visited, e);
}

void project_plugin::mark_rec(expr_mark& visited, expr_ref_vector const& es) {
    for (unsigned i = 0; i < es.size(); ++i) {
        mark_rec(visited, es[i]);
    }
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
    th_rewriter m_rw;
    ptr_vector<project_plugin> m_plugins;
    expr_mark m_visited;

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
        for (unsigned i = 0; i < lits.size(); ++i) {
            expr* e = lits[i].get(), *l, *r;
            if (m.is_eq(e, l, r) && reduce_eq(is_var, l, r, v, t)) {
                reduced = true;
                project_plugin::erase(lits, i);
                expr_safe_replace sub(m);
                sub.insert(v, t);
                is_rem.mark(v);
                for (unsigned j = 0; j < lits.size(); ++j) {
                    sub(lits[j].get(), tmp);
                    m_rw(tmp);
                    lits[j] = tmp;
                }
            }
        }
        if (reduced) {
            unsigned j = 0;
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (!is_rem.is_marked(vars[i].get())) {
                    if (i != j) {
                        vars[j] = vars[i].get();
                    }
                    ++j;
                }
            }
            vars.shrink(j);
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


    void filter_variables(model& model, app_ref_vector& vars, expr_ref_vector& lits, expr_ref_vector& unused_lits) {
        expr_mark lit_visited;
        project_plugin::mark_rec(lit_visited, lits);

        unsigned j = 0;
        for (unsigned i = 0; i < vars.size(); ++i) {
            app* var = vars[i].get();
            if (lit_visited.is_marked(var)) {
                if (i != j) {
                    vars[j] = vars[i].get();
                }
                ++j;
            }
        }
        if (vars.size() != j) {
            vars.resize(j);
        }
    }


    void extract_bools(model& model, expr_ref_vector& fmls, expr* fml) {
        TRACE("qe", tout << "extract bools: " << mk_pp(fml, m) << "\n";);
        ptr_vector<expr> todo;
        if (is_app(fml)) {
            todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());
        }
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (m_visited.is_marked(e)) {
                continue;
            }
            m_visited.mark(e);
            if (m.is_bool(e)) {
                expr_ref val(m);
                VERIFY(model.eval(e, val));
                TRACE("qe", tout << "found: " << mk_pp(e, m) << "\n";);
                if (m.is_true(val)) {
                    fmls.push_back(e);
                }
                else {
                    fmls.push_back(mk_not(m, e));
                }
            }
            else if (is_app(e)) {
                todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else {
                TRACE("qe", tout << "expression not handled " << mk_pp(e, m) << "\n";);
            }
        }
    }

    void project_bools(model& model, app_ref_vector& vars, expr_ref_vector& fmls) {
        expr_safe_replace sub(m);
        expr_ref val(m);
        unsigned j = 0;
        for (unsigned i = 0; i < vars.size(); ++i) {
            app* var = vars[i].get();
            if (m.is_bool(var)) {
                VERIFY(model.eval(var, val));
                sub.insert(var, val);
            }
            else {
                if (j != i) {
                    vars[j] = vars[i].get();
                }
                ++j;
            }
        }
        if (j != vars.size()) {
            vars.resize(j);
            j = 0;
            for (unsigned i = 0; i < fmls.size(); ++i) {
                sub(fmls[i].get(), val);
                m_rw(val);
                if (!m.is_true(val)) {
                    TRACE("qe", tout << mk_pp(fmls[i].get(), m) << " -> " << val << "\n";);
                    fmls[i] = val;
                    if (j != i) {
                        fmls[j] = fmls[i].get();
                    }
                    ++j;
                }
            }
            if (j != fmls.size()) {
                fmls.resize(j);
            }
        }
    }

public:


    opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt) {
        arith_project_plugin arith(m);
        return arith.maximize(fmls, mdl, t, ge, gt);
    }

    void extract_literals(model& model, expr_ref_vector& fmls) {
        expr_ref val(m);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            expr* fml = fmls[i].get(), *nfml, *f1, *f2, *f3;
            SASSERT(m.is_bool(fml));
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
                fmls[i] = f1;
                project_plugin::push_back(fmls, f2);
                --i;
            }
            else if (m.is_implies(fml, f1, f2)) {
                VERIFY (model.eval(f2, val));
                if (m.is_true(val)) {
                    fmls[i] = f2;
                }
                else {
                    fmls[i] = mk_not(m, f1);
                }
                --i;
            }
            else if (m.is_ite(fml, f1, f2, f3)) {
                VERIFY (model.eval(f1, val));                
                if (m.is_true(val)) {
                    project_plugin::push_back(fmls, f1);
                    project_plugin::push_back(fmls, f2);
                }
                else {
                    project_plugin::push_back(fmls, mk_not(m, f1));
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
                    project_plugin::push_back(fmls, f1);
                    project_plugin::push_back(fmls, mk_not(m, f2));
                }
                else {
                    project_plugin::push_back(fmls, mk_not(m, f1));
                    project_plugin::push_back(fmls, mk_not(m, f3));
                }
                project_plugin::erase(fmls, i);
            }
            else if (m.is_not(fml, nfml)) {
                extract_bools(model, fmls, nfml);
            }
            else {
                extract_bools(model, fmls, fml);
                // TBD other Boolean operations.
            }
        }
        m_visited.reset();
    }

    impl(ast_manager& m):m(m), m_rw(m) {
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

    bool validate_model(model& model, expr_ref_vector const& fmls) {
        expr_ref val(m);
        for (unsigned i = 0; i < fmls.size(); ++i) { 
            VERIFY(model.eval(fmls[i], val) && m.is_true(val)); 
        }
        return true;
    }

    void operator()(bool force_elim, app_ref_vector& vars, model& model, expr_ref_vector& fmls) {
        SASSERT(validate_model(model, fmls));
        expr_ref val(m), tmp(m);
        app_ref var(m);
        expr_ref_vector unused_fmls(m);
        bool progress = true;
        preprocess_solve(model, vars, fmls);
        filter_variables(model, vars, fmls, unused_fmls);
        project_bools(model, vars, fmls);
        while (progress && !vars.empty() && !fmls.empty()) {
            app_ref_vector new_vars(m);
            progress = false;
            for (unsigned i = 0; i < m_plugins.size(); ++i) {
                project_plugin* p = m_plugins[i];
                if (p) {
                    (*p)(model, vars, fmls);
                }
            }
            while (!vars.empty() && !fmls.empty()) {                
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
            if (!progress && !new_vars.empty() && !fmls.empty() && force_elim) {
                var = new_vars.back();
                new_vars.pop_back();
                expr_safe_replace sub(m);
                VERIFY(model.eval(var, val));
                sub.insert(var, val);
                for (unsigned i = 0; i < fmls.size(); ++i) {
                    sub(fmls[i].get(), tmp);
                    m_rw(tmp);
                    if (m.is_true(tmp)) {
                        project_plugin::erase(fmls, i);
                    }
                    else {
                        fmls[i] = tmp;
                    }
                }            
                progress = true;
            }
            vars.append(new_vars);
            if (progress) {
                preprocess_solve(model, vars, fmls);
            }
        }
        if (fmls.empty()) {
            vars.reset();
        }
        fmls.append(unused_fmls);
        SASSERT(validate_model(model, fmls));
        TRACE("qe", tout << vars << " " << fmls << "\n";);
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

opt::inf_eps mbp::maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt) {
    return m_impl->maximize(fmls, mdl, t, ge, gt);
}
