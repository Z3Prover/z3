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
#include "qe/qe_mbp.h"
#include "qe/mbp/mbp_arith.h"
#include "qe/mbp/mbp_arrays.h"
#include "qe/mbp/mbp_datatypes.h"
#include "qe/qe_lite.h"
#include "model/model_pp.h"
#include "model/model_evaluator.h"


using namespace qe;


class mbproj::impl {
    ast_manager& m;
    params_ref                      m_params;
    th_rewriter                     m_rw;
    ptr_vector<mbp::project_plugin> m_plugins;

    // parameters
    bool m_reduce_all_selects;
    bool m_dont_sub;

    void add_plugin(mbp::project_plugin* p) {
        family_id fid = p->get_family_id();
        SASSERT(!m_plugins.get(fid, nullptr));
        m_plugins.setx(fid, p, nullptr);
    }

    mbp::project_plugin* get_plugin(app* var) {
        family_id fid = var->get_sort()->get_family_id();
        return m_plugins.get(fid, nullptr);
    }

    bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        expr_mark is_var, is_rem;
        if (vars.empty()) {
            return false;
        }
        bool reduced = false;
        for (expr* v : vars)
            is_var.mark(v);
        expr_ref tmp(m), t(m), v(m);

        for (unsigned i = 0; i < lits.size(); ++i) {
            expr* e = lits.get(i), * l, * r;
            if (m.is_eq(e, l, r) && reduce_eq(is_var, l, r, v, t)) {
                reduced = true;
                mbp::project_plugin::erase(lits, i);
                expr_safe_replace sub(m);
                sub.insert(v, t);
                is_rem.mark(v);
                for (unsigned j = 0; j < lits.size(); ++j) {
                    sub(lits.get(j), tmp);
                    m_rw(tmp);
                    lits[j] = tmp;
                }
            }
        }
        if (reduced) {
            unsigned j = 0;
            for (app* v : vars)
                if (!is_rem.is_marked(v))
                    vars[j++] = v;
            vars.shrink(j);
        }
        return reduced;
    }

    bool reduce_eq(expr_mark& is_var, expr* l, expr* r, expr_ref& v, expr_ref& t) {
        if (is_var.is_marked(r)) 
            std::swap(l, r);        
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
        mbp::project_plugin::mark_rec(lit_visited, lits);
        unsigned j = 0;
        for (app* var : vars)
            if (lit_visited.is_marked(var))
                vars[j++] = var;
        vars.shrink(j);
    }

    void project_bools(model& mdl, app_ref_vector& vars, expr_ref_vector& fmls) {
        expr_safe_replace sub(m);
        expr_ref val(m);
        model_evaluator eval(mdl, m_params);
        eval.set_model_completion(true);
        unsigned j = 0;
        for (app* var : vars) {
            if (m.is_bool(var)) 
                sub.insert(var, eval(var));            
            else 
                vars[j++] = var;            
        }
        if (j == vars.size()) 
            return;        
        vars.shrink(j);
        j = 0;
        for (expr* fml : fmls) {
            sub(fml, val);
            m_rw(val);
            if (!m.is_true(val)) {
                TRACE("qe", tout << mk_pp(fml, m) << " -> " << val << "\n";);
                fmls[j++] = val;
            }
        }
        fmls.shrink(j);
    }


    void subst_vars(model_evaluator& eval, app_ref_vector const& vars, expr_ref& fml) {
        expr_safe_replace sub(m);
        for (app* v : vars) 
            sub.insert(v, eval(v));        
        sub(fml);
    }

    struct index_term_finder {
        ast_manager& m;
        array_util       m_array;
        app_ref          m_var;
        expr_ref_vector& m_res;

        index_term_finder(ast_manager& mgr, app* v, expr_ref_vector& res) :
            m(mgr), m_array(m), m_var(v, m), m_res(res) {}

        void operator() (var* n) {}
        void operator() (quantifier* n) {}
        void operator() (app* n) {
            expr* e1, * e2;
            if (m_array.is_select(n)) {
                for (expr* arg : *n) {
                    if (arg->get_sort() == m_var->get_sort() && arg != m_var)
                        m_res.push_back(arg);
                }
            }
            else if (m.is_eq(n, e1, e2)) {
                if (e1 == m_var)
                    m_res.push_back(e2);
                else if (e2 == m_var)
                    m_res.push_back(e1);
            }
        }
    };

    bool project_var(model_evaluator& eval, app* var, expr_ref& fml) {
        expr_ref val = eval(var);

        TRACE("mbqi_project_verbose", tout << "MBQI: var: " << mk_pp(var, m) << "\n" << "fml: " << fml << "\n";);
        expr_ref_vector terms(m);
        index_term_finder finder(m, var, terms);
        for_each_expr(finder, fml);

        TRACE("mbqi_project_verbose", tout << "terms:\n" << terms;);

        for (expr* term : terms) {
            expr_ref tval = eval(term);

            TRACE("mbqi_project_verbose", tout << "term: " << mk_pp(term, m) << " tval: " << tval << " val: " << val << "\n";);

            // -- if the term does not contain an occurrence of var
            // -- and is in the same equivalence class in the model
            if (tval == val && !occurs(var, term)) {
                TRACE("mbqi_project",
                    tout << "MBQI: replacing " << mk_pp(var, m) << " with " << mk_pp(term, m) << "\n";);
                expr_safe_replace sub(m);
                sub.insert(var, term);
                sub(fml);
                return true;
            }
        }

        TRACE("mbqi_project",
            tout << "MBQI: failed to eliminate " << mk_pp(var, m) << " from " << fml << "\n";);

        return false;
    }

    void project_vars(model& M, app_ref_vector& vars, expr_ref& fml) {
        model_evaluator eval(M);
        eval.set_model_completion(false);
        // -- evaluate to initialize eval cache
        eval(fml);
        unsigned j = 0;
        for (app* v : vars) 
            if (!project_var(eval, v, fml)) 
                vars[j++] = v;                    
        vars.shrink(j);
    }

public:

    opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt) {
        mbp::arith_project_plugin arith(m);
        return arith.maximize(fmls, mdl, t, ge, gt);
    }

    void extract_literals(model& model, app_ref_vector const& vars, expr_ref_vector& fmls) {
        mbp::project_plugin proj(m);
        proj.extract_literals(model, vars, fmls);
    }

    impl(ast_manager& m, params_ref const& p) :m(m), m_params(p), m_rw(m) {
        add_plugin(alloc(mbp::arith_project_plugin, m));
        add_plugin(alloc(mbp::datatype_project_plugin, m));
        add_plugin(alloc(mbp::array_project_plugin, m));
        updt_params(p);
    }

    ~impl() {
        std::for_each(m_plugins.begin(), m_plugins.end(), delete_proc<mbp::project_plugin>());
    }

    void updt_params(params_ref const& p) {
        m_params.append(p);
        m_reduce_all_selects = m_params.get_bool("reduce_all_selects", false);
        m_dont_sub = m_params.get_bool("dont_sub", false);
    }

    void preprocess_solve(model& model, app_ref_vector& vars, expr_ref_vector& fmls) {
        extract_literals(model, vars, fmls);
        bool change = true;
        while (change && !vars.empty()) {
            change = solve(model, vars, fmls);
            for (auto* p : m_plugins) {
                if (p && p->solve(model, vars, fmls)) {
                    change = true;
                }
            }
        }
    }

    bool validate_model(model& model, expr_ref_vector const& fmls) {
        expr_ref val(m);
        model_evaluator eval(model);
        for (expr* f : fmls) {
            VERIFY(!model.is_false(f));
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
        while (progress && !vars.empty() && !fmls.empty() && m.limit().inc()) {
            app_ref_vector new_vars(m);
            progress = false;
            for (mbp::project_plugin* p : m_plugins) {
                if (p)
                    (*p)(model, vars, fmls);
            }
            while (!vars.empty() && !fmls.empty() && m.limit().inc()) {
                var = vars.back();
                vars.pop_back();
                mbp::project_plugin* p = get_plugin(var);
                if (p && (*p)(model, var, vars, fmls)) {
                    progress = true;
                }
                else {
                    new_vars.push_back(var);
                }
            }
            if (!progress && !new_vars.empty() && !fmls.empty() && force_elim && m.limit().inc()) {
                var = new_vars.back();
                new_vars.pop_back();
                expr_safe_replace sub(m);
                val = model(var);
                sub.insert(var, val);
                unsigned j = 0;
                for (expr* f : fmls) {
                    sub(f, tmp);
                    m_rw(tmp);
                    if (!m.is_true(tmp))
                        fmls[j++] = tmp;
                }
                fmls.shrink(j);
                progress = true;
            }
            if (!m.limit().inc())
                return;
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

    void do_qe_lite(app_ref_vector& vars, expr_ref& fml) {
        qe_lite qe(m, m_params, false);
        qe(vars, fml);
        m_rw(fml);
        TRACE("qe", tout << "After qe_lite:\n" << fml << "\n" << "Vars: " << vars << "\n";);
        SASSERT(!m.is_false(fml));
    }

    void do_qe_bool(model& mdl, app_ref_vector& vars, expr_ref& fml) {
        expr_ref_vector fmls(m);
        fmls.push_back(fml);
        project_bools(mdl, vars, fmls);
        fml = mk_and(fmls);
    }

    void spacer(app_ref_vector& vars, model& mdl, expr_ref& fml) {
        TRACE("qe", tout << "Before projection:\n" << fml << "\n" << "Vars: " << vars << "\n";);

        model_evaluator eval(mdl, m_params);
        eval.set_model_completion(true);
        app_ref_vector other_vars(m);
        app_ref_vector array_vars(m);
        array_util arr_u(m);
        arith_util ari_u(m);

        flatten_and(fml);

        while (!vars.empty()) {

            do_qe_lite(vars, fml);

            do_qe_bool(mdl, vars, fml);

            // sort out vars into bools, arith (int/real), and arrays
            for (app* v : vars) {
                if (arr_u.is_array(v)) {
                    array_vars.push_back(v);
                }
                else {
                    other_vars.push_back(v);
                }
            }

            TRACE("qe", tout << "Array vars: " << array_vars << "\n";);

            vars.reset();

            // project arrays
            mbp::array_project_plugin ap(m);
            ap(mdl, array_vars, fml, vars, m_reduce_all_selects);
            SASSERT(array_vars.empty());
            m_rw(fml);
            SASSERT(!m.is_false(fml));

            TRACE("qe",
                tout << "extended model:\n" << mdl;
                tout << "Vars: " << vars << "\n";);
        }

        // project reals, ints and other variables.
        if (!other_vars.empty()) {
            TRACE("qe", tout << "Other vars: " << other_vars << "\n" << mdl;);

            expr_ref_vector fmls(m);
            flatten_and(fml, fmls);

            (*this)(false, other_vars, mdl, fmls);
            fml = mk_and(fmls);
            m_rw(fml);

            TRACE("qe",
                tout << "Projected other vars:\n" << fml << "\n";
            tout << "Remaining other vars:\n" << other_vars << "\n";);
            SASSERT(!m.is_false(fml));
        }

        if (!other_vars.empty()) {
            project_vars(mdl, other_vars, fml);
            m_rw(fml);
        }

        // substitute any remaining other vars
        if (!m_dont_sub && !other_vars.empty()) {
            subst_vars(eval, other_vars, fml);
            TRACE("qe", tout << "After substituting remaining other vars:\n" << fml << "\n";);
            // an extra round of simplification because subst_vars is not simplifying
            m_rw(fml);
            other_vars.reset();
        }

        SASSERT(!eval.is_false(fml));

        vars.reset();
        vars.append(other_vars);
    }

};

mbproj::mbproj(ast_manager& m, params_ref const& p) {
    scoped_no_proof _sp(m);
    m_impl = alloc(impl, m, p);
}

mbproj::~mbproj() {
    dealloc(m_impl);
}

void mbproj::updt_params(params_ref const& p) {
    m_impl->updt_params(p);
}

void mbproj::get_param_descrs(param_descrs& r) {
    r.insert("reduce_all_selects", CPK_BOOL, "(default: false) reduce selects");
    r.insert("dont_sub", CPK_BOOL, "(default: false) disable substitution of values for free variables");
}

void mbproj::operator()(bool force_elim, app_ref_vector& vars, model& mdl, expr_ref_vector& fmls) {
    scoped_no_proof _sp(fmls.get_manager());
    (*m_impl)(force_elim, vars, mdl, fmls);
}

void mbproj::spacer(app_ref_vector& vars, model& mdl, expr_ref& fml) {
    scoped_no_proof _sp(fml.get_manager());
    m_impl->spacer(vars, mdl, fml);
}

void mbproj::solve(model& model, app_ref_vector& vars, expr_ref_vector& fmls) {
    scoped_no_proof _sp(fmls.get_manager());
    m_impl->preprocess_solve(model, vars, fmls);
}

opt::inf_eps mbproj::maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt) {
    scoped_no_proof _sp(fmls.get_manager());
    return m_impl->maximize(fmls, mdl, t, ge, gt);
}
