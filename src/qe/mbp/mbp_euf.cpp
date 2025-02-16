/*++
Copyright (c) 2025 Microsoft Corporation

--*/


#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "qe/mbp/mbp_euf.h"

namespace mbp {
    euf_project_plugin::euf_project_plugin(ast_manager& m): project_plugin(m) {        
    }

    euf_project_plugin::~euf_project_plugin() {
    }
    
    bool euf_project_plugin::project1(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        return false;
    }
    
    family_id euf_project_plugin::get_family_id() {
        return basic_family_id;        
    }
    

    void euf_project_plugin::solve_eqs(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs) {
        flatten_and(lits);
        expr_mark var_set;
        auto is_pure = [&](expr_mark& var_set, expr* v) {
            return all_of(subterms::all(expr_ref(v, m)), [&](expr* w) { return !var_set.is_marked(w); });
        };
        for (auto v : vars)
            var_set.mark(v, true);
        // solve trivial equations
        for (auto e : lits) {
            expr* x = nullptr, *y = nullptr;
            if (m.is_eq(e, x, y) && var_set.is_marked(x) && is_pure(var_set, y)) {
                vars.erase(to_app(x));
                defs.push_back({ expr_ref(x, m), expr_ref(y, m) });
            }
            else if (m.is_eq(e, y, x) && var_set.is_marked(x) && is_pure(var_set, y)) {
                vars.erase(to_app(x));
                defs.push_back({ expr_ref(x, m), expr_ref(y, m) });
            }
        }
    }

    bool euf_project_plugin::solve_eqs_saturate(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs) {
        unsigned sz = defs.size();
        while (true) {
            unsigned sz1 = defs.size();
            solve_eqs(model, vars, lits, defs);
            if (sz1 == defs.size())
                break;
        }
        return sz < defs.size();
    }


    bool euf_project_plugin::operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        if (vars.empty())
            return false;
        // check if there is a variable of uninterp sort
        if (all_of(vars, [&](expr* v) { return !m.is_uninterp(v->get_sort()); }))
            return false;

        vector<def> defs;
        if (solve_eqs_saturate(model, vars, lits, defs))
            return true;
        term_graph tg(m);
        tg.add_lits(lits);
        for (auto v : vars) 
            if (m.is_uninterp(v->get_sort()))
                tg.add_var(v);

        auto result = tg.project(model);
        lits.reset();
        lits.append(result);

        unsigned j = 0;
        for (app* v : vars) 
            if (!m.is_uninterp(v->get_sort())) 
                vars[j++] = v;
        vars.shrink(j);

        return true;
    }

    bool euf_project_plugin::project(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs) {
        if (vars.empty())
            return false;

        // check if there is a variable of uninterp sort
        if (all_of(vars, [&](expr* v) { return !m.is_uninterp(v->get_sort()); }))
            return false;

        if (solve_eqs_saturate(model, vars, lits, defs))
            return true;
        

        term_graph tg(m);
        tg.add_lits(lits);
        for (auto v : vars) 
            if (m.is_uninterp(v->get_sort()))
                tg.add_var(v);

        expr_ref_vector terms(m);
        for (expr* f : subterms::all(lits))
            terms.push_back(f);

        // try to project on representatives:
        tg.add_model_based_terms(model, terms);

        // save rep_of. It gets reset by tg.get_partition.
        struct scoped_reset {
            euf_project_plugin& p;
            scoped_reset(euf_project_plugin& p): p(p) {}
            ~scoped_reset() { p.m_reps.reset(); p.m_parents.reset(); }
        };
        scoped_reset _reset(*this);
        expr_ref_vector pinned(m);
        for (auto t : terms) {
            m_reps.insert(t, tg.rep_of(t));
            pinned.push_back(tg.rep_of(t));
            if (is_app(t)) {
                for (expr* arg : *to_app(t))
                    m_parents.insert_if_not_there(arg, {}).push_back(t);
            }
        }
        unsigned j = 0;
        bool solved = false;
        for (app* v : vars) {
            if (m.is_uninterp(v->get_sort())) {
                expr* r = m_reps[v];
                if (r) 
                    defs.push_back({ expr_ref(v, m), expr_ref(r, m) }), solved = true;
                else
                    vars[j++] = v;
            }
            else
                vars[j++] = v;
        }
        vars.shrink(j);

        if (solved)
            return true;
       

        // walk equivalence classes.
        // try to unify with pure classes.
        // some parent of y contains f(y) and class of f contains f(t) with repr(t) != nullptr
        // merge y = t, provided parent f(y) is not distinct from f(t)
        // unification can break distinctness, and should require a full solver call.
        // a conservative rule is to walk only the equivalence class of f(y) to check if it
        // contains f(t),
        // or recursively if there is a term g(f(t)) that is equal to g(f(y))
        // thus, take equivalence classes that contain a repr and unify
        //
        // this can still break satisfiability if f(y) is required distinct from f(t) even
        // if g(f(t)) = g(f(y))
        // so as a simplification unification is only allowed if g(f(y)) is the only parent of f(y) 

        auto Ps = tg.get_partition(model);
        for (auto const& p : Ps) {
            expr* r = m_reps[p[0]];
            if (!r)
                continue;
            for (auto e : p) {
                if (!is_app(e))
                    continue;
                app* a = to_app(e);
                func_decl* f = a->get_decl();
                if (!is_uninterp(f))
                    continue;
                if (all_of(*a, [&](expr* arg) { return !!m_reps[arg]; }))
                    continue;
                if (try_unify(tg, a, p, vars, defs)) 
                    return true;
            }
        }        
        
        return false;
    }

    bool euf_project_plugin::try_unify(term_graph& tg, app* a, expr_ref_vector const& partition, app_ref_vector& vars, vector<def>& defs) {

        auto same_decl = [&](expr* x, expr* y) {
            if (!is_app(x) || !is_app(y))
                return false;
            app* a = to_app(x);
            app* b = to_app(y);
            if (a->get_decl() != b->get_decl())
                return false;
            return a->get_num_args() == b->get_num_args();
        };

        auto is_var = [&](expr* x) {
            return is_uninterp_const(x) && m.is_uninterp(x->get_sort()) && vars.contains(to_app(x));
        };
        
        for (auto e : partition) {
            if (a == e)
                continue;
            if (!same_decl(a, e))
                continue;
            app* b = to_app(e);
            if (!all_of(*b, [&](expr* arg) { return !!m_reps[arg]; }))
                continue;
            // same function symbol. All kids of b are defined, some kid of a is not defined.
            svector<std::pair<expr*, expr*>> todo;
            obj_map<expr, expr*> soln;
            for (unsigned i = 0; i < b->get_num_args(); ++i) {
                expr* x = a->get_arg(i);
                expr* y = b->get_arg(i);
                todo.push_back({x, y});
            }
            bool failed = false;
            while (!todo.empty()) {
                auto [x, y] = todo.back();
                todo.pop_back();
                auto rx = m_reps[x];
                auto ry = m_reps[y];
                SASSERT(ry);
                if (rx == ry) 
                    continue;
                if (rx) {
                    failed = true;
                    break;
                }
                if (m_parents[x].size() > 1)
                    // a crude safey hatch to preserve models
                    // we could require that every parent of x
                    // has a pure representative which comes from a correspondnig
                    // parent of y
                    break;
                expr* s = nullptr;
                if (soln.find(x, s)) {
                    if (s != ry) {
                        failed = true;
                        break;
                    }
                    continue;
                }
                if (is_var(x)) {
                    soln.insert(x, ry);
                    continue;
                }
                if (!same_decl(x, y)) {
                    failed = true;
                    break;
                }
                app* ax = to_app(x);
                app* ay = to_app(y);
                for (unsigned i = 0; i < ax->get_num_args(); ++i) 
                    todo.push_back({ ax->get_arg(i), ay->get_arg(i) });
            }

            TRACE("qe", tout << "unification attempt\n";
                  for (auto [a, b] : todo)                 
                      tout << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n";
                  for (auto [key, value] : soln)
                      tout << mk_pp(key, m) << " -> " << mk_pp(value, m) << "\n";
                  );


            if (!failed && todo.empty() && !soln.empty()) {
                for (auto [key, value] : soln) {
                    vars.erase(to_app(key));
                    defs.push_back( { expr_ref(key, m), expr_ref(value, m) });
                }
                return true;
            }
        }
        return false;
    }


}
