/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_datatypes.cpp

Abstract:

    Simple projection function for algebraic datatypes.

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_functors.h"
#include "model/model_v2_pp.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "util/obj_pair_hashtable.h"
#include "qe/mbp/mbp_datatypes.h"

namespace mbp {
    
    struct datatype_project_plugin::imp  {
        ast_manager&              m;
        datatype_util             dt;
        app_ref                   m_val;
        scoped_ptr<contains_app>  m_var;
        
        imp(ast_manager& m):
            m(m), dt(m), m_val(m) {}
        
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            return lift_foreign(vars, lits);
        }

        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
            expr_ref val = model(var);
            SASSERT(is_app(val));
            TRACE("qe", tout << mk_pp(var, m) << " := " << val << "\n";);
            m_val = to_app(val);
            if (!dt.is_constructor(m_val)) {
                // assert: var does not occur in lits.
                return true;
            }
            m_var = alloc(contains_app, m, var);


            try {
                if (dt.is_recursive(var->get_sort())) {
                    project_rec(model, vars, lits);
                }
                else {
                    project_nonrec(model, vars, lits);
                }
            }
            catch (const cant_project &) {
                TRACE("qe", tout << "can't project:" << mk_pp(var, m) << "\n";);
                return false;
            }
            return true;
        }        
    
        void project_nonrec(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            expr_ref tmp(m), val(m);
            expr_ref_vector args(m);
            app_ref arg(m);
            SASSERT(dt.is_constructor(m_val));
            func_decl* f = m_val->get_decl();
            ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(f);
            for (unsigned i = 0; i < acc.size(); ++i) {
                auto str = acc[i]->get_name().str();
                arg = m.mk_fresh_const(str.c_str(), acc[i]->get_range());
                vars.push_back(arg);
                model.register_decl(arg->get_decl(), m_val->get_arg(i));
                args.push_back(arg);
            }
            val = m.mk_app(f, args.size(), args.data());
            TRACE("qe", tout << mk_pp(m_var->x(), m) << " |-> " << val << "\n";);
            reduce(val, lits);
        }

        void project_rec(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            expr_ref rhs(m);
            expr_ref_vector eqs(m);
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (solve(model, vars, lits[i].get(), rhs, eqs)) {
                    project_plugin::erase(lits, i);
                    reduce(rhs, lits);
                    lits.append(eqs);
                    return;
                }
            }

            // otherwise, unfold the constructor associated with m_var
            // once according to the model. In this way, selector-constructor
            // redexes are reduced and disequalities are eventually solved
            // by virtue of the constructors being different.
            project_nonrec(model, vars, lits);
        }

        void reduce(expr* val, expr_ref_vector& lits) {
            expr_safe_replace sub(m);
            th_rewriter rw(m);
            expr_ref tmp(m);
            sub.insert(m_var->x(), val);
            TRACE("qe", tout << mk_pp(m_var->x(), m) << " = " << mk_pp(val, m) << "\n";
                  tout << lits << "\n";);
            for (unsigned i = 0; i < lits.size(); ++i) {                
                sub(lits[i].get(), tmp);
                rw(tmp);
                lits[i] = tmp;
            }
        }

        bool contains_x(expr* e) {
            return (*m_var)(e);
        }

        bool solve(model& model, app_ref_vector& vars, expr* fml, expr_ref& t, expr_ref_vector& eqs) {
            expr* t1, *t2;
            if (m.is_eq(fml, t1, t2)) {
                if (contains_x(t1) && !contains_x(t2) && is_app(t1)) {
                    return solve(model, vars, to_app(t1), t2, t, eqs);
                }
                if (contains_x(t2) && !contains_x(t1) && is_app(t2)) {
                    return solve(model, vars, to_app(t2), t1, t, eqs);
                }
            }
            if (m.is_not(fml, t1) && m.is_distinct(t1)) {
                expr_ref eq = project_plugin::pick_equality(m, model, t1);
                return solve(model, vars, eq, t, eqs);
            }
            return false;
        }

        bool solve(model& model, app_ref_vector& vars, app* a, expr* b, expr_ref& t, expr_ref_vector& eqs) {
            SASSERT(contains_x(a));
            SASSERT(!contains_x(b));
            if (m_var->x() == a) {
                t = b;
                return true;
            }
            if (!dt.is_constructor(a)) {
                return false;
            }
            func_decl* c = a->get_decl();
            func_decl_ref rec(dt.get_constructor_is(c), m);
            ptr_vector<func_decl> const & acc = *dt.get_constructor_accessors(c);
            SASSERT(acc.size() == a->get_num_args());
            //
            // It suffices to solve just the first available equality.
            // The others are determined by the first.
            //
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr* l = a->get_arg(i);
                if (is_app(l) && contains_x(l)) {
                    expr_ref r(m);
                    r = access(c, i, acc, b);
                    if (solve(model, vars, to_app(l), r, t, eqs)) {
                        for (unsigned j = 0; j < c->get_arity(); ++j) {
                            if (i != j) {
                                eqs.push_back(m.mk_eq(access(c, j, acc, b), a->get_arg(j)));
                            }
                        }
                        if (!is_app_of(b, c)) {
                            eqs.push_back(m.mk_app(rec, b));
                        }

                        return true;
                    }
                }
            }
            return false;
        }


        expr* access(func_decl* c, unsigned i, ptr_vector<func_decl> const& acc, expr* e) {
            if (is_app_of(e,c)) {
                return to_app(e)->get_arg(i);
            }
            else {
                return m.mk_app(acc[i], e);
            }
        }

        bool lift_foreign(app_ref_vector const& vars, expr_ref_vector& lits) {

            bool reduced = false;
            expr_mark visited;
            expr_mark has_var;
            bool inserted = false;
            for (app* v : vars) {
                if (m.is_bool(v)) continue;
                if (dt.is_datatype(v->get_sort())) continue;
                inserted = true;
                has_var.mark(v);
                visited.mark(v);
            }
            if (inserted) {
                for (unsigned i = 0; i < lits.size(); ++i) {
                    expr* e = lits.get(i), *l, *r;
                    if (m.is_eq(e, l, r) && reduce_eq(visited, has_var, l, r, lits)) {
                        project_plugin::erase(lits, i);
                        reduced = true;
                    }
                }
                CTRACE("qe", reduced, tout << vars << "\n" << lits << "\n";);
            }
            return reduced;
        }

        bool reduce_eq(expr_mark& has_var, expr_mark& visited, expr* l, expr* r, expr_ref_vector& lits) {
            if (!is_app(l) || !is_app(r)) {
                return false;
            }
            bool reduce = false;
            if (dt.is_constructor(to_app(r)) && contains_foreign(has_var, visited, r)) {
                std::swap(l, r);
                reduce = true;
            }
            reduce |= dt.is_constructor(to_app(l)) && contains_foreign(has_var, visited, l);
            if (!reduce) {
                return false;
            }
            func_decl* c = to_app(l)->get_decl();
            ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(c);
            if (!is_app_of(r, c)) {
                lits.push_back(m.mk_app(dt.get_constructor_is(c), r));
            }
            for (unsigned i = 0; i < acc.size(); ++i) {
                lits.push_back(m.mk_eq(to_app(l)->get_arg(i), access(c, i, acc, r)));
            }
            return true;
        }


        ptr_vector<expr> todo;

        bool contains_foreign(expr_mark& has_var, expr_mark& visited, expr* e) {
            todo.push_back(e);
            while (!todo.empty()) {
                expr* _f = todo.back();
                if (visited.is_marked(_f)) {
                    todo.pop_back();
                    continue;
                }
                if (!is_app(_f)) {
                    visited.mark(_f);                   
                    todo.pop_back();
                    continue;
                }
                app* f = to_app(_f);
                bool has_new = false, has_v = false;
                for (expr* arg : *f) {
                    if (!visited.is_marked(arg)) {
                        todo.push_back(arg);
                        has_new = true;
                    }
                    else {
                        has_v |= has_var.is_marked(arg);
                    }
                }
                if (has_new) {
                    continue;
                }
                todo.pop_back();
                if (has_v) {
                    has_var.mark(f);
                }
                TRACE("qe", tout << "contains: " << mk_pp(f, m) << " " << has_var.is_marked(f) << "\n";);
                visited.mark(f);
            }
            TRACE("qe", tout << "contains: " << mk_pp(e, m) << " " << has_var.is_marked(e) << "\n";);
            return has_var.is_marked(e);
        }
        
    };
    
    datatype_project_plugin::datatype_project_plugin(ast_manager& m):
        project_plugin(m) {
        m_imp = alloc(imp, m);
    }
    
    datatype_project_plugin::~datatype_project_plugin() {
        dealloc(m_imp);
    }
    
    bool datatype_project_plugin::operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        return (*m_imp)(model, var, vars, lits);
    }

    bool datatype_project_plugin::solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return m_imp->solve(model, vars, lits);
    }

    vector<def> datatype_project_plugin::project(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return vector<def>();
    }

    void datatype_project_plugin::saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) {
        NOT_IMPLEMENTED_YET();
    }

    
    family_id datatype_project_plugin::get_family_id() {
        return m_imp->dt.get_family_id();
    }
    
}



