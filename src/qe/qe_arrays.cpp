/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_arrays.cpp

Abstract:

    Model based projection for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/


#include "qe_arrays.h"
#include "rewriter_def.h"
#include "expr_functors.h"
#include "expr_safe_replace.h"
#include "lbool.h"
#include "ast_util.h"
#include "ast_pp.h"

namespace qe {

    struct array_project_plugin::imp {

        // rewriter or direct procedure.
        struct rw_cfg : public default_rewriter_cfg {
            ast_manager&    m;
            array_util&     a;
            expr_ref_vector m_lits;
            model*          m_model; 
            imp*            m_imp;
            
            rw_cfg(ast_manager& m, array_util& a):
                m(m), a(a), m_lits(m), m_model(0) {}
            
            br_status reduce_app(func_decl* f, unsigned n, expr* const* args, expr_ref& result, proof_ref & pr) {
                if (a.is_select(f) && a.is_store(args[0])) {                    
                    expr_ref val1(m), val2(m); 
                    app* b = to_app(args[0]);
                    SASSERT(b->get_num_args() == n + 1);
                    for (unsigned i = 1; i < n; ++i) {
                        expr* arg1 = args[i];
                        expr* arg2 = b->get_arg(i);
                        if (arg1 == arg2) {
                            val1 = val2 = arg1;
                        }
                        else {
                            VERIFY(m_model->eval(arg1, val1));
                            VERIFY(m_model->eval(arg2, val2));
                        }
                        switch(compare(val1, val2)) {
                        case l_true:
                            if (arg1 != arg2) {
                                m_lits.push_back(m.mk_eq(arg1, arg2));
                            }
                            break;
                        case l_false: {
                            ptr_vector<expr> new_args;
                            if (i > 0) {
                                m_lits.resize(m_lits.size() - i);
                            }
                            m_lits.push_back(m.mk_not(m.mk_eq(arg1, arg2)));
                            new_args.push_back(b->get_arg(0));
                            new_args.append(n-1, args+1);
                            result = m.mk_app(f, n, new_args.c_ptr());
                            return BR_REWRITE1;
                        }
                        case l_undef:
                            return BR_FAILED;
                        }
                    }
                    result = b->get_arg(n);
                    return BR_DONE;
                }
                return BR_FAILED;
            }

            lbool compare(expr* x, expr* y) {
                NOT_IMPLEMENTED_YET();
                return l_undef;
            }
        };

        struct indices {
            expr_ref_vector m_values;
            expr* const*    m_vars;

            indices(ast_manager& m, model& model, unsigned n, expr* const* vars): 
                m_values(m), m_vars(vars) {
                expr_ref val(m);
                for (unsigned i = 0; i < n; ++i) {
                    VERIFY(model.eval(vars[i], val));
                    m_values.push_back(val);
                }
            }
        };
        
        ast_manager& m;
        array_util   a;
        scoped_ptr<contains_app> m_var;
        
        imp(ast_manager& m): m(m), a(m) {}
        ~imp() {}

        virtual bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            return false;
        }

        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {

            TRACE("qe", tout << mk_pp(var, m) << "\n" << lits;);
            m_var = alloc(contains_app, m, var);

            // reduce select-store redeces based on model.
            // rw_cfg rw(m);
            // rw(lits);

            // try first to solve for var.
            if (solve_eq(model, vars, lits)) {
                return true;
            } 

            app_ref_vector selects(m);

            // check that only non-select occurrences are in disequalities.
            if (!check_diseqs(lits, selects)) {
                TRACE("qe", tout << "Could not project " << mk_pp(var, m) << " for:\n" << lits << "\n";);
                return false;
            }

            // remove disequalities.
            elim_diseqs(lits);

            // Ackerman reduction on remaining select occurrences
            // either replace occurrences by model value or other node
            // that is congruent to model value.

            ackermanize_select(model, selects, vars, lits);
           
            TRACE("qe", tout << selects << "\n" << lits << "\n";);
            return true;
        }

        void ackermanize_select(model& model, app_ref_vector const& selects, app_ref_vector& vars, expr_ref_vector& lits) {
            expr_ref_vector vals(m), reps(m);
            expr_ref val(m);
            expr_safe_replace sub(m);

            if (selects.empty()) {
                return;
            }

            app_ref sel(m);
            for (unsigned i = 0; i < selects.size(); ++i) {                
                sel = m.mk_fresh_const("sel", m.get_sort(selects[i]));
                VERIFY (model.eval(selects[i], val));
                model.register_decl(sel->get_decl(), val);
                vals.push_back(to_app(val));
                reps.push_back(val);               // TODO: direct pass could handle nested selects.
                vars.push_back(sel);
                sub.insert(selects[i], val);
            }

            sub(lits);
            remove_true(lits);
            project_plugin::partition_args(model, selects, lits);
            project_plugin::partition_values(model, reps, lits);
        }

        void remove_true(expr_ref_vector& lits) {
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (m.is_true(lits[i].get())) {
                    project_plugin::erase(lits, i);
                }
            }            
        }

        bool contains_x(expr* e) {
            return (*m_var)(e);
        }

        void mk_eq(indices& x, indices y, expr_ref_vector& lits) {
            unsigned n = x.m_values.size();
            for (unsigned j = 0; j < n; ++j) {
                lits.push_back(m.mk_eq(x.m_vars[j], y.m_vars[j]));
            }
        }
        
        // check that x occurs only under selects or in disequalities.
        bool check_diseqs(expr_ref_vector const& lits, app_ref_vector& selects) {
            expr_mark mark;
            ptr_vector<app> todo;
            app* e;
            for (unsigned i = 0; i < lits.size(); ++i) {
                e = to_app(lits[i]);
                if (is_diseq_x(e)) {
                    continue;
                }
                if (contains_x(e)) {
                    todo.push_back(e);
                }
            }
            while (!todo.empty()) {
                e = todo.back();
                todo.pop_back();                    
                if (mark.is_marked(e)) {
                    continue;
                }
                mark.mark(e);
                if (m_var->x() == e) {
                    return false;
                }
                unsigned start = 0;
                if (a.is_select(e)) {
                    if (e->get_arg(0) == m_var->x()) {
                        start = 1;
                        selects.push_back(e);
                    } 
                }
                for (unsigned i = start; i < e->get_num_args(); ++i) {
                    todo.push_back(to_app(e->get_arg(i)));
                }
            }
            return true;
        }

        void elim_diseqs(expr_ref_vector& lits) {
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (is_diseq_x(lits[i].get())) {
                    project_plugin::erase(lits, i);
                }
            }
        }

        bool is_update_x(app* e) {
            do {
                if (m_var->x() == e) {
                    return true;
                }
                if (a.is_store(e) && contains_x(e->get_arg(0))) {
                    for (unsigned i = 1; i < e->get_num_args(); ++i) {
                        if (contains_x(e->get_arg(i))) {
                            return false;
                        }
                    }
                    e = to_app(e->get_arg(0));
                    continue;
                }
            }
            while (false);
            return false;
        }

        bool is_diseq_x(expr* e) {
            expr *f, * s, *t;
            if (m.is_not(e, f) && m.is_eq(f, s, t)) {
                if (contains_x(s) && !contains_x(t) && is_update_x(to_app(s))) return true;
                if (contains_x(t) && !contains_x(s) && is_update_x(to_app(t))) return true;
            }
            return false;
        }

        bool solve_eq(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
            // find an equality to solve for.
            expr* s, *t;
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (m.is_eq(lits[i].get(), s, t)) {
                    vector<indices> idxs;
                    expr_ref save(m), back(m);
                    save = lits[i].get();
                    back = lits.back();
                    lits[i] = back;
                    lits.pop_back();
                    unsigned sz = lits.size();
                    if (contains_x(s) && !contains_x(t) && is_app(s)) {
                        if (solve(model, to_app(s), t, idxs, vars, lits)) {
                            return true;
                        }
                    }
                    else if (contains_x(t) && !contains_x(s) && is_app(t)) {
                        if (solve(model, to_app(t), s, idxs, vars, lits)) {
                            return true;
                        }
                    }
                    // put back the equality literal.
                    lits.resize(sz);
                    lits.push_back(back);
                    lits[i] = save;
                }
                // TBD: not distinct?
            }
            return false;
        }

        bool solve(model& model, app* s, expr* t, vector<indices>& idxs, app_ref_vector& vars, expr_ref_vector& lits) {
            SASSERT(contains_x(s));
            SASSERT(!contains_x(t));

            if (s == m_var->x()) {
                expr_ref result(t, m);
                expr_ref_vector args(m);
                sort* range = get_array_range(m.get_sort(s));
                for (unsigned i = 0; i < idxs.size(); ++i) {
                    app_ref var(m), sel(m);
                    expr_ref val(m);
                    var = m.mk_fresh_const("value", range);
                    vars.push_back(var);
                    args.reset();
                    
                    args.push_back (s);
                    args.append(idxs[i].m_values.size(), idxs[i].m_vars);
                    sel = a.mk_select (args.size (), args.c_ptr ());
                    VERIFY (model.eval (sel, val));
                    model.register_decl (var->get_decl (), val);
                    
                    args[0] = result;
                    args.push_back(var);
                    result = a.mk_store(args.size(), args.c_ptr());
                }
                expr_safe_replace sub(m);
                sub.insert(s, result);
                for (unsigned i = 0; i < lits.size(); ++i) {
                    sub(lits[i].get(), result);
                    lits[i] = result;
                }
                return true;
            }

            if (a.is_store(s)) {
                unsigned n = s->get_num_args()-2;
                indices idx(m, model, n, s->get_args()+1);
                for (unsigned i = 1; i < n; ++i) {
                    if (contains_x(s->get_arg(i))) {
                        return false;
                    }
                } 
                unsigned i;
                expr_ref_vector args(m);
                switch (contains(idx, idxs, i)) {
                case l_true:
                    mk_eq(idx, idxs[i], lits);
                    return solve(model, to_app(s->get_arg(0)), t, idxs, vars, lits);
                case l_false:
                    for (unsigned i = 0; i < idxs.size(); ++i) {
                        expr_ref_vector eqs(m);
                        mk_eq(idx, idxs[i], eqs);
                        lits.push_back(m.mk_not(mk_and(eqs))); // TBD: extract single index of difference based on model.
                    }
                    args.push_back(t);
                    args.append(n, s->get_args()+1);
                    lits.push_back(m.mk_eq(a.mk_select(args.size(), args.c_ptr()), s->get_arg(n+1)));
                    idxs.push_back(idx);
                    return solve(model, to_app(s->get_arg(0)), t, idxs, vars, lits);
                case l_undef:
                    return false;
                }                
            }
            return false;
        }

        lbool contains(indices const& idx, vector<indices> const& idxs, unsigned& j) {
            for (unsigned i = 0; i < idxs.size(); ++i) {
                switch (compare(idx, idxs[i])) {
                case l_true: 
                    j = i;
                    return l_true;
                case l_false:
                    break;
                case l_undef:
                    return l_undef;                
                }
            }
            return l_false;
        }

        lbool compare(indices const& idx1, indices const& idx2) {
            unsigned n = idx1.m_values.size();
            for (unsigned i = 0; i < n; ++i) {
                switch (compare(idx1.m_values[i], idx2.m_values[i])) {
                case l_true:
                    break;
                case l_false:
                    return l_false;
                case l_undef:
                    return l_undef;
                }
            }
            return l_true;
        }

        lbool compare(expr* val1, expr* val2) {
            if (m.are_equal (val1, val2)) return l_true;
            if (m.are_distinct (val1, val2)) return l_false;
            
            if (is_uninterp(val1) ||
                is_uninterp(val2)) {
                // TBD chase definition of nested array.
                return l_undef;
            }
            return l_undef;
        }            
    };
    
    
    array_project_plugin::array_project_plugin(ast_manager& m) {
        m_imp = alloc(imp, m);
    }
    
    array_project_plugin::~array_project_plugin() {
        dealloc(m_imp);
    }
    
    bool array_project_plugin::operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) {
        return (*m_imp)(model, var, vars, lits);
    }

    bool array_project_plugin::solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) {
        return m_imp->solve(model, vars, lits);
    }
    
    family_id array_project_plugin::get_family_id() {
        return m_imp->a.get_family_id();
    }

};

