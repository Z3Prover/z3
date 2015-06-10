
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#include "qe.h"
#include "array_decl_plugin.h"
#include "expr_safe_replace.h"
#include "ast_pp.h"
#include "arith_decl_plugin.h"

namespace qe {
    // ---------------------
    // arrays

    class array_plugin : public qe_solver_plugin {

        expr_safe_replace m_replace;

    public:

        array_plugin(i_solver_context& ctx, ast_manager& m) : 
            qe_solver_plugin(m, m.mk_family_id("array"), ctx),
            m_replace(m)
        {
        }

        virtual ~array_plugin() {}

        
        virtual void assign(contains_app& x, expr* fml, rational const& vl) {
            UNREACHABLE();
        }
        
        virtual bool get_num_branches( contains_app& x, expr* fml, rational& num_branches) {
            return false;
        }
        
        virtual void subst(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) {
            UNREACHABLE();
        }
        

        virtual bool solve(conj_enum& conjs, expr* fml) {

            conj_enum::iterator it = conjs.begin(), end = conjs.end();
            for (; it != end; ++it) {
                expr* e = *it;
                if (m.is_eq(e) && solve_eq(to_app(e), fml)) {
                    return true;
                }
            }
            expr_ref_vector eqs(m);
            conjs.extract_equalities(eqs);
            for (unsigned i = 0; i < eqs.size(); ++i) {
                TRACE("qe_verbose", 
                      tout << mk_pp(eqs[i].get(), m) << "\n";);
                expr* e = eqs[i].get();
                if (solve_eq_zero(e, fml)) {
                    return true;
                }
            }
            return false;
        }

        virtual bool is_uninterpreted(app* f) {
            return true;
        }

           
    private:
        
        bool solve_eq(app* eq, expr* fml) {
            SASSERT(m.is_eq(eq));
            expr* arg1 = eq->get_arg(0);
            expr* arg2 = eq->get_arg(1);
            return solve_eq(arg1, arg2, fml) || solve_eq(arg2, arg1, fml);
        }

        bool solve_eq_zero(expr* e, expr* fml) {
            arith_util arith(m); 
            if (arith.is_add(e)) {
                app* a = to_app(e);
                expr* e1, *e2;
                unsigned sz = a->get_num_args();
                expr_ref_vector args(m);
                expr_ref lhs(m), rhs(m);
                rational r;
                args.append(sz, a->get_args());
                for (unsigned i = 0; i < sz; ++i) {
                    expr_ref save(m);
                    save = lhs = args[i].get();                    
                    args[i] = arith.mk_numeral(rational(0), m.get_sort(lhs));
                    rhs = arith.mk_uminus(arith.mk_add(args.size(), args.c_ptr()));
                    if (arith.is_mul(lhs, e1, e2) && 
                        arith.is_numeral(e1, r) &&
                        r.is_minus_one()) {
                        lhs = to_app(e2);
                        rhs = arith.mk_uminus(rhs);
                    }
                    if (solve_eq(lhs, rhs, fml)) {
                        return true;
                    }
                    args[i] = save;
                }
            }
            return false;
        }


        
        bool solve_eq(expr* lhs, expr* rhs, expr* fml) {
            
            if (!is_app(lhs)) {
                return false;
            }
            
            TRACE("qe_verbose", 
                  tout << mk_pp(lhs, m) << 
                  " == " << mk_pp(rhs, m) << "\n";);
            expr_ref tmp(m);
            app* a = to_app(lhs);
            //
            // A = t, A not in t.
            //
            unsigned idx = 0;
            if (m_ctx.is_var(a, idx) && 
                !m_ctx.contains(idx)(rhs)) {
                expr_ref result(fml, m);
                m_replace.apply_substitution(a, rhs, result);
                m_ctx.elim_var(idx, result, rhs);
                return true;
            }                 
            if (solve_store(a, rhs, fml)) {
                return true;
            }
            if (solve_select(a, rhs, fml)) {
                return true;
            }
            return false;
        }

        bool solve_select2(app* lhs, expr* rhs, expr* fml) {
            //
            // (select (select A i) j) = t, A not in i, j,  t
            // A |-> (store B' j (store B i t)), where B, B' are fresh.
            // 
            // TBD
            return false;
        }

        bool solve_select(app* lhs, expr* rhs, expr* fml) {
            //
            // (select A i) = t, A not in i, v, t
            // A |-> (store B i t), where B is fresh.
            // 
            unsigned idx = 0;
            vector<ptr_vector<expr> > args;
            if (is_select(lhs, idx, rhs, args) && args.size() == 1) {
                contains_app& contains_A = m_ctx.contains(idx);
                app* A = contains_A.x();
                app_ref B(m);
                expr_ref store_B_i_t(m);

                unsigned num_args = args[0].size();
                B = m.mk_fresh_const("B", m.get_sort(A));
                ptr_buffer<expr> args2;
                args2.push_back(B);
                for (unsigned i = 0; i < num_args; ++i) {
                    args2.push_back(args[0][i]);
                }
                args2.push_back(rhs);
                
                store_B_i_t = m.mk_app(m_fid, OP_STORE, args2.size(), args2.c_ptr());
                
                TRACE("qe", 
                      tout << "fml: " << mk_pp(fml, m) << "\n";
                      tout << "solved form: " << mk_pp(store_B_i_t, m) << "\n";
                      tout << "eq: " << mk_pp(lhs, m) << " == " << mk_pp(rhs, m) << "\n";
                      );
                expr_ref result(fml, m);
                m_replace.apply_substitution(A, store_B_i_t, result);
                m_ctx.add_var(B);
                m_ctx.elim_var(idx, result, store_B_i_t);
                return true;

            }
            return false;
        }

        bool is_array_app_of(app* a, unsigned& idx, expr* t, decl_kind k) {
            if (!is_app_of(a, m_fid, k)) {
                return false;
            }
            expr* v = a->get_arg(0);
            if (!m_ctx.is_var(v, idx)) {
                return false;
            }
            contains_app& contains_v = m_ctx.contains(idx);
            
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                if (contains_v(a->get_arg(i))) {
                    return false;
                }
            }        
            if (contains_v(t)) {
                return false;
            }
            return true;
        }


        bool solve_store(app* lhs, expr* rhs, expr* fml) {
            //
            // store(store(A, j, u), i, v) = t, A not in i, j, u, v, t
            // -> 
            // A |-> store(store(t, i, w), j, w') where w, w' are fresh.
            // t[i] = v
            // store(t, i, v)[j] = u
            //
            unsigned idx = 0;
            vector<ptr_vector<expr> > args;
            if (is_store_update(lhs, idx, rhs, args)) {
                contains_app& contains_A = m_ctx.contains(idx);
                app* A = contains_A.x();
                app_ref w(m);

                expr_ref store_t(rhs, m), store_T(rhs, m), select_t(m);
                ptr_vector<expr> args2;
                for (unsigned i = args.size(); i > 0; ) {
                    --i;
                    args2.reset();
                    w = m.mk_fresh_const("w", m.get_sort(args[i].back()));
                    args2.push_back(store_T);
                    args2.append(args[i]);
                    
                    select_t = m.mk_app(m_fid, OP_SELECT, args2.size()-1, args2.c_ptr());
                    fml = m.mk_and(fml, m.mk_eq(select_t, args2.back()));
                    store_T = m.mk_app(m_fid, OP_STORE, args2.size(), args2.c_ptr());

                    args2[0] = store_t;
                    args2.back() = w;
                    store_t = m.mk_app(m_fid, OP_STORE, args2.size(), args2.c_ptr());

                    m_ctx.add_var(w);
                }
                               
                TRACE("qe", 
                      tout << "Variable: " << mk_pp(A, m) << "\n";
                      tout << "fml: " << mk_pp(fml, m) << "\n";
                      tout << "solved form: " << mk_pp(store_t, m) << "\n";
                      tout << "eq: " << mk_pp(lhs, m) << " == " << mk_pp(rhs, m) << "\n";
                      );
                expr_ref result(fml, m);
                m_replace.apply_substitution(A, store_t, result);
                m_ctx.elim_var(idx, result, store_t);
                return true;
            }        
            return false;
        }

        bool is_array_app_of(app* a, unsigned& idx, expr* t, decl_kind k, vector<ptr_vector<expr> >& args) {
            if (m_ctx.is_var(a, idx)) {
                contains_app& contains_v = m_ctx.contains(idx);
                if (args.empty() || contains_v(t)) {
                    return false;
                }
                for (unsigned i = 0; i < args.size(); ++i) {
                    for (unsigned j = 0; j < args[i].size(); ++j) {
                        if (contains_v(args[i][j])) {
                            return false;
                        }
                    }
                }
                return true;
            }            
            if (!is_app_of(a, m_fid, k)) {
                return false;
            }
            args.push_back(ptr_vector<expr>());
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                args.back().push_back(a->get_arg(i));
            }
            if (!is_app(a->get_arg(0))) {
                return false;
            }
            return is_array_app_of(to_app(a->get_arg(0)), idx, t, k, args);
        }

        bool is_store_update(app* a, unsigned& idx, expr* t, vector<ptr_vector<expr> >& args) {
            return is_array_app_of(a, idx, t, OP_STORE, args);
        }
        
        bool is_select(app* a, unsigned& idx, expr* t, vector<ptr_vector<expr> >& args) {
            return is_array_app_of(a, idx, t, OP_SELECT, args);
        }
    };

    qe_solver_plugin* mk_array_plugin(i_solver_context& ctx) {
        return alloc(array_plugin, ctx, ctx.get_manager());
    }
    
}
