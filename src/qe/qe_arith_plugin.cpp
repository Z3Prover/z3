/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    arith_plugin.cpp

Abstract:

    Eliminate Arithmetical variable from formula

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:


--*/

#include "qe.h"
#include "ast_pp.h"
#include "expr_safe_replace.h"
#include "bool_rewriter.h"
#include "bv_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "arith_eq_solver.h"
#include "arith_rewriter.h"
#include "th_rewriter.h"
#include "factor_rewriter.h"
#include "obj_pair_hashtable.h"
#include "nlarith_util.h"
#include "model_evaluator.h"
#include "smt_kernel.h"

namespace qe {

    class bound {        
        rational   m_coeff;
        expr_ref  m_term;
        bool      m_is_strict;
    public:
        bound(ast_manager& m, rational const& n, expr* t, bool is_strict) : m_coeff(n), m_term(t, m), m_is_strict(is_strict) { 
        }
        bool  is_strict() const { return m_is_strict; }
        expr* term() const { return m_term.get(); }
        rational const& coeff() const { return m_coeff; }
        
        void update(rational const& k, expr* t) {
            m_coeff = k;
            m_term = t;
        }
        
        void pp(std::ostream& out, app* x) {
            ast_manager& m = m_term.get_manager();
            out << "(<= (+ (* " << coeff() << " " << mk_pp(x, m)
                << ") " << mk_pp(term(), m) << ") 0)";
        }
    };

    typedef rational numeral;

    // m_k | (m_a * x + m_term)
    class div_constraint {        
        numeral  m_k;
        numeral  m_a;
        expr*    m_term;
    public:
        div_constraint(numeral const& k, numeral const& a, expr* t):
            m_k(k), m_a(a), m_term(t) {}
        numeral const& a() const { return m_a; }
        numeral const& k() const { return m_k; }
        expr*         t() const { return m_term; }
        numeral&   a_ref() { return m_a; }
        numeral&   k_ref() { return m_k; }
        expr*&     t_ref() { return m_term; }
    };
    typedef vector<div_constraint> div_constraints;

    class arith_qe_util {
        ast_manager&      m;
        i_solver_context& m_ctx;
    public:
        arith_util        m_arith; // initialize before m_zero_i, etc.
        th_rewriter       simplify;
    private:
        arith_eq_solver   m_arith_solver;
        bv_util           m_bv;

        expr_ref     m_zero_i;
        expr_ref     m_one_i;
        expr_ref     m_minus_one_i;
        expr_ref     m_zero_r;
        expr_ref     m_one_r;
        expr_ref     m_tmp;
    public: 
        expr_safe_replace          m_replace;
        
        bool_rewriter              m_bool_rewriter;
        arith_rewriter             m_arith_rewriter;

        arith_qe_util(ast_manager& m, smt_params& p, i_solver_context& ctx) : 
            m(m), 
            m_ctx(ctx),
            m_arith(m),
            simplify(m),
            m_arith_solver(m),
            m_bv(m),
            m_zero_i(m_arith.mk_numeral(numeral(0), true), m),
            m_one_i(m_arith.mk_numeral(numeral(1), true), m),
            m_minus_one_i(m_arith.mk_numeral(numeral(-1), true), m),
            m_zero_r(m_arith.mk_numeral(numeral(0), false), m),
            m_one_r(m_arith.mk_numeral(numeral(1), false), m),
            m_tmp(m), 
            m_replace(m),
            m_bool_rewriter(m),
            m_arith_rewriter(m) {
        }

        ast_manager& get_manager() { return m; }
        
        //
        // match e := k*x + rest, where k != 0.
        // 
        bool get_coeff(contains_app& contains_x, expr* p, rational& k, expr_ref& rest) {
            app* x = contains_x.x();
            ptr_vector<expr> restl, todo;
            todo.push_back(p);
            bool found = false;
            expr* e1, *e2;
            while (!todo.empty()) {
                expr* e = todo.back();
                todo.pop_back();
                if (m_arith.is_add(e)) {
                    for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
                        todo.push_back(to_app(e)->get_arg(i));
                    }
                }
                else if (e == x) {
                    k = numeral(1);
                    found = true;
                    break;
                }
                else if (m_arith.is_mul(e, e1, e2) && 
                         e1 == x &&
                         m_arith.is_numeral(e2, k)) {
                    found = true;
                    break;
                }
                else if (m_arith.is_mul(e, e1, e2) && 
                         e2 == x &&
                         m_arith.is_numeral(e1, k)) {
                    found = true;
                    break;
                }
                else {
                    restl.push_back(e);
                }
            }
            if (!found) {
                TRACE("qe_verbose", 
                      tout 
                      << "Did not find: " 
                      << mk_pp(x, m) << " in " 
                      << mk_pp(p, m) << "\n";
                      );

                return false;
            }

            while (!todo.empty()) {
                restl.push_back(todo.back());
                todo.pop_back();
            }
            if (restl.empty()) {
                rest = mk_zero(x);
            }
            else {
                rest = m_arith.mk_add(restl.size(), restl.c_ptr());
            }
            if (contains_x(rest)) {
                return false;
            }
            TRACE("qe_verbose", 
                  tout 
                  << mk_pp(p, m) << " = " 
                  << "(+ (* " << k << " "
                  << mk_pp(x, m) << ") "
                  << mk_pp(rest, m) << ")\n";
                  );
            return true;
        }

        //
        // match p := k + rest
        // where k is a numeral and rest does not contain numerals.
        //
        void get_const(expr* p, rational& k, expr_ref& rest) {
            ptr_vector<expr> todo, restl;
            todo.push_back(p);
            k = numeral(0);
            while(!todo.empty()) {
                p = todo.back();
                todo.pop_back();
                if (m_arith.is_add(p)) {
                    for (unsigned i = 0; i < to_app(p)->get_num_args(); ++i) {
                        todo.push_back(to_app(p)->get_arg(i));
                    }
                }
                else if (m_arith.is_numeral(p, k)) {
                    break;
                }
                else {
                    restl.push_back(p);
                }
            }
            while (!todo.empty()) {
                restl.push_back(todo.back());
                todo.pop_back();
            }
            if (restl.empty()) {        
                rest = mk_zero(p);
            }
            else {
                rest = m_arith.mk_add(restl.size(), restl.c_ptr());
            }
        }

        //
        // match (not ne)
        bool is_neg(app* e, expr_ref& ne) {
            if (m.is_not(e)) {
                ne = to_app(e)->get_arg(0);
                return true;
            }
            return false;
        }

        bool is_le(app* e, expr_ref& p) {
            return is_le_ge_core<1>(e, p);
        }
 
        bool is_ge(app* e, expr_ref& p) {
            return is_le_ge_core<0>(e, p);
        }
                
        // match e = p < 0 or p > 0
        bool is_lt(app* e, expr_ref& p) {
            numeral   k;        
            expr* a1, *a2;

            if (m_arith.is_lt(e, a1, a2) || m_arith.is_gt(e, a2, a1)) {
                p = a1;
                if (m_arith.is_numeral(a2, k) && k.is_zero()) {
                    return true;
                }
            }
            else {
                return false;
            }
            p = mk_sub(p, a2);
            simplify(p);
            return true;
        }

        // 
        // match 0 == p mod k, p mod k == 0
        //
        bool is_divides(app* e, numeral& k, expr_ref& p) {
            expr* e1, *e2;
            if (!m.is_eq(e, e1, e2)) {
                return false;
            }
            return is_divides(e1, e2, k, p) || is_divides(e2, e1, k, p);
        }
    
        bool is_divides(expr* e1, expr* e2, numeral& k, expr_ref& p) {  
            if (m_arith.is_mod(e2) && 
                m_arith.is_numeral(e1, k) && 
                k.is_zero() &&
                m_arith.is_numeral(to_app(e2)->get_arg(1), k)) {
                p = to_app(e2)->get_arg(0);
                return true;
            }
            return false;
        }

        bool is_not_divides(app* e, app_ref& n, numeral& k, expr_ref& p) {
            if (!m.is_not(e)) {
                return false;
            }
            if (!is_app(to_app(e)->get_arg(0))) {
                return false;
            }
            n = to_app(to_app(e)->get_arg(0));
            return is_divides(n, k, p);
        }


        bool is_real(app* x) const { return m_arith.is_real(x); }

        //
        // b*t <= a*s  
        //
        
        template<bool is_strict>
        void mk_bound_aux(rational const& a, expr* t, rational const& b, expr* s, expr_ref& result) {
            SASSERT(a.is_neg() == b.is_neg());
            expr_ref tt(t, m), ss(s, m), e(m);
            // hack to fix wierd gcc compilation error
            rational abs_a(a);
            rational abs_b(b);
            if (abs_a.is_neg()) abs_a.neg();
            if (abs_b.is_neg()) abs_b.neg();
            ss = mk_mul(abs_a, ss);
            tt = mk_mul(abs_b, tt);
            if(a.is_neg()) {
                e = mk_sub(tt, ss);
                if (is_strict) {
                    if (m_arith.is_int(e)) {
                        e = mk_add(e, m_one_i);
                        mk_le(e, result);
                    }
                    else {
                        mk_lt(e, result);
                    }
                }
                else {
                    mk_le(e, result);
                }
            }
            else {
                e = mk_sub(ss, tt);
                if (is_strict) {
                    if (m_arith.is_int(e)) {
                        e = mk_add(e, m_one_i);
                        mk_le(e, result);
                    }
                    else {
                        mk_lt(e, result);
                    }
                }
                else {
                    mk_le(e, result);
                }
            }
        }
        
        void mk_bound(rational const& a, expr* t, rational const& b, expr* s, expr_ref& result) {
            mk_bound_aux<false>(a, t, b, s, result);
        }
        
        void mk_strict_bound(rational const& a, expr* t, rational const& b, expr* s, expr_ref& result) {
            mk_bound_aux<true>(a, t, b, s, result);
        }

        void mk_divides(numeral n, expr* e, expr_ref& result) {
            SASSERT(n.is_int());
            expr_ref tmp1(e, m), tmp2(m);
            simplify(tmp1);
            m_arith_rewriter.mk_mod(tmp1, mk_numeral(n), tmp2);
            m_bool_rewriter.mk_eq(m_zero_i, tmp2, result);
        }

        void mk_div(expr* a, numeral const & k, expr_ref& result) {
            result = m_arith.mk_div(a, m_arith.mk_numeral(k, false));
            simplify(result);
        }

        expr* mk_numeral(numeral const& k, bool is_int = true) { return m_arith.mk_numeral(k, is_int); }

        expr* mk_numeral(int k, bool is_int) { return mk_numeral(numeral(k),is_int); }

        expr* mk_uminus(expr* e) {
            return m_arith.mk_uminus(e);
        }

        expr* mk_abs(expr* e) {
            rational val;
            if (m_arith.is_numeral(e, val)) {
                if (val.is_neg()) {
                    return m_arith.mk_uminus(e);
                }
                else {
                    return e;
                }
            }
            else {
                return m.mk_ite(m_arith.mk_le(mk_zero(e), e), e, m_arith.mk_uminus(e));
            }
        }

        template<bool is_max>
        expr_ref mk_min_max(unsigned num_args, expr* const* args) {
            SASSERT(num_args > 0);
            if (num_args == 1) {
                return expr_ref(args[0], m);
            }
            else {
                expr_ref e2 = mk_min_max<is_max>(num_args-1,args+1);
                expr* e1 = args[0];
                expr* cmp = is_max?m_arith.mk_le(e1, e2):m_arith.mk_le(e2, e1);
                return expr_ref(m.mk_ite(cmp, e2, e1), m);
            }
        }

        expr_ref mk_max(unsigned num_args, expr* const* args) {
            return mk_min_max<true>(num_args, args);
        }

        expr_ref mk_min(unsigned num_args, expr* const* args) {
            return mk_min_max<false>(num_args, args);
        }

        expr* mk_mul(expr* a, expr* b) { return m_arith.mk_mul(a,b); }

        expr* mk_add(expr* a, expr* b) { return m_arith.mk_add(a,b); }

        expr* mk_sub(expr* a, expr* b) { return m_arith.mk_sub(a,b); }

        expr* mk_mul(numeral const& a, expr* b) { 
            if (a.is_one()) return b;
            return m_arith.mk_mul(mk_numeral(a, m_arith.is_int(b)),b); 
        }

        expr* mk_zero(sort* s) { return m_arith.is_int(s)?m_zero_i:m_zero_r; }

        expr* mk_zero(expr* e) { return m_arith.is_int(e)?m_zero_i:m_zero_r; }
        
        expr* mk_one(sort* s) { return m_arith.is_int(s)?m_one_i:m_one_r; }
        
        expr* mk_one(expr* e) { return m_arith.is_int(e)?m_one_i:m_one_r; }

        void mk_le(expr* e, expr_ref& result) {
            expr_ref tmp(e, m);
            simplify(tmp);
            m_arith_rewriter.mk_le(tmp, mk_zero(e), result);
        }

        void mk_lt(expr* e, expr_ref& result) {
            rational r;
            if (m_arith.is_numeral(e, r)) {
                if (r.is_neg()) {
                    result = m.mk_true();
                }
                else {
                    result = m.mk_false();
                }
            }
            else if (m_arith.is_int(e)) {
                result = m_arith.mk_le(e, m_minus_one_i);
            }
            else {
                result = m.mk_not(m_arith.mk_le(mk_zero(e), e));
            }
            simplify(result);
            TRACE("qe_verbose", tout << "mk_lt " << mk_pp(result, m) << "\n";);
        }

        // ax + t = 0
        void mk_eq(rational const& a, app* x, expr* t, expr_ref& result) {
            result = m_arith.mk_eq(mk_add(mk_mul(a, x), t), mk_zero(x));
        }

        void mk_and(unsigned sz, expr*const* args, expr_ref& result) {
            m_bool_rewriter.mk_and(sz, args, result);
        }
        
        void mk_and(expr* e1, expr* e2, expr_ref& result) {
            m_bool_rewriter.mk_and(e1, e2, result);
        }

        void add_and(expr* e, ptr_vector<expr>& conjs) {
            if (m.is_and(e)) {
                conjs.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            }
            else {
                conjs.push_back(e);
            }
        }

        void mk_flat_and(expr* e1, expr* e2, expr_ref& result) {
            ptr_vector<expr> conjs;
            add_and(e1, conjs);
            add_and(e2, conjs);
            m_bool_rewriter.mk_and(conjs.size(), conjs.c_ptr(), result);
        }
        
        void mk_or(unsigned sz, expr*const* args, expr_ref& result) {
            m_bool_rewriter.mk_or(sz, args, result);
        }
        
        void mk_or(expr* e1, expr* e2, expr_ref& result) {
            m_bool_rewriter.mk_or(e1, e2, result);
        }

        //
        // b*t <= a*s
        // 
        void mk_resolve(app* x, bool is_strict, rational const& a, expr* t, rational const& b, expr* s, expr_ref& result) {
            rational abs_a(abs(a)), abs_b(abs(b));
            SASSERT(a.is_neg() == b.is_pos());
            SASSERT(!is_strict || (abs_a.is_one() && abs_b.is_one()));
            
            expr_ref bt(mk_mul(abs_b, t), m);
            expr_ref as(mk_mul(abs_a, s), m);
            expr_ref as_bt(mk_add(as, bt), m);
            
            if(is_strict) {
                mk_lt(as_bt, result);
            }
            else {
                mk_le(as_bt, result);
            }
            
            if (!abs_a.is_one() && !abs_b.is_one()) {
                // integer resolution case.            
                SASSERT(!is_strict);
                SASSERT(abs_a > rational::one() && abs_b > rational::one());
                expr_ref slack(mk_numeral((abs_a-numeral(1))*(abs_b-numeral(1)), true), m);
                expr_ref result1(m), result2(m);
                
                // a*s + b*t <= 0
                expr_ref as_bt_le_0(result, m), tmp2(m), asz_bt_le_0(m), tmp3(m), tmp4(m);
                expr_ref b_divides_sz(m);
                
                // a*s + b*t + (a-1)(b-1) <= 0
                tmp2 = m_arith.mk_add(as_bt, slack);
                mk_le(tmp2, result1);
                
                rational a1 = a, b1 = b;
                if (abs_a < abs_b) {
                    std::swap(abs_a, abs_b);
                    std::swap(a1, b1);
                    std::swap(s, t);
                    std::swap(as, bt);
                }
                SASSERT(abs_a >= abs_b);
                
                // create finite disjunction for |b|.                                
                //    exists x, z in [0 .. |b|-2] . b*x + s + z = 0 && ax + t <= 0 && bx + s <= 0
                // <=> 
                //    exists x, z in [0 .. |b|-2] . b*x = -z - s && ax + t <= 0 && bx + s <= 0
                // <=>
                //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && bx + s <= 0
                // <=>
                //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && -z - s + s <= 0
                // <=>
                //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0 && -z <= 0
                // <=>
                //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a|b|x + |b|t <= 0
                // <=>
                //    exists x, z in [0 .. |b|-2] . b*x = -z - s && a*n_sign(b)(s + z) + |b|t <= 0
                // <=>
                //    exists z in [0 .. |b|-2] . |b| | (z + s) && a*n_sign(b)(s + z) + |b|t <= 0
                //
                
                expr_ref sz(mk_add(s, x), m);
                
                if (b1.is_pos()) {
                    sz = m_arith.mk_uminus(sz);
                }
                tmp4 = mk_add(mk_mul(a1, sz), bt);
                mk_le(tmp4, asz_bt_le_0);

                if (to_app(asz_bt_le_0)->get_arg(0) == x &&
                    m_arith.is_zero(to_app(asz_bt_le_0)->get_arg(1))) {
                    //    exists z in [0 .. |b|-2] . |b| | (z + s) && z <= 0
                    // <=>
                    //    |b| | s 
                    mk_divides(abs_b, s, tmp2);
                }
                else {
                    mk_divides(abs_b, sz, b_divides_sz);
                    mk_and(b_divides_sz, asz_bt_le_0, tmp4);
                    mk_big_or(abs_b - numeral(2), x, tmp4, tmp2);                  
                    TRACE("qe",
                          tout << "b | s + z: " << mk_pp(b_divides_sz, m) << "\n";
                          tout << "a(s+z) + bt <= 0: " << mk_pp(asz_bt_le_0, m) << "\n";
                          );                   
                }
                mk_flat_and(as_bt_le_0, tmp2, result2); 
                mk_or(result1, result2, result);
                simplify(result);


                //    a*s + b*t + (a-1)(b-1) <= 0 
                // or exists z in [0 .. |b|-2] . |b| | (z + s) && a*n_sign(b)(s + z) + |b|t <= 0
            }
            
            TRACE("qe", 
                  {
                      tout << (is_strict?"strict":"non-strict") << "\n";
                      bound(m, a, t, false).pp(tout, x);
                      tout << "\n";
                      bound(m, b, s, false).pp(tout, x);
                      tout << "\n";
                      tout << mk_pp(result, m) << "\n";
                  });            
        }
        
        struct mul_lt {
            arith_util& u;
            mul_lt(arith_qe_util& u): u(u.m_arith) {}
            bool operator()(expr* n1, expr* n2) const {
                
                expr* x, *y;
                if (u.is_mul(n1, x, y) && u.is_numeral(x)) {
                    n1 = y;
                }
                if (u.is_mul(n2, x, y) && u.is_numeral(x)) {
                    n2 = y;
                }
                return n1->get_id() < n2->get_id();
            }
        };

        void normalize_sum(expr_ref& p) {
            simplify(p);
            if (!m_arith.is_add(p)) {
                return;
            }
            unsigned sz = to_app(p)->get_num_args();
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < sz; ++i) {
                args.push_back(to_app(p)->get_arg(i));
            }
            std::sort(args.begin(), args.end(), mul_lt(*this));
            p = m_arith.mk_add(args.size(), args.c_ptr());
        }

        void pp_div(std::ostream& out, app* x, div_constraint const& div) {
            out << div.k() << " | (" << div.a() << "*" << mk_pp(x, m) 
                << " + " << mk_pp(div.t(), m) << ") ";
        }
        
        void pp_divs(std::ostream& out, app* x, div_constraints const& divs) {
            for (unsigned i = 0; i < divs.size(); ++i) {
                pp_div(out, x, divs[i]);
                out << " ";
            }
        }

        bool mk_atom(expr* e, bool p, expr_ref& result) {
            // retain equalities.
            if (!is_app(e)) {
                return false;
            }
            app* a = to_app(e);

            expr_ref t1(m), t2(m);
            expr_ref tmp1(m), tmp2(m);
            rational k;
            expr* a0, *a1;

            if (p && is_divides(a, k, tmp1)) {
                result = e;
            }
            else if (!p && is_divides(a, k, tmp1)) {
                m_bool_rewriter.mk_not(e, result);
            }
            else if (p && m.is_eq(e, a0, a1) && is_arith(a0)) {
                t1 = mk_sub(a0, a1);                                
                simplify(t1);
                t2 = mk_sub(a1, a0);
                simplify(t2);
                mk_le(t1, tmp1);  
                mk_le(t2, tmp2);  
                mk_and(tmp1, tmp2, result);
            }
            else if (!p && m.is_eq(e, a0, a1) && m_arith.is_int(a0)) {
                tmp1 = mk_sub(a0, a1);                                
                t1 = mk_add(mk_one(a0), tmp1);
                simplify(t1);
                t2 = mk_sub(mk_one(a0), tmp1);
                simplify(t2);
                mk_le(t1, tmp1);  // a0 < a1 <=> 1 + a0 - a1 <= 0
                mk_le(t2, tmp2);  // a0 > a1 <=> 1 - a0 + a1 <= 0 
                mk_or(tmp1, tmp2, result);
            }
            else if (!p && m.is_eq(e, a0, a1) && m_arith.is_real(a0)) {
                t1 = mk_sub(a0, a1);                                
                simplify(t1);
                t2 = mk_sub(a1, a0);
                simplify(t2);
                mk_lt(t1, tmp1); 
                mk_lt(t2, tmp2);  
                mk_or(tmp1, tmp2, result);
            }
            else if (!p && (m_arith.is_le(e, a0, a1) || m_arith.is_ge(e, a1, a0))) {
                tmp1 = mk_sub(a1, a0);                                
                mk_lt(tmp1, result);
            }
            else if (p && (m_arith.is_le(e) || m_arith.is_ge(e))) {
                result = e;
            }
            else if (p && (m_arith.is_lt(e, a0, a1) || m_arith.is_gt(e, a1, a0))) {
                tmp1 = mk_sub(a0, a1);
                mk_lt(tmp1, result);
            }
            else if (!p && (m_arith.is_lt(e, a0, a1) || m_arith.is_gt(e, a1, a0))) {
                tmp1 = mk_sub(a1, a0);
                mk_le(tmp1, result);
            }
            else {
                return false;
            }
            TRACE("qe_verbose", tout << "Atom: " << mk_pp(result, m) << "\n";);
            return true;
        }

        void mk_bounded_var(rational const& n, app_ref& z_bv, app_ref& z) {
            rational two(2), b(n);
            unsigned sz = 0;
            do {
                ++sz;
                b = div(b, two);
            }
            while (b.is_pos());
            sort* s = m_bv.mk_sort(sz);
            z_bv = m.mk_fresh_const("z", s);
            expr_ref tmp(m);
            z = m_bv.mk_bv2int(z_bv);
        }

        bool solve(conj_enum& conjs, expr* fml) {
            expr_ref_vector eqs(m);
            extract_equalities(conjs, eqs);
            return reduce_equations(eqs.size(), eqs.c_ptr(), fml);
        }

        // ----------------------------------------------------------------------
        // 
        // Equation solving features.
        //
        // Extract equalities from current goal.
        // 
        void extract_equalities(conj_enum& conjs, expr_ref_vector& eqs) { 
            obj_hashtable<expr> leqs;
            expr_ref_vector trail(m);
            expr_ref tmp1(m), tmp2(m);
            expr *a0, *a1;
            eqs.reset();
            conj_enum::iterator it = conjs.begin(), end = conjs.end();
            for (; it != end; ++it) {
                expr* e = *it;
                bool is_leq = false;
                
                if (m.is_eq(e, a0, a1) && is_arith(a0)) {
                    m_arith_rewriter.mk_sub(a0, a1, tmp1);
                    simplify(tmp1);
                    eqs.push_back(tmp1);
                }
                else if (m_arith.is_le(e, a0, a1) || m_arith.is_ge(e, a1, a0)) {
                    m_arith_rewriter.mk_sub(a0, a1, tmp1);
                    is_leq = true;
                }
                else {
                    // drop equality.
                }
                
                if (is_leq) {
                    normalize_sum(tmp1);
                    tmp2 = m_arith.mk_uminus(tmp1);
                    normalize_sum(tmp2);
                    if (leqs.contains(tmp2)) {
                        eqs.push_back(tmp1);
                        TRACE("qe", tout << "found:  " << mk_pp(tmp1, m) << "\n";);
                    }
                    else {
                        trail.push_back(tmp1);
                        leqs.insert(tmp1);
                        TRACE("qe_verbose", tout << "insert: " << mk_pp(tmp1, m) << "\n";);
                    }
                }
            }
        }


    private:

        //
        // match p <= 0 or p >= 0
        //
        template<unsigned IS_LE>
        bool is_le_ge_core(app* e, expr_ref& p) { 
            numeral   k;        
            expr_ref  tmp(m);
            expr* a2;

            if (m_arith.is_le(e)) {
                p = e->get_arg(1-IS_LE);
                a2 = e->get_arg(IS_LE);
                if (m_arith.is_numeral(a2, k) && k.is_zero()) {
                    return true;
                }
            }
            else if (m_arith.is_ge(e)) {
                p = e->get_arg(IS_LE);
                a2 = e->get_arg(1-IS_LE);
                if (m_arith.is_numeral(a2, k) && k.is_zero()) {
                    return true;
                }
            }
            else {
                return false;
            }
            p = mk_sub(p, a2);
            simplify(p);
            return true;
        }

        bool is_arith(expr* e) {
            return m_arith.is_int(e) || m_arith.is_real(e);
        }

        void mk_big_or(numeral up, app* x, expr* body, expr_ref& result) {
            TRACE("qe", tout << mk_pp(x, m) << " " << mk_pp(body, m) << "\n";);
            if (numeral(1) >= up) {
                mk_big_or_blast(up, x, body, result);
            }
            else {
                mk_big_or_symbolic_blast(up, x, body, result);
            }
        }
    
        void mk_big_or_blast(numeral up, app* x, expr* body, expr_ref& result) {        
            expr_ref_vector ors(m);
            numeral index(0);
            while (index <= up) {
                expr* n = mk_numeral(index);
                result = body;
                m_replace.apply_substitution(x, n, result);
                ors.push_back(result);
                ++index;
            }
            mk_or(ors.size(), ors.c_ptr(), result);
            TRACE("qe", 
                  tout 
                  << "[0 " << up << "] " 
                  << mk_pp(x, m) << "\n" 
                  << mk_pp(body, m) << "\n" 
                  << mk_pp(result, m) << "\n";);
        }

        void mk_big_or_symbolic(numeral up, app* x, expr* body, expr_ref& result) {
            app_ref z_bv(m);
            mk_big_or_symbolic(up, x, body, z_bv, result);
            m_ctx.add_var(z_bv);
        }        

        void mk_big_or_symbolic_blast(numeral up, app* x, expr* body, expr_ref& result) {
            app_ref z_bv(m);
            mk_big_or_symbolic(up, x, body, z_bv, result);
            m_ctx.blast_or(z_bv, result);
        }

        void mk_big_or_symbolic(numeral up, app* x, expr* body, app_ref& z_bv, expr_ref& result) {
            expr* e1 = m_arith.mk_le(x, m_arith.mk_numeral(up, true));
            mk_flat_and(e1, body, result);
            app_ref z(m);
            mk_bounded_var(up, z_bv, z);
            m_replace.apply_substitution(x, z, result);
        }        





        //
        // Determine if 'x' can be isolated.
        // Return the coefficient if found.
        //
        bool isolate_x(expr* p, app* x, contains_app& contains_x, numeral& coeff) {
            numeral k;
            
            while (m_arith.is_add(p)) {
                bool found_x = false;
                expr* next_p = 0;
                for (unsigned i = 0; i < to_app(p)->get_num_args(); ++i) {
                    expr* arg = to_app(p)->get_arg(i);
                    if (contains_x(arg)) {
                        if (found_x) {
                            return false;
                        }
                        found_x = true;
                        next_p = arg;
                    }
                }
                if (!next_p) {
                    return false;
                }
                p = next_p;
            }
            
            expr *e1, *e2;
            if (p == x) {
                coeff = numeral(1);
                return true;
            }
            else if (m_arith.is_mul(p, e1, e2) &&
                     m_arith.is_numeral(e1, k) &&
                     e2 == x) {
                coeff = k;
                return true;
            }
            else if (m_arith.is_mul(p, e1, e2) &&
                     m_arith.is_numeral(e2, k) &&
                     e1 == x) {
                coeff = k;
                return true;
            }
            return false;        
        }

        //
        // Reduce equations.
        // Singular equations eliminate variables directly.
        // Linear equations eliminate original variables and introduce auxiliary variables.
        // 
        
        bool reduce_equations(unsigned num_eqs, expr * const* eqs, expr* fml) {
            for (unsigned i = 0; i < num_eqs; ++i) {
                if (reduce_equation(eqs[i], fml)) {
                    return true;
                }
            }
            return false;
        }

        bool solve_singular(unsigned var_idx, expr* p, expr* fml) {
            rational k;
            expr_ref e(m), tmp(m);

            app* x = m_ctx.get_var(var_idx);

            if (!isolate_x(p, x, m_ctx.contains(var_idx), k)) {
                return false;
            }
            if (m_arith.is_int(x) && !(abs(k).is_one())) {
                return false;
            }

            if (abs(k).is_one()) {
                if (k.is_neg()) {
                    e = m_arith.mk_add(p, x);
                }
                else {
                    e = m_arith.mk_sub(x, p);
                }
            }
            else {
                SASSERT(!m_arith.is_int(x));
                //    p = p' + k*x = 0
                // <=>
                //    -k*x = p' = p - k*x
                // =>
                //    x = (p - k*x)/ -k
                expr* ke = m_arith.mk_numeral(-k, false);
                tmp = m_arith.mk_mul(ke, x);
                tmp = m_arith.mk_add(p, tmp);
                e = m_arith.mk_div(tmp, ke);
            }
            TRACE("qe", 
                  tout << "is singular:\n" 
                  << mk_pp(p, m) << "\n"
                  << mk_pp(fml, m) << "\n"
                  << mk_pp(x, m) << " = " 
                  << mk_pp(e, m) << "\n";
                  );
            expr_ref result(fml, m);
            m_replace.apply_substitution(x, e, result);
            simplify(result);
            TRACE("qe", 
                  tout << "singular solved:\n" 
                  << mk_pp(result, m) << "\n";
                  );
            m_ctx.elim_var(var_idx, result, e);
            return true;
        }

        bool solve_singular(expr* p, expr* fml) {
            unsigned num_vars = m_ctx.get_num_vars();
            for (unsigned i = 0; i < num_vars; ++i) {
                if (solve_singular(i, p, fml)) {
                    return true;
                }
            }
            return false;
        }

        bool solve_linear(expr* p, expr* fml) {
            vector<numeral> values;
            unsigned num_vars = m_ctx.get_num_vars();
            app*const* vars_ptr = m_ctx.get_vars();
            
            if (!is_linear(p, num_vars, vars_ptr, values)) {
                return false;
            }

            TRACE("qe", tout << "is linear: " << mk_pp(p, m) << "\n";);
            SASSERT(values.size() == num_vars + 1);
            SASSERT(num_vars > 0);
            
            unsigned index;
            bool is_aux;
            //
            // The first entry in values is the constant.
            //
            VERIFY(m_arith_solver.solve_integer_equation(values, index, is_aux));

            SASSERT(1 <= index && index <= num_vars);
            app_ref x(m_ctx.get_var(index-1), m);
            app_ref z(m);
            expr_ref p1(m);
            if (is_aux) {
                // An auxiliary variable was introduced in lieu of 'x'.
                // it has coefficient 'm' = values[index].
                SASSERT(values[index] >= rational(3));
                z  = m.mk_fresh_const("x", m_arith.mk_int());
                m_ctx.add_var(z);
                p1 = m_arith.mk_mul(m_arith.mk_numeral(values[index], true), z);
            }
            else {                
                // the coefficient to 'x' is -1.
                p1 = m_arith.mk_numeral(numeral(0), true);
            }
            
            for (unsigned i = 1; i <= num_vars; ++i) {
                numeral k = values[i];
                if (!k.is_zero() && i != index) {
                    p1 = m_arith.mk_add(p1, m_arith.mk_mul(m_arith.mk_numeral(k, true), m_ctx.get_var(i-1)));
                }
            }
            p1 = m_arith.mk_add(p1, m_arith.mk_numeral(values[0], true));
            
            TRACE("qe", 
                  tout << "is linear:\n" 
                  << mk_pp(fml, m) << "\n"
                  << mk_pp(p, m) << "\n"
                  << mk_pp(x, m) << " = " 
                  << mk_pp(p1, m) << "\n";
                  tout << values[0] << " + ";
                  for (unsigned i = 0; i < num_vars; ++i) {
                      tout << " + " << values[i+1] << " * " << mk_pp(m_ctx.get_var(i), m) << " ";
                  }
                  tout << " = 0\n";
                  );
            expr_ref result(fml, m);
            m_replace.apply_substitution(x, p1, result);
            simplify(result);            
            m_ctx.elim_var(index-1, result, p1);
            TRACE("qe", tout << "Reduced: " << mk_pp(result, m) << "\n";);
            return true;
        }        

        bool reduce_equation(expr* p, expr* fml) {
            numeral k;
            
            if (m_arith.is_numeral(p, k) && k.is_zero()) {
                return false;
            }

            return 
                solve_singular(p, fml) ||
                solve_linear(p, fml);
        }

        bool find_variable(expr* p, unsigned num_vars, app* const* vars, numeral* values, numeral const& k) {
            if (!is_app(p) || to_app(p)->get_num_args() > 0) {
                return false;
            }        
            for (unsigned i = 0; i < num_vars; ++i) {
                if (p == vars[i]) {
                    values[i] += k;
                    return true;
                }
            }
            return false;
        }

        bool is_linear(expr* p, unsigned num_vars, app* const* vars, vector<numeral>& values) {
            if (num_vars == 0) {
                return false;
            }
            values.reset();
            for (unsigned i = 0; i <= num_vars; ++i) {
                values.push_back(numeral(0));
            }
            numeral* vars_ptr = values.c_ptr() + 1;
            ptr_vector<expr> todo;
            numeral k;
            expr* e1, *e2;
            todo.push_back(p);
            while (!todo.empty()) {
                p = todo.back();
                todo.pop_back();
                if (m_arith.is_add(p)) {
                    for (unsigned i = 0; i < to_app(p)->get_num_args(); ++i) {
                        todo.push_back(to_app(p)->get_arg(i));
                    }
                }
                else if (m_arith.is_mul(p, e1, e2) &&
                         m_arith.is_numeral(e1, k) &&
                         find_variable(e2, num_vars, vars, vars_ptr, k)) {
                    // ok
                }
                else if (m_arith.is_mul(p, e1, e2) &&
                         m_arith.is_numeral(e2, k) &&
                         find_variable(e1, num_vars, vars, vars_ptr, k)) {
                    // ok
                }
                else if (find_variable(p, num_vars, vars, vars_ptr, k)) {
                    // ok
                }
                else if (m_arith.is_numeral(p, k)) {
                    values[0] += k;
                }
                else {
                    TRACE("qe_verbose", tout << "non-linear " << mk_pp(p, m) << "\n";);
                    return false;
                }
            }
            return true;
        }

    };

    class bounds_proc {
        arith_qe_util&   m_util;
        ast_mark         m_mark;
        expr_ref_vector  m_le_terms, m_ge_terms, m_lt_terms, m_gt_terms;
        vector<rational> m_le_coeffs, m_ge_coeffs, m_lt_coeffs, m_gt_coeffs;
        app_ref_vector   m_le_atoms, m_ge_atoms, m_lt_atoms, m_gt_atoms;
        
        expr_ref_vector  m_div_terms;
        vector<rational> m_div_coeffs, m_div_divisors;
        app_ref_vector   m_div_atoms;
        app_ref          m_div_z;

        expr_ref_vector  m_nested_div_terms;
        vector<rational> m_nested_div_coeffs, m_nested_div_divisors;
        app_ref_vector   m_nested_div_atoms;
        app_ref_vector   m_nested_div_z;
        rational         m_d;

    public:
        bounds_proc(arith_qe_util& u):
            m_util(u),
            m_le_terms(u.get_manager()),
            m_ge_terms(u.get_manager()),
            m_lt_terms(u.get_manager()),
            m_gt_terms(u.get_manager()),
            m_le_atoms(u.get_manager()),
            m_ge_atoms(u.get_manager()),
            m_lt_atoms(u.get_manager()),
            m_gt_atoms(u.get_manager()),
            m_div_terms(u.get_manager()),
            m_div_atoms(u.get_manager()),
            m_div_z(u.get_manager()),
            m_nested_div_terms(u.get_manager()),
            m_nested_div_atoms(u.get_manager()),
            m_nested_div_z(u.get_manager())
        {
            reset();
        }
        

        bool get_bound(contains_app& contains_x, app* a) {
            ast_manager& m = m_util.get_manager();
            app* x = contains_x.x();
            if (m_mark.is_marked(a) ||
                get_le_bound(contains_x, a) ||
                get_lt_bound(contains_x, a) ||
                get_divides(contains_x, a) ||
                get_nested_divs(contains_x, a)) {
                TRACE("qe_verbose", tout << "Bound for " << mk_pp(x, m) << " within " << mk_pp(a, m) << "\n";);
                m_mark.mark(a, true);
                return true;
            }
            else {
                TRACE("qe", tout << "No bound for " << mk_pp(x, m) << " within " << mk_pp(a, m) << "\n";);
                return false;
            }
        }

        unsigned lt_size() { return m_lt_terms.size(); }
        unsigned le_size() { return m_le_terms.size(); }
        unsigned gt_size() { return m_gt_terms.size(); }
        unsigned ge_size() { return m_ge_terms.size(); }
        unsigned t_size(bool is_l) { return is_l?lt_size():gt_size(); }
        unsigned e_size(bool is_l) { return is_l?le_size():ge_size(); }
        unsigned size(bool is_strict, bool is_l) { return is_strict?t_size(is_l):e_size(is_l); }

        expr* const* lt() { return m_lt_terms.c_ptr(); }
        expr* const* le() { return m_le_terms.c_ptr(); }
        expr* const* gt() { return m_gt_terms.c_ptr(); }
        expr* const* ge() { return m_ge_terms.c_ptr(); }
        expr* const* t(bool is_l) { return is_l?lt():gt(); }
        expr* const* e(bool is_l) { return is_l?le():ge(); }
        expr* const* exprs(bool is_strict, bool is_l) { return is_strict?t(is_l):e(is_l);}

        rational const* lt_coeffs() { return m_lt_coeffs.c_ptr(); }
        rational const* le_coeffs() { return m_le_coeffs.c_ptr(); }
        rational const* gt_coeffs() { return m_gt_coeffs.c_ptr(); }
        rational const* ge_coeffs() { return m_ge_coeffs.c_ptr(); }
        rational const* t_coeffs(bool is_l) { return is_l?lt_coeffs():gt_coeffs(); }
        rational const* e_coeffs(bool is_l) { return is_l?le_coeffs():ge_coeffs(); }
        rational const* coeffs(bool is_strict, bool is_l) { return is_strict?t_coeffs(is_l):e_coeffs(is_l); }

        app* const* lt_atoms() { return m_lt_atoms.c_ptr(); }
        app* const* le_atoms() { return m_le_atoms.c_ptr(); }
        app* const* gt_atoms() { return m_gt_atoms.c_ptr(); }
        app* const* ge_atoms() { return m_ge_atoms.c_ptr(); }
        app* const* t_atoms(bool is_l) { return is_l?lt_atoms():gt_atoms(); }
        app* const* e_atoms(bool is_l) { return is_l?le_atoms():ge_atoms(); }
        app* const* atoms(bool is_strict, bool is_l) { return is_strict?t_atoms(is_l):e_atoms(is_l); }
        
        unsigned div_size() const    { return m_div_terms.size(); }
        app* const* div_atoms()      { return m_div_atoms.c_ptr(); }
        rational const* div_coeffs() { return m_div_coeffs.c_ptr(); }
        expr* const* div_terms()     { return m_div_terms.c_ptr(); }
        rational const* divisors()   { return m_div_divisors.c_ptr(); }

        bool div_z(rational & d, app_ref& z_bv, app_ref& z) {
            if (m_div_z.get()) {
                z = m_div_z;
                z_bv = to_app(z->get_arg(0));
                d = m_d;
                return true;
            }
            if (m_div_terms.empty() && m_nested_div_terms.empty()) {
                return false;
            }
            m_d = rational(1);
            for (unsigned i = 0; i < m_div_divisors.size(); ++i) {
                m_d = lcm(m_div_divisors[i], m_d); 
            }
            for (unsigned i = 0; i < m_nested_div_divisors.size(); ++i) {
                m_d = lcm(m_nested_div_divisors[i], m_d); 
            }
            if (abs(m_d).is_one()) {
                return false;
            }
            m_util.mk_bounded_var(m_d, z_bv, m_div_z);
            z = m_div_z;
            d = m_d;
            return true;
        }

        unsigned nested_div_size() const               { return m_nested_div_terms.size(); }
        app* nested_div_atom(unsigned idx)             { return m_nested_div_atoms[idx].get(); }
        rational const& nested_div_coeff(unsigned idx) { return m_nested_div_coeffs[idx]; }
        expr* nested_div_term(unsigned idx)            { return m_nested_div_terms[idx].get(); }
        rational const& nested_divisor(unsigned idx)   { return m_nested_div_divisors[idx]; }
        app* nested_div_z(unsigned idx)                { return m_nested_div_z[idx].get(); }
        app* nested_div_z_bv(unsigned idx)             { return to_app(m_nested_div_z[idx]->get_arg(0)); }

        void reset() {
            m_lt_terms.reset();
            m_gt_terms.reset();
            m_ge_terms.reset();
            m_le_terms.reset();
            m_gt_coeffs.reset();
            m_lt_coeffs.reset();
            m_ge_coeffs.reset();
            m_le_coeffs.reset();
            m_lt_atoms.reset();
            m_gt_atoms.reset();
            m_le_atoms.reset();
            m_ge_atoms.reset();
            m_div_terms.reset();
            m_div_coeffs.reset();
            m_div_divisors.reset();
            m_div_atoms.reset();
            m_div_z = 0;
            m_nested_div_terms.reset();
            m_nested_div_coeffs.reset();
            m_nested_div_divisors.reset();
            m_nested_div_atoms.reset();
            m_nested_div_z.reset();
        }

    private:
        bool get_nested_divs(contains_app& contains_x, app* a) {
            ast_manager& m = m_util.get_manager();
            ptr_vector<expr> todo;
            todo.push_back(a);
            rational k1, k2;
            expr_ref rest(m);
            while (!todo.empty()) {
                expr* e = todo.back();
                todo.pop_back();
                if (m_mark.is_marked(e)) {
                    continue;
                }
                m_mark.mark(e, true);
                if (!contains_x(e)) {
                    continue;
                }
                if (contains_x.x() == e) {
                    return false;
                }
                if (!is_app(e)) {
                    return false;
                }
                a = to_app(e);
                if (m_util.m_arith.is_mod(e) && 
                    m_util.m_arith.is_numeral(to_app(e)->get_arg(1), k1) &&
                    m_util.get_coeff(contains_x, to_app(e)->get_arg(0), k2, rest)) {
                    app_ref z(m), z_bv(m);
                    m_util.mk_bounded_var(k1, z_bv, z);
                    m_nested_div_terms.push_back(rest);
                    m_nested_div_divisors.push_back(k1);
                    m_nested_div_coeffs.push_back(k2);
                    m_nested_div_atoms.push_back(a);
                    m_nested_div_z.push_back(z);
                    continue;
                }
                unsigned num_args = a->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    todo.push_back(a->get_arg(i));
                }                
            }              
            return true;
        }

        bool get_le_bound(contains_app& contains_x, app* a) {
            ast_manager& m = m_util.get_manager();
            expr_ref p(m), rest(m);
            rational k;
            if (m_util.is_le(a, p) && m_util.get_coeff(contains_x, p, k, rest)) {
                // k*x + rest <= 0
                if (m_util.is_real(contains_x.x())) {
                    m_util.mk_div(rest, abs(k), rest);
                    k = k.is_pos()?rational::one():rational::minus_one();
                }
                if (k.is_neg()) {
                    m_le_terms.push_back(rest);
                    m_le_coeffs.push_back(k);
                    m_le_atoms.push_back(a);
                }
                else {
                    m_ge_terms.push_back(rest);
                    m_ge_coeffs.push_back(k);
                    m_ge_atoms.push_back(a);
                }
                return true;
            }
            return false;
        }

        bool get_lt_bound(contains_app& contains_x, app* a) {
            ast_manager& m = m_util.get_manager();
            expr_ref p(m), rest(m), na(m);
            rational k;
            if (m_util.is_lt(a, p) && m_util.get_coeff(contains_x, p, k, rest)) {  
                // k*x + rest < 0
            }
            else if (m_util.is_neg(a, na) && is_app(na) && 
                     m_util.is_ge(to_app(na), p) && 
                     m_util.get_coeff(contains_x, p, k, rest)) {
                //
                //   not (k*x + rest >= 0)
                // <=>
                //   k*x + rest < 0
                //
            }
            else {
                return false;
            }

            SASSERT(m_util.is_real(contains_x.x()));
            m_util.mk_div(rest, abs(k), rest);
            if (k.is_neg()) {
                m_lt_terms.push_back(rest);
                m_lt_coeffs.push_back(rational::minus_one());
                m_lt_atoms.push_back(a);
            }
            else {
                m_gt_terms.push_back(rest);
                m_gt_coeffs.push_back(rational::one());
                m_gt_atoms.push_back(a);
            }
            return true;
        }

        bool get_divides(contains_app& contains_x, app* a) {
            ast_manager& m = m_util.get_manager();
            expr_ref p(m), rest(m);
            app_ref a2(m);
            numeral k, k2;

            if (m_util.is_divides(a, k, p) && m_util.get_coeff(contains_x, p, k2, rest)) {
                m_div_terms.push_back(rest);
                m_div_divisors.push_back(k);
                m_div_coeffs.push_back(k2);
                m_div_atoms.push_back(a);
                return true;
            }
            if (m_util.is_not_divides(a, a2, k, p) && m_util.get_coeff(contains_x, p, k2, rest)) {
                m_div_terms.push_back(rest);
                m_div_divisors.push_back(k);
                m_div_coeffs.push_back(k2);
                m_div_atoms.push_back(a2);
                return true;
            }
            return false;
        }
public:
        void display(std::ostream& out) {
            ast_manager& m = m_util.get_manager();
            for (unsigned i = 0; i < lt_size(); ++i) {
                out << mk_pp(lt()[i], m) << " < 0\n";
            }
            for (unsigned i = 0; i < le_size(); ++i) {
                out << mk_pp(le()[i], m) << " < 0\n";
            }
            for (unsigned i = 0; i < gt_size(); ++i) {
                out << mk_pp(gt()[i], m) << " < 0\n";
            }
            for (unsigned i = 0; i < ge_size(); ++i) {
                out << mk_pp(ge()[i], m) << " < 0\n";
            }
        }
    };

    class x_subst {
        arith_qe_util& m_super;
        expr_ref m_t;
        rational m_coeff;
    public:

        x_subst(arith_qe_util& s):
            m_super(s),
            m_t(s.get_manager()),
            m_coeff(rational::one())
        {}

        void set_term(expr* t) { m_t = t; }

        void set_coeff(rational const& k) { m_coeff = k; }

        expr* get_term() const { return m_t; }

        rational get_coeff() const { return m_coeff; }

        expr_ref mk_term(rational const& c, expr* t) {
            // return t + c*m_t
            ast_manager& m = m_super.get_manager();
            if (m_t.get()) {
                return expr_ref(m_super.mk_add(m_super.mk_mul(c, m_t), t), m);
            }
            else {
                return expr_ref(t, m);
            }            
        }

        rational mk_coeff(rational const& k) {
            return k * m_coeff;
        }
    };

    
    struct branch_formula {
        expr*    m_fml;
        app*     m_var;
        unsigned m_branch;
        expr*    m_result;
        rational m_coeff;
        expr*    m_term;

        branch_formula(): m_fml(0), m_var(0), m_branch(0), m_result(0), m_term(0) {}
        
        branch_formula(expr* fml, app* var, unsigned b, expr* r, rational coeff, expr* term):
            m_fml(fml),
            m_var(var),
            m_branch(b),
            m_result(r),
            m_coeff(coeff),
            m_term(term)
        {}
        
        unsigned mk_hash() const {
            return mk_mix(m_fml?m_fml->hash():0, m_var?m_var->hash():0, m_branch);
        }
        
        bool mk_eq(branch_formula const& other) const {
            return 
                m_fml == other.m_fml &&
                m_var == other.m_var &&
                m_branch == other.m_branch;
        }
        
        struct hash {
            typedef branch_formula data;
            unsigned operator()(data const& d) const { return d.mk_hash(); }
        };
        
        struct eq {
            typedef branch_formula data;
            bool operator()(data const& x, data const& y) const { return x.mk_eq(y); }
        };
    };

    class arith_plugin : public qe_solver_plugin {
        typedef obj_pair_map<app,  expr, bounds_proc*> bounds_cache;
        typedef obj_pair_map<expr, expr, expr*>        resolve_cache;
        typedef hashtable<branch_formula, branch_formula::hash, branch_formula::eq> subst_cache;

        arith_qe_util      m_util;
        expr_ref_vector    m_trail;
        bounds_cache       m_bounds_cache;
        subst_cache        m_subst;

    public:
        arith_plugin(i_solver_context& ctx, ast_manager& m, smt_params& p): 
            qe_solver_plugin(m, m.mk_family_id("arith"), ctx),
            m_util(m, p, ctx),
            m_trail(m)
        {}

        ~arith_plugin() {
            bounds_cache::iterator it = m_bounds_cache.begin(), end = m_bounds_cache.end();
            for (; it != end; ++it) {
                dealloc(it->get_value());
            }
        }

        virtual void assign(contains_app& contains_x, expr* fml, rational const& vl) {
            SASSERT(vl.is_unsigned());
            app* x = contains_x.x();
            unsigned v     = vl.get_unsigned();
            expr_ref result(fml, m);
            unsigned t_size, e_size;
            x_subst x_t(m_util);

            if (get_cache(x, fml, v, result)) {
                return;
            }
            
            bounds_proc& bounds = get_bounds(x, fml);            
            bool is_lower = get_bound_sizes(bounds, x, t_size, e_size);            
            assign_nested_divs(contains_x, bounds, result);
            assign_divs(contains_x, bounds, x_t, result);

            //assign_all(contains_x, fml);

            if (v == 0) {
                //
                // index is for the infinity case.
                // assert v => ~(x <= t) each t
                // assert v => (x >= s) each s
                //
                mk_non_bounds(bounds, true,   is_lower, result);
                mk_non_bounds(bounds, false,  is_lower, result);
                
                mk_non_resolve(bounds, true,  is_lower, result);
                mk_non_resolve(bounds, false, is_lower, result);
                m_util.simplify(result);
                add_cache(x, fml, v, result, x_t.get_coeff(), x_t.get_term());
                TRACE("qe", 
                        tout << vl << " " << mk_pp(x, m) << " infinite case\n";
                        tout << mk_pp(fml, m) << "\n";
                        tout << mk_pp(result, m) << "\n";);
                return;
            }
            unsigned index = v-1;
            bool is_strict = e_size <= index;
            bool is_eq = false;
            
            SASSERT(index < t_size + e_size);
            if (is_strict) {
                index -= e_size;
                TRACE("qe_verbose", bounds.display(tout); );               
            }
            else if (m_util.is_real(x)) {
                SASSERT(0 == (e_size & 0x1));
                is_eq = (0 == (index & 0x1));
                index  /= 2;
                e_size /= 2;
            }
            SASSERT(is_strict || index < e_size);
            SASSERT(!is_strict || index < t_size);

            // 
            // index is for the upper/lower-bound case.
            // assert v => (x <= t_i) 
            // assert v => (x <= t_j => t_i <= t_j), add new atom to stack.
            // assert v => (x >= s   => s <= t_i),   add new atom to stack.
            //
            // assert v => (x < t_j => t_i < t_j)
            //
            SASSERT(index < bounds.size(is_strict, is_lower));
            expr_ref t(bounds.exprs(is_strict, is_lower)[index], m);
            rational a = bounds.coeffs(is_strict, is_lower)[index];

            
                                
            mk_bounds(bounds, x, true,  is_eq, is_strict, is_lower, index, a, t, result);
            mk_bounds(bounds, x, false, is_eq, is_strict, is_lower, index, a, t, result);

            t = x_t.mk_term(a, t);
            a = x_t.mk_coeff(a);
            
            mk_resolve(bounds, x, x_t, true,  is_eq, is_strict, is_lower, index, a, t, result);
            mk_resolve(bounds, x, x_t, false, is_eq, is_strict, is_lower, index, a, t, result);
            m_util.simplify(result);
            add_cache(x, fml, v, result, x_t.get_coeff(), x_t.get_term());
            TRACE("qe", 
                  {
                      tout << vl << " " << mk_pp(bounds.atoms(is_strict, is_lower)[index],m) << "\n";
                      tout << mk_pp(fml, m) << "\n";
                      tout << mk_pp(result, m) << "\n";
                  }
                  );
        }


        virtual bool get_num_branches(contains_app& contains_x, expr* fml, rational& nb) { 
            app* x = contains_x.x();
            if (!update_bounds(contains_x, fml)) {
                return false;
            }
            bounds_proc& bounds = get_bounds(x, fml);
            unsigned t_size, e_size;
            get_bound_sizes(bounds, x, t_size, e_size);
            nb = rational(t_size + e_size + 1);
            return true;
        }

        virtual void subst(contains_app& contains_x, rational const& vl, expr_ref& fml, expr_ref* def) {
            SASSERT(vl.is_unsigned());            
           if (def) {
               get_def(contains_x, vl.get_unsigned(), fml, *def);
            }
            VERIFY(get_cache(contains_x.x(), fml, vl.get_unsigned(), fml));
            TRACE("qe", tout << mk_pp(contains_x.x(), m) << " " << vl << "\n" << mk_pp(fml, m) << "\n";);
        } 

        virtual bool project(contains_app& x, model_ref& model, expr_ref& fml) {
            if (!update_bounds(x, fml)) {
                TRACE("qe", tout << mk_pp(x.x(), m) << " failed to update bounds\n";);
                return false;
            }
            if (m_util.m_arith.is_real(x.x())) {
                return project_real(x, model, fml);
            }
            else {
                return project_int(x, model, fml);
            }
        }


        virtual unsigned get_weight(contains_app& contains_x, expr* fml) {
            return 2;
        }

        virtual bool solve(conj_enum& conjs, expr* fml) {
            return m_util.solve(conjs, fml);
        }

        virtual bool mk_atom(expr* e, bool p, expr_ref& result) {
            return m_util.mk_atom(e, p, result);
        }

        virtual bool is_uninterpreted(app* f) {
            switch(f->get_decl_kind()) {
            case OP_NUM:
            case OP_LE:
            case OP_LT:
            case OP_GE:
            case OP_GT:
            case OP_ADD:
            case OP_SUB:
            case OP_UMINUS:
                return false;
            case OP_MOD:
                if(m_util.m_arith.is_numeral(f->get_arg(1))) {
                    return false;
                }
                return true;
            case OP_MUL: {
                arith_util& a = m_util.m_arith;
                expr* m, *n;
                if (a.is_mul(f, m, n) && (a.is_numeral(m) || a.is_numeral(n))) {
                    return false;
                }
                return true;
            }
            default:                
                return true;
            }
        }

    private:

        /**
           \brief Compute least upper/greatest lower bounds for x.

           Assume:
           (not (= k 0))
           (<= 0 (mod m k)) 
           (< (mod m k) (abs k))
           (= m (+ (* k (div m k)) (mod m k)))
           i.e. 
             k * (e div k) + (e mod k) = e

           
           When k is positive, least upper bound 
           for x such that: k*x <= e is e div k

           When k is negative, greatest lower bound 
           for x such that k*x <= e is e div k

           k * (e div k) + (e mod k) = e                   
         */
        expr_ref mk_idiv(expr* e, numeral k) {            
            SASSERT(!k.is_zero());
            arith_util& a = m_util.m_arith; 
            if (k.is_one()) {
                return expr_ref(e, m);
            }
            if (k.is_minus_one()) {
                return expr_ref(a.mk_uminus(e), m);
            }
            SASSERT(a.is_int(e));
            return expr_ref(a.mk_idiv(e, a.mk_numeral(k, true)), m);
        }
    

        void get_def(contains_app& contains_x, unsigned v, expr* fml, expr_ref& def) {
            app* x = contains_x.x();
            x_subst x_t(m_util);
            bounds_proc& bounds = get_bounds(x, fml);    
            branch_formula bf;
            VERIFY (m_subst.find(branch_formula(fml, x, v, 0, rational::zero(), 0), bf));
            x_t.set_term(bf.m_term);
            x_t.set_coeff(bf.m_coeff);

            // x is of the form: x_t.get_coeff()*x' + x_t.get_term()
            CTRACE("qe", x_t.get_term(), tout << x_t.get_coeff() << " " << mk_pp(x_t.get_term(), m) << "\n";);
            //
            // a*x + t <= 0
            // a*(c*x' + s) + t <= 0
            // a*c*x' + a*s + t <= 0
            // 

            unsigned t_size, e_size, sz;        
            bool is_lower = get_bound_sizes(bounds, x, t_size, e_size);            
            bool is_strict;
            if (v == 0) {
                is_strict = false;
                sz = bounds.size(is_strict, !is_lower);
                expr_ref_vector terms(m);
                if (sz == 0) {
                    terms.push_back(m_util.mk_zero(x));
                }
                for (unsigned i = 0; i < sz; ++i) {
                    // a*x + term <= 0
                    expr_ref term(bounds.exprs(is_strict, !is_lower)[i], m);
                    rational a = bounds.coeffs(is_strict, !is_lower)[i];

                    if (x_t.get_term()) {
                        // x := coeff * x' + s                        
                        // solve instead for
                        // a*coeff*x' + term + a*s <= 0
                        TRACE("qe", tout << x_t.get_coeff() << "* " << mk_pp(x,m) << " + " 
                              << mk_pp(x_t.get_term(), m) << "\n";);
                        SASSERT(x_t.get_coeff().is_pos());
                        term = m_util.mk_add(term, m_util.mk_mul(a, x_t.get_term()));
                        a    = a * x_t.get_coeff();
                    }

                    TRACE("qe", tout << a << "* " << mk_pp(x,m) << " + " << mk_pp(term, m) << " <= 0\n";);
                    SASSERT(a.is_int());
                    SASSERT(is_lower == a.is_pos());                    

                    //    a*x + t <= 0
                    // <=
                    //   x <= -t div a + 1
                    
                    term = m_util.mk_uminus(term);
                    term = mk_idiv(term, a);
                    terms.push_back(term);
                    TRACE("qe", tout << "a: " << a << " term: " << mk_pp(term, m) << "\n";);
                }
                is_strict = true;
                sz = bounds.size(is_strict, !is_lower);
                for (unsigned i = 0; i < sz; ++i) {
                    expr_ref term(bounds.exprs(is_strict, !is_lower)[i], m);
                    SASSERT(abs(bounds.coeffs(is_strict, !is_lower)[i]).is_one());
                    //
                    if (is_lower) {
                        //    x + t < 0
                        // <= 
                        //    x <= -t -1
                        term = m_util.mk_uminus(m_util.mk_add(term, m_util.mk_one(x)));
                    }
                    else {
                        //   -x + t < 0
                        // <=
                        //    t + 1 <= x
                        term = m_util.mk_add(term, m_util.mk_one(x));
                    }
                    terms.push_back(term);
                }
                if (is_lower) {
                    def = m_util.mk_min(terms.size(), terms.c_ptr());
                }
                else {
                    def = m_util.mk_max(terms.size(), terms.c_ptr());
                }
                
                if (x_t.get_term()) {
                    // x := coeff * x + s
                    TRACE("qe", tout << x_t.get_coeff() << "* " << mk_pp(x,m) << " + " 
                          << mk_pp(x_t.get_term(), m) << "\n";);
                    def = m_util.mk_add(m_util.mk_mul(x_t.get_coeff(), def), x_t.get_term());
                }
                m_util.simplify(def);
                return;
            }
            --v;
            is_strict = e_size <= v;
            
            SASSERT(v < t_size + e_size);
            if (is_strict) {
                v -= e_size;
                TRACE("qe_verbose", bounds.display(tout); );               
            }
            else if (m_util.is_real(x)) {
                SASSERT(0 == (e_size & 0x1));
                v  /= 2;
                e_size /= 2;
            }
            SASSERT(is_strict || v < e_size);
            SASSERT(!is_strict || v < t_size); 

            // 
            // index is for the upper/lower-bound case.
            // assert v => (x <= t_i) 
            //
            SASSERT(v < bounds.size(is_strict, is_lower));
            def = bounds.exprs(is_strict, is_lower)[v];
            rational a = bounds.coeffs(is_strict, is_lower)[v];

            if (x_t.get_term()) {
                // x := coeff * x' + s                        
                // solve instead for
                // a*coeff*x' + term + a*s <= 0
                TRACE("qe", tout << x_t.get_coeff() << "* " << mk_pp(x,m) << " + " 
                      << mk_pp(x_t.get_term(), m) << "\n";);
                SASSERT(x_t.get_coeff().is_pos());
                def = m_util.mk_add(def, m_util.mk_mul(a, x_t.get_term()));
                a    = a * x_t.get_coeff();
            }

            SASSERT(a.is_int());
            SASSERT(is_lower != a.is_pos());                    

            //    a*x + t <= 0
            // <=
            //   x <= -t div a 
            
            def = m_util.mk_uminus(def);
            def = mk_idiv(def, a);

            if (x_t.get_term()) {
                // x := coeff * x + s
                def = m_util.mk_add(m_util.mk_mul(x_t.get_coeff(), def), x_t.get_term());
            }
            if (is_strict) {
                SASSERT(m_util.m_arith.is_real(x));
                // We actually want a supremum, such that dual inequalities are satisfied.
                // i.e. for every dual inequality , if the dual bound is feasible, make sure to
                // choose a value in the feasible range.
                def = m_util.mk_sub(def, m_util.mk_one(x));
            }

            m_util.simplify(def);


            TRACE("qe", tout << "TBD (for Real): " << a << " " << mk_pp(def, m) << "\n";);
        }

        expr_ref mk_not(expr* e) {
            expr* r;
            if (m.is_not(e,r)) {
                return expr_ref(r, m);
            }
            return expr_ref(m.mk_not(e), m);
        }

        //
        // Projection function for x of type real.
        // TBD: model-based selection soundness/completeness?
        //      when model selects bound different from what is the smaller half, what then?
        //      shouldn't we find candidate among either lt or gt, and then if both can be found
        //      only then select which one to go with. Then assign has to be context-aware.
        //      Perhaps not really: the model is used as a hint.
        // 

        bool project_real(contains_app& x, model_ref& model, expr_ref& fml) {
            SASSERT(m_util.m_arith.is_real(x.x()));
            model_evaluator model_eval(*model);
            bounds_proc& bounds = get_bounds(x.x(), fml);
            bool is_lower   = bounds.le_size() + bounds.lt_size() < bounds.ge_size() + bounds.gt_size();
            unsigned e_size = bounds.e_size(is_lower);
            numeral bound1, bound2, vl, x_val;
            unsigned idx1, idx2;
            bool found1 = find_min_max(is_lower, false, bounds, model_eval, bound1, idx1);
            bool found2 = find_min_max(is_lower, true,  bounds, model_eval, bound2, idx2);

            if (!found1 && !found2) {
                vl = numeral(0);
            }
            else if (found2 && (!found1 || bound2 <= bound1)) {
                // strict indices come after non-strict indices. There 
                // is a pair of index values for non-strict inequalities 
                // corresponding to the disjunction (x < t || x = t)
                vl = numeral(1 + 2*e_size + idx2);
            }
            else if (found1 && (!found2 || bound1 < bound2)) {
                expr_ref val_x(m);
                model_eval(x.x(), val_x);
                VERIFY(m_util.m_arith.is_numeral(val_x, x_val));
                if (x_val == bound1) {
                    vl = numeral(1 + 2*idx1); // even indicates equality between x and bound.
                }
                else {
                    vl = numeral(1 + 2*idx1 + 1); // odd indicates strict bound.
                }
            }
            assign(x, fml, vl);
            subst(x, vl, fml, 0);
            TRACE("qe", tout << mk_pp(fml, m) << "\n";);            
            return true;
        }

        bool project_int(contains_app& x, model_ref& model, expr_ref& fml) {
            model_evaluator model_eval(*model);
            bounds_proc& bounds = get_bounds(x.x(), fml);
            SASSERT(m_util.m_arith.is_int(x.x()));
            SASSERT(bounds.lt_size() == 0 && bounds.gt_size() == 0);
            bool is_lower   = bounds.le_size() < bounds.ge_size();
            numeral bound, vl, x_val;
            unsigned idx = bounds.le_size() + bounds.ge_size();
            bool found = find_min_max(is_lower, false, bounds, model_eval, bound, idx);

            if (found) {
                SASSERT(idx < bounds.size(false, is_lower));
                vl = numeral(1 + idx);
            }
            else {
                vl = numeral(0);
            }
            assign(x, fml, vl);
            subst(x, vl, fml, 0);
            TRACE("qe", tout << mk_pp(fml, m) << "\n";);
            
            return true;
        }

        bool find_min_max(bool is_lower, bool is_strict, bounds_proc& bounds, 
                          model_evaluator& eval, rational& bound, unsigned& idx) {
            bool found = false;
            unsigned num_bounds = bounds.size(is_strict, is_lower);
            rational num;
            for (unsigned i = 0; i < num_bounds; ++i) {
                expr_ref vl(m);
                eval(bounds.atoms(is_strict, is_lower)[i], vl);
                if (!m.is_true(vl)) {
                    continue;
                }
                eval(bounds.exprs(is_strict, is_lower)[i], vl);
                VERIFY(m_util.m_arith.is_numeral(vl, num));
                num /= abs(bounds.coeffs(is_strict,is_lower)[i]);
                if (found) {
                    if (is_lower?(num < bound):(num > bound)) {
                        bound = num;
                        idx = i;
                    }
                }
                else {
                    found = true;
                    idx = i;
                    bound = num;
                }                
            }
            return found;
        }


        bool get_bound_sizes(bounds_proc& bounds, app* x, unsigned& t_size, unsigned& e_size) {
            unsigned le_size = bounds.le_size();
            unsigned ge_size = bounds.ge_size();
            if (m_util.is_real(x)) {
                le_size *= 2;
                ge_size *= 2;
            }
            if (le_size + bounds.lt_size() < ge_size + bounds.gt_size()) {
                e_size = le_size;
                t_size = bounds.lt_size();
                return true;
            }
            else {
                e_size = ge_size;
                t_size = bounds.gt_size();
                return false;
            }
        }

        void add_cache(app* x, expr* fml, unsigned v, expr* result, rational coeff, expr* term) {
            m_trail.push_back(x);
            m_trail.push_back(fml);
            m_trail.push_back(result);
            if (term) m_trail.push_back(term);
            m_subst.insert(branch_formula(fml, x, v, result, coeff, term));
        }
        
        bool get_cache(app* x, expr* fml, unsigned v, expr_ref& result) {
            branch_formula bf;
            if (!m_subst.find(branch_formula(fml, x, v, 0, rational::zero(), 0), bf)) {
                return false;
            }
            SASSERT(bf.m_result);
            result = bf.m_result;
            return true;
        }

        void assign_divs(contains_app& contains_x, bounds_proc& bounds, x_subst& x_t, expr_ref& result) {
            app* x = contains_x.x();
            
            app_ref z(m), z_bv(m);
            rational d;
            if (!bounds.div_z(d, z_bv, z)) {
                return;
            }
            m_ctx.add_var(z_bv);
            
            //
            // assert 
            //        z < d
            //        d | (x - z)
            //        (c | ax + t <-> c | az + t) for each divisor.
            // 

            // z < d
            expr* z_lt_d = m_util.m_arith.mk_le(z, m_util.m_arith.mk_numeral(d-rational(1), true));
            m_ctx.add_constraint(false, z_lt_d);
            TRACE("qe", tout << mk_pp(z_lt_d, m) << "\n";);

            // result <- result & z <= d - 1
            SASSERT(!abs(d).is_one());
            rational d1 = d - rational(1);
            expr_ref tmp(m);
            m_util.m_arith_rewriter.mk_le(z, m_util.m_arith.mk_numeral(d1, true), tmp);
            m_util.m_bool_rewriter.mk_and(result, tmp, result);

            // d | (x - z)
            expr_ref t1(m), new_atom(m);
            t1 = m_util.mk_sub(x, z);
            m_util.mk_divides(d, t1, new_atom);
            m_ctx.add_constraint(false, new_atom);
            TRACE("qe", tout << mk_pp(new_atom, m) << "\n";);
            
            // (c | ax + t <-> c | az + t) for each divisor.
            mk_div_equivs(bounds, z, result);
            TRACE("qe", tout << mk_pp(result, m) << "\n";);
            
            // update x_t to map x |-> dx + z
            x_t.set_term(z);
            x_t.set_coeff(d);
        }

        //
        //   (c | ax + t <-> c | az + t) for each divisor.
        //
        void mk_div_equivs(bounds_proc& bounds, expr* z, expr_ref& result) {
            unsigned sz = bounds.div_size();
            app* const* atoms        = bounds.div_atoms();
            rational const* coeffs   = bounds.div_coeffs();
            expr* const* terms       = bounds.div_terms();
            rational const* divisors = bounds.divisors();
            expr_ref new_atom(m), t1(m);

            for (unsigned i = 0; i < sz; ++i) {        
                app* atm = atoms[i];        
                t1 = m_util.mk_add(m_util.mk_mul(coeffs[i], z), terms[i]);
                m_util.mk_divides(divisors[i], t1, new_atom);
                m_util.m_replace.apply_substitution(atm, new_atom.get(), result);
                
                m_ctx.add_constraint(false, mk_not(atm), new_atom);
                m_ctx.add_constraint(false, mk_not(new_atom), atm);
            }
        }

        void assign_nested_divs(contains_app& contains_x, bounds_proc& bounds, expr_ref& result) {
            unsigned num_nested_divs = bounds.nested_div_size();
            if (num_nested_divs == 0) {
                return;
            }
            app_ref z(m), z_bv(m);
            rational d;
            VERIFY (bounds.div_z(d, z_bv, z));
            for (unsigned i = 0; i < num_nested_divs; ++i) {
                //
                // mod_term = arg_0 mod k
                //
                app* atm = bounds.nested_div_atom(i);
                rational const& k = bounds.nested_divisor(i);

                app* z1_bv = bounds.nested_div_z_bv(i);
                app* z1 = bounds.nested_div_z(i);

                m_ctx.add_var(z1_bv);

                //
                // assert
                //    z < k
                //    (coeff*x + rest - z) mod k == 0
                // 

                expr* z_lt_k = m_util.m_arith.mk_le(z1, m_util.m_arith.mk_numeral(k-rational(1), true));
                m_ctx.add_constraint(false, z_lt_k);
                expr* e1 = m_util.m_arith.mk_sub(atm->get_arg(0), z1);
                expr* e2 = atm->get_arg(1);
                expr_ref mod_term2(m_util.m_arith.mk_mod(e1, e2), m);
                m_util.simplify(mod_term2);
                m_ctx.add_constraint(false, m.mk_eq(mod_term2, m_util.mk_zero(mod_term2)));

                m_util.m_replace.apply_substitution(atm, z1, result);  

                //
                // conjoin (coeff*z + rest - z1) mod k == 0 to result
                //
                expr_ref mod_eq(m), tmp1(m), tmp2(m);
                
                tmp2 = m_util.mk_numeral(bounds.nested_div_coeff(i), true);
                tmp1 = m_util.m_arith.mk_mul(tmp2, z1);
                tmp2 = m_util.m_arith.mk_sub(bounds.nested_div_term(i), z);
                tmp2 = m_util.m_arith.mk_add(tmp1, tmp2);
                tmp1 = m_util.m_arith.mk_mod(tmp2, bounds.nested_div_atom(i)->get_arg(1));

                mod_eq = m.mk_eq(tmp1, m_util.mk_zero(z));
                m_util.simplify(mod_eq);
                result = m.mk_and(result, mod_eq);

                TRACE("qe", tout << mk_pp(mod_eq, m) << "\n";);
            }
        }

        bounds_proc& get_bounds(app* x, expr* fml) {
            bounds_proc* result = 0;
            VERIFY (m_bounds_cache.find(x, fml, result));
            return *result;
        }      

        void mk_non_bounds(bounds_proc& bounds, bool is_strict, bool is_lower, expr_ref& result) {
            unsigned sz = bounds.size(is_strict, is_lower);
            for (unsigned i = 0; i < sz; ++i) {
                app* e = bounds.atoms(is_strict, is_lower)[i];
                m_ctx.add_constraint(true, mk_not(e));
                m_util.m_replace.apply_substitution(e, m.mk_false(), result);
            }            
        }

        void mk_non_resolve(bounds_proc& bounds, bool is_strict, bool is_lower, expr_ref& result) {
            unsigned sz = bounds.size(is_strict, !is_lower);
            for (unsigned i = 0; i < sz; ++i) {
                app* e = bounds.atoms(is_strict, !is_lower)[i];
                m_ctx.add_constraint(true, e);
                m_util.m_replace.apply_substitution(e, m.mk_true(), result); 
            }
        }

        //
        // phi[x < t, x <= s, x >= u, x > v]
        // 
        // x = +oo: phi[false, false, true, true]
        // x < t:   phi[true,    t-e < s, t - e >= u, t - e > v] == phi[true,   t <= s, t > u,  t > v]
        // x < s:   phi[s-e < t, true,    s - e >= u, s - e > v] == phi[s <= t, true,   s > u,  s > v]
        // x = s:                                                   phi[s < t,  true,   s >= u, s > v]
        // 
        // assert 
        //      path1 => x < t 
        // bounds:
        //      path1 => x < t' => t < t'  when index(t') < index(t)
        //      path1 => x < t' => t <= t' when index(t') >= index(t)
        //      path1 => x <= s => t <= s
        // resolve:
        //      path1 => x >= u => t > u
        //      path1 => x > v  => t > v
        // symmetry reduction:
        //      
        // 
        //      path2 => x <= s
        // bounds:
        //      path2 => x < s => x < t => s <= t
        //      path2 => x = s => x < t => s < t
        //      path2 => x <= s => x <= s' => s <  s' when index(s') < index(s)
        //      path2 => x <= s => x <= s' => s <= s' when index(s') >= index(s)
        // resolve:
        //      path2 => x < s => x >= u => s > u
        //      path2 => x = s => x >= u => s >= u
        //      path2 => x <= s => x > v => s > v
        //


        void mk_bound(bool is_strict, bool is_lower, 
                      rational const& a, expr* t,
                      rational const& b, expr* s,
                      expr_ref& result) 
        {
            if (is_strict) {
                if (is_lower) {
                    // b*t > a*s
                    m_util.mk_strict_bound(b, s, a, t, result);
                }
                else {
                    // b*t < a*s
                    m_util.mk_strict_bound(a, t, b, s, result);
                }
            }
            else {                        
                if (is_lower) {
                    // b*t >= a*s
                    m_util.mk_bound(b, s, a, t, result);
                }
                else {
                    // b*t <= a*s
                    m_util.mk_bound(a, t, b, s, result);
                }
            }
            m_util.simplify(result);
            TRACE("qe", 
                  tout << (is_strict?"strict":"non-strict") << "\n";
                  tout << (is_lower?"is-lower":"is-upper") << "\n";
                  tout << "a: " << a << " " << mk_pp(t, m) << "\n";
                  tout << "b: " << b << " " << mk_pp(s, m) << "\n";
                  tout << mk_pp(result, m) << "\n";);
        }

        //
        // a*x <= t, a*x < t
        // 
        /*
            - bounds 
            - add_assertion - flag whether to add side-effect to state
            - x             - the variable to be eliminated
            - is_strict     - whether to loop over strict inequalities
            - is_eq_ctx     - whether non-strict inequality is to be treated as equality case.
            - is_strict_ctx - whether 'atm' is a strict inequality
            - is_lower      - whether 'x' is given a lower-bound in 'atm'
            - index         - index of 'atm' in 'bounds' 'atm = bounds[index]'
            - a             - coefficient to 'x' in 'atm'
            - t             - upper/lower bound to 'x' in 'atm'
        */


        void mk_bounds(bounds_proc& bounds, 
                       app* x, bool is_strict, bool is_eq_ctx, 
                       bool is_strict_ctx, bool is_lower, unsigned index, 
                       rational const& a, expr* t,
                       expr_ref& result) 
        {
            TRACE("qe", tout << mk_pp(t, m) << "\n";);
            SASSERT(!is_eq_ctx || !is_strict_ctx);
            unsigned sz = bounds.size(is_strict, is_lower);
            expr_ref tmp(m), eq(m);            
            bool same_strict = (is_strict == is_strict_ctx);
            bool non_strict_real = m_util.is_real(x) && !is_strict_ctx;
            app* atm = bounds.atoms(is_strict_ctx, is_lower)[index];

            for (unsigned i = 0; i < sz; ++i) {
                app* e   = bounds.atoms(is_strict, is_lower)[i];
                expr_ref s(bounds.exprs(is_strict, is_lower)[i], m);
                rational b = bounds.coeffs(is_strict, is_lower)[i]; 
               
                if (same_strict && i == index) {                    
                    if (non_strict_real) {
                        m_util.mk_eq(a, x, t, eq);
                        TRACE("qe", tout << "a:" << a << " x: " << mk_pp(x, m) << "t: " << 
                              mk_pp(t, m) << " eq: " << mk_pp(eq, m) << "\n";);
                        if (is_eq_ctx) {
                            m_ctx.add_constraint(true, eq);
                        }
                        else {
                            m_ctx.add_constraint(true, mk_not(eq));
                            m_ctx.add_constraint(true, e);
                        }
                    }
                    else {
                        m_ctx.add_constraint(true, e);
                    }
                    m_util.m_replace.apply_substitution(atm, m.mk_true(), result);
                    continue;
                }
           
                //
                // Break symmetries by using index:
                // bounds before me are strictly larger.
                // Cases:
                // ax <= t & ax != t & bx < s => bt <= as
                // ax <= t & ax = t  & bx < s => bt < as
                //                     bx <= s => bt < as or bt <= as depending on symmetry
                //     
                bool result_is_strict = 
                    (non_strict_real && is_eq_ctx && is_strict) ||
                    (same_strict && i < index);


                mk_bound(result_is_strict, is_lower, a, t, b, s, tmp);
                m_util.m_replace.apply_substitution(e, tmp.get(), result);

                TRACE("qe", 
                      tout << (result_is_strict?"strict result":"non-strict result") << "\n";
                      tout << (is_strict?"strict":"non-strict") << "\n";
                      tout << mk_pp(atm, m) << " & ";
                      tout << mk_pp(e,  m) << " --> ";
                      tout << mk_pp(tmp.get(), m) << "\n";);

                m_ctx.add_constraint(true, mk_not(e), tmp);
            }
        }

        //  x <= t
        //      x != t => x >= u => t > u
        //      x = t => x >= u => t >= u
        void mk_resolve(bounds_proc& bounds, 
                        app* x, x_subst& x_t, bool is_strict, bool is_eq_ctx, bool is_strict_ctx, bool is_lower, 
                        unsigned index, 
                        rational const& a, expr* t, expr_ref& result) 
        {
            expr_ref tmp(m);
            unsigned sz = bounds.size(is_strict, !is_lower);
            bool is_strict_real = !is_eq_ctx && m_util.is_real(x) && !is_strict_ctx;                   
            bool strict_resolve = is_strict || is_strict_ctx || is_strict_real;
            app* atm = bounds.atoms(is_strict_ctx, is_lower)[index];    

            for (unsigned i = 0; i < sz; ++i) {
                app* e = bounds.atoms(is_strict, !is_lower)[i];
                expr_ref s(bounds.exprs(is_strict, !is_lower)[i], m);
                rational b = bounds.coeffs(is_strict, !is_lower)[i];
                SASSERT(!b.is_zero());
                SASSERT(b.is_pos() != a.is_pos());
                
                s = x_t.mk_term(b, s);
                b = x_t.mk_coeff(b);
                m_util.mk_resolve(x, strict_resolve, a, t, b, s, tmp);
                expr_ref save_result(result);
                m_util.m_replace.apply_substitution(e, tmp.get(), result);
                
                m_ctx.add_constraint(true, mk_not(e), tmp);

                TRACE("qe_verbose", 
                      tout << mk_pp(atm, m) << " ";
                      tout << mk_pp(e, m) << " ==>\n";
                      tout << mk_pp(tmp, m) << "\n";
                      tout << "old fml: " << mk_pp(save_result, m) << "\n";
                      tout << "new fml: " << mk_pp(result, m) << "\n";
                      );           
            }            
        }

        bool update_bounds(bounds_proc& bounds, contains_app& contains_x, expr* fml, atom_set const& tbl, bool is_pos) 
        {
            app_ref tmp(m);
            atom_set::iterator it = tbl.begin(), end = tbl.end();
            for (; it != end; ++it) {
                app* e = *it; 
                if (!contains_x(e)) {
                    continue;
                }

                if (!is_pos) {
                    SASSERT(!m.is_not(e));
                    tmp = m.mk_not(e);
                    e = tmp;
                }
                
                if (!bounds.get_bound(contains_x, e)) {
                    return false;
                }
            }    
            return true;
        }

        bool update_bounds(contains_app& contains_x, expr* fml) {
            bounds_proc* bounds = 0;
            if (m_bounds_cache.find(contains_x.x(), fml, bounds)) {
                return true;
            }
            bounds = alloc(bounds_proc, m_util);

            if (!update_bounds(*bounds, contains_x, fml, m_ctx.pos_atoms(), true)) {
                dealloc(bounds);
                return false;
            }
            if (!update_bounds(*bounds, contains_x, fml, m_ctx.neg_atoms(), false)) {
                dealloc(bounds);
                return false;
            }
            
            m_trail.push_back(contains_x.x());
            m_trail.push_back(fml);
            m_bounds_cache.insert(contains_x.x(), fml, bounds);
            return true;
        }
    };

    // ---------------------
    // non-linear arithmetic
    class nlarith_plugin : public qe_solver_plugin {
        typedef obj_map<app, unsigned> weight_m;
        typedef obj_pair_map<expr, expr, nlarith::branch_conditions*> bcs_t;
        typedef obj_map<expr, weight_m* > weights_t;
        bcs_t                        m_cache;
        weights_t                    m_weights;
        th_rewriter                  m_rewriter;        
        nlarith::util                m_util;
        expr_safe_replace            m_replace;
        expr_ref_vector              m_trail;
        factor_rewriter_star         m_factor_rw;
        bool                         m_produce_models;
    public:
        nlarith_plugin(i_solver_context& ctx, ast_manager& m, bool produce_models) : 
            qe_solver_plugin(m, m.mk_family_id("arith"), ctx),
            m_rewriter(m),
            m_util(m),
            m_replace(m),
            m_trail(m),
            m_factor_rw(m),
            m_produce_models(produce_models) {
            TRACE("qe", tout << "produce models: " << produce_models << "\n";);
            m_util.set_enable_linear(true); // (produce_models);
        }

        virtual ~nlarith_plugin() {
            bcs_t::iterator it = m_cache.begin(), end = m_cache.end();
            for (; it != end; ++it) {
                dealloc(it->get_value());
            }
            weights_t::iterator it2 = m_weights.begin(), e2 = m_weights.end();
            for (; it2 != e2; ++it2) {
                dealloc(it2->get_value());
            }                        
        }

        virtual bool simplify(expr_ref& fml) { 
            expr_ref tmp(m), tmp2(m);
            m_factor_rw(fml, tmp);
            m_rewriter(tmp, tmp2);
            if (fml.get() != tmp2.get()) {
                fml = tmp2;
                return true;
            }
            return false; 
        }
                
        virtual void assign(contains_app& x, expr* fml, rational const& vl) {
            nlarith::branch_conditions *brs;
            VERIFY (m_cache.find(x.x(), fml, brs));
            SASSERT(vl.is_unsigned());
            SASSERT(vl.get_unsigned() < brs->size());
            expr* branch_fml = brs->branches(vl.get_unsigned());
            expr_ref result(m), tmp(m);
            m_factor_rw(branch_fml, tmp);
            m_rewriter(tmp, result);
            TRACE("qe", tout << vl << " " << mk_pp(result.get(), m) << "\n";);
            m_ctx.add_constraint(true, result);
        }
        
        virtual bool get_num_branches(contains_app& x, 
                                      expr* fml, rational& num_branches) {
            nlarith::branch_conditions *brs;
            if (m_cache.find(x.x(), fml, brs)) {
                num_branches = rational(brs->size());
                return true;
            }
            expr_ref_vector lits(m);
            update_bounds(lits, m_ctx.pos_atoms(), true);
            update_bounds(lits, m_ctx.neg_atoms(), false);

            brs = alloc(nlarith::branch_conditions, m);
            
            TRACE("nlarith", tout << mk_pp(fml, m) << "\n";);
            if (!m_util.create_branches(x.x(), lits.size(), lits.c_ptr(), *brs)) {
                TRACE("nlarith", tout << "no branches for " << mk_pp(x.x(), m) << "\n";);
                dealloc(brs);
                return false;
            }            
            num_branches = rational(brs->size());            
            insert_cache(x.x(), fml, brs);
            return true;
        }
        
        virtual void subst(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) {
            nlarith::branch_conditions *brs;
            VERIFY (m_cache.find(x.x(), fml, brs));
            SASSERT(vl.is_unsigned());
            SASSERT(vl.get_unsigned() < brs->size());
            unsigned j = vl.get_unsigned();
            m_replace.reset();            
            for (unsigned i = 0; i < brs->preds().size(); ++i) {
                m_replace.insert(brs->preds(i), brs->subst(j)[i]);
            }
            m_replace(fml);
            expr_ref tmp(m.mk_and(brs->constraints(j), fml), m);
            m_factor_rw(tmp, fml);
            if (def) {
                m_factor_rw(brs->def(j), *def);
            }
        }

        
        virtual unsigned get_weight(contains_app& x, expr* fml) { 
            obj_map<app, unsigned>* weights = 0;
            unsigned weight = 0;
            if (!m_weights.find(fml, weights)) {
                weights = alloc(weight_m);
                m_weights.insert(fml, weights);
                m_trail.push_back(fml);
                ptr_vector<app> nl_vars;
                m_util.extract_non_linear(to_app(fml), nl_vars);
                for (unsigned i = 0; i < nl_vars.size(); ++i) {
                    weights->insert(nl_vars[i], 100);                   
                }
            }
            if (weights->find(x.x(), weight)) {
                return weight;
            }
            return UINT_MAX; 
        }

        virtual bool solve(conj_enum& conjs, expr* fml) { return false; }

        // we don't need to modify the atom.
        virtual bool mk_atom(expr* e, bool p, expr_ref& result) { return false;  }

        virtual bool is_uninterpreted(app* f) {
            if (m_produce_models) {
                return true;
            }
            switch(f->get_decl_kind()) {
            case OP_NUM:
            case OP_LE:
            case OP_LT:
            case OP_GE:
            case OP_GT:
            case OP_ADD:
            case OP_SUB:
            case OP_UMINUS:
                return false;
            case OP_MUL: {
                arith_util a(m);
                expr* m, *n;
                if (a.is_mul(f, m, n) && (a.is_numeral(m) || a.is_numeral(n))) {
                    return false;
                }
                return true;
            }
            default:                
                return true;
            }
            return true;
        }
    private:

        void insert_cache(app* x, expr* e, nlarith::branch_conditions* brs) {
            m_trail.push_back(x);
            m_trail.push_back(e);
            m_cache.insert(x, e, brs);
        }

        void update_bounds(expr_ref_vector& lits, atom_set const& tbl, bool is_pos) {
            atom_set::iterator it = tbl.begin(), end = tbl.end();
            for (; it != end; ++it) {
                app* e = *it; 
                lits.push_back(is_pos?e:m.mk_not(e));                
            }                
        }
    };


    qe_solver_plugin* mk_arith_plugin(i_solver_context& ctx, bool produce_models, smt_params& p) {
        if (p.m_nlquant_elim) {
            return alloc(nlarith_plugin, ctx, ctx.get_manager(), produce_models);
        }
        else {
            return alloc(arith_plugin, ctx, ctx.get_manager(), p);
        }
    }

}
