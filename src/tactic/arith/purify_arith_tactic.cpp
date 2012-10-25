/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    purify_arith_tactic.h

Abstract:

    Tactic for eliminating arithmetic operators: DIV, IDIV, MOD,
    TO_INT, and optionally (OP_IRRATIONAL_ALGEBRAIC_NUM).

    This tactic uses the simplifier for also eliminating:
    OP_SUB, OP_UMINUS, OP_POWER (optionally), OP_REM, OP_IS_INT. 
    
Author:

    Leonardo de Moura (leonardo) 2011-12-30.

Revision History:

--*/
#include"tactical.h"
#include"rewriter_def.h"
#include"arith_decl_plugin.h"
#include"algebraic_numbers.h"
#include"nnf_tactic.h"
#include"simplify_tactic.h"
#include"th_rewriter.h"
#include"filter_model_converter.h"
#include"ast_smt2_pp.h"

/*
----
Some of the rules needed in the conversion are implemented in
arith_rewriter.cpp. Here is a summary of these rules:

  (^ t (/ p q)) --> (^ (^ t (/ 1 q)) p)  

  (^ t n) --> t*...*t   
  when integer power expansion is requested

  (is-int t) --> t = (to-real (to-int t))

  (rem t1 t2) --> ite(t2 >= 0, (mod t1 t2), -(mod t1 t2))

----
The tactic implements a set of transformation rules.  These rules
create fresh constants or (existential) variables, and add new
constraints to the context.
The context is the set of asserted formulas or a quantifier.

A rule is represented as:

        From --> To | C

It means, any expression that matches From is replaced by To,
and the constraints C are added to the context.
For clarity reasons, I write the constraints using ad-hoc notation.


Rules
  (^ t 0) --> k  |  t != 0 implies k = 1,   t = 0 implies k = 0^0 
  where k is fresh
  0^0 is a constant used to capture the meaning of (^ 0 0).
       
  (^ t (/ 1 n)) --> k  | t = k^n  
  when n is odd
  where k is fresh
 
  (^ t (/ 1 n)) --> k  |  t >= 0 implies t = k^n, t < 0 implies t = neg-root(t, n)   
  when n is even
  where k is fresh
  neg-root is a function symbol used to capture the meaning of a negative root

  (root-obj p(x) i) -->  k  |  p(k) = 0,  l < k < u
  when root object elimination is requested
  where k is fresh
  (l, u) is an isolating interval for the i-th root of p.

  (to-int t) --> k  |  0 <= to-real(k) - t < 1
  where k is a fresh integer constant/variable
  
  (/ t1 t2) --> k |  t2 != 0 implies k*t2 = t1,  t2 = 0 implies k = div-0(t1)
  where k is fresh
  div-0 is a function symbol used to capture the meaning of division by 0.
  
  Remark: If it can be shown that t2 != 0, then the div-0(t1) function application
  vanishes from the formula.

  (div t1 t2) --> k1  |  t2 = 0  \/ t1 = k1 * t2 + k2,
                         t2 = 0  \/ 0 <= k2,
                         t2 = 0  \/ k2 < |t2|,
                         t2 != 0 \/ k1 = idiv-0(t1),
                         t2 != 0 \/ k2 = mod-0(t1)
  k1 is a fresh name for (div t1 t2)
  k2 is a fresh name for (mod t1 t2)
  
  (mod t1 t2) --> k2 |  same constraints as above
*/

struct purify_arith_decls {
    ast_manager & m;
    func_decl * m_int_0_pw_0_decl;    // decl for: int  0^0
    func_decl * m_real_0_pw_0_decl;   // decl for: rel 0^0
    func_decl * m_neg_root_decl;  // decl for: even root of negative (real) number 
    func_decl * m_div_0_decl;     // decl for: x/0
    func_decl * m_idiv_0_decl;    // decl for: div(x, 0)
    func_decl * m_mod_0_decl;     // decl for: mod(x, 0)
    func_decl * m_asin_u_decl;    // decl for: asin(x) when x < -1 or x > 1 
    func_decl * m_acos_u_decl;    // decl for: acos(x) when x < -1 or x > 1
    
    void inc_refs() {
        m.inc_ref(m_int_0_pw_0_decl);
        m.inc_ref(m_real_0_pw_0_decl);
        m.inc_ref(m_neg_root_decl);
        m.inc_ref(m_div_0_decl);
        m.inc_ref(m_idiv_0_decl);
        m.inc_ref(m_mod_0_decl);
        m.inc_ref(m_asin_u_decl);
        m.inc_ref(m_acos_u_decl);
    }

    void dec_refs() {
        m.dec_ref(m_int_0_pw_0_decl);
        m.dec_ref(m_real_0_pw_0_decl);
        m.dec_ref(m_neg_root_decl);
        m.dec_ref(m_div_0_decl);
        m.dec_ref(m_idiv_0_decl);
        m.dec_ref(m_mod_0_decl);
        m.dec_ref(m_asin_u_decl);
        m.dec_ref(m_acos_u_decl);
    }

    purify_arith_decls(arith_util & u):
        m(u.get_manager()) {
        sort * i = u.mk_int();
        sort * r = u.mk_real();
        m_int_0_pw_0_decl = m.mk_const_decl(symbol("0^0-int"), i);
        m_real_0_pw_0_decl = m.mk_const_decl(symbol("0^0-real"), r);
        sort * rr[2] = { r, r };
        m_neg_root_decl = m.mk_func_decl(symbol("neg-root"), 2, rr, r);
        m_div_0_decl = m.mk_func_decl(symbol("/0"), 1, &r, r);
        m_idiv_0_decl = m.mk_func_decl(symbol("div0"), 1, &i, i);
        m_mod_0_decl = m.mk_func_decl(symbol("mod0"), 1, &i, i);
        m_asin_u_decl = m.mk_func_decl(symbol("asin-u"), 1, &r, r);
        m_acos_u_decl = m.mk_func_decl(symbol("acos-u"), 1, &r, r);
        inc_refs();
    }

    purify_arith_decls(ast_manager & _m, 
                       func_decl * int_0_pw_0,
                       func_decl * real_0_pw_0,
                       func_decl * neg_root,
                       func_decl * div_0,
                       func_decl * idiv_0,
                       func_decl * mod_0,
                       func_decl * asin_u,
                       func_decl * acos_u
                       ):
        m(_m),
        m_int_0_pw_0_decl(int_0_pw_0),
        m_real_0_pw_0_decl(real_0_pw_0),
        m_neg_root_decl(neg_root),
        m_div_0_decl(div_0),
        m_idiv_0_decl(idiv_0),
        m_mod_0_decl(mod_0),
        m_asin_u_decl(asin_u),
        m_acos_u_decl(acos_u) {
        inc_refs();
    }
    
    ~purify_arith_decls() { 
        dec_refs();
    }
};

struct purify_arith_proc {
    arith_util &         m_util;
    purify_arith_decls & m_aux_decls;
    bool                 m_produce_proofs;
    bool                 m_elim_root_objs;
    bool                 m_elim_inverses;
    bool                 m_complete;

    purify_arith_proc(arith_util & u, purify_arith_decls & d, bool produce_proofs, bool elim_root_objs, bool elim_inverses, bool complete):
        m_util(u),
        m_aux_decls(d),
        m_produce_proofs(produce_proofs),
        m_elim_root_objs(elim_root_objs),
        m_elim_inverses(elim_inverses),
        m_complete(complete) {
    }

    arith_util & u() { 
        return m_util; 
    }

    ast_manager & m() { 
        return u().get_manager();
    }

    struct rw_cfg : public default_rewriter_cfg {
        purify_arith_proc &  m_owner;
        obj_map<app, expr*>  m_app2fresh;
        obj_map<app, proof*> m_app2pr;
        expr_ref_vector      m_pinned;
        expr_ref_vector      m_new_cnstrs;
        proof_ref_vector     m_new_cnstr_prs;
        expr_ref             m_subst;
        proof_ref            m_subst_pr;
        bool                 m_in_q;
        unsigned             m_var_idx;

        rw_cfg(purify_arith_proc & o, bool in_q):
            m_owner(o),
            m_pinned(o.m()),
            m_new_cnstrs(o.m()),
            m_new_cnstr_prs(o.m()),
            m_subst(o.m()),
            m_subst_pr(o.m()),
            m_in_q(in_q),
            m_var_idx(0) {
        }

        ast_manager & m() { return m_owner.m(); }

        arith_util & u() { return m_owner.u(); }

        bool produce_proofs() const { return m_owner.m_produce_proofs; }
        bool complete() const { return m_owner.m_complete; }
        bool elim_root_objs() const { return m_owner.m_elim_root_objs; }
        bool elim_inverses() const { return m_owner.m_elim_inverses; }

        expr * mk_fresh_var(bool is_int) {
            if (m_in_q) {
                unsigned idx = m_var_idx;
                m_var_idx++;
                return m().mk_var(idx, is_int ? u().mk_int() : u().mk_real());
            }
            else {
                return m().mk_fresh_const(0, is_int ? u().mk_int() : u().mk_real());
            }
        }

        expr * mk_fresh_real_var() { return mk_fresh_var(false); }

        expr * mk_fresh_int_var() { return mk_fresh_var(true); }

        func_decl * div0_decl() { return m_owner.m_aux_decls.m_div_0_decl; }
        func_decl * idiv0_decl() { return m_owner.m_aux_decls.m_idiv_0_decl; }
        func_decl * mod0_decl() { return m_owner.m_aux_decls.m_mod_0_decl; }
        func_decl * int_0_pw_0_decl() { return m_owner.m_aux_decls.m_int_0_pw_0_decl; }
        func_decl * real_0_pw_0_decl() { return m_owner.m_aux_decls.m_real_0_pw_0_decl; }
        func_decl * neg_root_decl() { return m_owner.m_aux_decls.m_neg_root_decl; }
        func_decl * asin_u_decl() { return m_owner.m_aux_decls.m_asin_u_decl; }
        func_decl * acos_u_decl() { return m_owner.m_aux_decls.m_acos_u_decl; }
        
        expr * mk_int_zero() { return u().mk_numeral(rational(0), true); }

        expr * mk_real_zero() { return u().mk_numeral(rational(0), false); }

        bool already_processed(app * t, expr_ref & result, proof_ref & result_pr) { 
            expr * r;
            if (m_app2fresh.find(t, r)) {
                result = r;
                if (produce_proofs())
                    result_pr = m_app2pr.find(t);
                return true;
            }
            return false;
        }
   
        void mk_def_proof(expr * k, expr * def, proof_ref & result_pr) {
            result_pr = 0;
            if (produce_proofs()) {
                expr * eq   = m().mk_eq(k, def);
                proof * pr1 = m().mk_def_intro(eq);
                result_pr   = m().mk_apply_def(k, def, pr1);
            }
        }

        void push_cnstr_pr(proof * def_pr) {
            if (produce_proofs())
                m_new_cnstr_prs.push_back(m().mk_th_lemma(u().get_family_id(), m_new_cnstrs.back(), 1, &def_pr));
        }

        void push_cnstr_pr(proof * def_pr1, proof * def_pr2) {
            if (produce_proofs()) {
                proof * prs[2] = { def_pr1, def_pr2 };
                m_new_cnstr_prs.push_back(m().mk_th_lemma(u().get_family_id(), m_new_cnstrs.back(), 2, prs));
            }
        }

        void push_cnstr(expr * cnstr) {
            m_new_cnstrs.push_back(cnstr);
        }

        void cache_result(app * t, expr * r, proof * pr) {
            m_app2fresh.insert(t, r);
            m_pinned.push_back(t);
            m_pinned.push_back(r);
            if (produce_proofs()) {
                m_app2pr.insert(t, pr);
                m_pinned.push_back(pr);
            }
        }
        
        expr * OR(expr * arg1, expr * arg2) { return m().mk_or(arg1, arg2); }
        expr * AND(expr * arg1, expr * arg2) { return m().mk_and(arg1, arg2); }
        expr * EQ(expr * lhs, expr * rhs) { return m().mk_eq(lhs, rhs); }
        expr * NOT(expr * arg) { return m().mk_not(arg); }

        void process_div(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return;

            expr * k = mk_fresh_real_var();
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            expr * x = args[0];
            expr * y = args[1];
            // y = 0 \/ y*k = x
            push_cnstr(OR(EQ(y, mk_real_zero()),
                          EQ(u().mk_mul(y, k), x)));
            push_cnstr_pr(result_pr);

            if (complete()) {
                // y != 0 \/ k = div-0(x)
                push_cnstr(OR(NOT(EQ(y, mk_real_zero())),
                              EQ(k, m().mk_app(div0_decl(), x))));
                push_cnstr_pr(result_pr);
            }
        }
   
        void process_idiv(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            app_ref div_app(m());
            div_app = m().mk_app(f, num, args);
            if (already_processed(div_app, result, result_pr))
                return;

            expr * k1 = mk_fresh_int_var();
            result = k1;
            mk_def_proof(k1, div_app, result_pr);
            cache_result(div_app, result, result_pr);
            
            expr * k2 = mk_fresh_int_var();
            app_ref mod_app(m());
            proof_ref mod_pr(m());
            mod_app = u().mk_mod(args[0], args[1]);
            mk_def_proof(k2, mod_app, mod_pr);
            cache_result(mod_app, k2, mod_pr);
            
            expr * x = args[0];
            expr * y = args[1];
            //  (div x y) --> k1  |  y = 0  \/ x = k1 * y + k2,
            //                       y = 0  \/ 0 <= k2,
            //                       y = 0  \/ k2 < |y|,
            //                       y != 0 \/ k1 = idiv-0(x),
            //                       y != 0 \/ k2 = mod-0(x)
            //  We can write y = 0  \/ k2 < |y| as:
            //       y > 0 implies k2 < y   --->  y <= 0 \/ k2 < y
            //       y < 0 implies k2 < -y  --->  y >= 0 \/ k2 < -y
            //     
            expr * zero = mk_int_zero();
            push_cnstr(OR(EQ(y, zero), EQ(x, u().mk_add(u().mk_mul(k1, y), k2))));
            push_cnstr_pr(result_pr, mod_pr);

            push_cnstr(OR(EQ(y, zero), u().mk_le(zero, k2)));
            push_cnstr_pr(mod_pr);

            push_cnstr(OR(u().mk_le(y, zero), u().mk_lt(k2, y)));
            push_cnstr_pr(mod_pr);

            push_cnstr(OR(u().mk_ge(y, zero), u().mk_lt(k2, u().mk_mul(u().mk_numeral(rational(-1), true), y))));
            push_cnstr_pr(mod_pr);

            if (complete()) {
                push_cnstr(OR(NOT(EQ(y, zero)), EQ(k1, m().mk_app(idiv0_decl(), x))));
                push_cnstr_pr(result_pr);

                push_cnstr(OR(NOT(EQ(y, zero)), EQ(k2, m().mk_app(mod0_decl(), x))));
                push_cnstr_pr(mod_pr);
            }
        }
   
        void process_mod(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return;
            process_idiv(f, num, args, result, result_pr); // it will create mod
            VERIFY(already_processed(t, result, result_pr));
        }
        
        void process_to_int(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return;

            expr * k = mk_fresh_int_var();
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            expr * x = args[0];
            // to-real(k) - x >= 0
            expr * diff = u().mk_add(u().mk_to_real(k), u().mk_mul(u().mk_numeral(rational(-1), false), x));
            push_cnstr(u().mk_ge(diff, mk_real_zero()));
            push_cnstr_pr(result_pr);
            
            // not(to-real(k) - x >= 1)
            push_cnstr(NOT(u().mk_ge(diff, u().mk_numeral(rational(1), false))));
            push_cnstr_pr(result_pr);
        }
   
        br_status process_power(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            rational y;
            if (!u().is_numeral(args[1], y))
                return BR_FAILED;
            if (y.is_int() && !y.is_zero())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return BR_DONE;

            bool is_int = u().is_int(args[0]);

            expr * k = mk_fresh_var(is_int);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            expr * x = args[0];
            expr * zero = u().mk_numeral(rational(0), is_int);
            expr * one  = u().mk_numeral(rational(1), is_int);
            if (y.is_zero()) {
                // (^ x 0) --> k  |  x != 0 implies k = 1,   x = 0 implies k = 0^0 
                push_cnstr(OR(EQ(x, zero), EQ(k, one)));
                push_cnstr_pr(result_pr);
                if (complete()) {
                    func_decl * z_pw_z = is_int ? int_0_pw_0_decl() : real_0_pw_0_decl();
                    push_cnstr(OR(NOT(EQ(x, zero)), EQ(k, m().mk_const(z_pw_z))));
                    push_cnstr_pr(result_pr);
                }
            }
            else if (!is_int) {
                SASSERT(!y.is_int());
                SASSERT(numerator(y).is_one());
                rational n = denominator(y);
                if (!n.is_even()) {
                    // (^ x (/ 1 n)) --> k  | x = k^n  
                    // when n is odd
                    push_cnstr(EQ(x, u().mk_power(k, u().mk_numeral(n, false))));
                    push_cnstr_pr(result_pr);
                }
                else {
                    SASSERT(n.is_even());
                    // (^ x (/ 1 n)) --> k  |  x >= 0 implies (x = k^n and k >= 0), x < 0 implies k = neg-root(x, n)   
                    // when n is even
                    push_cnstr(OR(NOT(u().mk_ge(x, zero)),
                                  AND(EQ(x, u().mk_power(k, u().mk_numeral(n, false))),
                                      u().mk_ge(k, zero))));
                    push_cnstr_pr(result_pr);
                    if (complete()) {
                        push_cnstr(OR(u().mk_ge(x, zero),
                                      EQ(k, m().mk_app(neg_root_decl(), x, u().mk_numeral(n, false)))));
                        push_cnstr_pr(result_pr);
                    }
                }
            }
            else {
                // root not supported for integers.
                SASSERT(is_int);
                SASSERT(!y.is_int());
                return BR_FAILED;
            }
            return BR_DONE;
        }

        void process_irrat(app * s, expr_ref & result, proof_ref & result_pr) { 
            if (already_processed(s, result, result_pr))
                return;

            expr * k = mk_fresh_real_var();
            result = k;
            mk_def_proof(k, s, result_pr);
            cache_result(s, result, result_pr);

            anum_manager & am = u().am();
            anum const & a = u().to_irrational_algebraic_numeral(s);
            scoped_mpz_vector p(am.qm());
            am.get_polynomial(a, p);
            rational lower, upper;
            am.get_lower(a, lower);
            am.get_upper(a, upper);
            unsigned sz = p.size();
            SASSERT(sz > 2);
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < sz; i++) {
                if (am.qm().is_zero(p[i]))
                    continue;
                rational coeff = rational(p[i]);
                if (i == 0) {
                    args.push_back(u().mk_numeral(coeff, false));
                }
                else {
                    expr * m;
                    if (i == 1)
                        m = k;
                    else
                        m = u().mk_power(k, u().mk_numeral(rational(i), false));
                    args.push_back(u().mk_mul(u().mk_numeral(coeff, false), m));
                }
            }
            SASSERT(args.size() >= 2);
            push_cnstr(EQ(u().mk_add(args.size(), args.c_ptr()), mk_real_zero()));
            push_cnstr_pr(result_pr);
            push_cnstr(u().mk_lt(u().mk_numeral(lower, false), k));
            push_cnstr_pr(result_pr);
            push_cnstr(u().mk_lt(k, u().mk_numeral(upper, false)));
            push_cnstr_pr(result_pr);
        }

        br_status process_asin(func_decl * f, expr * x, expr_ref & result, proof_ref & result_pr) {
            if (!elim_inverses())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, x);
            if (already_processed(t, result, result_pr))
                return BR_DONE;
            
            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            // Constraints:
            // -1 <= x <= 1 implies sin(k) = x, -pi/2 <= k <= pi/2
            // If complete()
            // x < -1       implies k = asin_u(x) 
            // x >  1       implies k = asin_u(x) 
            expr * one   = u().mk_numeral(rational(1), false);
            expr * mone  = u().mk_numeral(rational(-1), false);
            expr * pi2   = u().mk_mul(u().mk_numeral(rational(1,2), false), u().mk_pi());
            expr * mpi2  = u().mk_mul(u().mk_numeral(rational(-1,2), false), u().mk_pi());
            // -1 <= x <= 1 implies sin(k) = x, -pi/2 <= k <= pi/2
            push_cnstr(OR(OR(NOT(u().mk_ge(x, mone)),
                             NOT(u().mk_le(x, one))),
                          AND(EQ(x, u().mk_sin(k)),
                              AND(u().mk_ge(k, mpi2),
                                  u().mk_le(k, pi2)))));
            push_cnstr_pr(result_pr);
            if (complete()) {
                // x < -1       implies k = asin_u(x) 
                // x >  1       implies k = asin_u(x) 
                push_cnstr(OR(u().mk_ge(x, mone),
                              EQ(k, m().mk_app(asin_u_decl(), x))));
                push_cnstr_pr(result_pr);
                push_cnstr(OR(u().mk_le(x, one),
                              EQ(k, m().mk_app(asin_u_decl(), x))));
                push_cnstr_pr(result_pr);
            }
            return BR_DONE;
        }

        br_status process_acos(func_decl * f, expr * x, expr_ref & result, proof_ref & result_pr) {
            if (!elim_inverses())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, x);
            if (already_processed(t, result, result_pr))
                return BR_DONE;
            
            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            // Constraints:
            // -1 <= x <= 1 implies cos(k) = x, 0 <= k <= pi
            // If complete()
            // x < -1       implies k = acos_u(x) 
            // x >  1       implies k = acos_u(x) 
            expr * one   = u().mk_numeral(rational(1), false);
            expr * mone  = u().mk_numeral(rational(-1), false);
            expr * pi    = u().mk_pi();
            expr * zero  = u().mk_numeral(rational(0), false);
            // -1 <= x <= 1 implies cos(k) = x, 0 <= k <= pi
            push_cnstr(OR(OR(NOT(u().mk_ge(x, mone)),
                             NOT(u().mk_le(x, one))),
                          AND(EQ(x, u().mk_cos(k)),
                              AND(u().mk_ge(k, zero),
                                  u().mk_le(k, pi)))));
            push_cnstr_pr(result_pr);
            if (complete()) {
                // x < -1       implies k = acos_u(x) 
                // x >  1       implies k = acos_u(x) 
                push_cnstr(OR(u().mk_ge(x, mone),
                              EQ(k, m().mk_app(acos_u_decl(), x))));
                push_cnstr_pr(result_pr);
                push_cnstr(OR(u().mk_le(x, one),
                              EQ(k, m().mk_app(acos_u_decl(), x))));
                push_cnstr_pr(result_pr);
            }
            return BR_DONE;
        }

        br_status process_atan(func_decl * f, expr * x, expr_ref & result, proof_ref & result_pr) {
            if (!elim_inverses())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, x);
            if (already_processed(t, result, result_pr))
                return BR_DONE;
            
            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            // Constraints:
            // tan(k) = x, -pi/2 < k < pi/2
            expr * pi2   = u().mk_mul(u().mk_numeral(rational(1,2), false), u().mk_pi());
            expr * mpi2  = u().mk_mul(u().mk_numeral(rational(-1,2), false), u().mk_pi());
            push_cnstr(AND(EQ(x, u().mk_tan(k)),
                           AND(u().mk_gt(k, mpi2),
                               u().mk_lt(k, pi2))));
            push_cnstr_pr(result_pr);
            return BR_DONE;
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            if (f->get_family_id() != u().get_family_id())
                return BR_FAILED;
            switch (f->get_decl_kind()) {
            case OP_DIV: 
                process_div(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_IDIV: 
                process_idiv(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_MOD:
                process_mod(f, num, args, result, result_pr);                
                return BR_DONE;
            case OP_TO_INT:
                process_to_int(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_POWER:
                return process_power(f, num, args, result, result_pr);
            case OP_ASIN:
                return process_asin(f, args[0], result, result_pr);
            case OP_ACOS:
                return process_acos(f, args[0], result, result_pr);
            case OP_ATAN:
                return process_atan(f, args[0], result, result_pr);
            default:
                return BR_FAILED;
            }
        }
        
        bool get_subst(expr * s, expr * & t, proof * & t_pr) { 
            if (is_quantifier(s)) {
                m_owner.process_quantifier(to_quantifier(s), m_subst, m_subst_pr);
                t    = m_subst.get();
                t_pr = m_subst_pr.get();
                return true;
            }
            else if (u().is_irrational_algebraic_numeral(s) && elim_root_objs()) {
                process_irrat(to_app(s), m_subst, m_subst_pr);
                t    = m_subst.get();
                t_pr = m_subst_pr.get();
                return true;
            }
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(purify_arith_proc & o, bool in_q):
            rewriter_tpl<rw_cfg>(o.m(), o.m_produce_proofs, m_cfg),
            m_cfg(o, in_q) {
        }
    };

    /**
       \brief Return the number of (auxiliary) variables needed for converting an expression.
    */
    struct num_vars_proc {
        arith_util &     m_util;
        expr_fast_mark1  m_visited;
        ptr_vector<expr> m_todo;
        unsigned         m_num_vars;
        bool             m_elim_root_objs;
        
        num_vars_proc(arith_util & u, bool elim_root_objs):
            m_util(u),
            m_elim_root_objs(elim_root_objs) {
        }
        
        void visit(expr * t) {
            if (m_visited.is_marked(t)) 
                return;
            m_visited.mark(t);
            m_todo.push_back(t);
        }
        
        void process(app * t) {
            if (t->get_family_id() == m_util.get_family_id()) {
                if (m_util.is_power(t)) {
                    rational k;
                    if (m_util.is_numeral(t->get_arg(1), k) && (k.is_zero() || !k.is_int())) {
                        m_num_vars++;
                    }
                }
                else if (m_util.is_div(t)    || 
                         m_util.is_idiv(t)   || 
                         m_util.is_mod(t)    || 
                         m_util.is_to_int(t) || 
                         (m_util.is_irrational_algebraic_numeral(t) && m_elim_root_objs)) {
                    m_num_vars++;
                }
            }
            unsigned num_args = t->get_num_args();
            for (unsigned i = 0; i < num_args; i++)
                visit(t->get_arg(i));
        }
        
        unsigned operator()(expr * t) {
            m_num_vars = 0;
            visit(t);
            while (!m_todo.empty()) {
                expr * t = m_todo.back();
                m_todo.pop_back();
                if (is_app(t)) 
                    process(to_app(t));
            }
            m_visited.reset();
            return m_num_vars;
        }
    };
    
    void process_quantifier(quantifier * q, expr_ref & result, proof_ref & result_pr) { 
        result_pr = 0;
        num_vars_proc p(u(), m_elim_root_objs);
        expr_ref body(m());
        unsigned num_vars = p(q->get_expr());
        if (num_vars > 0) {
            // open space for aux vars
            var_shifter shifter(m());
            shifter(q->get_expr(), num_vars, body);
        }
        else {
            body = q->get_expr();
        }

        rw r(*this, true);
        expr_ref new_body(m());
        proof_ref new_body_pr(m());
        r(body, new_body, new_body_pr);
        TRACE("purify_arith", 
              tout << "num_vars: " << num_vars << "\n";
              tout << "body: " << mk_ismt2_pp(body, m()) << "\nnew_body: " << mk_ismt2_pp(new_body, m()) << "\n";);
        if (num_vars == 0) {
            result = m().update_quantifier(q, new_body);
            if (m_produce_proofs)
                result_pr = m().mk_quant_intro(q, to_quantifier(result.get()), result_pr);
        }
        else {
            expr_ref_vector & cnstrs = r.cfg().m_new_cnstrs;
            cnstrs.push_back(new_body);
            new_body = m().mk_and(cnstrs.size(), cnstrs.c_ptr());
            ptr_buffer<sort> sorts;
            buffer<symbol>   names;
            for (unsigned i = 0; i < num_vars; i++) {
                sorts.push_back(u().mk_real());
                names.push_back(m().mk_fresh_var_name("x"));
            }
            new_body = m().mk_exists(num_vars, sorts.c_ptr(), names.c_ptr(), new_body);
            result = m().update_quantifier(q, new_body);
            if (m_produce_proofs) {
                proof_ref_vector & cnstr_prs = r.cfg().m_new_cnstr_prs;
                cnstr_prs.push_back(result_pr);
                // TODO: improve proof
                result_pr = m().mk_quant_intro(q, to_quantifier(result.get()), 
                                               m().mk_rewrite_star(q->get_expr(), new_body, cnstr_prs.size(), cnstr_prs.c_ptr())); 
            }
        }
    }

    void operator()(goal & g, model_converter_ref & mc, bool produce_models) {
        rw r(*this, false);
        // purify
        expr_ref   new_curr(m());
        proof_ref  new_pr(m());
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g.form(i);
            r(curr, new_curr, new_pr);
            if (m_produce_proofs) {
                proof * pr = g.pr(i);
                new_pr     = m().mk_modus_ponens(pr, new_pr);
            }
            g.update(i, new_curr, new_pr, g.dep(i));
        }
        
        // add cnstraints
        sz = r.cfg().m_new_cnstrs.size();
        for (unsigned i = 0; i < sz; i++) {
            g.assert_expr(r.cfg().m_new_cnstrs.get(i), m_produce_proofs ? r.cfg().m_new_cnstr_prs.get(i) : 0, 0);
        }
        
        // add filter_model_converter to eliminate auxiliary variables from model
        if (produce_models) {
            filter_model_converter * fmc = alloc(filter_model_converter, m());
            mc = fmc;
            obj_map<app, expr*> & f2v = r.cfg().m_app2fresh;
            obj_map<app, expr*>::iterator it  = f2v.begin();
            obj_map<app, expr*>::iterator end = f2v.end();
            for (; it != end; ++it) {
                app * v = to_app(it->m_value);
                SASSERT(is_uninterp_const(v));
                fmc->insert(v->get_decl());
            }
        }
    }
};

class purify_arith_tactic : public tactic {
    arith_util         m_util;
    purify_arith_decls m_aux_decls;
    params_ref         m_params;
public:
    purify_arith_tactic(ast_manager & m, params_ref const & p):
        m_util(m),
        m_aux_decls(m_util),
        m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(purify_arith_tactic, m, m_params);
    }
        
    virtual ~purify_arith_tactic() {
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
    }

    virtual void collect_param_descrs(param_descrs & r) {
        r.insert(":complete", CPK_BOOL, 
                 "(default: true) add constraints to make sure that any interpretation of a underspecified arithmetic operators is a functio. The result will include additional uninterpreted functions/constants: /0, div0, mod0, 0^0, neg-root");
        r.insert(":elim-root-objects", CPK_BOOL,
                 "(default: true) eliminate root objects.");
        r.insert(":elim-inverses", CPK_BOOL,
                 "(default: true) eliminate inverse trigonometric functions (asin, acos, atan).");
        th_rewriter::get_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("purify-arith", *g);
            bool produce_proofs = g->proofs_enabled();
            bool produce_models = g->models_enabled();
            bool elim_root_objs = m_params.get_bool(":elim-root-objects", true);
            bool elim_inverses  = m_params.get_bool(":elim-inverses", true);
            bool complete       = m_params.get_bool(":complete", true);
            purify_arith_proc proc(m_util, m_aux_decls, produce_proofs, elim_root_objs, elim_inverses, complete);
            
            proc(*(g.get()), mc, produce_models);
            
            g->inc_depth();
            result.push_back(g.get());
            TRACE("purify_arith", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }
    
    virtual void cleanup() {
    }

    virtual void set_cancel(bool f) {
    }
};

tactic * mk_purify_arith_tactic(ast_manager & m, params_ref const & p) {
    params_ref elim_rem_p = p;
    elim_rem_p.set_bool(":elim-rem", true);
    
    params_ref skolemize_p;
    skolemize_p.set_bool(":skolemize", false);

    return and_then(using_params(mk_snf_tactic(m, skolemize_p), skolemize_p),
                    using_params(mk_simplify_tactic(m, elim_rem_p), elim_rem_p),
                    alloc(purify_arith_tactic, m, p),
                    mk_simplify_tactic(m, p));
}
