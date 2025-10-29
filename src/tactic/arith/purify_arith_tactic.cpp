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
#include "tactic/tactical.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/arith_decl_plugin.h"
#include "math/polynomial/algebraic_numbers.h"
#include "tactic/core/nnf_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/converters/generic_model_converter.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_replacer.h"

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

struct purify_arith_proc {
    arith_util &         m_util;
    goal &               m_goal;
    bool                 m_produce_proofs;
    bool                 m_elim_root_objs;
    bool                 m_elim_inverses;
    bool                 m_complete;

    ast_mark             m_unsafe_exprs;
    bool                 m_unsafe_found;
    obj_map<app, std::pair<expr*, expr*> > m_sin_cos;
    expr_ref_vector      m_pinned;

    purify_arith_proc(goal & g, arith_util & u, bool produce_proofs, bool elim_root_objs, bool elim_inverses, bool complete):
        m_util(u),
        m_goal(g),
        m_produce_proofs(produce_proofs),
        m_elim_root_objs(elim_root_objs),
        m_elim_inverses(elim_inverses),
        m_complete(complete),
        m_unsafe_found(false),
        m_pinned(m()) {
    }

    arith_util & u() { 
        return m_util; 
    }

    ast_manager & m() { 
        return u().get_manager();
    }

    struct find_unsafe_proc {
        purify_arith_proc& m_owner;
        find_unsafe_proc(purify_arith_proc& o) : m_owner(o) {}
        void operator()(app* a) {
            if (!m_owner.u().is_sin(a) && 
                !m_owner.u().is_cos(a)) {               
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    m_owner.m_unsafe_exprs.mark(a->get_arg(i), true);
                }
            }
        }
        void operator()(quantifier *q) {}
        void operator()(var* v) {}
    };

    void find_unsafe() {
        if (m_unsafe_found) return;
        find_unsafe_proc proc(*this);
        expr_fast_mark1 visited;
        unsigned sz = m_goal.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = m_goal.form(i);
            for_each_expr_core<find_unsafe_proc, expr_fast_mark1, true, true>(proc, visited, curr);
        }        
        m_unsafe_found = true;
    }

    bool convert_basis(expr* theta, expr*& x, expr*& y) {
        if (!is_uninterp_const(theta)) {
            return false;
        }
        find_unsafe();
        if (m_unsafe_exprs.is_marked(theta)) {
            return false;
        }
        std::pair<expr*, expr*> pair;
        if (!m_sin_cos.find(to_app(theta), pair)) {
            pair.first = m().mk_fresh_const(nullptr, u().mk_real());
            pair.second = m().mk_fresh_const(nullptr, u().mk_real());
            m_sin_cos.insert(to_app(theta), pair);
            m_pinned.push_back(pair.first);
            m_pinned.push_back(pair.second);
            m_pinned.push_back(theta);
            // TBD for model conversion
        }
        x = pair.first;
        y = pair.second;
        return true;
    }
  
    struct bin_def {
        expr* x, *y, *d;
        bin_def(expr* x, expr* y, expr* d): x(x), y(y), d(d) {}
    };

    struct rw_cfg : public default_rewriter_cfg {
        purify_arith_proc &  m_owner;
        obj_hashtable<func_decl>  m_cannot_purify;
        obj_map<app, expr*>  m_app2fresh;
        obj_map<app, proof*> m_app2pr;
        expr_ref_vector      m_pinned;
        expr_ref_vector      m_new_cnstrs;
        proof_ref_vector     m_new_cnstr_prs;
        svector<bin_def>     m_divs, m_idivs, m_mods;
        expr_ref             m_ipower0, m_rpower0;
        expr_ref             m_subst;
        proof_ref            m_subst_pr;
        expr_ref_vector      m_new_vars;

        rw_cfg(purify_arith_proc & o):
            m_owner(o),
            m_pinned(o.m()),
            m_new_cnstrs(o.m()),
            m_new_cnstr_prs(o.m()),
            m_ipower0(o.m()),
            m_rpower0(o.m()),
            m_subst(o.m()),           
            m_subst_pr(o.m()),
            m_new_vars(o.m()) {
            init_cannot_purify();
        }

        ast_manager & m() { return m_owner.m(); }

        arith_util & u() { return m_owner.u(); }

        bool produce_proofs() const { return m_owner.m_produce_proofs; }
        bool complete() const { return m_owner.m_complete; }
        bool elim_root_objs() const { return m_owner.m_elim_root_objs; }
        bool elim_inverses() const { return m_owner.m_elim_inverses; }

        void init_cannot_purify() {
            struct proc {
                rw_cfg& o;
                proc(rw_cfg& o):o(o) {}
                void operator()(app* a) {
                    for (expr* arg : *a) {
                        if (!is_ground(arg)) {
                            auto* f = a->get_decl();
                            o.m_cannot_purify.insert(f);
                            break;
                        }
                    }
                }
                void operator()(expr* ) {}
            };
            
            expr_fast_mark1 visited;
            proc p(*this);
            unsigned sz = m_owner.m_goal.size();
            for (unsigned i = 0; i < sz; i++) {
                expr* f = m_owner.m_goal.form(i);
                for_each_expr_core<proc, expr_fast_mark1, true, true>(p, visited, f);
            }
        }

        expr * mk_fresh_var(bool is_int) {
            expr * r = m().mk_fresh_const(nullptr, is_int ? u().mk_int() : u().mk_real());
            m_new_vars.push_back(r);
            return r;
        }

        expr * mk_fresh_real_var() { return mk_fresh_var(false); }

        expr * mk_fresh_int_var() { return mk_fresh_var(true); }

        expr * mk_int_zero() { return u().mk_numeral(rational(0), true); }

        expr * mk_real_zero() { return u().mk_numeral(rational(0), false); }

        expr * mk_real_one() { return u().mk_numeral(rational(1), false); }

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
            result_pr = nullptr;
            if (produce_proofs()) {
                expr * eq   = m().mk_eq(def, k);
                proof * pr1 = m().mk_def_intro(eq);
                result_pr   = m().mk_apply_def(def, k, pr1);
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
            TRACE(purify_arith, tout << mk_pp(cnstr, m()) << "\n";);
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
            expr_ref y_is_zero(m());
            expr_ref mul_term(m());
            expr_ref mul_eq_x(m());
            expr_ref disj_y_zero_or_mul(m());
            expr_ref zero_val(m());
            zero_val = mk_real_zero();
            y_is_zero = EQ(y, zero_val);
            mul_term = u().mk_mul(y, k);
            mul_eq_x = EQ(mul_term, x);
            disj_y_zero_or_mul = OR(y_is_zero, mul_eq_x);
            push_cnstr(disj_y_zero_or_mul);
            push_cnstr_pr(result_pr);
            rational r;
            if (complete()) {
                // y != 0 \/ k = div-0(x)
                expr_ref not_y_zero(m());
                expr_ref div_zero(m());
                expr_ref k_eq_div_zero(m());
                expr_ref disj_nonzero_or_def(m());
                not_y_zero = NOT(y_is_zero);
                div_zero = u().mk_div(x, zero_val);
                k_eq_div_zero = EQ(k, div_zero);
                disj_nonzero_or_def = OR(not_y_zero, k_eq_div_zero);
                push_cnstr(disj_nonzero_or_def);
                push_cnstr_pr(result_pr);
            }
            m_divs.push_back(bin_def(x, y, k));
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
            expr * x = args[0];
            expr * y = args[1];
            mod_app = u().mk_mod(x, y);
            mk_def_proof(k2, mod_app, mod_pr);
            cache_result(mod_app, k2, mod_pr);
            
            m_mods.push_back(bin_def(x, y, k2));
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
            expr_ref y_eq_zero(m());
            expr_ref mul_k1_y(m());
            expr_ref sum_expr(m());
            expr_ref x_eq_sum(m());
            expr_ref or_y_zero_or_sum(m());
            y_eq_zero = EQ(y, zero);
            mul_k1_y = u().mk_mul(k1, y);
            sum_expr = u().mk_add(mul_k1_y, k2);
            x_eq_sum = EQ(x, sum_expr);
            or_y_zero_or_sum = OR(y_eq_zero, x_eq_sum);
            push_cnstr(or_y_zero_or_sum);
            push_cnstr_pr(result_pr, mod_pr);

            expr_ref zero_le_k2(m());
            expr_ref or_y_zero_or_le(m());
            zero_le_k2 = u().mk_le(zero, k2);
            or_y_zero_or_le = OR(y_eq_zero, zero_le_k2);
            push_cnstr(or_y_zero_or_le);
            push_cnstr_pr(mod_pr);

            expr_ref y_le_zero(m());
            expr_ref k2_lt_y(m());
            expr_ref or_y_le_or_lt(m());
            y_le_zero = u().mk_le(y, zero);
            k2_lt_y = u().mk_lt(k2, y);
            or_y_le_or_lt = OR(y_le_zero, k2_lt_y);
            push_cnstr(or_y_le_or_lt);
            push_cnstr_pr(mod_pr);

            expr_ref y_ge_zero(m());
            expr_ref neg_one(m());
            expr_ref neg_y(m());
            expr_ref k2_lt_neg_y(m());
            expr_ref or_y_ge_or_lt(m());
            y_ge_zero = u().mk_ge(y, zero);
            neg_one = u().mk_numeral(rational(-1), true);
            neg_y = u().mk_mul(neg_one, y);
            k2_lt_neg_y = u().mk_lt(k2, neg_y);
            or_y_ge_or_lt = OR(y_ge_zero, k2_lt_neg_y);
            push_cnstr(or_y_ge_or_lt);
            push_cnstr_pr(mod_pr);

            rational r;
            if (complete() && (!u().is_numeral(y, r) || r.is_zero())) {
                expr_ref not_y_zero(m());
                expr_ref idiv_zero(m());
                expr_ref k1_eq_idiv_zero(m());
                expr_ref or_nonzero_or_idiv(m());
                not_y_zero = NOT(y_eq_zero);
                idiv_zero = u().mk_idiv(x, zero);
                k1_eq_idiv_zero = EQ(k1, idiv_zero);
                or_nonzero_or_idiv = OR(not_y_zero, k1_eq_idiv_zero);
                push_cnstr(or_nonzero_or_idiv);
                push_cnstr_pr(result_pr);

                expr_ref mod_zero(m());
                expr_ref k2_eq_mod_zero(m());
                expr_ref or_nonzero_or_mod(m());
                mod_zero = u().mk_mod(x, zero);
                k2_eq_mod_zero = EQ(k2, mod_zero);
                or_nonzero_or_mod = OR(not_y_zero, k2_eq_mod_zero);
                push_cnstr(or_nonzero_or_mod);
                push_cnstr_pr(mod_pr);
            }
            m_idivs.push_back(bin_def(x, y, k1));
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
            // x - to-real(k) >= 0
            
            expr * diff = u().mk_add(x, u().mk_mul(u().mk_numeral(rational(-1), false), u().mk_to_real(k)));
            push_cnstr(u().mk_ge(diff, mk_real_zero()));
            push_cnstr_pr(result_pr);
            
            // not(x - to-real(k) >= 1)
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

            expr * x = args[0];
            bool is_int = u().is_int(x);

            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);
            
            expr_ref zero(u().mk_numeral(rational(0), is_int), m());
            expr_ref one(u().mk_numeral(rational(1), is_int), m());
            if (y.is_zero()) {
                expr* p0;
                if (is_int) {
                    if (!m_ipower0) m_ipower0 = mk_fresh_var(false);
                    p0 = m_ipower0;
                }
                else {
                    if (!m_rpower0) m_rpower0 = mk_fresh_var(false);
                    p0 = m_rpower0;
                }

                // (^ x 0) --> k  |  x != 0 implies k = 1,   x = 0 implies k = 0^0 
                expr_ref x_eq_zero(m());
                expr_ref k_eq_one(m());
                expr_ref disj_zero_or_one(m());
                x_eq_zero = EQ(x, zero);
                k_eq_one = EQ(k, one);
                disj_zero_or_one = OR(x_eq_zero, k_eq_one);
                push_cnstr(disj_zero_or_one);
                push_cnstr_pr(result_pr);
                expr_ref not_x_eq_zero(m());
                expr_ref k_eq_p0(m());
                expr_ref disj_nonzero_or_p0(m());
                not_x_eq_zero = NOT(x_eq_zero);
                k_eq_p0 = EQ(k, p0);
                disj_nonzero_or_p0 = OR(not_x_eq_zero, k_eq_p0);
                push_cnstr(disj_nonzero_or_p0);
                push_cnstr_pr(result_pr);
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
                    expr_ref ge_x_zero(m());
                    expr_ref not_ge_x_zero(m());
                    expr_ref power_arg(m());
                    expr_ref x_eq_power(m());
                    expr_ref ge_k_zero(m());
                    expr_ref conj_eq_and_ge(m());
                    expr_ref disj_even_case(m());
                    ge_x_zero = u().mk_ge(x, zero);
                    not_ge_x_zero = NOT(ge_x_zero);
                    power_arg = u().mk_numeral(n, false);
                    x_eq_power = EQ(x, u().mk_power(k, power_arg));
                    ge_k_zero = u().mk_ge(k, zero);
                    conj_eq_and_ge = AND(x_eq_power, ge_k_zero);
                    disj_even_case = OR(not_ge_x_zero, conj_eq_and_ge);
                    push_cnstr(disj_even_case);
                    push_cnstr_pr(result_pr);

                    expr_ref neg_root_arg(m());
                    expr_ref k_eq_neg_root(m());
                    expr_ref or_ge_or_neg_root(m());
                    neg_root_arg = u().mk_numeral(n, false);
                    k_eq_neg_root = EQ(k, u().mk_neg_root(x, neg_root_arg));
                    or_ge_or_neg_root = OR(ge_x_zero, k_eq_neg_root);
                    push_cnstr(or_ge_or_neg_root);
                    push_cnstr_pr(result_pr);
                }
//                else {
//                    return BR_FAILED;
//                }
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
            push_cnstr(EQ(u().mk_add(args.size(), args.data()), mk_real_zero()));
            push_cnstr_pr(result_pr);
            push_cnstr(u().mk_lt(u().mk_numeral(lower, false), k));
            push_cnstr_pr(result_pr);
            push_cnstr(u().mk_lt(k, u().mk_numeral(upper, false)));
            push_cnstr_pr(result_pr);
        }

        br_status process_sin_cos(bool first, func_decl *f, expr * theta, expr_ref & result, proof_ref & result_pr) {
            expr* x, *y;
            if (m_owner.convert_basis(theta, x, y)) {
                result = first ? x : y;
                app_ref t(m().mk_app(f, theta), m());
                mk_def_proof(result, t, result_pr);
                cache_result(t, result, result_pr);
                push_cnstr(EQ(mk_real_one(), u().mk_add(u().mk_mul(x, x), u().mk_mul(y, y))));
                push_cnstr_pr(result_pr);
                return BR_DONE;
            }
            else {
                expr_ref s(u().mk_sin(theta), m());
                expr_ref c(u().mk_cos(theta), m());
                expr_ref axm(EQ(mk_real_one(), u().mk_add(u().mk_mul(s, s), u().mk_mul(c, c))), m());
                push_cnstr(axm);
                push_cnstr_pr(m().mk_asserted(axm));
                return BR_FAILED;
            }
        }

        br_status process_sin(func_decl *f, expr * theta, expr_ref & result, proof_ref & result_pr) {
            return process_sin_cos(true, f, theta, result, result_pr);
        }

        br_status process_cos(func_decl *f, expr * theta, expr_ref & result, proof_ref & result_pr) {
            return process_sin_cos(false, f, theta, result, result_pr);
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
            expr_ref ge_x_mone(m());
            expr_ref le_x_one(m());
            expr_ref not_ge_x_mone(m());
            expr_ref not_le_x_one(m());
            expr_ref sin_k(m());
            expr_ref eq_x_sin(m());
            expr_ref ge_k_mpi2(m());
            expr_ref le_k_pi2(m());
            expr_ref bounds_conj(m());
            expr_ref sin_conj(m());
            expr_ref interval_disj(m());
            ge_x_mone = u().mk_ge(x, mone);
            le_x_one = u().mk_le(x, one);
            not_ge_x_mone = NOT(ge_x_mone);
            not_le_x_one = NOT(le_x_one);
            sin_k = u().mk_sin(k);
            eq_x_sin = EQ(x, sin_k);
            ge_k_mpi2 = u().mk_ge(k, mpi2);
            le_k_pi2 = u().mk_le(k, pi2);
            bounds_conj = AND(ge_k_mpi2, le_k_pi2);
            sin_conj = AND(eq_x_sin, bounds_conj);
            interval_disj = OR(OR(not_ge_x_mone, not_le_x_one), sin_conj);
            push_cnstr(interval_disj);
            push_cnstr_pr(result_pr);
            if (complete()) {
                // x < -1       implies k = asin_u(x) 
                // x >  1       implies k = asin_u(x) 
                expr_ref ge_x_mone_guard(m());
                expr_ref asin_val(m());
                expr_ref k_eq_asin(m());
                expr_ref ge_guard_or_eq(m());
                ge_x_mone_guard = u().mk_ge(x, mone);
                asin_val = u().mk_u_asin(x);
                k_eq_asin = EQ(k, asin_val);
                ge_guard_or_eq = OR(ge_x_mone_guard, k_eq_asin);
                push_cnstr(ge_guard_or_eq);
                push_cnstr_pr(result_pr);
                expr_ref le_x_one_guard(m());
                expr_ref k_eq_asin_upper(m());
                expr_ref le_guard_or_eq(m());
                le_x_one_guard = u().mk_le(x, one);
                k_eq_asin_upper = EQ(k, asin_val);
                le_guard_or_eq = OR(le_x_one_guard, k_eq_asin_upper);
                push_cnstr(le_guard_or_eq);
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
            expr_ref ge_x_mone(m());
            expr_ref le_x_one(m());
            expr_ref not_ge_x_mone(m());
            expr_ref not_le_x_one(m());
            expr_ref cos_k(m());
            expr_ref eq_x_cos(m());
            expr_ref ge_k_zero(m());
            expr_ref le_k_pi(m());
            expr_ref bounds_conj(m());
            expr_ref cos_conj(m());
            expr_ref interval_disj(m());
            ge_x_mone = u().mk_ge(x, mone);
            le_x_one = u().mk_le(x, one);
            not_ge_x_mone = NOT(ge_x_mone);
            not_le_x_one = NOT(le_x_one);
            cos_k = u().mk_cos(k);
            eq_x_cos = EQ(x, cos_k);
            ge_k_zero = u().mk_ge(k, zero);
            le_k_pi = u().mk_le(k, pi);
            bounds_conj = AND(ge_k_zero, le_k_pi);
            cos_conj = AND(eq_x_cos, bounds_conj);
            interval_disj = OR(OR(not_ge_x_mone, not_le_x_one), cos_conj);
            push_cnstr(interval_disj);
            push_cnstr_pr(result_pr);
            if (complete()) {
                // x < -1       implies k = acos_u(x) 
                // x >  1       implies k = acos_u(x) 
                expr_ref ge_x_mone_guard(m());
                expr_ref acos_val(m());
                expr_ref k_eq_acos(m());
                expr_ref ge_guard_or_eq(m());
                ge_x_mone_guard = u().mk_ge(x, mone);
                acos_val = u().mk_u_acos(x);
                k_eq_acos = EQ(k, acos_val);
                ge_guard_or_eq = OR(ge_x_mone_guard, k_eq_acos);
                push_cnstr(ge_guard_or_eq);
                push_cnstr_pr(result_pr);
                expr_ref le_x_one_guard(m());
                expr_ref k_eq_acos_upper(m());
                expr_ref le_guard_or_eq(m());
                le_x_one_guard = u().mk_le(x, one);
                k_eq_acos_upper = EQ(k, acos_val);
                le_guard_or_eq = OR(le_x_one_guard, k_eq_acos_upper);
                push_cnstr(le_guard_or_eq);
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
            expr_ref eq_x_tan(m());
            expr_ref gt_k_mpi2(m());
            expr_ref lt_k_pi2(m());
            expr_ref bounds_conj(m());
            expr_ref tan_conj(m());
            eq_x_tan = EQ(x, u().mk_tan(k));
            gt_k_mpi2 = u().mk_gt(k, mpi2);
            lt_k_pi2 = u().mk_lt(k, pi2);
            bounds_conj = AND(gt_k_mpi2, lt_k_pi2);
            tan_conj = AND(eq_x_tan, bounds_conj);
            push_cnstr(tan_conj);
            push_cnstr_pr(result_pr);
            return BR_DONE;
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            if (f->get_family_id() != u().get_family_id())
                return BR_FAILED;
            if (m_cannot_purify.contains(f))
                return BR_FAILED;
            switch (f->get_decl_kind()) {
            case OP_DIV: 
                process_div(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_IDIV: 
                if (!m_cannot_purify.empty())
                    return BR_FAILED;
                process_idiv(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_MOD:
                if (!m_cannot_purify.empty())
                    return BR_FAILED;
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
            case OP_SIN:
                return process_sin(f, args[0], result, result_pr);
            case OP_COS:
                return process_cos(f, args[0], result, result_pr);
            case OP_ATAN:
                return process_atan(f, args[0], result, result_pr);
            default:
                return BR_FAILED;
            }
        }
        
        bool get_subst(expr * s, expr * & t, proof * & t_pr) { 
            if (is_quantifier(s)) {
                m_owner.process_quantifier(*this, to_quantifier(s), m_subst, m_subst_pr);
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

    expr * mk_real_zero() { return u().mk_numeral(rational(0), false); }

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(purify_arith_proc & o):
            rewriter_tpl<rw_cfg>(o.m(), o.m_produce_proofs, m_cfg),
            m_cfg(o) {
        }
    };

    struct rw_rec : public rewriter_tpl<rw_cfg> {
        rw_cfg& m_cfg;
        rw_rec(rw_cfg& cfg):            
            rewriter_tpl<rw_cfg>(cfg.m(), cfg.produce_proofs(), cfg),
            m_cfg(cfg) {
        }
    };
    
    void process_quantifier(rw_cfg& cfg, quantifier * q, expr_ref & result, proof_ref & result_pr) { 
        result_pr = nullptr;
        rw_rec r(cfg);
        expr_ref new_body(m());
        proof_ref new_body_pr(m());
        r(q->get_expr(), new_body, new_body_pr);
        TRACE(purify_arith, 
              tout << "body: " << mk_ismt2_pp(q->get_expr(), m()) << "\nnew_body: " << new_body << "\n";);
        result = m().update_quantifier(q, new_body);
        if (m_produce_proofs) {
            result_pr = m().mk_rewrite(q->get_expr(), new_body);
            result_pr = m().mk_quant_intro(q, to_quantifier(result.get()), result_pr);
        }
    }

    void operator()(model_converter_ref & mc, bool produce_models) {
        rw r(*this);
        // purify
        expr_ref   new_curr(m());
        proof_ref  new_pr(m());
        unsigned sz = m_goal.size();
        for (unsigned i = 0; !m_goal.inconsistent() && i < sz; i++) {
            expr * curr = m_goal.form(i);
            r(curr, new_curr, new_pr);
            if (m_produce_proofs) {
                proof * pr = m_goal.pr(i);
                new_pr     = m().mk_modus_ponens(pr, new_pr);
            }
            m_goal.update(i, new_curr, new_pr, m_goal.dep(i));
        }
        
        // add constraints
        sz = r.cfg().m_new_cnstrs.size();
        TRACE(purify_arith, tout << r.cfg().m_new_cnstrs << "\n";);
        TRACE(purify_arith, tout << r.cfg().m_new_cnstr_prs << "\n";);
        for (unsigned i = 0; i < sz; i++) {
            m_goal.assert_expr(r.cfg().m_new_cnstrs.get(i), m_produce_proofs ? r.cfg().m_new_cnstr_prs.get(i) : nullptr, nullptr);
        }
        auto const& divs  = r.cfg().m_divs;
        auto const& idivs = r.cfg().m_idivs;
        auto const& mods  = r.cfg().m_mods;
        for (unsigned i = 0; i < divs.size(); ++i) {
            auto const& p1 = divs[i];
            for (unsigned j = i + 1; j < divs.size(); ++j) {
                auto const& p2 = divs[j];
                expr_ref eq_x(m());
                expr_ref eq_y(m());
                expr_ref antecedent(m());
                expr_ref consequent(m());
                expr_ref implication(m());
                eq_x = m().mk_eq(p1.x, p2.x);
                eq_y = m().mk_eq(p1.y, p2.y);
                antecedent = m().mk_and(eq_x, eq_y);
                consequent = m().mk_eq(p1.d, p2.d);
                implication = m().mk_implies(antecedent, consequent);
                m_goal.assert_expr(implication);
            }
        }
        for (unsigned i = 0; i < mods.size(); ++i) {
            auto const& p1 = mods[i];
            for (unsigned j = i + 1; j < mods.size(); ++j) {
                auto const& p2 = mods[j];
                expr_ref eq_x(m());
                expr_ref eq_y(m());
                expr_ref antecedent(m());
                expr_ref consequent(m());
                expr_ref implication(m());
                eq_x = m().mk_eq(p1.x, p2.x);
                eq_y = m().mk_eq(p1.y, p2.y);
                antecedent = m().mk_and(eq_x, eq_y);
                consequent = m().mk_eq(p1.d, p2.d);
                implication = m().mk_implies(antecedent, consequent);
                m_goal.assert_expr(implication);
            }
        }
        for (unsigned i = 0; i < idivs.size(); ++i) {
            auto const& p1 = idivs[i];
            for (unsigned j = i + 1; j < idivs.size(); ++j) {
                auto const& p2 = idivs[j];
                expr_ref eq_x(m());
                expr_ref eq_y(m());
                expr_ref antecedent(m());
                expr_ref consequent(m());
                expr_ref implication(m());
                eq_x = m().mk_eq(p1.x, p2.x);
                eq_y = m().mk_eq(p1.y, p2.y);
                antecedent = m().mk_and(eq_x, eq_y);
                consequent = m().mk_eq(p1.d, p2.d);
                implication = m().mk_implies(antecedent, consequent);
                m_goal.assert_expr(implication);
            }
        }
        
        // add generic_model_converter to eliminate auxiliary variables from model
        if (produce_models) {
            generic_model_converter * fmc = alloc(generic_model_converter, m(), "purify");
            mc = fmc;
            obj_map<app, expr*> & f2v = r.cfg().m_app2fresh;
            for (auto const& kv : f2v) {
                app * v = to_app(kv.m_value);
                SASSERT(is_uninterp_const(v));
                fmc->hide(v->get_decl());
            }
            if (!divs.empty()) {
                expr_ref body(u().mk_real(0), m());
                expr_ref v0(m().mk_var(0, u().mk_real()), m());
                expr_ref v1(m().mk_var(1, u().mk_real()), m());
                for (auto const& p : divs) {
                    expr_ref eq_v0_x(m());
                    expr_ref eq_v1_y(m());
                    expr_ref guard(m());
                    expr_ref new_body(m());
                    eq_v0_x = m().mk_eq(v0, p.x);
                    eq_v1_y = m().mk_eq(v1, p.y);
                    guard = m().mk_and(eq_v0_x, eq_v1_y);
                    new_body = m().mk_ite(guard, p.d, body);
                    body = new_body;
                }
                fmc->add(u().mk_div0(), body);
            }
            if (!mods.empty()) {
                expr_ref body(u().mk_int(0), m());
                expr_ref v0(m().mk_var(0, u().mk_int()), m());
                expr_ref v1(m().mk_var(1, u().mk_int()), m());
                for (auto const& p : mods) {
                    expr_ref eq_v0_x(m());
                    expr_ref eq_v1_y(m());
                    expr_ref guard(m());
                    expr_ref new_body(m());
                    eq_v0_x = m().mk_eq(v0, p.x);
                    eq_v1_y = m().mk_eq(v1, p.y);
                    guard = m().mk_and(eq_v0_x, eq_v1_y);
                    new_body = m().mk_ite(guard, p.d, body);
                    body = new_body;
                }
                
                fmc->add(u().mk_mod0(), body);
                body = m().mk_ite(u().mk_ge(v1, u().mk_int(0)), body, u().mk_uminus(body));
                fmc->add(u().mk_rem0(), body);
            }
            if (!idivs.empty()) {
                expr_ref body(u().mk_int(0), m());
                expr_ref v0(m().mk_var(0, u().mk_int()), m());
                expr_ref v1(m().mk_var(1, u().mk_int()), m());
                for (auto const& p : idivs) {
                    expr_ref eq_v0_x(m());
                    expr_ref eq_v1_y(m());
                    expr_ref guard(m());
                    expr_ref new_body(m());
                    eq_v0_x = m().mk_eq(v0, p.x);
                    eq_v1_y = m().mk_eq(v1, p.y);
                    guard = m().mk_and(eq_v0_x, eq_v1_y);
                    new_body = m().mk_ite(guard, p.d, body);
                    body = new_body;
                }
                fmc->add(u().mk_idiv0(), body);
            }
            if (r.cfg().m_ipower0) {
                fmc->add(u().mk_ipower0(), r.cfg().m_ipower0);
            }
            if (r.cfg().m_rpower0) {
                fmc->add(u().mk_rpower0(), r.cfg().m_rpower0);
            }
        }
        if (produce_models && !m_sin_cos.empty()) {
            generic_model_converter* emc = alloc(generic_model_converter, m(), "purify_sin_cos");
            mc = concat(mc.get(), emc);
            for (auto const& kv : m_sin_cos) {
                expr_ref ge_nonneg(m());
                expr_ref acos_val(m());
                expr_ref neg_acos_val(m());
                expr_ref pi_sum(m());
                expr_ref ite_expr(m());
                ge_nonneg = u().mk_ge(kv.m_value.first, mk_real_zero());
                acos_val = u().mk_acos(kv.m_value.second);
                neg_acos_val = u().mk_acos(u().mk_uminus(kv.m_value.second));
                pi_sum = u().mk_add(neg_acos_val, u().mk_pi());
                ite_expr = m().mk_ite(ge_nonneg, acos_val, pi_sum);
                emc->add(kv.m_key->get_decl(), ite_expr);
            }

        }
    }


};

class purify_arith_tactic : public tactic {
    arith_util         m_util;
    params_ref         m_params;
public:
    purify_arith_tactic(ast_manager & m, params_ref const & p):
        m_util(m),
        m_params(p) {
    }

    tactic * translate(ast_manager & m) override {
        return alloc(purify_arith_tactic, m, m_params);
    }

    char const* name() const override { return "purify_arith"; }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        r.insert("complete", CPK_BOOL, 
                 "add constraints to make sure that any interpretation of a underspecified arithmetic operators is a function. The result will include additional uninterpreted functions/constants: /0, div0, mod0, 0^0, neg-root", "true");
        r.insert("elim_root_objects", CPK_BOOL,
                 "eliminate root objects.", "true");
        r.insert("elim_inverses", CPK_BOOL,
                 "eliminate inverse trigonometric functions (asin, acos, atan).", "true");
        th_rewriter::get_param_descrs(r);
    }
    
    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        try {
            tactic_report report("purify-arith", *g);
            TRACE(goal, g->display(tout););
            bool produce_proofs = g->proofs_enabled();
            bool produce_models = g->models_enabled();
            bool elim_root_objs = m_params.get_bool("elim_root_objects", true);
            bool elim_inverses  = m_params.get_bool("elim_inverses", true);
            bool complete       = m_params.get_bool("complete", true);
            purify_arith_proc proc(*(g.get()), m_util, produce_proofs, elim_root_objs, elim_inverses, complete);            
            model_converter_ref mc;
            proc(mc, produce_models);
            g->add(mc.get());
            g->inc_depth();
            result.push_back(g.get());
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.what());
        }
    }
    
    void cleanup() override {
    }

};

tactic * mk_purify_arith_tactic(ast_manager & m, params_ref const & p) {
    params_ref elim_rem_p = p;
    elim_rem_p.set_bool("elim_rem", true);
    
    params_ref skolemize_p;
    skolemize_p.set_bool("skolemize", false);

    return and_then(using_params(mk_snf_tactic(m, skolemize_p), skolemize_p),
                    using_params(mk_simplify_tactic(m, elim_rem_p), elim_rem_p),
                    alloc(purify_arith_tactic, m, p),
                    mk_simplify_tactic(m, p));
}
