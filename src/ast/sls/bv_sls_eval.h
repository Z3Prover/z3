/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls.h

Abstract:

    A Stochastic Local Search (SLS) engine

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/
#pragma once

#include "ast/ast.h"
#include "ast/sls/sls_valuation.h"
#include "ast/sls/bv_sls_fixed.h"
#include "ast/bv_decl_plugin.h"

namespace bv {

    class sls_fixed;

    class sls_eval_plugin {
    public:
        virtual ~sls_eval_plugin() {}
        
    };

    class sls_eval {
        struct config {
            unsigned m_prob_randomize_extract = 50;
        };

        friend class sls_fixed;
        friend class sls_test;
        ast_manager&        m;
        bv_util             bv;
        sls_fixed           m_fix;
        mutable mpn_manager mpn;
        ptr_vector<expr>    m_todo;
        random_gen          m_rand;
        config              m_config;

        scoped_ptr_vector<sls_eval_plugin> m_plugins;



        scoped_ptr_vector<sls_valuation> m_values; // expr-id -> bv valuation
        bool_vector                      m_eval;   // expr-id -> boolean valuation
        bool_vector                      m_fixed;  // expr-id -> is Boolean fixed

        mutable bvect m_tmp, m_tmp2, m_tmp3, m_tmp4, m_zero, m_one, m_minus_one;
        bvect m_a, m_b, m_nextb, m_nexta, m_aux;

        using bvval = sls_valuation;


        void init_eval_basic(app* e);
        void init_eval_bv(app* e);
       
        /**
        * Register e as a bit-vector. 
        * Return true if not already registered, false if already registered.
        */
        bool add_bit_vector(app* e);
        sls_valuation* alloc_valuation(app* e);

        bool bval1_basic(app* e) const;
        bool bval1_bv(app* e) const;  

        /**
        * Repair operations
        */
        bool try_repair_basic(app* e, unsigned i);
        bool try_repair_bv(app * e, unsigned i);
        bool try_repair_and_or(app* e, unsigned i);
        bool try_repair_not(app* e);
        bool try_repair_eq(app* e, unsigned i);
        bool try_repair_xor(app* e, unsigned i);
        bool try_repair_ite(app* e, unsigned i);
        bool try_repair_implies(app* e, unsigned i);
        bool try_repair_band(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_bor(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_add(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_sub(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_mul(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_bxor(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_bnot(bvect const& e, bvval& a);
        bool try_repair_bneg(bvect const& e, bvval& a);
        bool try_repair_ule(bool e, bvval& a, bvval const& b);
        bool try_repair_uge(bool e, bvval& a, bvval const& b);
        bool try_repair_sle(bool e, bvval& a, bvval const& b);
        bool try_repair_sge(bool e, bvval& a, bvval const& b);
        bool try_repair_sge(bvval& a, bvect const& b, bvect const& p2);
        bool try_repair_sle(bvval& a, bvect const& b, bvect const& p2);
        bool try_repair_shl(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_ashr(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_lshr(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_lshr0(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_lshr1(bvect const& e, bvval const& a, bvval& b);
        bool try_repair_ashr0(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_ashr1(bvect const& e, bvval const& a, bvval& b);
        bool try_repair_bit2bool(bvval& a, unsigned idx);
        bool try_repair_udiv(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_urem(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_rotate_left(bvect const& e, bvval& a, unsigned n) const;
        bool try_repair_rotate_left(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_rotate_right(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_ule(bool e, bvval& a, bvect const& t);
        bool try_repair_uge(bool e, bvval& a, bvect const& t);
        bool try_repair_umul_ovfl(bool e, bvval& a, bvval& b, unsigned i);
        bool try_repair_zero_ext(bvect const& e, bvval& a);
        bool try_repair_sign_ext(bvect const& e, bvval& a);
        bool try_repair_concat(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_extract(bvect const& e, bvval& a, unsigned lo);
        bool try_repair_comp(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_eq(bool is_true, bvval& a, bvval const& b);
        void add_p2_1(bvval const& a, bvect& t) const;

        bool add_overflow_on_fixed(bvval const& a, bvect const& t);
        bool mul_overflow_on_fixed(bvval const& a, bvect const& t);
        void set_div(bvect const& a, bvect const& b, unsigned nw,
            bvect& quot, bvect& rem) const;

        digit_t random_bits();
        bool random_bool() { return m_rand() % 2 == 0; }

        sls_valuation& wval(app* e, unsigned i) { return wval(e->get_arg(i)); }

        void eval(app* e, sls_valuation& val) const;

        bvect const& eval_value(app* e) const { return wval(e).eval; }

    public:
        sls_eval(ast_manager& m);

        void init_eval(expr_ref_vector const& es, std::function<bool(expr*, unsigned)> const& eval);

        void tighten_range(expr_ref_vector const& es) { m_fix.init(es); }

        ptr_vector<expr>& sort_assertions(expr_ref_vector const& es);

        /**
         * Retrieve evaluation based on cache.
         * bval - Boolean values
         * wval - Word (bit-vector) values
         */
        
        bool bval0(expr* e) const { return m_eval[e->get_id()]; }

        sls_valuation& wval(expr* e) const;

        bool is_fixed0(expr* e) const { return m_fixed.get(e->get_id(), false); }

        /**
         * Retrieve evaluation based on immediate children.         
         */
        bool bval1(app* e) const;
        bool can_eval1(app* e) const;
        
        sls_valuation& eval(app* e) const;

        void commit_eval(app* e);

        void init_eval(app* e);

        void set_random(app* e);

        bool eval_is_correct(app* e);

        bool re_eval_is_correct(app* e);

        expr_ref get_value(app* e);

        /**
         * Override evaluaton.
         */

        void set(expr* e, bool b) {
            m_eval[e->get_id()] = b;
        }        

        /*
        * Try to invert value of child to repair value assignment of parent.
        */

        bool try_repair(app* e, unsigned i);

        /*
        * Propagate repair up to parent
        */
        bool repair_up(expr* e);


        std::ostream& display(std::ostream& out, expr_ref_vector const& es);

        std::ostream& display_value(std::ostream& out, expr* e);
    };
}
