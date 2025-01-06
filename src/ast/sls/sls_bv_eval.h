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
#include "ast/sls/sls_bv_valuation.h"
#include "ast/sls/sls_bv_fixed.h"
#include "ast/sls/sls_context.h"
#include "ast/sls/sls_bv_lookahead.h"
#include "ast/bv_decl_plugin.h"


 
namespace sls {

    class bv_terms;


    using bvect = sls::bvect;

    class bv_eval {
        friend class bv_lookahead;

        struct config {
            unsigned m_prob_randomize_extract = 50;
        };

        friend class sls::bv_fixed;
        friend class sls_test;
        ast_manager&        m;
        sls::context&       ctx;
        sls::bv_terms&      terms;
        sls::bv_lookahead   m_lookahead;
        bv_util             bv;
        sls::bv_fixed       m_fix;
        mutable mpn_manager mpn;
        ptr_vector<expr>    m_todo;
        random_gen          m_rand;
        config              m_config;
        bool_vector         m_is_fixed;
        unsigned            m_lookahead_steps = 0;
        unsigned            m_lookahead_phase_size = 10;
        mutable svector<lbool>      m_tmp_bool_values;
        mutable svector<std::pair<unsigned, lbool>>  m_tmp_bool_value_updates;
        

        scoped_ptr_vector<sls::bv_valuation> m_values; // expr-id -> bv valuation

        mutable bvect m_tmp, m_tmp2, m_tmp3, m_tmp4, m_mul_tmp, m_zero, m_one, m_minus_one;
        bvect m_a, m_b, m_nextb, m_nexta, m_aux;

        using bvval = sls::bv_valuation;

        void init_eval_bv(app* e);

       
        /**
        * Register e as a bit-vector. 
        * Return true if not already registered, false if already registered.
        */
        void add_bit_vector(app* e);
        sls::bv_valuation* alloc_valuation(app* e);

        bool bval1_bv(app* e) const;  
        bool bval1_bool(app* e) const;



        void fold_oper(bvect& out, app* e, unsigned i, std::function<void(bvect&, bvval const&)> const& f);
        /**
        * Repair operations
        */
        bool try_repair_bv(app * e, unsigned i);
        bool try_repair_band(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_band(app* t, unsigned i);
        bool try_repair_bor(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_bor(app* t, unsigned i);
        bool try_repair_add(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_add(app* t, unsigned i);
        bool try_repair_sub(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_mul(bvect const& e, bvval& a, bvect const& b);
        bool try_repair_bxor(bvect const& e, bvval& a, bvval const& b);
        bool try_repair_bxor(app* t, unsigned i);
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
        bool try_repair_sdiv(bvect const& e, bvval& a, bvval& b, unsigned i);
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
        bool try_repair_concat(app* e, unsigned i);
        bool try_repair_extract(bvect const& e, bvval& a, unsigned lo);
        bool try_repair_comp(bvect const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_eq(bool is_true, bvval& a, bvval const& b);
        bool try_repair_eq(app* e, unsigned i);

        bool try_repair_int2bv(bvect const& e, expr* arg);
        void add_p2_1(bvval const& a, bvect& t) const;

        bool add_overflow_on_fixed(bvval const& a, bvect const& t);
        bool mul_overflow_on_fixed(bvval const& a, bvect const& t);
        void set_div(bvect const& a, bvect const& b, unsigned nw,
            bvect& quot, bvect& rem) const;

        digit_t random_bits();
        bool random_bool() { return m_rand() % 2 == 0; }

        sls::bv_valuation& wval(app* e, unsigned i) { return wval(e->get_arg(i)); }

        void eval(expr* e, sls::bv_valuation& val) const;

        bvect const& assign_value(app* e) const { return wval(e).bits(); }


        /**
         * Retrieve evaluation based on immediate children.
         */

        bool can_eval1(expr* e) const;

        void commit_eval(expr* p, app* e);

        bool is_lookahead_phase();

    public:
        bv_eval(sls::bv_terms& terms, sls::context& ctx);

        void init() { m_fix.init(); }

        void start_propagation();

        void register_term(expr* e);

        /**
         * Retrieve evaluation based on cache.
         * bval - Boolean values
         * wval - Word (bit-vector) values
         */        

        sls::bv_valuation& wval(expr* e) const;

        void set(expr* e, sls::bv_valuation const& val);

        bool is_fixed0(expr* e) const { return m_is_fixed.get(e->get_id(), false); }
        
        // control whether if-then-else is eavaluated based on SAT solver or temporary values.
        bool m_use_tmp_bool_value = false;
        sls::bv_valuation& eval(app* e) const;

        void set_random(app* e);

        bool eval_is_correct(app* e);

        bool is_uninterpreted(app* e) const;

        expr_ref get_value(app* e);

        bool bval0(expr* e) const { return ctx.is_true(e); }
        bool bval1(expr* e) const;

        unsigned bool_value_restore_point() const { return m_tmp_bool_value_updates.size(); }
        void set_bool_value_log(expr* e, bool val);
        void set_bool_value_no_log(expr* e, bool val);
        void restore_bool_values(unsigned restore_point);
        void commit_bool_values() { m_tmp_bool_value_updates.reset(); }
        bool get_bool_value(expr* e) const;
      
        /*
         * Try to invert value of child to repair value assignment of parent.
         */

        bool repair_down(app* e, unsigned i);

        /*
        * Propagate repair up to parent
        */
        bool repair_up(expr* e);

        void collect_statistics(statistics& st) const;

        std::ostream& display(std::ostream& out) const;

        std::ostream& display_value(std::ostream& out, expr* e) const;
    };
}
