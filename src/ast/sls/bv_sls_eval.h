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

    class sls_eval {
        friend class sls_fixed;
        ast_manager&        m;
        bv_util             bv;
        sls_fixed           m_fix;
        mutable mpn_manager         mpn;
        ptr_vector<expr>    m_todo;
        random_gen          m_rand;

        scoped_ptr_vector<sls_valuation> m_values0, m_values1; // expr-id -> bv valuation
        bool_vector                      m_eval;   // expr-id -> boolean valuation
        bool_vector                      m_fixed;  // expr-id -> is Boolean fixed

        mutable svector<digit_t> m_tmp, m_tmp2, m_zero, m_one;

        using bvval = sls_valuation;


        void init_eval_basic(app* e);
        void init_eval_bv(app* e);
       
        /**
        * Register e as a bit-vector. 
        * Return true if not already registered, false if already registered.
        */
        bool add_bit_vector(expr* e);
        sls_valuation* alloc_valuation(unsigned bit_width);

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
        bool try_repair_band(bvval const& e, bvval& a, bvval const& b);
        bool try_repair_bor(bvval const& e, bvval& a, bvval const& b);
        bool try_repair_add(bvval const& e, bvval& a, bvval const& b);
        bool try_repair_mul(bvval const& e, bvval& a, bvval const& b);
        bool try_repair_bxor(bvval const& e, bvval& a, bvval const& b);
        bool try_repair_bnot(bvval const& e, bvval& a);
        bool try_repair_bneg(bvval const& e, bvval& a);
        bool try_repair_ule(bool e, bvval& a, bvval const& b);
        bool try_repair_uge(bool e, bvval& a, bvval const& b);
        bool try_repair_sle(bool e, bvval& a, bvval const& b);
        bool try_repair_sge(bool e, bvval& a, bvval const& b);
        bool try_repair_shl(bvval const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_ashr(bvval const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_lshr(bvval const& e, bvval& a, bvval& b, unsigned i);
        bool try_repair_bit2bool(bvval& a, unsigned idx);

        sls_valuation& wval0(app* e, unsigned i) { return wval0(e->get_arg(i)); }

        void wval1(app* e, sls_valuation& val) const;

    public:
        sls_eval(ast_manager& m);

        void init_eval(expr_ref_vector const& es, std::function<bool(expr*, unsigned)> const& eval);

        void init_fixed(expr_ref_vector const& es) { m_fix.init(es); }

        ptr_vector<expr>& sort_assertions(expr_ref_vector const& es);

        /**
         * Retrieve evaluation based on cache.
         * bval - Boolean values
         * wval - Word (bit-vector) values
         */
        
        bool bval0(expr* e) const { return m_eval[e->get_id()]; }

        sls_valuation& wval0(expr* e) const { return *m_values0[e->get_id()]; }

        bool is_fixed0(expr* e) const { return m_fixed[e->get_id()]; }

        /**
         * Retrieve evaluation based on immediate children.         
         */
        bool bval1(app* e) const;

        svector<digit_t>& wval1(app* e) const;

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
        void repair_up(expr* e);
    };
}
