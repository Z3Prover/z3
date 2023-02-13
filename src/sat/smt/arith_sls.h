/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_local_search.h

Abstract:

    Theory plugin for arithmetic local search

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/arith_decl_plugin.h"
#include "math/lp/lp_solver.h"
#include "math/lp/lp_primal_simplex.h"
#include "math/lp/lp_dual_simplex.h"
#include "math/lp/indexed_value.h"
#include "math/lp/lar_solver.h"
#include "math/lp/nla_solver.h"
#include "math/lp/lp_types.h"
#include "math/lp/lp_api.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "sat/smt/sat_th.h"
#include "sat/sat_ddfw.h"

namespace arith {

    class solver;

    // local search portion for arithmetic
    class sls {
        enum class ineq_kind { EQ, LE, LT, NE };
        enum class var_kind { INT, REAL };
        typedef unsigned var_t;
        typedef unsigned atom_t;

        struct config {
            double cb = 0.0;
            unsigned L = 20;
            unsigned t = 45;
            unsigned max_no_improve = 500000;
            double sp = 0.0003;
        };

        struct stats {
            unsigned m_num_flips = 0;
        };

    public:
        // encode args <= bound, args = bound, args < bound
        struct ineq {
            vector<std::pair<int64_t, var_t>> m_args;
            ineq_kind  m_op = ineq_kind::LE;
            int64_t   m_bound;
            int64_t   m_args_value;

            bool is_true() const {
                switch (m_op) {
                case ineq_kind::LE:
                    return m_args_value <= m_bound;
                case ineq_kind::EQ:
                    return m_args_value == m_bound;
                case ineq_kind::NE:
                    return m_args_value != m_bound;
                default:
                    return m_args_value < m_bound;
                }
            }
            std::ostream& display(std::ostream& out) const {
                bool first = true;
                for (auto const& [c, v] : m_args)
                    out << (first? "": " + ") << c << " * v" << v, first = false;
                switch (m_op) {
                case ineq_kind::LE:
                    return out << " <= " << m_bound << "(" << m_args_value << ")";
                case ineq_kind::EQ:
                    return out << " == " << m_bound << "(" << m_args_value << ")";
                case ineq_kind::NE:
                    return out << " != " << m_bound << "(" << m_args_value << ")";
                default:
                    return out << " < " << m_bound << "(" << m_args_value << ")";
                }
            }
        };
    private:

        struct var_info {
            int64_t      m_value;
            int64_t      m_best_value;
            var_kind     m_kind = var_kind::INT;
            vector<std::pair<int64_t, sat::literal>> m_literals;
        };

        struct clause {
            unsigned m_weight = 1;
            int64_t m_dts = 1;
        };

        solver& s;
        ast_manager& m;
        sat::ddfw* m_bool_search = nullptr;
        unsigned                     m_max_arith_steps = 0;
        unsigned                     m_best_min_unsat = UINT_MAX;
        stats                        m_stats;
        config                       m_config;
        scoped_ptr_vector<ineq>      m_literals;
        vector<var_info>             m_vars;
        vector<clause>               m_clauses;
        svector<std::pair<lp::tv, euf::theory_var>> m_terms;


        indexed_uint_set& unsat() { return m_bool_search->unsat_set(); }
        unsigned num_clauses() const { return m_bool_search->num_clauses(); }
        sat::clause& get_clause(unsigned idx) { return *get_clause_info(idx).m_clause; }
        sat::clause const& get_clause(unsigned idx) const { return *get_clause_info(idx).m_clause; }
        sat::ddfw::clause_info& get_clause_info(unsigned idx) { return m_bool_search->get_clause_info(idx); }
        sat::ddfw::clause_info const& get_clause_info(unsigned idx) const { return m_bool_search->get_clause_info(idx); }
        bool is_true(sat::literal lit) { return lit.sign() != m_bool_search->get_value(lit.var()); }

        void reset();
        ineq* atom(sat::literal lit) const { return m_literals[lit.index()]; }
        unsigned& get_weight(unsigned idx) { return m_clauses[idx].m_weight; }
        unsigned get_weight(unsigned idx) const { return m_clauses[idx].m_weight; }
        bool flip();
        void log();
        bool flip_unsat();
        bool flip_clauses();
        bool flip_dscore();
        bool flip_dscore(unsigned cl);
        bool flip(unsigned cl);
        int64_t dtt(ineq const& ineq) const { return dtt(ineq.m_args_value, ineq); }
        int64_t dtt(int64_t args, ineq const& ineq) const;
        int64_t dtt(ineq const& ineq, var_t v, int64_t new_value) const;
        int64_t dts(unsigned cl, var_t v, int64_t new_value) const;
        int64_t compute_dts(unsigned cl) const;
        bool cm(ineq const& ineq, var_t v, int64_t& new_value);
        int cm_score(var_t v, int64_t new_value);
        void update(var_t v, int64_t new_value);
        void paws();
        int64_t dscore(var_t v, int64_t new_value) const;
        void save_best_values();
        void add_vars();
        sls::ineq& new_ineq(ineq_kind op, int64_t const& bound);
        void add_arg(sat::literal lit, ineq& ineq, int64_t const& c, var_t v);
        void add_bounds(sat::literal_vector& bounds);
        void add_args(sat::literal lit, ineq& ineq, lp::tv t, euf::theory_var v, int64_t sign);
        void init_literal(sat::literal lit);
        void init_bool_var_assignment(sat::bool_var v);
        void init_literal_assignment(sat::literal lit);

        int64_t value(var_t v) const { return m_vars[v].m_value; }
        int64_t to_numeral(rational const& r);

    public:
        sls(solver& s);
        lbool operator ()(bool_vector& phase);
        void set_bounds_begin();
        void set_bounds_end(unsigned num_literals);
        void set_bounds(euf::enode* n);
        void set(sat::ddfw* d);
    };

    inline std::ostream& operator<<(std::ostream& out, sls::ineq const& ineq) {
        return ineq.display(out);
    }
}
