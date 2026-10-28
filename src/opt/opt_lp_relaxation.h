/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_lp_relaxation.h

Abstract:

    Linear relaxation of a MaxSMT problem. Boolean literals become real
    variables in [0, 1]. Hard constraints that are pseudo-Boolean atoms,
    clauses over literals, linear arithmetic over such literals and numeric
    variables, or pairs of indicator clauses on the same term are kept;
    every other constraint is dropped, so the relaxation contains every
    model of the original problem. The minimum cost over the relaxation is
    a lower bound on the MaxSMT cost, and the relaxation's model proposes
    values for the soft literals.

Author:

    Lev Nachmanson (levnach) 2026-10-28

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "opt/maxsmt.h"

namespace opt {

    class lp_relaxation {
    public:
        struct result {
            // l_true: lower is a certified bound on the cost of the soft constraints.
            lbool    status = l_undef;
            rational lower;
            // Soft constraint index with the value of its literal in the relaxation's model.
            vector<std::pair<unsigned, bool>> rounding;
        };

        lp_relaxation(ast_manager& m, generic_model_converter& fm, params_ref const& p);

        // Relax one hard constraint. Returns false for a constraint outside
        // the linear fragment, which is dropped. An indicator clause, a
        // literal or a linear atom, is kept back until a clause on the
        // opposite literal bounds the same term.
        bool add_hard(expr* f);

        unsigned num_dropped() const { return m_num_dropped; }
        unsigned num_constraints() const { return m_constraints.size(); }

        // Minimize the weighted cost of the soft constraints over the relaxation.
        result minimize_cost(vector<soft> const& softs, unsigned rlimit);

    private:
        // constant + sum of coefficient * variable
        struct linear {
            rational constant;
            vector<std::pair<app*, rational>> terms;
            void add(linear const& other, rational const& scale);
            bool is_constant() const { return terms.empty(); }
            // merge coefficients per variable and order the variables
            void normalize();
            bool same_terms(linear const& other) const;
        };

        // l < 0 when strict, otherwise l <= 0
        struct bound {
            linear l;
            bool   strict;
        };

        // atoms implied by a Boolean constant and by its negation
        struct indicator_group {
            vector<bound> when_true;
            vector<bound> when_false;
        };

        ast_manager&             m;
        generic_model_converter& m_fm;
        params_ref               m_params;
        arith_util               a;
        pb_util                  pb;
        obj_map<expr, app*>      m_proxies;     // Boolean or numeric constant -> real variable
        expr_ref_vector          m_trail;
        expr_ref_vector          m_constraints;
        obj_map<expr, unsigned>  m_indicator_index;
        vector<indicator_group>  m_indicators;
        unsigned                 m_num_dropped = 0;

        app* proxy(expr* c);
        bool is_literal(expr* l) const;
        bool relax_literal(expr* l, linear& out);
        bool relax_term(expr* t, rational const& scale, linear& out);
        bool relax_formula(expr* f, bool sign);
        bool comparison_bounds(expr* f, bool sign, vector<bound>& out);
        bool relax_comparison(expr* f, bool sign);
        bool relax_pb(expr* f, bool sign);
        bool relax_clause(unsigned n, expr* const* lits);
        bool keep_indicator(unsigned n, expr* const* lits);
        void relax_indicators();
        void add_constraint(linear const& l, bool strict_lt, bool eq);
        expr_ref mk_expr(linear const& l);
        bool eval(model& mdl, linear const& l, rational& value);
        rational lattice_step(vector<soft> const& softs);
    };
}
