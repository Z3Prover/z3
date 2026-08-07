/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/
#pragma once

#include "math/lp/nla_common.h"
#include "math/lp/nla_intervals.h"
#include "util/uint_set.h"

namespace nla {
    class core;
    class monomial_bounds : common {
        dep_intervals& dep;

        bool tighten_lp_bound(dep_interval const &range, lpvar v, unsigned p);
        bool tighten_lp_upper_bound(dep_interval const& range, lpvar v, unsigned p);
        bool tighten_lp_lower_bound(dep_interval const& range, lpvar v, unsigned p);
        bool tighten_lp_bound(dep_interval &mi, lpvar v, unsigned power, dep_interval &product);
 
        void propagate_lp_bound(lpvar v, lp::lconstraint_kind cmp, rational const &q, u_dependency *d);


        bool should_propagate_lower(dep_interval const& range, lpvar v, unsigned p);
        bool should_propagate_upper(dep_interval const& range, lpvar v, unsigned p);

        void var2interval(lpvar v, scoped_dep_interval& i);
        bool is_too_big(mpq const& q) const;
        void compute_product(unsigned start, monic const& m, scoped_dep_interval& i);
        bool generate_lemma(monic const& m);
        bool tighten_lp(monic const& m);
        bool propagate_fixed_to_zero(monic const& m, lpvar fixed_to_zero);
        bool propagate_fixed(monic const& m, rational const& k);
        bool propagate_nonfixed(monic const& m, rational const& k, lpvar w);
        u_dependency* explain_fixed(monic const& m, rational const& k);
        lp::explanation get_explanation(u_dependency* dep);
        bool propagate_shared_factor(monic const& m);
        bool propagate_binomial_sign(monic const& m);
        void analyze_monomial(monic const& m, unsigned& num_free, lpvar& free_v, unsigned& power) const;
        bool is_free(lpvar v) const;
        bool is_zero(lpvar v) const;
        bool add_lemma();

        // linear-monomial equality propagation:
        // when all but one variable of a monomial are fixed, the monomial is
        // linear and its value/equality can be propagated into the LP solver.
        bool propagate_linear_bound(monic & m);
        bool is_linear(monic const& m, lpvar& w, lpvar & fixed_to_zero);
        rational fixed_var_product(monic const& m, lpvar w);

        // ----------------------------------------------------------------
        // max_min: incremental LP bound optimization.
        //
        // Adapted from smt::theory_arith::max_min (theory_arith_aux.h): a
        // bounded-variable primal-simplex walk that maximizes/minimizes a
        // single column over the current LP tableau by pivoting, leaving the
        // tableau at an optimal feasible vertex.  Replaces the expensive
        // lar_solver::find_improved_bound (which rebuilds the objective and
        // re-solves from scratch on every call) and rounds the resulting
        // bound to respect the integrality of integer columns.
        // ----------------------------------------------------------------
        //
        // Gain of a candidate move: how far a non-basic column may travel in the
        // chosen direction.  'min_gain' is the integrality quantum -- the
        // smallest integral step that keeps every dependent integer column at an
        // integral value (-1 means "no quantum", i.e. a rational column);
        // 'max_gain' is the largest feasible step (valid only when !unbounded).
        //
        struct mm_gain {
            bool      unbounded = true;              // no bound blocks the move
            rational  min_gain  = rational::minus_one();
            lp::impq  max_gain;
        };
        lpvar mm_basic_in_row(unsigned row) const;
        bool mm_safe_gain(mm_gain const& g) const;
        mm_gain mm_init_gains(lpvar x, bool inc) const;
        bool mm_update_gains(bool inc, lpvar x_i, rational const& a_ij, mm_gain& g) const;
        bool mm_pick_var_to_leave(lpvar x_j, bool inc, rational& a_ij, mm_gain& g, lpvar& x_i) const;
        bool mm_move_to_bound(lpvar x_i, bool inc, unsigned& best_efforts);
        void mm_update_value(lpvar j, lp::impq const& delta);
        bool mm_optimize(lpvar v, bool maximize, rational& opt_value);
        u_dependency* mm_dep_from_row(lpvar v, bool maximize);
    public:
        monomial_bounds(core* core);
        void generate_lemmas();
        bool tighten_lp_bounds();
        bool propagate_linear_bounds();
        bool propagate_changed_bounds();
        bool propagate_fixed_rows();

        // Maximize (is_lower == false) or minimize (is_lower == true) column j
        // over the LP tableau and, if the resulting bound improves j's current
        // bound, return its explanation and set 'bound'; otherwise return nullptr.
        u_dependency* improve_bound(lpvar j, bool is_lower, rational& bound);
    }; 
}
