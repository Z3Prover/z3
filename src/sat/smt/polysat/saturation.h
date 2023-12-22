/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/inequality.h"

namespace polysat {

    /**
     * Introduce lemmas that derive new (simpler) constraints from the current conflict and partial model.
     */
    class saturation {

        using clause = std::initializer_list<std::variant<constraint_id, signed_constraint>>;
        core& c;
        constraints& C;
        char const* m_rule = nullptr;
        bool m_propagated = false;
        void set_rule(char const* r) { m_rule = r; }

        void propagate(signed_constraint const& sc, std::initializer_list<constraint_id> const& premises);
        void add_clause(char const* name, clause const& cs, bool is_redundant);

        bool match_core(std::function<bool(signed_constraint const& sc)> const& p, constraint_id& id);
        bool match_constraints(std::function<bool(signed_constraint const& sc)> const& p, constraint_id& id);


        // a * b does not overflow
        bool is_non_overflow(pdd const& a, pdd const& b);
        bool is_non_overflow(pdd const& x, pdd const& y, signed_constraint& c);


        void propagate_infer_equality(pvar x, inequality const& a_l_b);
        void try_ugt_x(pvar v, inequality const& i);
        void try_ugt_y(pvar v, inequality const& i);
        void try_ugt_z(pvar z, inequality const& i);

        signed_constraint ineq(bool is_strict, pdd const& x, pdd const& y);
        
#if 0
        parity_tracker m_parity_tracker;
        unsigned_vector m_occ;
        unsigned_vector m_occ_cnt;

        

        
        signed_constraint ineq(bool strict, pdd const& lhs, pdd const& rhs);

        void log_lemma(pvar v, conflict& core);
        bool propagate(pvar v, conflict& core, signed_constraint crit1, signed_constraint c);
        bool propagate(pvar v, conflict& core, inequality const& crit1, signed_constraint c);
        bool propagate(pvar v, conflict& core, signed_constraint c);
        bool add_conflict(pvar v, conflict& core, inequality const& crit1, signed_constraint c);
        bool add_conflict(pvar v, conflict& core, inequality const& crit1, inequality const& crit2, signed_constraint c);

        bool try_ugt_x(pvar v, conflict& core, inequality const& c);

        bool try_ugt_y(pvar v, conflict& core, inequality const& c);
        bool try_ugt_y(pvar v, conflict& core, inequality const& l_y, inequality const& yx_l_zx, pdd const& x, pdd const& z);

        bool try_y_l_ax_and_x_l_z(pvar x, conflict& core, inequality const& c);
        bool try_y_l_ax_and_x_l_z(pvar x, conflict& core, inequality const& x_l_z, inequality const& y_l_ax, pdd const& a, pdd const& y);

        bool try_ugt_z(pvar z, conflict& core, inequality const& c);
        bool try_ugt_z(pvar z, conflict& core, inequality const& x_l_z0, inequality const& yz_l_xz, pdd const& y, pdd const& x);

        bool try_parity(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_parity_diseq(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_mul_bounds(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_factor_equality(pvar x, conflict& core, inequality const& a_l_b);
        bool try_infer_equality(pvar x, conflict& core, inequality const& a_l_b);
        bool try_mul_eq_1(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_mul_odd(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_mul_eq_bound(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_transitivity(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_tangent(pvar v, conflict& core, inequality const& c);
        bool try_add_overflow_bound(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_add_mul_bound(pvar x, conflict& core, inequality const& axb_l_y);
        bool try_infer_parity_equality(pvar x, conflict& core, inequality const& a_l_b);
        bool try_div_monotonicity(conflict& core);

        bool try_nonzero_upper_extract(pvar v, conflict& core, inequality const& i);
        bool try_congruence(pvar v, conflict& core, inequality const& i);


        rational round(rational const& M, rational const& x);
        bool eval_round(rational const& M, pdd const& p, rational& r);
        bool extract_linear_form(pdd const& q, pvar& y, rational& a, rational& b);
        bool extract_bilinear_form(pvar x, pdd const& p, pvar& y, bilinear& b);
        bool adjust_bound(rational const& x_min, rational const& x_max, rational const& y0, rational const& M,
                          bilinear& b, rational& x_split);
        bool update_min(rational& y_min, rational const& x_min, rational const& x_max,
                        bilinear const& b);
        bool update_max(rational& y_max, rational const& x_min, rational const& x_max,
                        bilinear const& b);
        bool update_bounds_for_xs(rational const& x_min, rational const& x_max, rational& y_min, rational& y_max,
                                  rational const& y0, bilinear b1, bilinear b2,
                                  rational const& M, inequality const& a_l_b);
        void fix_values(pvar x, pvar y, pdd const& p);
        void fix_values(pvar y, pdd const& p);
        


        bool is_add_overflow(pvar x, inequality const& i, pdd& y, bool& is_minus);

        bool has_upper_bound(pvar x, conflict& core, rational& bound, vector<signed_constraint>& x_ge_bound);

        bool has_lower_bound(pvar x, conflict& core, rational& bound, vector<signed_constraint>& x_le_bound);

        // inequality i implies x != 0
        bool is_nonzero_by(pvar x, inequality const& i);

        // determine min/max parity of polynomial
        unsigned min_parity(pdd const& p, vector<signed_constraint>& explain);
        unsigned max_parity(pdd const& p, vector<signed_constraint>& explain);
        unsigned min_parity(pdd const& p) { vector<signed_constraint> ex; return min_parity(p, ex); }
        unsigned max_parity(pdd const& p) { vector<signed_constraint> ex; return max_parity(p, ex); }

        lbool get_multiple(const pdd& p1, const pdd& p2, pdd& out);
        
        bool is_forced_eq(pdd const& p, rational const& val);
        bool is_forced_eq(pdd const& p, int i) { return is_forced_eq(p, rational(i)); }
        
        bool is_forced_diseq(pdd const& p, rational const& val, signed_constraint& c);
        bool is_forced_diseq(pdd const& p, int i, signed_constraint& c) { return is_forced_diseq(p, rational(i), c); }

        bool is_forced_odd(pdd const& p, signed_constraint& c);

        bool is_forced_false(signed_constraint const& sc);

        bool is_forced_true(signed_constraint const& sc);



        bool try_umul_ovfl(pvar v, signed_constraint c);
        bool try_umul_ovfl_noovfl(pvar v, signed_constraint c);
        bool try_umul_noovfl_lo(pvar v, signed_constraint c);
        bool try_umul_noovfl_bounds(pvar v, signed_constraint c);
        bool try_umul_ovfl_bounds(pvar v, signed_constraint c);

        bool try_op(pvar v, signed_constraint c);
#endif


        void propagate(pvar v, inequality const& i);

    public:
        saturation(core& c);
        void propagate(pvar v);
        bool propagate(pvar v, constraint_id cid);
    };
}
