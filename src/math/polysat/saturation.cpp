/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

TODO:
- saturation instantiates lemmas that are used for unit propagation.
- the unit propagated constraint should/could be added to Gamma & core and enable simpler conflict resolution.

TODO: preserve falsification
- each rule selects a certain premise that is problematic, 
  We assume that problematic premises are false in the current assignment
  The derived consequence should also be false in the current assignment to be effective, but simpler so that we can resolve.

TODO:
- remove level information from created constraints.
- 
--*/
#include "math/polysat/saturation.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    constraint_manager& inference_engine::cm() { return s().m_constraints; }

    /** Polynomial superposition between two equalities that contain v.
     */
    bool inf_polynomial_superposition::perform(pvar v, conflict_core& core) {
        // TODO: check superposition into disequality again (see notes)

        // TODO: use indexing/marking for this instead of allocating a temporary vector
        // TODO: core saturation premises are from \Gamma (i.e., has_bvar)... but here we further restrict to the core; might need to revise
        //       -- especially: should take into account results from previous saturations (they will be in \Gamma, but only if we use the constraint or one of its descendants for the lemma)
        //       actually: we want to take one from the current cjust (currently true) and one from the conflict (currently false)
        vector<signed_constraint> candidates;
        for (auto c : core)
            if (c->has_bvar() && c.is_positive() && c->is_eq() && c->contains_var(v))
                candidates.push_back(c);

        // TODO: c1 should a currently true constraint, while c2 should take a currently false constraint.
        //       remove candidates vector (premature optimization)
        //      we may want to apply this multiple times (a single resolve might not eliminate the variable).

        LOG_H3("Trying polynomial superposition...");
        for (auto it1 = candidates.begin(); it1 != candidates.end(); ++it1) {
            for (auto it2 = it1 + 1; it2 != candidates.end(); ++it2) {
                signed_constraint c1 = *it1;
                signed_constraint c2 = *it2;
                SASSERT(c1 != c2);
                LOG("c1: " << c1);
                LOG("c2: " << c2);

                pdd a = c1->to_eq().p();
                pdd b = c2->to_eq().p();
                pdd r = a;
                if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
                    continue;
                unsigned const lvl = std::max(c1->level(), c2->level());
                signed_constraint c = cm().eq(lvl, r);
                LOG("resolved: " << c << "        currently false? " << c.is_currently_false(s()));
                if (!c.is_currently_false(s()))
                    continue;
                vector<signed_constraint> premises;
                premises.push_back(c1);
                premises.push_back(c2);
                core.insert(c, std::move(premises));
                return true;

//             clause_builder clause(m_solver);
//             clause.push_literal(~c1->blit());
//             clause.push_literal(~c2->blit());
//             clause.push_new_constraint(m_solver.m_constraints.eq(lvl, r));
//             return clause.build();
            }
        }

        return false;
    }

    bool inf_saturate::perform(pvar v, conflict_core& core) {
        for (auto c1 : core) {
            auto c = c1.as_inequality();
            if (try_ugt_x(v, core, c))
                return true;
            if (try_ugt_y(v, core, c))
                return true;
            if (try_ugt_z(v, core, c))
                return true;
            if (try_y_l_ax_and_x_l_z(v, core, c))
                return true;
        }
        return false;
    }


    // TODO: needs to be justified by the reason lemma that is created on the fly.
    void inf_saturate::push_l(conflict_core& core, unsigned lvl, bool is_strict, pdd const& lhs, pdd const& rhs) {
        if (is_strict)
            core.insert(s().m_constraints.ult(lvl, lhs, rhs));
        else
            core.insert(s().m_constraints.ule(lvl, lhs, rhs));
    }

    /// Add Ω*(x, y) to the conflict state.
    ///
    /// @param[in] p    bit width
    bool inf_saturate::push_omega_mul(conflict_core& core, unsigned level, pdd const& x, pdd const& y) {
        LOG_H3("Omega^*(x, y)");
        LOG("x = " << x);
        LOG("y = " << y);
        auto& pddm = x.manager();   
        unsigned p = pddm.power_of_2();
        unsigned min_k = 0;
        unsigned max_k = p - 1;
        unsigned k = p / 2;

        rational x_val;
        if (s().try_eval(x, x_val)) {
            unsigned x_bits = x_val.bitsize();
            LOG("eval x: " << x << " := " << x_val << " (x_bits: " << x_bits << ")");
            SASSERT(x_val < rational::power_of_two(x_bits));
            min_k = x_bits;
        }

        rational y_val;
        if (s().try_eval(y, y_val)) {
            unsigned y_bits = y_val.bitsize();
            LOG("eval y: " << y << " := " << y_val << " (y_bits: " << y_bits << ")");
            SASSERT(y_val < rational::power_of_two(y_bits));
            max_k = p - y_bits;
        }

        if (min_k > max_k) {
            // In this case, we cannot choose k such that both literals are false.
            // This means x*y overflows in the current model and the chosen rule is not applicable.
            // (or maybe we are in the case where we need the msb-encoding for overflow).
            return false;
        }

        SASSERT(min_k <= max_k);  // if this assertion fails, we cannot choose k s.t. both literals are false

        // TODO: could also choose other value for k (but between the bounds)
        if (min_k == 0)
            k = max_k;
        else
            k = min_k;

        LOG("k = " << k << "; min_k = " << min_k << "; max_k = " << max_k << "; p = " << p);
        SASSERT(min_k <= k && k <= max_k);

        // x >= 2^k
        auto c1 = s().m_constraints.ule(level, pddm.mk_val(rational::power_of_two(k)), x);
        // y > 2^{p-k}
        auto c2 = s().m_constraints.ult(level, pddm.mk_val(rational::power_of_two(p - k)), y);

        // TODO: these need to be justified as well.
        core.insert(~c1);
        core.insert(~c2);
        return true;
    }

    /*
    * Match [v] .. <= v 
    */
    bool inf_saturate::is_l_v(pvar v, inequality const& i) {
        return i.rhs == s().var(v);
    }

    /*
    * Match [v] v <= ...
    */
    bool inf_saturate::is_g_v(pvar v, inequality const& i) {
        return i.lhs == s().var(v);
    }

    /*
    * Match [x] y <= a*x
    */
    bool inf_saturate::is_Y_l_Ax(pvar x, inequality const& d, pdd& a, pdd& y) {
        y = d.lhs;
        return d.rhs.degree(x) == 1 && d.rhs.factor(x, 1, a);
    }

    bool inf_saturate::verify_Y_l_Ax(pvar x, inequality const& d, pdd const& a, pdd const& y) {        
        return d.lhs == y && d.rhs == a * s().var(x);
    }

    /**
    * Match [v] v*x <= z*x
    */
    bool inf_saturate::is_Xy_l_XZ(pvar v, inequality const& c, pdd& x, pdd& z) {
        if (c.lhs.degree(v) != 1)
            return false;

        if (!c.lhs.factor(v, 1, x))
            return false;

        // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
        //       so for now we just allow the form 'value*variable'.
        //        (extension to arbitrary monomials for 'x' should be fairly easy too)
        if (!x.is_unary())
            return false;
        unsigned x_var = x.var();
        rational x_coeff = x.hi().val();
        pdd xz = x;
        if (!c.rhs.try_div(x_coeff, xz))
            return false;
        if (!xz.factor(x_var, 1, z))
            return false;
        LOG("zx > yx: " << show_deref(c.src));
        return true;
    }

    bool inf_saturate::verify_Xy_l_XZ(pvar v, inequality const& c, pdd const& x, pdd const& z) {
        return c.lhs == s().var(v) * x && c.rhs == z * x;
    }

    /**
    * Match [z] yx <= zx
    */
    bool inf_saturate::is_YX_l_zX(pvar z, inequality const& c, pdd& x, pdd& y) {
        if (c.rhs.degree(z) != 1)
            return false;
        if (!c.rhs.factor(z, 1, x))
            return false;
        // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
        //       so for now we just allow the form 'value*variable'.
        //       (extension to arbitrary monomials for 'x' should be fairly easy too)
        if (!x.is_unary())
            return false;

        unsigned x_var = x.var();
        rational x_coeff = x.hi().val();
        pdd xy = x;
        return c.lhs.try_div(x_coeff, xy) && xy.factor(x_var, 1, y);
    }

    bool inf_saturate::verify_YX_l_zX(pvar z, inequality const& c, pdd const& x, pdd const& y) {
        return c.lhs == y * x && c.rhs == s().var(z) * x;
    }

    /**
     * Implement the inferences
     *  [x] zx > yx  ==>  Ω*(x,y) \/ z > y
     *  [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z
     */
    bool inf_saturate::try_ugt_x(pvar v, conflict_core& core, inequality const& c) {
        if (c.lhs.degree(v) != 1)
            return false;
        if (c.rhs.degree(v) != 1)
            return false;
        pdd const x = s().var(v);

        pdd y = x;
        if (!c.lhs.factor(v, 1, y))
            return false;
        pdd z = x;
        if (!c.rhs.factor(v, 1, z))
            return false;

        unsigned const lvl = c.src->level();

        // Omega^*(x, y)
        if (!push_omega_mul(core, lvl, x, y))
            return false;
        push_l(core, lvl, c.is_strict, y, z);

        return true;
    }

    /// [y] z' <= y /\ zx > yx  ==>  Ω*(x,y) \/ zx > z'x
    /// [y] z' <= y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
    bool inf_saturate::try_ugt_y(pvar v, conflict_core& core, inequality const& le_y, inequality const& yx_l_zx, pdd const& x, pdd const& z) {
        LOG_H3("Try z' <= y && zx > yx where y := v" << v);
        pdd const y = s().var(v);

        SASSERT(is_l_v(v, le_y));
        SASSERT(verify_Xy_l_XZ(v, yx_l_zx, x, z));
          
        unsigned const lvl = std::max(yx_l_zx.src->level(), le_y.src->level());
        pdd const& z_prime = le_y.lhs;

        // Omega^*(x, y)
        if (!push_omega_mul(core, lvl, x, y))
            return false;

        // z'x <= zx
        push_l(core, lvl, yx_l_zx.is_strict || le_y.is_strict, z_prime * x, z * x);

        return true;
    }

    bool inf_saturate::try_ugt_y(pvar v, conflict_core& core, inequality const& c) {
        if (!is_l_v(v, c))
            return false;
        pdd x = s().var(v);
        pdd z = x;
        for (auto dd : core) {
            auto d = dd.as_inequality();
            if (is_Xy_l_XZ(v, d, x, z) && try_ugt_y(v, core, c, d, x, z))
                return true;
        }
        return false;
    }


    /// [x]  y <= ax /\ x <= z  (non-overflow case)
    ///     ==>   Ω*(a, z)  \/  y <= az
    bool inf_saturate::try_y_l_ax_and_x_l_z(pvar x, conflict_core& core, inequality const& c) {
        if (!is_g_v(x, c))
            return false;

        pdd y = s().var(x);
        pdd a = y;
        for (auto dd : core) {
            auto d = dd.as_inequality();
            if (is_Y_l_Ax(x, d, a, y) && try_y_l_ax_and_x_l_z(x, core, c, d, a, y))
                return true;
        }
        return false;
    }

    bool inf_saturate::try_y_l_ax_and_x_l_z(pvar x, conflict_core& core, inequality const& x_l_z, inequality const& y_l_ax, pdd const& a, pdd const& y) {

        SASSERT(is_g_v(x, x_l_z));
        SASSERT(verify_Y_l_Ax(x, y_l_ax, a, y));
        pdd z = x_l_z.rhs;
        unsigned const lvl = std::max(x_l_z.src->level(), y_l_ax.src->level());
        if (!push_omega_mul(core, lvl, a, z))
            return false;
        push_l(core, lvl, x_l_z.is_strict || y_l_ax.is_strict, y, a * z);
        return true;
    }


    /// [z] z <= y' /\ zx > yx  ==>  Ω*(x,y') \/ y'x > yx
    /// [z] z <= y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
    bool inf_saturate::try_ugt_z(pvar z, conflict_core& core, inequality const& c) {
        if (!is_g_v(z, c))
            return false;

        pdd y = s().var(z);
        pdd x = y;
        for (auto dd : core) {
            auto d = dd.as_inequality();
            if (is_YX_l_zX(z, d, x, y) && try_ugt_z(z, core, c, d, x, y))
                return true;
        }
        return false;
    }

    bool inf_saturate::try_ugt_z(pvar z, conflict_core& core, inequality const& c, inequality const& d, pdd const& x, pdd const& y) {
        SASSERT(is_g_v(z, c));
        SASSERT(verify_YX_l_zX(z, d, x, y));

        unsigned const lvl = std::max(c.src->level(), d.src->level());
        pdd const& y_prime = c.rhs;

        // Omega^*(x, y')
        if (!push_omega_mul(core, lvl, x, y_prime))
            return false;
        // yx <= y'x
        push_l(core, lvl, c.is_strict || d.is_strict, y * x, y_prime * x);
        return true;
    }


}
