/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation / resolution

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/explain.h"
#include "math/polysat/log.h"
#include "math/polysat/solver.h"

namespace polysat {

    constraint_manager& explainer::cm() { return s().m_constraints; }

    // TODO(later): check superposition into disequality again (see notes)
    bool ex_polynomial_superposition::try_explain(pvar v, /* vector<signed_constraint> const& cjust_v, */ conflict_core& core) {
        // TODO: core saturation premises are from \Gamma (i.e., has_bvar)... but here we further restrict to the core; might need to revise
        //       -- especially: should take into account results from previous saturations (they will be in \Gamma, but only if we use the constraint or one of its descendants for the lemma)
        //       actually: we want to take one from the current cjust (currently true) and one from the conflict (currently false)

        // TODO: resolve multiple times... a single time might not be enough to eliminate the variable.

        LOG_H3("Trying polynomial superposition...");
        for (auto it1 = core.begin(); it1 != core.end(); ++it1) {
            signed_constraint c1 = *it1;
            if (!c1->has_bvar())
                continue;
            if (!c1.is_positive())
                continue;
            if (!c1->is_eq())
                continue;
            if (!c1->contains_var(v))
                continue;
            if (!c1.is_currently_true(s()))
                continue;

            for (auto it2 = core.begin(); it2 != core.end(); ++it2) {
                signed_constraint c2 = *it2;
                if (!c2->has_bvar())
                    continue;
                if (!c2.is_positive())
                    continue;
                if (!c2->is_eq())
                    continue;
                if (!c2->contains_var(v))
                    continue;
                if (!c2.is_currently_false(s()))
                    continue;

                // TODO: separate method for this; then try_explain1 and try_explain* for multi-steps; replace the false constraint in the core.
                // c1 is true, c2 is false
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
                if (!c->contains_var(v)) {
                    core.reset(); // TODO: doesn't work; this removes the premises as well... / instead: remove the false one.
                    core.insert(c, std::move(premises));
                    return true;
                } else {
                    core.insert(c, std::move(premises));
                }
            }
        }

        return false;
    }








//         LOG_H3("Attempting to explain conflict for v" << v);
//         m_var = v;
//         m_cjust_v = cjust;

//         for (auto* c : cjust)
//             m_conflict.push_back(c);

//         for (auto* c : m_conflict.units())
//             LOG("Constraint: " << show_deref(c));
//         for (auto* c : m_conflict.clauses())
//             LOG("Clause: " << show_deref(c));

//         // TODO: this is a temporary workaround! we should not get any undef constraints at this point
//         constraints_and_clauses confl = std::move(m_conflict);
//         SASSERT(m_conflict.empty());
//         for (auto* c : confl.units())
//             if (!c->is_undef())
//                 m_conflict.push_back(c);
//         for (auto* c : confl.clauses())
//             m_conflict.push_back(c);

//         // Collect unit constraints
//         //
//         // TODO: the distinction between units and unit clauses is a bit awkward; maybe it should be removed.
//         //       We could then also remove the hybrid container 'constraints_and_clauses' by a clause_ref_vector
//         SASSERT(m_conflict_units.empty());
//         for (constraint* c : m_conflict.units())
//             // if (c->is_eq())
//                 m_conflict_units.push_back(c);
//         for (auto clause : m_conflict.clauses()) {
//             if (clause->size() == 1) {
//                 sat::literal lit = (*clause)[0];
//                 constraint* c = m_solver.m_constraints.lookup(lit.var());
//                 LOG("unit clause: " << show_deref(c));
//                 // Morally, a derived unit clause is always asserted at the base level.
//                 // (Even if we don't want to keep this one around. But maybe we should? Do we want to reconstruct proofs?)
//                 c->set_unit_clause(clause);
//                 c->assign(!lit.sign());
//                 // this clause is really a unit.
//                 // if (c->is_eq()) {
//                     m_conflict_units.push_back(c);
//                 // }
//             }
//         }

//         // TODO: we should share work done for examining constraints between different resolution methods
//         clause_ref lemma;
//         if (!lemma) lemma = by_polynomial_superposition();
//         if (!lemma) lemma = by_ugt_x();
//         if (!lemma) lemma = by_ugt_y();
//         if (!lemma) lemma = by_ugt_z();
//         if (!lemma) lemma = y_ule_ax_and_x_ule_z();

//         DEBUG_CODE({
//             if (lemma) {
//                 LOG("New lemma: " << *lemma);
//                 for (auto* c : lemma->new_constraints()) {
//                     LOG("New constraint: " << show_deref(c));
//                 }
//                 // All constraints in the lemma must be false in the conflict state
//                 for (auto lit : lemma->literals()) {
//                     if (m_solver.m_bvars.value(lit) == l_false)
//                         continue;
//                     SASSERT(m_solver.m_bvars.value(lit) != l_true);
//                     constraint* c = m_solver.m_constraints.lookup(lit.var());
//                     SASSERT(c);
//                     tmp_assign _t(c, lit);
//                     // if (c->is_currently_true(m_solver)) {
//                     //     LOG("ERROR: constraint is true: " << show_deref(c));
//                     //     SASSERT(false);
//                     // }
//                     // SASSERT(!c->is_currently_true(m_solver));
//                     // SASSERT(c->is_currently_false(m_solver));   // TODO: pvar v may not have a value at this point...
//                 }
//             }
//             else {
//                 LOG("No lemma");
//             }
//         });

//         m_var = null_var;
//         m_cjust_v.reset();
//         return lemma;
//     }

//     /// [x] zx > yx  ==>  Ω*(x,y) \/ z > y
//     /// [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z
//     clause_ref conflict_explainer::by_ugt_x() {
//         LOG_H3("Try zx > yx where x := v" << m_var);

//         pdd const x = m_solver.var(m_var);
//         unsigned const sz = m_solver.size(m_var);
//         pdd const zero = m_solver.sz2pdd(sz).zero();

//         // Find constraint of shape: yx <= zx
//         for (auto* c1 : m_conflict.units()) {
//             auto c = c1->as_inequality();
//             if (c.lhs.degree(m_var) != 1)
//                 continue;
//             if (c.rhs.degree(m_var) != 1)
//                 continue;
//             pdd y = zero;
//             pdd rest = zero;
//             c.lhs.factor(m_var, 1, y, rest);
//             if (!rest.is_zero())
//                 continue;
//             pdd z = zero;
//             c.rhs.factor(m_var, 1, z, rest);
//             if (!rest.is_zero())
//                 continue;

//             unsigned const lvl = c.src->level();

//             clause_builder clause(m_solver);
//             clause.push_literal(~c.src->blit());
//             // Omega^*(x, y)
//             if (!push_omega_mul(clause, lvl, sz, x, y))
//                 continue;
//             constraint_literal y_le_z;
//             if (c.is_strict)
//                 y_le_z = m_solver.m_constraints.ult(lvl, y, z);
//             else
//                 y_le_z = m_solver.m_constraints.ule(lvl, y, z);
//             LOG("z>y: " << show_deref(y_le_z));
//             clause.push_new_constraint(std::move(y_le_z));

//             return clause.build();
//         }
//         return nullptr;
//     }

//     /// [y] z' <= y /\ zx > yx  ==>  Ω*(x,y) \/ zx > z'x
//     /// [y] z' <= y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
//     clause_ref conflict_explainer::by_ugt_y() {
//         LOG_H3("Try z' <= y && zx > yx where y := v" << m_var);

//         pdd const y = m_solver.var(m_var);
//         unsigned const sz = m_solver.size(m_var);
//         pdd const zero = m_solver.sz2pdd(sz).zero();

//         // Collect constraints of shape "_ <= y"
//         vector<inequality> ds;
//         for (auto* d1 : m_conflict.units()) {
//             auto d = d1->as_inequality();
//             // TODO: a*y where 'a' divides 'x' should also be easy to handle (assuming for now they're numbers)
//             // TODO: also z' < y should follow the same pattern.
//             if (d.rhs != y)
//                 continue;
//             LOG("z' <= y candidate: " << show_deref(d.src));
//             ds.push_back(std::move(d));
//         }
//         if (ds.empty())
//             return nullptr;

//         // Find constraint of shape: yx <= zx
//         for (auto* c1 : m_conflict.units()) {
//             auto c = c1->as_inequality();
//             if (c.lhs.degree(m_var) != 1)
//                 continue;
//             pdd x = zero;
//             pdd rest = zero;
//             c.lhs.factor(m_var, 1, x, rest);
//             if (!rest.is_zero())
//                 continue;
//             // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
//             //       so for now we just allow the form 'value*variable'.
//             //       (extension to arbitrary monomials for 'x' should be fairly easy too)
//             if (!x.is_unary())
//                 continue;
//             unsigned x_var = x.var();
//             rational x_coeff = x.hi().val();
//             pdd xz = zero;
//             if (!c.rhs.try_div(x_coeff, xz))
//                 continue;
//             pdd z = zero;
//             xz.factor(x_var, 1, z, rest);
//             if (!rest.is_zero())
//                 continue;

//             LOG("zx > yx: " << show_deref(c.src));

//             // TODO: for now, we just try all ds
//             for (auto const& d : ds) {
//                 unsigned const lvl = std::max(c.src->level(), d.src->level());
//                 pdd const& z_prime = d.lhs;

//                 clause_builder clause(m_solver);
//                 clause.push_literal(~c.src->blit());
//                 clause.push_literal(~d.src->blit());
//                 // Omega^*(x, y)
//                 if (!push_omega_mul(clause, lvl, sz, x, y))
//                     continue;
//                 // z'x <= zx
//                 constraint_literal zpx_le_zx;
//                 if (c.is_strict || d.is_strict)
//                     zpx_le_zx = m_solver.m_constraints.ult(lvl, z_prime*x, z*x);
//                 else
//                     zpx_le_zx = m_solver.m_constraints.ule(lvl, z_prime*x, z*x);
//                 LOG("zx>z'x: " << show_deref(zpx_le_zx));
//                 clause.push_new_constraint(std::move(zpx_le_zx));

//                 return clause.build();
//             }
//         }
//         return nullptr;
//     }

//     /// [z] z <= y' /\ zx > yx  ==>  Ω*(x,y') \/ y'x > yx
//     /// [z] z <= y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
//     clause_ref conflict_explainer::by_ugt_z() {
//         LOG_H3("Try z <= y' && zx > yx where z := v" << m_var);

//         pdd const z = m_solver.var(m_var);
//         unsigned const sz = m_solver.size(m_var);
//         pdd const zero = m_solver.sz2pdd(sz).zero();

//         // Collect constraints of shape "z <= _"
//         vector<inequality> ds;
//         for (auto* d1 : m_conflict.units()) {
//             auto d = d1->as_inequality();
//             // TODO: a*y where 'a' divides 'x' should also be easy to handle (assuming for now they're numbers)
//             // TODO: also z < y' should follow the same pattern.
//             if (d.lhs != z)
//                 continue;
//             LOG("z <= y' candidate: " << show_deref(d.src));
//             ds.push_back(std::move(d));
//         }
//         if (ds.empty())
//             return nullptr;

//         // Find constraint of shape: yx <= zx
//         for (auto* c1 : m_conflict.units()) {
//             auto c = c1->as_inequality();
//             if (c.rhs.degree(m_var) != 1)
//                 continue;
//             pdd x = zero;
//             pdd rest = zero;
//             c.rhs.factor(m_var, 1, x, rest);
//             if (!rest.is_zero())
//                 continue;
//             // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
//             //       so for now we just allow the form 'value*variable'.
//             //       (extension to arbitrary monomials for 'x' should be fairly easy too)
//             if (!x.is_unary())
//                 continue;
//             unsigned x_var = x.var();
//             rational x_coeff = x.hi().val();
//             pdd xy = zero;
//             if (!c.lhs.try_div(x_coeff, xy))
//                 continue;
//             pdd y = zero;
//             xy.factor(x_var, 1, y, rest);
//             if (!rest.is_zero())
//                 continue;

//             LOG("zx > yx: " << show_deref(c.src));

//             // TODO: for now, we just try all ds
//             for (auto const& d : ds) {
//                 unsigned const lvl = std::max(c.src->level(), d.src->level());
//                 pdd const& y_prime = d.rhs;

//                 clause_builder clause(m_solver);
//                 clause.push_literal(~c.src->blit());
//                 clause.push_literal(~d.src->blit());
//                 // Omega^*(x, y')
//                 if (!push_omega_mul(clause, lvl, sz, x, y_prime))
//                     continue;
//                 // yx <= y'x
//                 constraint_literal yx_le_ypx;
//                 if (c.is_strict || d.is_strict)
//                     yx_le_ypx = m_solver.m_constraints.ult(lvl, y*x, y_prime*x);
//                 else
//                     yx_le_ypx = m_solver.m_constraints.ule(lvl, y*x, y_prime*x);
//                 LOG("y'x>yx: " << show_deref(yx_le_ypx));
//                 clause.push_new_constraint(std::move(yx_le_ypx));

//                 return clause.build();
//             }
//         }
//         return nullptr;
//     }

//     /// [x]  y <= ax /\ x <= z  (non-overflow case)
//     ///     ==>   Ω*(a, z)  \/  y <= az
//     clause_ref conflict_explainer::y_ule_ax_and_x_ule_z() {
//         LOG_H3("Try y <= ax && x <= z where x := v" << m_var);

//         pdd const x = m_solver.var(m_var);
//         unsigned const sz = m_solver.size(m_var);
//         pdd const zero = m_solver.sz2pdd(sz).zero();

//         // Collect constraints of shape "x <= _"
//         vector<inequality> ds;
//         for (auto* d1 : m_conflict.units()) {
//             inequality d = d1->as_inequality();
//             if (d.lhs != x)
//                 continue;
//             LOG("x <= z' candidate: " << show_deref(d.src));
//             ds.push_back(std::move(d));
//         }
//         if (ds.empty())
//             return nullptr;

//         // Find constraint of shape: y <= ax
//         for (auto* c1 : m_conflict.units()) {
//             inequality c = c1->as_inequality();
//             if (c.rhs.degree(m_var) != 1)
//                 continue;
//             pdd a = zero;
//             pdd rest = zero;
//             c.rhs.factor(m_var, 1, a, rest);
//             if (!rest.is_zero())
//                 continue;
//             pdd const& y = c.lhs;

//             LOG("y <= ax: " << show_deref(c1));

//             // TODO: for now, we just try all of the other constraints in order
//             for (auto const& d : ds) {
//                 unsigned const lvl = std::max(c1->level(), d.src->level());
//                 pdd const& z = d.rhs;

//                 clause_builder clause(m_solver);
//                 clause.push_literal(~c.src->blit());
//                 clause.push_literal(~d.src->blit());
//                 // Omega^*(a, z)
//                 if (!push_omega_mul(clause, lvl, sz, a, z))
//                     continue;
//                 // y'x > yx
//                 constraint_literal y_ule_az;
//                 if (c.is_strict || d.is_strict)
//                     y_ule_az = m_solver.m_constraints.ult(lvl, y, a*z);
//                 else
//                     y_ule_az = m_solver.m_constraints.ule(lvl, y, a*z);
//                 LOG("y<=az: " << show_deref(y_ule_az));
//                 clause.push_new_constraint(std::move(y_ule_az));

//                 return clause.build();
//             }
//         }
//         return nullptr;
//     }

//     /// Add Ω*(x, y) to the clause.
//     ///
//     /// @param[in] p    bit width
//     bool conflict_explainer::push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y) {
//         LOG_H3("Omega^*(x, y)");
//         LOG("x = " << x);
//         LOG("y = " << y);
//         auto& pddm = m_solver.sz2pdd(p);
//         unsigned min_k = 0;
//         unsigned max_k = p - 1;
//         unsigned k = p/2;

//         rational x_val;
//         if (m_solver.try_eval(x, x_val)) {
//             unsigned x_bits = x_val.bitsize();
//             LOG("eval x: " << x << " := " << x_val << " (x_bits: " << x_bits << ")");
//             SASSERT(x_val < rational::power_of_two(x_bits));
//             min_k = x_bits;
//         }

//         rational y_val;
//         if (m_solver.try_eval(y, y_val)) {
//             unsigned y_bits = y_val.bitsize();
//             LOG("eval y: " << y << " := " << y_val << " (y_bits: " << y_bits << ")");
//             SASSERT(y_val < rational::power_of_two(y_bits));
//             max_k = p - y_bits;
//         }

//         if (min_k > max_k) {
//             // In this case, we cannot choose k such that both literals are false.
//             // This means x*y overflows in the current model and the chosen rule is not applicable.
//             // (or maybe we are in the case where we need the msb-encoding for overflow).
//             return false;
//         }

//         SASSERT(min_k <= max_k);  // if this assertion fails, we cannot choose k s.t. both literals are false

//         // TODO: could also choose other value for k (but between the bounds)
//         if (min_k == 0)
//             k = max_k;
//         else
//             k = min_k;

//         LOG("k = " << k << "; min_k = " << min_k << "; max_k = " << max_k << "; p = " << p);
//         SASSERT(min_k <= k && k <= max_k);

//         // x >= 2^k
//         auto c1 = m_solver.m_constraints.ule(level, pddm.mk_val(rational::power_of_two(k)), x);
//         // y > 2^{p-k}
//         auto c2 = m_solver.m_constraints.ult(level, pddm.mk_val(rational::power_of_two(p-k)), y);
//         clause.push_new_constraint(std::move(c1));
//         clause.push_new_constraint(std::move(c2));
//         return true;
//     }

}
