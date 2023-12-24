/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6


TODO: preserve falsification
- each rule selects a certain premises that are problematic.
  If the problematic premise is false under the current assignment, the newly inferred
  literal should also be false in the assignment in order to preserve conflicts.


TODO: when we check that 'x' is "unary":
- in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
  so for now we just allow the form 'value*variable'.
   (extension to arbitrary monomials for 'x' should be fairly easy too)

--*/
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/saturation.h"
#include "sat/smt/polysat/umul_ovfl_constraint.h"
#include "sat/smt/polysat/ule_constraint.h"
#include "util/log.h"


namespace polysat {

    saturation::saturation(core& c) : c(c), C(c.cs()) {}

    bool saturation::resolve(pvar v, constraint_id id) {
        if (c.eval(id) == l_true)
            return false;
        auto sc = c.get_constraint(id);
        if (!sc.vars().contains(v))
            return false;
        if (sc.is_ule())
            resolve(v, inequality::from_ule(c, id));
        else if (sc.is_umul_ovfl())
            try_umul_ovfl(v, umul_ovfl(id, sc));

        return c.inconsistent();
    }

    void saturation::resolve(pvar v, inequality const& i) {
        if (c.size(v) != i.lhs().power_of_2())
            return;
        if (!c.inconsistent())
            try_ugt_x(v, i);  
        if (!c.inconsistent())
            try_ugt_y(v, i);
        if (!c.inconsistent())
            try_ugt_z(v, i);    
    }

    void saturation::propagate(signed_constraint const& sc, std::initializer_list<constraint_id> const& premises) {
        c.propagate(sc, constraint_id_vector(premises));        
    }

    void saturation::add_clause(char const* name, clause const& cs, bool is_redundant) { 
        vector<constraint_or_dependency> lemma;
        for (auto const& e : cs) {
            if (std::holds_alternative<dependency>(e)) {
                auto d = *std::get_if<dependency>(&e);
                lemma.push_back(~d);
            }
            else if (std::holds_alternative<signed_constraint>(e)) {
                auto sc = *std::get_if<signed_constraint>(&e);
                if (c.eval(sc) != l_false)
                    return;
                auto d = c.propagate(~sc, c.explain_eval(sc));
                lemma.push_back(~d);
            }
            else
                UNREACHABLE();
        }        
        c.add_axiom(name, lemma.begin(), lemma.end(), is_redundant);
        SASSERT(c.inconsistent());
    }

    bool saturation::match_core(std::function<bool(signed_constraint const& sc)> const& p, constraint_id& id_out) {
        for (auto id : c.unsat_core()) {
            auto sc = c.get_constraint(id);
            if (p(sc)) {
                id_out = id;
                return true;
            }
        }
        return false;
    }

    bool saturation::match_constraints(std::function<bool(signed_constraint const& sc)> const& p, constraint_id& id_out) {
        for (auto id : c.assigned_constraints()) {
            auto sc = c.get_constraint(id);
            if (p(sc)) {
                id_out = id;
                return true;
            }
        }
        return false;
    }

    signed_constraint saturation::ineq(bool is_strict, pdd const& x, pdd const& y) {
        return is_strict ? c.cs().ult(x, y) : c.cs().ule(x, y);
    }

    /**
     * TODO: this does not belong in saturation, but on the fly? 
     * p <= q, q <= p => p = q
     */
    void saturation::propagate_infer_equality(pvar x, inequality const& i) {
        if (i.is_strict())
            return;
        if (i.lhs().degree(x) == 0 && i.rhs().degree(x) == 0)
            return;
        constraint_id id;
        if (!match_core([&](auto const& sc) { return sc.is_ule() && !sc.sign() && sc.to_ule().lhs() == i.rhs() && sc.to_ule().rhs() == i.lhs(); }, id))
            return;
        c.propagate(c.eq(i.lhs(), i.rhs()), { id, i.id() });     
    }

    /**
     * Implement the inferences
     *  [x] yx < zx   ==>  Ω*(x,y) \/ y < z
     *  [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z \/ x = 0
     */
    void saturation::try_ugt_x(pvar v, inequality const& i) {
        pdd x = c.var(v);
        pdd y = x;
        pdd z = x;       
        auto& C = c.cs();

        if (!i.is_xY_l_xZ(v, y, z))
            return;

        auto ovfl = C.umul_ovfl(x, y);
        if (i.is_strict()) 
            add_clause("[x] yx < zx ==>  Ω*(x,y) \\/ y < z", { i.dep(), ovfl, C.ult(y, z)}, false);
        else 
            add_clause("[x] yx <= zx  ==>  Ω*(x,y) \\/ y <= z \\/ x = 0", { i.dep(), ovfl, C.eq(x), C.ule(y, z) }, false);
    }

    /**
     * [y] z' <= y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
     * [y] z' <= y /\ yx <  zx  ==>  Ω*(x,y) \/ z'x <  zx
     * [y] z' <  y /\ yx <= zx  ==>  Ω*(x,y) \/ z'x <= zx
     * [y] z' <  y /\ yx <  zx  ==>  Ω*(x,y) \/ z'x <  zx
     * [y] z' <  y /\ yx <  zx  ==>  Ω*(x,y) \/ z'x + 1 < zx     (TODO?)
     * [y] z' <  y /\ yx <  zx  ==>  Ω*(x,y) \/ (z' + 1)x < zx   (TODO?)
     */
    void saturation::try_ugt_y(pvar v, inequality const& i) {
        auto y = c.var(v);
        pdd x = y;
        pdd z = y;
        auto& C = c.cs();
        if (!i.is_Xy_l_XZ(v, x, z))
            return;
        for (constraint_id id : constraint_iterator(c, [&](auto const& sc) { return inequality::is_l_v(y, sc); })) {
            auto j = inequality::from_ule(c, id);
            pdd const& z_prime = i.lhs();
            bool is_strict = i.is_strict() || j.is_strict();
            add_clause("[y] z' <= y & yx <= zx", { i.dep(), j.dep(), C.umul_ovfl(x, y), ineq(is_strict, z_prime * x, z * x) }, true);
        }
    }

    /**
     * [z] z <= y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
     * [z] z <= y' /\ yx <  zx  ==>  Ω*(x,y') \/ yx <  y'x
     * [z] z <  y' /\ yx <= zx  ==>  Ω*(x,y') \/ yx <= y'x
     * [z] z <  y' /\ yx <  zx  ==>  Ω*(x,y') \/ yx <  y'x
     * [z] z <  y' /\ yx <  zx  ==>  Ω*(x,y') \/ yx+1 < y'x     (TODO?)
     * [z] z <  y' /\ yx <  zx  ==>  Ω*(x,y') \/ (y+1)x < y'x   (TODO?)
     */
    void saturation::try_ugt_z(pvar v, inequality const& i) {
        auto z = c.var(v);
        pdd y = z;
        pdd x = z;
        if (!i.is_YX_l_zX(v, x, y))
            return;
        for (auto id : constraint_iterator(c, [&](auto const& sc) { return inequality::is_g_v(z, sc); })) {
            auto j = inequality::from_ule(c, id);
            auto y_prime = j.rhs();
            bool is_strict = i.is_strict() || j.is_strict();
            add_clause("[z] z <= y' && yx <= zx", { i.dep(), j.dep(), c.umul_ovfl(x, y_prime), ineq(is_strict, y * x, y_prime * x) }, true);
        }
    }

    // Ovfl(x, y) & ~Ovfl(y, z) ==> x > z
    void saturation::try_umul_ovfl(pvar v, umul_ovfl const& sc) {
    
        auto p = sc.p(), q = sc.q();
        auto& C = c.cs();
        auto match_mul_arg = [&](auto const& sc2) { 
            auto p2 = sc2.to_umul_ovfl().p(), q2 = sc2.to_umul_ovfl().q(); 
            return p == p2 || p == q2 || q == p2 || q == q2;
        };
        auto extract_mul_args = [&](auto const& sc2) -> std::pair<pdd, pdd> {
            auto p2 = sc2.to_umul_ovfl().p(), q2 = sc2.to_umul_ovfl().q();
            if (p == p2)
                return { q, q2 };
            else if (p == q2)
                return { q, p2 };
            else if (q == p2)
                return { p, q2 };
            else {
                SASSERT(q == q2);
                return { p, p2 };
            }
        };
        for (auto id : constraint_iterator(c, [&](auto const& sc2) { return sc2.is_umul_ovfl() && sc.sign() != sc2.sign() && match_mul_arg(sc2); })) {
            auto sc2 = c.get_constraint(id);
            auto d1 = c.get_dependency(sc.id());
            auto d2 = c.get_dependency(id);
            auto [q1, q2] = extract_mul_args(sc2);
            if (sc.sign())
                add_clause("[y] ~ovfl(p, q1) & ovfl(p, q2) ==> q1 < q2", { d1, d2, C.ult(q1, q2) }, false);
            else 
                add_clause("[y] ovfl(p, q1) & ~ovfl(p, q2) ==> q1 > q2", { d1, d2, C.ult(q2, q1)}, false);
        }         
    }

}
