/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/saturation.h"
#include "sat/smt/polysat/umul_ovfl_constraint.h"
#include "sat/smt/polysat/ule_constraint.h"


namespace polysat {

    saturation::saturation(core& c) : c(c), C(c.cs()) {}

    lbool saturation::operator()() {
        bool has_conflict = false;
        for (auto idx : c.assigned_constraints()) {
            auto sc = c.get_constraint(idx);
            lbool eval_value = c.strong_eval(sc);
            if (eval_value == l_true)
                continue;
            has_conflict = true;
            if (eval_value == l_undef)
                continue;
            
            TRACE("bv", sc.display(tout << "eval: ") << " evaluates to " << eval_value << "\n");

            has_conflict = true;
            auto vars = c.find_conflict_variables(idx);
            for (auto v : vars)
                if (resolve(v, idx))
                    return l_false;
        }
        if (has_conflict)
            return l_undef;
        return l_true;
    }

    bool saturation::resolve(pvar v, constraint_id id) {
        auto sc = c.get_constraint(id);
        if (!sc.unfold_vars().contains(v))
            return false;
        if (sc.is_ule())
            resolve(v, inequality::from_ule(c, id));
        else if (sc.is_umul_ovfl())
            try_umul_ovfl(v, umul_ovfl(id, sc));
        else if (sc.is_op())
            try_op(v, sc, c.get_dependency(id));

        return c.inconsistent();
    }

    void saturation::resolve(pvar v, inequality const& i) {
        if (c.size(v) != i.lhs().power_of_2())
            return;
        if (false && !c.inconsistent())
            try_ugt_x(v, i);  
        if (false && !c.inconsistent())
            try_ugt_y(v, i);
        if (false && !c.inconsistent())
            try_ugt_z(v, i);    
        if (false && !c.inconsistent())
            try_eq_resolve(v, i);
    }

    void saturation::add_clause(char const* name, clause const& cs, bool is_redundant) { 
        vector<constraint_or_dependency> lemma;
        for (auto const& e : cs) {
            if (std::holds_alternative<dependency>(e)) {
                auto d = *std::get_if<dependency>(&e);
                lemma.push_back(d);
            }
            else if (std::holds_alternative<signed_constraint>(e)) {
                auto sc = *std::get_if<signed_constraint>(&e);
                if (c.strong_eval(sc) != l_false)
                    return;
                auto d = c.propagate(~sc, c.explain_strong_eval(sc));
                lemma.push_back(d);
            }
            else
                UNREACHABLE();
        }        
        c.add_axiom(name, lemma.begin(), lemma.end(), is_redundant);
        SASSERT(c.inconsistent());
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
     * Implement the inferences
     *  [x] yx < zx   ==>  Ω*(x,y) \/ y < z
     *  [x] yx <= zx  ==>  Ω*(x,y) \/ y <= z \/ x = 0
     */
    void saturation::try_ugt_x(pvar v, inequality const& i) {
        pdd x = c.var(v);
        pdd y = x;
        pdd z = x;       

        if (!i.is_xY_l_xZ(v, y, z))
            return;

        auto ovfl = C.umul_ovfl(x, y);
        if (i.is_strict()) 
            add_clause("[x] yx < zx ==> Ω*(x,y) \\/ y < z", { i.dep(), ovfl, C.ult(y, z)}, true);
        else 
            add_clause("[x] yx <= zx ==> Ω*(x,y) \\/ y <= z \\/ x = 0", { i.dep(), ovfl, C.eq(x), C.ule(y, z) }, true);
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
        if (!i.is_Xy_l_XZ(v, x, z))
            return;
        for (constraint_id id : constraint_iterator(c, [&](auto const& sc) { return inequality::is_l_v(y, sc); })) {
            auto j = inequality::from_ule(c, id);
            pdd const& z_prime = i.lhs();
            bool is_strict = i.is_strict() || j.is_strict();
            add_clause("[y] z' <= y & yx <= zx ==> Ω*(x,y) \\/ z'x <= zx", 
                { i.dep(), j.dep(), C.umul_ovfl(x, y), ineq(is_strict, z_prime * x, z * x) }, true);
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
            add_clause("[z] z <= y' && yx <= zx ==> Ω*(x,y') \\/ yx <= y'x", 
                { i.dep(), j.dep(), c.umul_ovfl(x, y_prime), ineq(is_strict, y * x, y_prime * x) }, true);
        }
    }

    // Ovfl(x, y) & ~Ovfl(y, z) ==> x > z
    void saturation::try_umul_monotonicity(umul_ovfl const& sc) {
        auto p = sc.p(), q = sc.q();
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
                add_clause("[y] ~ovfl(p, q1) & ovfl(p, q2) ==> q1 < q2", { d1, d2, C.ult(q1, q2) }, true);
            else
                add_clause("[y] ovfl(p, q1) & ~ovfl(p, q2) ==> q1 > q2", { d1, d2, C.ult(q2, q1) }, true);
        }
    }

    /**
    * Expand the following axioms:
    * Ovfl(x, y) & msb(x) <= k => msb(y) >= N - k - 1
    * Ovfl(x, y) & msb(x) <= k & msb(y) <= N - k - 1 => 0x * 0y >= 2^{N-1}
    * 
    * ~Ovfl(x,y) & msb(x) >= k => msb(y) <= N - k - 1
    * ~Ovfl(x,y) & msb(x) >= k & msb(y) >= N - k - 1 => 0x * 0y < 2^{N-1}
    */
    void saturation::try_umul_blast(umul_ovfl const& sc) {
        auto x = sc.p();
        auto y = sc.q();
        if (!x.is_val())
            return;
        if (!y.is_val())
            return;
        auto N = x.manager().power_of_2();
        auto d = c.get_dependency(sc.id());

        auto vx = x.val();
        auto vy = y.val();
        auto bx = vx.get_num_bits();
        auto by = vy.get_num_bits();
        if (bx > by) {
            std::swap(bx, by);
            std::swap(x, y);
        }

        // Keep in mind that
        // num-bits(0) = 1
        // num-bits(1) = 1
        // num-bits(2) = 2
        // num-bits(4) = 3
        // msb(0) = 0
        // msb(1) = 0
        // msb(2) = 1
        // msb(3) = 1
        // msb(2^N - 1) = N-1
        // msb(x) >= k <=> x >= 2^k,    for k > 0
        // msb(x) <= k <=> x < 2^{k+1}, for k + 1 < N

        auto msb_ge = [&](pdd const& x, unsigned k) {
            SASSERT(k > 0);
            return C.uge(x, rational::power_of_two(k));
        };

        auto msb_le = [&](pdd const& x, unsigned k) {
            SASSERT(k + 1 < N);
            return C.ult(x, rational::power_of_two(k + 1));
        };
 
        if (sc.sign()) {
            // Case ~Ovfl(x,y) is asserted by current assignment x * y is overflow
            SASSERT(bx > 1 && by > 1);
            SASSERT(bx + by >= N + 1);
            auto k = bx - 1;
            if (bx + by > N + 1) 
                add_clause("~Ovfl(x, y) & msb(x) >= k => msb(y) <= N - k - 1", 
                    {d, ~msb_ge(x, k), msb_le(y, N - k - 1)},
                    true);            
            else {
                auto x1 = c.mk_zero_extend(1, x);
                auto y1 = c.mk_zero_extend(1, y);                
                add_clause("~Ovfl(x, y) & msb(x) >= k & msb(y) >= N - k - 1 => 0x * 0y < 2^{N-1}",
                    { d, ~msb_ge(x, k),
                         ~msb_ge(y, N - k - 1),
                         C.ult(x1 * y1, rational::power_of_two(N - 1))
                    }, true);
            }
        }
        else {
            // Case Ovfl(x,y) 
            if (bx == 0) {
                add_clause("Ovfl(x, y) => x > 1", { d, C.ugt(x, 1) }, true);
            }
            else if (bx + by < N + 1) {
                SASSERT(bx <= by);
                auto k = bx - 1;
                add_clause("Ovfl(x, y) & msb(x) <= k => msb(y) >= N - k - 1",
                    { d, ~msb_le(x, k), msb_ge(y, N - k - 1) }, true);
            }
            else {
                auto k = bx - 1;
                auto x1 = c.mk_zero_extend(1, x);
                auto y1 = c.mk_zero_extend(1, y);
                add_clause("Ovfl(x, y) & msb(x) <= k & msb(y) <= N - k - 1 = > 0x * 0y >= 2 ^ {N - 1}",
                    { d, ~msb_le(x, k), ~msb_le(y, N - k - 1), C.uge(x1 * y1, rational::power_of_two(N - 1)) },
                    true);
            }
        }
    }


    void saturation::try_umul_ovfl(pvar v, umul_ovfl const& sc) {
        try_umul_monotonicity(sc);
        try_umul_blast(sc);           
    }

    void saturation::try_eq_resolve(pvar v, inequality const& i) {
        if (!i.rhs().is_zero() || i.is_strict())
            return;
        for (auto id : constraint_iterator(c, [&](auto const& sc) { return sc.is_ule() && !sc.sign() && sc.to_ule().rhs().is_zero(); })) {
            auto sc = c.get_constraint(id);
            if (!sc.unfold_vars().contains(v))
                continue;
            auto j = inequality::from_ule(c, id);
            SASSERT(!j.is_strict());
            try_eq_resolve(v, i, j);
        }
    }

    void saturation::try_eq_resolve(pvar v, inequality const& i, inequality const& j) {
        // i is true, j is false, both their rhs are 0.
        SASSERT(i.rhs().is_zero() && j.rhs().is_zero() && !i.is_strict() && !j.is_strict());
        pdd a = i.lhs();
        pdd b = j.lhs();
        unsigned degree_a = a.degree();
        unsigned degree_b = b.degree();
        pdd r = a;
        if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
            return;            
        unsigned degree_r = r.degree();
        if (degree_a < degree_r && degree_b < degree_r)
            return;
        // Only keep result if the degree in c2 was reduced.
        // (this condition might be too strict, but we use it for now to prevent looping)
        if (b.degree(v) <= r.degree(v))
            return;
        if (a.degree(v) <= r.degree(v))
            return;

        add_clause("ax + b = 0 & cx + d = 0 ==> cb - da = 0", { i.dep(), j.dep(), C.eq(r) }, true);
    }


    void saturation::try_op(pvar v, signed_constraint& sc, dependency const& d) {
        SASSERT(sc.is_op());
        VERIFY(sc.propagate(c, l_true, d));
    }

    // possible algebraic rule:
    // From "Hacker's Delight", section 2-2. Addition Combined with Logical Operations;
    // found via Int-Blasting paper; see https://doi.org/10.1007/978-3-030-94583-1_24
    // bor(p,q) = (p + q) - band(p, q); 

}
