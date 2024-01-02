/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat monomials

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "sat/smt/polysat/monomials.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/number.h"

namespace polysat {

    monomials::monomials(core& c):
        c(c), 
        C(c.cs())
    {}
        
    pvar monomials::mk(unsigned n, pdd const* args) {
        SASSERT(n > 1);
        auto& m = args[0].manager();
        unsigned sz = m.power_of_2();
        m_tmp.reset();
        pdd def = c.value(rational(1), sz);
        for (unsigned i = 0; i < n; ++i) {
            m_tmp.push_back(args[i]);
            def *= args[i];
        }

        pdd var = c.var(c.add_var(sz));
        m_monomials.push_back({m_tmp, var, def, {}, rational(0) });
        auto & mon = m_monomials.back();
              
        for (auto p : m_tmp) 
            mon.arg_vals.push_back(rational(0));
        
        c.trail().push(push_back_vector(m_monomials));
        return mon.var.var();
    }

    pdd monomials::subst(pdd const& p) {
        pdd r = p;
        for (unsigned i = m_monomials.size(); i-- > 0;) {
            if (&r.manager() == &m_monomials[i].var.manager())
                r = r.subst_pdd(m_monomials[i].var.var(), m_monomials[i].def);
        }
        return r;
    }
        
    lbool monomials::refine() {
        init_to_refine();
        if (m_to_refine.empty())
            return l_true;
        shuffle(m_to_refine.size(), m_to_refine.data(), c.rand());
        if (any_of(m_to_refine, [&](auto i) { return mul0(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return mul1(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return non_overflow_unit(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return non_overflow_zero(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return parity0(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return parity(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return prefix_overflow(m_monomials[i]); }))
            return l_false;
        if (any_of(m_to_refine, [&](auto i) { return non_overflow_monotone(m_monomials[i]); }))
            return l_false;
        if (false && any_of(m_to_refine, [&](auto i) { return mulp2(m_monomials[i]); }))
            return l_false;

        return l_undef;
    }

    // bit blast a monomial definition
    lbool monomials::bit_blast() {
        // disable for now
        return l_undef;
        init_to_refine();
        if (m_to_refine.empty())
            return l_true;
        shuffle(m_to_refine.size(), m_to_refine.data(), c.rand());
        if (any_of(m_to_refine, [&](auto i) { return bit_blast(m_monomials[i]); }))
            return l_false;
        return l_undef;
    }

    void monomials::init_to_refine() {
        m_to_refine.reset();
        for (unsigned i = 0; i < m_monomials.size(); ++i) 
            if (eval_to_false(i))
                m_to_refine.push_back(i);
    }

    bool monomials::eval_to_false(unsigned i) {
        rational rhs, lhs;
        auto& mon = m_monomials[i];
        if (!c.try_eval(mon.var, mon.val))
            return false;
        if (!c.try_eval(mon.def, rhs))
            return false;
        if (rhs == mon.val)
            return false;
        for (unsigned j = mon.size(); j-- > 0; ) 
            if (!c.try_eval(mon.args[j], mon.arg_vals[j]))
                return false;                               
        return true;
    }

    // check p = 0 => p * q = 0
    bool monomials::mul0(monomial const& mon) {
        for (unsigned j = mon.size(); j-- > 0; ) {
            if (mon.arg_vals[j] == 0) {
                auto const& p = mon.args[j];
                c.add_axiom("p = 0 => p * q = 0", { ~C.eq(p), C.eq(mon.var) }, true);
                return true;
            }                
        }
        return false;
    }

    // check p = 1 => p * q = q, p = -1 => p * q = -q
    bool monomials::mul1(monomial const& mon) {
        auto& m = mon.args[0].manager();
        return mul(mon, [&](rational const& r) { return r == m.max_value() || r == 1; });
    }

    // check p = k => p * q = k * q
    bool monomials::mulp2(monomial const& mon) {
        auto& m = mon.args[0].manager();
        return mul(mon, [&](rational const& r) { return r == m.max_value() || r.is_power_of_two(); });
    }

    bool monomials::mul(monomial const& mon, std::function<bool(rational const&)> const& p) {
        unsigned free_index = UINT_MAX;
        auto& m = mon.args[0].manager();
        for (unsigned j = mon.size(); j-- > 0; ) {
            auto const& arg_val = mon.arg_vals[j];
            if (p(arg_val))
                continue;
            if (free_index != UINT_MAX)
                return false;
            free_index = j;
        }
        constraint_or_dependency_vector cs;
        pdd offset = c.value(rational(1), mon.num_bits());
        for (unsigned j = mon.size(); j-- > 0; ) {
            if (j != free_index) {
                cs.push_back(~C.eq(mon.args[j], mon.arg_vals[j]));
                offset *= mon.arg_vals[j];
            }
        }
        if (free_index == UINT_MAX)
            cs.push_back(C.eq(mon.var, offset));
        else
            cs.push_back(C.eq(mon.var, offset * mon.args[free_index]));

        return c.add_axiom("p = k => p * q = k * q", cs, true);
    }

    // parity p >= i => parity p * q >= i
    bool monomials::parity(monomial const& mon) {       
        unsigned parity_val = get_parity(mon.val, mon.num_bits());
        for (unsigned j = 0; j < mon.args.size(); ++j) {
            unsigned k = get_parity(mon.arg_vals[j], mon.num_bits());
            if (k > parity_val) {
                auto const& p = mon.args[j];
                c.add_axiom("parity p >= i => parity p * q >= i", { ~C.parity_at_least(p, k), C.parity_at_least(mon.var, k) }, true);
                return true;
            }
        }
        return false;
    }

    // ~ovfl*(p,q) & q != 0 => p <= p*q    
    bool monomials::non_overflow_monotone(monomial const& mon) {
        rational product(1);
        unsigned big_index = UINT_MAX;
        for (auto const& val : mon.arg_vals)
            if (val == 0)
                return false;
        for (unsigned i = 0; i < mon.args.size(); ++i) 
            if (mon.arg_vals[i] > mon.val)
                big_index = i;       
        if (big_index == UINT_MAX)
            return false;
        for (auto const& val : mon.arg_vals)
            product *= val;
        if (product > mon.var.manager().max_value())
            return false;
        pdd p = mon.args[0];
        constraint_or_dependency_vector clause;
        for (unsigned i = 1; i < mon.args.size(); ++i) {
            clause.push_back(C.umul_ovfl(p, mon.args[i]));
            p *= mon.args[i];
        }
        for (unsigned i = 0; i < mon.args.size(); ++i)
            if (i != big_index)
                clause.push_back(C.eq(mon.args[i]));
        clause.push_back(C.ule(mon.args[big_index], mon.var));
        c.add_axiom("~ovfl*(p,q) & q != 0 => p <= p*q", clause, true);
        return true;
    }

    // ~ovfl*(p,q) & p*q = 1 => p = 1, q = 1
    bool monomials::non_overflow_unit(monomial const& mon) {
        if (mon.val != 1)
            return false;
        rational product(1);
        for (auto const& val : mon.arg_vals)
            product *= val;
        if (product > mon.var.manager().max_value())
            return false;
        constraint_or_dependency_vector clause;
        pdd p = mon.args[0];
        clause.push_back(~C.eq(mon.var, 1));
        for (unsigned i = 1; i < mon.args.size(); ++i) {
            clause.push_back(C.umul_ovfl(p, mon.args[i]));
            p *= mon.args[i];
        }        
        for (auto const& q : mon.args) {
            clause.push_back(C.eq(q, 1));
            c.add_axiom("~ovfl*(p,q) & p*q = 1 => p = 1", clause, true);
            clause.pop_back();
        }
        return true;
    }

    // ~ovfl*(p,q) & p*q = 0 => p = 0 or q = 0
    bool monomials::non_overflow_zero(monomial const& mon) {
        if (mon.val != 0)
            return false;
        for (auto const& val : mon.arg_vals)
            if (val == 0)
                return false;
        rational product(1);
        for (auto const& val : mon.arg_vals)
            product *= val;
        if (product > mon.var.manager().max_value())
            return false;
        constraint_or_dependency_vector clause;
        clause.push_back(~C.eq(mon.var));
        pdd p = mon.args[0];
        for (unsigned i = 1; i < mon.args.size(); ++i) {
            clause.push_back(C.umul_ovfl(p, mon.args[i]));
            p *= mon.args[i];
        }
        for (auto const& q : mon.args)
            clause.push_back(C.eq(q));
        
        c.add_axiom("~ovfl*(p,q) & p*q = 0 => p = 0 or q = 0", clause, true);
        return false;
    }

    // parity(p*q) > 0 => parity(p) > 0 or parity(q) > 0
    bool monomials::parity0(monomial const& mon) {
        if (mon.val.is_odd())
            return false;
        if (!all_of(mon.arg_vals, [&](auto const& v) { return v.is_odd(); }))
            return false;
        constraint_or_dependency_vector clause;
        clause.push_back(~C.parity_at_least(mon.var, 1));
        for (auto const& p : mon.args) 
            clause.push_back(C.parity_at_least(p, 1));        
        c.add_axiom("parity(p*q) > 0 => parity(p) > 0 or parity(q) > 0", clause, true);
        return true;
    }

    // 0p * 0q >= 2^k => ovfl(p,q), where |p| = |q| = k
    bool monomials::prefix_overflow(monomial const& mon) {
        if (mon.size() != 2)
            return false;
        if (!mon.args[0].is_var())
            return false;
        if (!mon.args[1].is_var())
            return false;
        if (mon.val <= mon.arg_vals[0])
            return false;
        if (mon.val <= mon.arg_vals[1])
            return false;
        auto x = mon.args[0].var();
        auto y = mon.args[1].var();
        offset_slices x_suffixes, y_suffixes;
        bool y_computed = false;
        c.get_bitvector_suffixes(x, x_suffixes);        
        rational x_val, y_val;
        for (auto const& xslice : x_suffixes) {
            if (c.size(xslice.v) == mon.num_bits())
                continue;
            auto const& xmax_value = c.var(xslice.v).manager().max_value();
            if (mon.val <= xmax_value)
                continue;
            if (!c.try_eval(c.var(xslice.v), x_val) || x_val != mon.arg_vals[0])
                continue;
            if (!y_computed)
                c.get_bitvector_suffixes(y, y_suffixes);
            y_computed = true;
            for (auto const& yslice : y_suffixes) {
                if (c.size(yslice.v) != c.size(xslice.v))
                    continue;
                if (!c.try_eval(c.var(yslice.v), y_val) || y_val != mon.arg_vals[1])
                    continue;
                bool added = c.add_axiom("0p * 0q >= 2^k => ovfl(p,q), where |p| = |q| = k",
                    { dependency({x, xslice}), dependency({y, yslice}),
                     ~C.ule(mon.args[0], xmax_value),
                     ~C.ule(mon.args[1], xmax_value),
                     ~C.ugt(mon.var, xmax_value), 
                      C.umul_ovfl(c.var(xslice.v), c.var(yslice.v)) }, 
                    true);
                if (added)
                    return true;
            }
        }       
        return false;
    }

    bool monomials::bit_blast(monomial const& mon) {
        if (mon.size() != 2)
            return false;
        unsigned sz = mon.num_bits();
        pdd n = mon.var.manager().mk_val(0);
        pdd zero = n.manager().mk_val(0);
        pdd p = mon.args[0];
        pdd q = mon.args[1];
        for (unsigned i = 0; i < sz; ++i) 
            n += c.mk_ite(C.bit(p, i), c.value(rational::power_of_two(i), sz) * q, zero);
        c.add_axiom("bit-blast", { C.eq(mon.var, n) }, true);
        return true;
    }

    std::ostream& monomials::display(std::ostream& out) const {
        for (auto const& mon : m_monomials) {
            out << mon.var << " := ";
            char const* sep = "";
            for (auto p : mon.args) 
                if (p.is_var())
                    out << sep << p, sep = " * ";
                else 
                    out << sep << "(" << p << ")", sep = " * ";
            out << "\n";
        }
        return out;
    }
}
