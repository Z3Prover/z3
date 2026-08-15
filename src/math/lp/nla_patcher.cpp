/*++
  Copyright (c) 2026 Microsoft Corporation

  Module Name:

  nla_patcher.cpp

  Author:
    Lev Nachmanson (levnach)

  --*/
#include "math/lp/nla_patcher.h"
#include "math/lp/nla_core.h"

namespace nla {

bool patcher::var_breaks_correct_monic_as_factor(lpvar j, const monic& m) const {
    if (!val(var(m)).is_zero())
        return true;

    if (!val(j).is_zero()) // j was not zero: the new value does not matter - m must have another zero factor
        return false;
    // do we have another zero in m?
    for (lpvar k : m) {
        if (k != j && val(k).is_zero()) {
            return false; // not breaking
        }
    }
    // j was the only zero in m
    return true;
}

bool patcher::var_breaks_correct_monic(lpvar j) const {
    if (c().is_monic_var(j) && !c().to_refine().contains(j)) {
        TRACE(nla_solver, tout << "j = " << j << ", m  = "; c().print_monic(c().emon(j), tout) << "\n";);
        return true; // changing the value of a correct monic
    }

    for (const monic & m : c().emons().get_use_list(j)) {
        if (c().to_refine().contains(m.var()))
            continue;
        if (var_breaks_correct_monic_as_factor(j, m))
            return true;
    }

    return false;
}

void patcher::update_to_refine_of_var(lpvar j) {
    for (const monic & m : c().emons().get_use_list(j)) {
        if (var_val(m) == mul_val(m))
            c().erase_from_to_refine(var(m));
        else
            c().insert_to_refine(var(m));
    }
    if (c().is_monic_var(j)) {
        const monic& m = c().emon(j);
        if (var_val(m) == mul_val(m))
            c().erase_from_to_refine(j);
        else
            c().insert_to_refine(j);
    }
}

// returns true if the patching is blocking
bool patcher::is_patch_blocked(lpvar u, const lp::impq& ival) const {
    TRACE(nla_solver, tout << "u = " << u << '\n';);
    if (m_cautious_patching &&
        (!c().lra.inside_bounds(u, ival) || (c().var_is_int(u) && ival.is_int() == false))) {
        TRACE(nla_solver, tout << "u = " << u << " blocked, for feas or integr\n";);
        return true; // block
    }

    if (u == m_patched_var) {
        TRACE(nla_solver, tout << "u == m_patched_var, no block\n";);

        return false; // do not block
    }
    // we can change only one variable in variables of m_patched_var
    if (m_patched_monic->contains_var(u) || u == var(*m_patched_monic)) {
        TRACE(nla_solver, tout << "u = " << u << " blocked as contained\n";);
        return true; // block
    }

    if (var_breaks_correct_monic(u)) {
        TRACE(nla_solver, tout << "u = " << u << " blocked as used in a correct monomial\n";);
        return true;
    }

    TRACE(nla_solver, tout << "u = " << u << ", m_patched_m  = "; c().print_monic(*m_patched_monic, tout) <<
          ", not blocked\n";);

    return false;
}

// it tries to patch m_patched_var
bool patcher::try_to_patch(const rational& v) {
    auto is_blocked = [this](lpvar u, const lp::impq& iv)  { return is_patch_blocked(u, iv); };
    auto change_report = [this](lpvar u) { update_to_refine_of_var(u); };
    return c().lra.try_to_patch(m_patched_var, v, is_blocked, change_report);
}

static bool in_power(const svector<lpvar>& vs, unsigned l) {
    unsigned k = vs[l];
    return (l != 0 && vs[l - 1] == k) || (l + 1 < vs.size() && k == vs[l + 1]);
}

bool patcher::to_refine_is_correct() const {
    for (unsigned j = 0; j < c().lra.number_of_vars(); ++j) {
        if (!c().is_monic_var(j)) continue;
        bool valid = check_monic(c().emon(j));
        if (valid == c().to_refine().contains(j)) {
            TRACE(nla_solver, tout << "inconstency in m_to_refine : ";
                  c().print_monic(c().emon(j), tout) << "\n";
                  if (valid) tout << "should NOT be in to_refine\n";
                  else tout << "should be in to_refine\n";);
            return false;
        }
    }
    return true;
}

void patcher::patch_monomial(lpvar j) {
    m_patched_monic =& (c().emon(j));
    m_patched_var = j;
    TRACE(nla_solver, tout << "m = "; c().print_monic(*m_patched_monic, tout) << "\n";);
    rational v = mul_val(*m_patched_monic);
    if (val(j) == v) {
        c().erase_from_to_refine(j);
        return;
    }
    if (!var_breaks_correct_monic(j) && try_to_patch(v)) {
        SASSERT(to_refine_is_correct());
        return;
    }

    // We could not patch j, now we try patching the factor variables.
    TRACE(nla_solver, tout << " trying squares\n";);
    // handle perfect squares
    if ((*m_patched_monic).vars().size() == 2 && (*m_patched_monic).vars()[0] == (*m_patched_monic).vars()[1]) {
        rational root;
        if (v.is_perfect_square(root)) {
            m_patched_var = (*m_patched_monic).vars()[0];
            if (!var_breaks_correct_monic(m_patched_var) && (try_to_patch(root) || try_to_patch(-root))) {
                TRACE(nla_solver, tout << "patched square\n";);
                return;
            }
        }
        TRACE(nla_solver, tout << " cannot patch\n";);
        return;
    }

    // We have v != abc, but we need to have v = abc.
    // If we patch b then b should be equal to v/ac = v/(abc/b) = b(v/abc)
    if (!v.is_zero()) {
        rational r = val(j) / v;
        SASSERT((*m_patched_monic).is_sorted());
        TRACE(nla_solver, tout << "r = " << r << ", v = " << v << "\n";);
        for (unsigned l = 0; l < (*m_patched_monic).size(); ++l) {
            m_patched_var = (*m_patched_monic).vars()[l];
            if (!in_power((*m_patched_monic).vars(), l) &&
                !var_breaks_correct_monic(m_patched_var) &&
                try_to_patch(r * val(m_patched_var))) { // r * val(k) gives the right value of k
                TRACE(nla_solver, tout << "patched  " << m_patched_var << "\n";);
                SASSERT(mul_val((*m_patched_monic)) == val(j));
                c().erase_from_to_refine(j);
                break;
            }
        }
    }
}

void patcher::patch_monomials_on_to_refine() {
    // the rest of the function might change m_to_refine, so have to copy
    unsigned_vector to_refine;
    for (unsigned j : c().to_refine())
        to_refine.push_back(j);

    unsigned sz = to_refine.size();

    unsigned start = random();
    for (unsigned i = 0; i < sz && !c().to_refine().empty(); ++i)
        patch_monomial(to_refine[(start + i) % sz]);

    TRACE(nla_solver, tout << "sz = " << sz << ", m_to_refine = " << c().to_refine().size() <<
          (sz > c().to_refine().size()? " less" : " same" ) << "\n";);
}

void patcher::patch_monomials() {
    m_cautious_patching = true;
    patch_monomials_on_to_refine();
}

}
