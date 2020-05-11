/*++
  Copyright (c) 2017 Microsoft Corporation


  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/
#include "math/lp/nla_common.h"
#include "math/lp/nla_core.h"

namespace nla {
bool common::done() const { return c().done(); }


template <typename T> rational common::val(T const& t) const { return c().val(t); }
template rational common::val<factor>(factor const& t) const;
rational common::val(lpvar t) const { return c().val(t); }
rational common::var_val(monic const& m) const { return c().var_val(m); }
rational common::mul_val(monic const& m) const { return c().mul_val(m); }

template <typename T> lpvar common::var(T const& t) const { return c().var(t); }
template lpvar common::var<factor>(factor const& t) const;
template lpvar common::var<monic>(monic const& t) const;
template <typename T> bool common::canonize_sign(const T& t) const {
    return c().canonize_sign(t);
}

template bool common::canonize_sign<monic>(const monic&) const;
template bool common::canonize_sign<factor>(const factor&) const;
template bool common::canonize_sign<lpvar>(const lpvar&) const;
template bool common::canonize_sign<factorization>(const factorization&) const;


template <typename T>
std::ostream& common::print_product(const T & m, std::ostream& out) const {
    return c().print_product(m, out);
}
template 
std::ostream& common::print_product<unsigned_vector>(const unsigned_vector & m, std::ostream& out) const;

std::ostream& common::print_monic(const monic & m, std::ostream& out) const {
    return c().print_monic(m, out);
}

std::ostream& common::print_factor(const factor & f, std::ostream& out) const {
    return c().print_factor(f, out);
}

std::ostream& common::print_var(lpvar j, std::ostream& out) const {
    return c().print_var(j, out);
}

bool common::check_monic(const monic& m) const {
    return c().check_monic(m);
}

unsigned common::random() {
    return c().random();
}

void common::add_deps_of_fixed(lpvar j, u_dependency*& dep) {
    unsigned lc, uc;
    auto& dep_manager = c().m_intervals.get_dep_intervals().dep_manager();
    c().m_lar_solver.get_bound_constraint_witnesses_for_column(j, lc, uc);
    dep = dep_manager.mk_join(dep, dep_manager.mk_leaf(lc));
    dep = dep_manager.mk_join(dep, dep_manager.mk_leaf(uc));                    
}


// creates a nex expression for the coeff and var, 
nex * common::nexvar(const rational & coeff, lpvar j, nex_creator& cn, u_dependency*& dep) {
    SASSERT(!coeff.is_zero());
    if (c().m_nla_settings.horner_subs_fixed() == 1 && c().var_is_fixed(j)) {
        add_deps_of_fixed(j, dep);
        return cn.mk_scalar(coeff * c().m_lar_solver.column_lower_bound(j).x);
    }
    if (c().m_nla_settings.horner_subs_fixed() == 2 && c().var_is_fixed_to_zero(j)) {
        add_deps_of_fixed(j, dep);
        return cn.mk_scalar(rational(0));
    }
    
    if (!c().is_monic_var(j)) {
        c().insert_to_active_var_set(j);
        return cn.mk_mul(cn.mk_scalar(coeff), cn.mk_var(j));
    }
    const monic& m = c().emons()[j];
    nex_creator::mul_factory mf(cn);
    mf *= coeff;
    u_dependency * initial_dep = dep;
    for (lpvar k : m.vars()) {
        if (c().m_nla_settings.horner_subs_fixed() && c().var_is_fixed(k)) {
            add_deps_of_fixed(k, dep);
            mf *= c().m_lar_solver.column_lower_bound(k).x;
        } else if (c().m_nla_settings.horner_subs_fixed() == 2 &&
                   c().var_is_fixed_to_zero(k)) {
            dep = initial_dep;
            add_deps_of_fixed(k, dep);
            return cn.mk_scalar(rational(0));
        }
        else {
            c().insert_to_active_var_set(k);
            mf *= cn.mk_var(k);
            CTRACE("nla_grobner", c().is_monic_var(k), c().print_var(k, tout) << "\n";);
        }
    }
    nex* e = mf.mk();
    TRACE("nla_grobner", tout << *e;);
    return e;
}


template <typename T> void common::create_sum_from_row(const T& row,
                                                       nex_creator& cn,
                                                       nex_creator::sum_factory& sum,
                                                       u_dependency*& dep) {

    TRACE("nla_horner", tout << "row="; m_core.print_row(row, tout) << "\n";);
    SASSERT(row.size() > 1);
    sum.reset();
    for (const auto &p : row) {
        nex* e = nexvar(p.coeff(), p.var(), cn, dep);
        if (!e)
            continue;
        sum += e;
    }
}



}
template void nla::common::create_sum_from_row<vector<lp::row_cell<rational>, true, unsigned int> >(vector<lp::row_cell<rational>, true, unsigned int> const&, nla::nex_creator&, nla::nex_creator::sum_factory&, u_dependency*&);  
