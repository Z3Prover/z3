/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#include "math/lp/nla_common.h"
#include "math/lp/nla_core.h"

namespace nla {
bool common::done() const { return c().done(); }

template <typename T> void common::explain(const T& t) {
    c().explain(t, c().current_expl());
}
template void common::explain<monic>(const monic& t);
template void common::explain<factor>(const factor& t);
template void common::explain<factorization>(const factorization& t);

void common::explain(lpvar j) { c().explain(j, c().current_expl()); }

template <typename T> rational common::val(T const& t) const { return c().val(t); }
template rational common::val<monic>(monic const& t) const;
template rational common::val<factor>(factor const& t) const;
rational common::val(lpvar t) const { return c().val(t); }
template <typename T> lpvar common::var(T const& t) const { return c().var(t); }
template lpvar common::var<factor>(factor const& t) const;
template lpvar common::var<monic>(monic const& t) const;
void common::add_empty_lemma() { c().add_empty_lemma(); }
template <typename T> bool common::canonize_sign(const T& t) const {
    return c().canonize_sign(t);
}

template bool common::canonize_sign<monic>(const monic&) const;
template bool common::canonize_sign<factor>(const factor&) const;
template bool common::canonize_sign<lpvar>(const lpvar&) const;
template bool common::canonize_sign<factorization>(const factorization&) const;

void common::mk_ineq(lp::lar_term& t, llc cmp, const rational& rs){
    c().mk_ineq(t, cmp, rs);
}
void common::mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs){
    c().mk_ineq(a, j, b, j, cmp, rs);
}

void common::mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs){
    c().mk_ineq(j, b, k, cmp, rs);
}

void common::mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp){
    c().mk_ineq(j, b, k, cmp);
}

void common::mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp) {
    c().mk_ineq(a, j, b, k, cmp);
}

void common::mk_ineq(bool a, lpvar j, bool b, lpvar k, llc cmp) {
    c().mk_ineq(sign_to_rat(a), j, sign_to_rat(b), k, cmp);
}

void common::mk_ineq(const rational& a ,lpvar j, lpvar k, llc cmp, const rational& rs) {
    c().mk_ineq(a, j, k, cmp, rs);
}

void common::mk_ineq(lpvar j, lpvar k, llc cmp, const rational& rs) {
    c().mk_ineq(j, k, cmp, rs);}

void common::mk_ineq(lpvar j, llc cmp, const rational& rs){
    c().mk_ineq(j, cmp, rs);}

void common::mk_ineq(const rational& a, lpvar j, llc cmp, const rational& rs) {
    c().mk_ineq(a, j, cmp, rs);
}
void common::mk_ineq(const rational& a, lpvar j, llc cmp){
    c().mk_ineq(a, j, cmp);
}

void common::mk_ineq(lpvar j, llc cmp){
    c().mk_ineq(j, cmp);
}
std::ostream& common::print_lemma(std::ostream& out) const {
    return c().print_lemma(out);  
}
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

// creates a nex expression for the coeff and var, 
nex * common::nexvar(const rational & coeff, lpvar j, nex_creator& cn) {
    SASSERT(!coeff.is_zero());
    if (c().m_nla_settings.horner_subs_fixed() == 1 && c().var_is_fixed(j)) {
        return cn.mk_scalar(coeff * c().m_lar_solver.column_lower_bound(j).x);
    }
    if (c().m_nla_settings.horner_subs_fixed() == 2 && c().var_is_fixed_to_zero(j)) {
        return cn.mk_scalar(rational(0));
    }
    
    if (!c().is_monic_var(j)) {
        c().insert_to_active_var_set(j);
        return cn.mk_mul(cn.mk_scalar(coeff), cn.mk_var(j));
    }
    const monic& m = c().emons()[j];
    nex_creator::mul_factory mf(cn);
    mf *= coeff;
    for (lpvar k : m.vars()) {
        if (c().m_nla_settings.horner_subs_fixed() && c().var_is_fixed(k)) {
            mf *= c().m_lar_solver.column_lower_bound(k).x;
        } else if (c().m_nla_settings.horner_subs_fixed() == 2 &&
                   c().var_is_fixed_to_zero(k)) {
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
                                                                nex_creator::sum_factory& sum
                                                                ) {

    TRACE("nla_horner", tout << "row="; m_core->print_row(row, tout) << "\n";);
    SASSERT(row.size() > 1);
    sum.reset();
    for (const auto &p : row) {
        nex* e = nexvar(p.coeff(), p.var(), cn);
        if (!e)
            continue;
        sum += e;
    }
}

template <typename T>
u_dependency* common::get_fixed_vars_dep_from_row(const T& row, u_dependency_manager& dep_manager) {
    TRACE("nla_horner", tout << "row="; m_core->print_term(row, tout) << "\n";);
    u_dependency* dep = nullptr;
    for (const auto &p : row) {
        lpvar j = p.var();        
        if (!c().is_monic_var(j)) {
            if (!c().var_is_fixed(j)) {
                continue;
            }
            lp::constraint_index lc,uc;
            c().m_lar_solver.get_bound_constraint_witnesses_for_column(j, lc, uc);
            dep = dep_manager.mk_join(dep, dep_manager.mk_leaf(lc));
            dep = dep_manager.mk_join(dep, dep_manager.mk_leaf(uc));            
        }
        else {
            const monic& m = c().emons()[j];
            for (lpvar k : m.vars()) {
                if (!c().var_is_fixed(k))
                    continue;
                lp::constraint_index lc,uc;
                c().m_lar_solver.get_bound_constraint_witnesses_for_column(k, lc, uc);
                dep = dep_manager.mk_join(dep, dep_manager.mk_leaf(lc));
                dep = dep_manager.mk_join(dep, dep_manager.mk_leaf(uc));
            }
        }
    }
    return dep;
}



}
template void nla::common::create_sum_from_row<old_vector<lp::row_cell<rational>, true, unsigned int> >(old_vector<lp::row_cell<rational>, true, unsigned int> const&, nla::nex_creator&, nla::nex_creator::sum_factory&);  
