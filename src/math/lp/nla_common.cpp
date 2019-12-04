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
// replaces the fixed vars with scalars
nex * common::nexvar(const rational & coeff, lpvar j, nex_creator& cn, bool fixed_as_scalars) {
    SASSERT(!coeff.is_zero());
    if (!c().is_monic_var(j)) {
        if (fixed_as_scalars && c().var_is_fixed(j)) {
            auto & b = c().m_lar_solver.get_lower_bound(j).x;
            if (b.is_zero())
                return nullptr;
            return cn.mk_scalar(coeff * b);
        } 
        c().insert_to_active_var_set(j);
        return cn.mk_mul(cn.mk_scalar(coeff), cn.mk_var(j));
    }
    const monic& m = c().emons()[j];
    nex_mul * e = cn.mk_mul(cn.mk_scalar(coeff));
    for (lpvar k : m.vars()) {
        if (fixed_as_scalars && c().var_is_fixed(k)) {
            auto & b = c().m_lar_solver.get_lower_bound(k).x;
            if (b.is_zero()) {
                TRACE("nla_grobner", tout << "[" << k << "] is fixed to zero\n";); 
                return nullptr;
            }
            e->coeff() *=  b;
            continue;
        }  
        c().insert_to_active_var_set(k);
        e->add_child(cn.mk_var(k));
        CTRACE("nla_horner", c().is_monic_var(k), c().print_var(k, tout) << "\n";);
    }
    TRACE("nla_cn", tout << *e;);
    return e;
}


template <typename T> void common::create_sum_from_row(const T& row,
                                                       nex_creator& cn,
                                                       nex_sum& sum, bool fixed_as_scalars) {

    TRACE("nla_horner", tout << "row="; m_core->print_term(row, tout) << "\n";);

    SASSERT(row.size() > 1);
    sum.children().clear();
    for (const auto &p : row) {
        nex* e = nexvar(p.coeff(), p.var(), cn, fixed_as_scalars);
        if (e)
            sum.add_child(e);        
    }
    TRACE("nla_horner", tout << "sum =" << sum << "\n";);
}

template <typename T>
common::ci_dependency* common::get_fixed_vars_dep_from_row(const T& row, ci_dependency_manager& dep_manager) {
    TRACE("nla_horner", tout << "row="; m_core->print_term(row, tout) << "\n";);
    ci_dependency* dep = nullptr;
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

void common::set_active_vars_weights() {
    m_nex_creator.set_number_of_vars(c().m_lar_solver.column_count());
    for (lpvar j : c().active_var_set()) {
        m_nex_creator.set_var_weight(j, static_cast<unsigned>(get_var_weight(j)));
    }
}



var_weight common::get_var_weight(lpvar j) const {
    var_weight k;
    switch (c().m_lar_solver.get_column_type(j)) {
        
    case lp::column_type::fixed:
        k = var_weight::FIXED;
        break;
    case lp::column_type::boxed:
        k = var_weight::BOUNDED;
        break;
    case lp::column_type::lower_bound:
    case lp::column_type::upper_bound:
        k = var_weight::NOT_FREE;
    case lp::column_type::free_column:
        k = var_weight::FREE;
        break;
    default:
        UNREACHABLE();
        break;
    }
    if (c().is_monic_var(j)) {
        return (var_weight)((int)k + 1);
    }
    return k;
}


}
template void nla::common::create_sum_from_row<old_vector<lp::row_cell<rational>, true, unsigned int> >(old_vector<lp::row_cell<rational>, true, unsigned int> const&, nla::nex_creator&, nla::nex_sum&, bool);  

template dependency_manager<nla::common::ci_dependency_config>::dependency* nla::common::get_fixed_vars_dep_from_row<old_vector<lp::row_cell<rational>, true, unsigned int> >(old_vector<lp::row_cell<rational>, true, unsigned int> const&, dependency_manager<nla::common::ci_dependency_config>&);
