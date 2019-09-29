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
#include "math/lp/nex_creator.h"
#include <map>
namespace nla {
nex * nex_creator::mk_div(const nex* a, lpvar j) {
    SASSERT(is_simplified(a));
    TRACE("nla_cn_details", tout << "a=" << *a << ", v" << j << "\n";);
    SASSERT((a->is_mul() && a->contains(j)) || (a->is_var() && to_var(a)->var() == j));
    if (a->is_var())
        return mk_scalar(rational(1));
    vector<nex_pow> bv; 
    bool seenj = false;
    for (auto& p : to_mul(a)->children()) {
        const nex * c = p.e();
        int pow = p.pow();
        if (!seenj) {
            if (c->contains(j)) {
                if (!c->is_var()) {                    
                    bv.push_back(nex_pow(mk_div(c, j)));
                    if (pow != 1) {
                        bv.push_back(nex_pow(clone(c), pow)); 
                    }
                } else {
                    SASSERT(to_var(c)->var() == j);
                    if (p.pow() != 1) {
                        bv.push_back(nex_pow(mk_var(j), pow - 1));
                    }
                }
                seenj = true;
            } 
        } else {
            bv.push_back(nex_pow(clone(c)));
        }
    }
    if (bv.size() > 1) { 
        return mk_mul(bv);
    }
    if (bv.size() == 1 && bv.begin()->pow() == 1) {
        return bv.begin()->e();
    }
    if (bv.size() == 0)
        return mk_scalar(rational(1));
    return mk_mul(bv);
}

bool nex_creator::eat_scalar_pow(nex_scalar *& r, nex_pow& p) {
    if (!p.e()->is_scalar())
        return false;
    nex_scalar *pe = to_scalar(p.e());
    if (r == nullptr) {
        r = pe;
        r->value() = r->value().expt(p.pow());                
    } else {
        r->value() *= pe->value().expt(p.pow());
    }
    return true;
}


void nex_creator::simplify_children_of_mul(vector<nex_pow> & children) {
    nex_scalar* r = nullptr;
    TRACE("nla_cn_details", print_vector(children, tout););
    vector<nex_pow> to_promote;
    int skipped = 0;
    for(unsigned j = 0; j < children.size(); j++) {        
        nex_pow& p = children[j];
        if (eat_scalar_pow(r, p)) {
            skipped++;
            continue;
        }
        
        p.e() = simplify(p.e());
        if ((p.e())->is_mul()) {
            to_promote.push_back(p);
        } else {
            unsigned offset = to_promote.size() + skipped;
            if (offset) {
                children[j - offset] = p;
            }
        }
    }
    
    children.shrink(children.size() - to_promote.size() - skipped);

    for (nex_pow & p : to_promote) {
        for (nex_pow& pp : to_mul(p.e())->children()) {
            if (!eat_scalar_pow(r, pp))
                children.push_back(nex_pow(pp.e(), pp.pow() * p.pow()));            
        }
    }

    if (r != nullptr) {
        children.push_back(nex_pow(r));
    }
        
    mul_to_powers(children);
    
    TRACE("nla_cn_details", print_vector(children, tout););    
}

bool nex_creator::mul_simplify_lt(const nex_mul* a, const nex_mul* b) {
    NOT_IMPLEMENTED_YET();
}


bool nex_creator::sum_simplify_lt(const nex* a, const nex* b) {
    int r = (int)(a->type()) - (int)(b->type());
    if (r) {
        return r < 0;
    }
    SASSERT(a->type() == b->type());
    switch (a->type()) {
    case expr_type::VAR: {
        return less_than(to_var(a)->var() , to_var(b)->var());
    }
    case expr_type::SCALAR: {
        return to_scalar(a)->value() < to_scalar(b)->value();
    }        
    case expr_type::MUL: {
        return mul_simplify_lt(to_mul(a), to_mul(b));
    }
    case expr_type::SUM: {
        UNREACHABLE();
        return false;
    }
    default:
        SASSERT(false);
        return false;
    }

    return false;

}

bool nex_creator::is_sorted(const nex_mul* e) const {
    for (unsigned j = 0; j < e->children().size() - 1; j++) {
        if (!(less_than_on_nex_pow(e->children()[j], e->children()[j+1])))
            return false;
    }
    return true;
}

bool nex_creator::less_than_nex(const nex* a, const nex* b) const {
    int r = (int)(a->type()) - (int)(b->type());
    if (r) {
        return r < 0;
    }
    SASSERT(a->type() == b->type());
    switch (a->type()) {
    case expr_type::VAR: {
        return less_than(to_var(a)->var() , to_var(b)->var());
    }
    case expr_type::SCALAR: {
        return to_scalar(a)->value() < to_scalar(b)->value();
    }        
    case expr_type::MUL: {
        NOT_IMPLEMENTED_YET();
        return false; // to_mul(a)->children() < to_mul(b)->children();
    }
    case expr_type::SUM: {
        NOT_IMPLEMENTED_YET();
        return false; //to_sum(a)->children() < to_sum(b)->children();
    }
    default:
        SASSERT(false);
        return false;
    }

    return false;
}


bool nex_creator::mul_is_simplified(const nex_mul* e) const {
    if (size() == 1 && e->children().begin()->pow() == 1)
        return false;
    std::set<const nex*, nex_lt> s([this](const nex* a, const nex* b) {return less_than_nex(a, b); });
    for (const auto &p : e->children()) {
        const nex* ee = p.e();
        if (p.pow() == 0)
            return false;
        if (ee->is_mul()) 
            return false;
        if (ee->is_scalar() && to_scalar(ee)->value().is_one())
            return false;

        auto it = s.find(ee);
        if (it == s.end()) {
            s.insert(ee);
        } else {
            TRACE("nla_cn_details", tout << "not simplified " << *ee << "\n";);
            return false;
        }
    }
    return is_sorted(e);
}

nex * nex_creator::simplify_mul(nex_mul *e) {
    TRACE("nla_cn_details", tout << *e << "\n";);
    simplify_children_of_mul(e->children());
    if (size() == 1 && e->children()[0].pow() == 1) 
        return e->children()[0].e();
    TRACE("nla_cn_details", tout << *e << "\n";);
    SASSERT(is_simplified(e));
    return e;
}

nex* nex_creator::simplify_sum(nex_sum *e) {
    simplify_children_of_sum(e->children());
    if (e->size() == 1)
        return e->children()[0];
    return e;
}

bool nex_creator::sum_is_simplified(nex_sum* e) const {
    if (e->size() < 2) return false;
    for (nex * ee : e->children()) {
        if (ee->is_sum())
            return false;
        if (ee->is_scalar() && to_scalar(ee)->value().is_zero())
            return false;
    }
    return true;
}

void nex_creator::mul_to_powers(vector<nex_pow>& children) {
    std::map<nex*, int, nex_lt> m([this](const nex* a, const nex* b) {return less_than_nex(a, b); });

    for (auto & p : children) {
        auto it = m.find(p.e());
        if (it == m.end()) {
            m[p.e()] = p.pow();
        } else {
            it->second+= p.pow();
        }
    }
    children.clear();
    for (auto & p : m) {
        children.push_back(nex_pow(p.first, p.second));
    }

    std::sort(children.begin(), children.end(), [this](const nex_pow& a, const nex_pow& b) {
                                                    return less_than_on_nex_pow(a, b);
                                                });
}

nex* nex_creator::create_child_from_nex_and_coeff(nex *e,
                                     const rational& coeff) {
    if (coeff.is_one())
        return e;
    SASSERT(is_simplified(e));
        switch (e->type()) {
        case expr_type::VAR: {
            if (coeff.is_one())
                return e;
            return mk_mul(mk_scalar(coeff), e);
        }
        case expr_type::SCALAR: {
            UNREACHABLE();
            return nullptr;
        }        
        case expr_type::MUL: {
            nex_mul * em = to_mul(e);
            nex_pow *np = em->children().begin();
            if (np->e()->is_scalar()) {
                SASSERT(np->pow() == 1);
                to_scalar(np->e())->value() = coeff;
                return e;
            }
            em->add_child(mk_scalar(coeff));
            std::sort(em->children().begin(), em->children().end(), [this](const nex_pow& a,
                                                                           const nex_pow& b) {return less_than_on_nex_pow(a, b);});
            return em;
        }
        case expr_type::SUM: {
            return mk_mul(mk_scalar(coeff), e);
        }
        default:
            UNREACHABLE();
            return nullptr;
        }
        
    }

    // a + 3bc + 2bc => a + 5bc 
void nex_creator::sort_join_sum(ptr_vector<nex> & children) {
    std::map<nex*, rational, nex_lt> m([this](const nex *a , const nex *b)
                                       { return sum_simplify_lt(a, b); });
    fill_map_with_children(m, children);
    children.clear();
    for (auto& p : m) {
        children.push_back(create_child_from_nex_and_coeff(p.first, p.second));
    }
}

rational nex_creator::extract_coeff_from_mul(const nex_mul* m) {
    const nex* e = m->children().begin()->e();
    if (e->is_scalar()) {
        SASSERT(m->children().begin()->pow() == 1);
        return to_scalar(e)->value();
    }
    return rational(1);
}

rational nex_creator::extract_coeff(const nex* m) {
    if (!m->is_mul())
        return rational(1);
    return extract_coeff_from_mul(to_mul(m));
}


void nex_creator::fill_map_with_children(std::map<nex*, rational, nex_lt> & m, ptr_vector<nex> & children) {
    nex_scalar * scalar = nullptr;
    TRACE("nla_cn_details", print_vector_of_ptrs(children, tout););
    for (nex* e : children) {
        if (e->is_scalar()) {
            if (scalar == nullptr) {
                scalar = to_scalar(e);
            } else {
                scalar->value() += to_scalar(e)->value(); 
            }
        } else {
            rational r = extract_coeff(e);
            auto it = m.find(e);
            if (it == m.end()) {
                m[e] = r;
            } else {
                it->second += r;
            }
        }
    }
    if (scalar && scalar->value().is_zero() == false) {
        m[scalar] = rational();
    }
    
}

bool is_zero_scalar(nex *e) {
    return e->is_scalar() && to_scalar(e)->value().is_zero();
}

void nex_creator::simplify_children_of_sum(ptr_vector<nex> & children) {
    ptr_vector<nex> to_promote;
    int skipped = 0;
    for(unsigned j = 0; j < children.size(); j++) {
        nex* e = children[j] = simplify(children[j]);
        if (e->is_sum()) {
            to_promote.push_back(e);
        } else if (is_zero_scalar(e)) {
            skipped ++;
            continue;
        } else {
            unsigned offset = to_promote.size() + skipped;
            if (offset) {
                children[j - offset] = e;
            }
        }
    }
    
    children.shrink(children.size() - to_promote.size() - skipped);
    
    for (nex *e : to_promote) {
        for (nex *ee : *(to_sum(e)->children_ptr())) {
            if (!is_zero_scalar(ee))
                children.push_back(ee);            
        }
    }

    sort_join_sum(children);
}

bool all_factors_are_elementary(const nex_mul* a) {
    for (auto & p : a->children())
        if (!p.e()->is_elementary())
            return false;

    return true;
}

bool have_no_scalars(const nex_mul* a) {
    for (auto & p : a->children())
        if (p.e()->is_scalar() && !to_scalar(p.e())->value().is_one())
            return false;

    return true;
}


nex * nex_creator::mk_div_by_mul(const nex* a, const nex_mul* b) {
    if (a->is_sum()) {
        nex_sum * r = mk_sum();
        const nex_sum * m = to_sum(a);
        for (auto e : m->children()) {
            r->add_child(mk_div_by_mul(e, b));
        }
        TRACE("nla_cn_details", tout << *r << "\n";);
        return r;
    }
    if (a->is_var() || (a->is_mul() && to_mul(a)->children().size() == 1)) {
        return mk_scalar(rational(1));
    }
    const nex_mul* am = to_mul(a);
    SASSERT(all_factors_are_elementary(am) && all_factors_are_elementary(b) && have_no_scalars(b));
    b->get_powers_from_mul(m_powers);
    nex_mul* ret = new nex_mul();
    for (auto& p : am->children()) {
        TRACE("nla_cn_details", tout << "p = " << p << "\n";);
        const nex* e = p.e();
        if (!e->is_var()) {
            SASSERT(e->is_scalar());
            ret->add_child_in_power(clone(e), p.pow());
            TRACE("nla_cn_details", tout << "processed scalar\n";);
            continue;
        }
        SASSERT(e->is_var());
        lpvar j = to_var(e)->var();
        auto it = m_powers.find(j);
        if (it == m_powers.end()) {
            ret->add_child_in_power(clone(e), p.pow());
        } else {
            unsigned pw = p.pow();
            SASSERT(pw);
            while (pw--) {
                SASSERT(it->second);
                it->second --;
                if (it->second == 0) {
                    m_powers.erase(it);
                    break;
                }
            }
            if (pw) {
                ret->add_child_in_power(clone(e), pw);
            }
        }
        TRACE("nla_cn_details", tout << *ret << "\n";);            
    }
    SASSERT(m_powers.size() == 0);
    if (ret->children().size() == 0) {
        delete ret;
        TRACE("nla_cn_details", tout << "return 1\n";);
        return mk_scalar(rational(1));
    }
    add_to_allocated(ret);
    TRACE("nla_cn_details", tout << *ret << "\n";);        
    return ret;
}

nex * nex_creator::mk_div(const nex* a, const nex* b) {
    TRACE("nla_cn_details", tout << *a <<" / " << *b << "\n";);
    if (b->is_var()) {
        return mk_div(a, to_var(b)->var());
    }
    return mk_div_by_mul(a, to_mul(b));
}

}
