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
#include <vector>

namespace nla {

nex * nex_creator::mk_div(const nex* a, lpvar j) {
    SASSERT(is_simplified(a));
    SASSERT((a->is_mul() && a->contains(j)) || (a->is_var() && to_var(a)->var() == j));
    if (a->is_var())
        return mk_scalar(rational(1));
    vector<nex_pow> bv; 
    bool seenj = false;
    for (auto& p : to_mul(a)->children()) {
        const nex * c = p.e();
        int pow = p.pow();
        if (!seenj && c->contains(j)) {
            if (!c->is_var()) {                    
                bv.push_back(nex_pow(mk_div(c, j)));
                if (pow != 1) {
                    bv.push_back(nex_pow(clone(c), pow - 1)); 
                }
            } else {
                SASSERT(to_var(c)->var() == j);
                if (p.pow() != 1) {
                    bv.push_back(nex_pow(mk_var(j), pow - 1));
                }
            }
            seenj = true;
        } else {
            bv.push_back(nex_pow(clone(c), pow));
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

bool nex_creator::eat_scalar_pow(nex_scalar *& r, nex_pow& p, unsigned pow) {
    if (!p.e()->is_scalar())
        return false;
    nex_scalar *pe = to_scalar(p.e());
    if (r == nullptr) {
        r = pe;
        r->value() = r->value().expt(p.pow()*pow);                
    } else {
        r->value() *= pe->value().expt(p.pow()*pow);
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
        if (eat_scalar_pow(r, p, 1)) {
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
        TRACE("nla_cn_details", tout << p << "\n";);
        for (nex_pow& pp : to_mul(p.e())->children()) {
            TRACE("nla_cn_details", tout << pp << "\n";);
            if (!eat_scalar_pow(r, pp, p.pow()))
                children.push_back(nex_pow(pp.e(), pp.pow() * p.pow()));            
        }
    }

    if (r != nullptr) {
        children.push_back(nex_pow(r));
    }
        
    mul_to_powers(children);
    
    TRACE("nla_cn_details", print_vector(children, tout););    
}

bool nex_creator::less_than_on_mul(const nex_mul* a, const nex_mul* b) const {
    // the scalar, if it is there, is at the beginning of the children()
    TRACE("nla_cn_details", tout << "a = " << *a << ", b = " << *b << "\n";);
    SASSERT(is_simplified(a));
    SASSERT(is_simplified(b));
    unsigned a_deg = a->get_degree();
    unsigned b_deg = b->get_degree();
    if (a_deg > b_deg)
        return true;
    if (a_deg < b_deg)
        return false;
    auto it_a  = a->children().begin();
    auto it_b  = b->children().begin();
    auto a_end = a->children().end();
    auto b_end = b->children().end();
    unsigned a_pow, b_pow;
    bool inside_a_p = false; // inside_a_p is true means we still compare the old position of it_a
    bool inside_b_p = false; // inside_b_p is true means we still compare the old position of it_b
    const nex* ae = nullptr;
    const nex *be = nullptr;
    if (it_a == a_end) {
        return it_b != b_end;
    }
    if (it_b == b_end)
        return false;
    for (; ;) {
        if (!inside_a_p) {
            ae = it_a->e();
            a_pow = it_a->pow();
        }
        if (!inside_b_p) {
            be = it_b->e();
            b_pow = it_b->pow();
        }

        if (lt(ae, be))
            return true;
        if (lt(be, ae))
            return false;
        if (a_pow == b_pow) {
            inside_a_p = inside_b_p = false;
            it_a++; it_b++;
            if (it_a == a_end) {
                return it_b != b_end;
            } else if (it_b == b_end) {
                return true;                
            }
            // no iterator reached the end
            continue;
        }
        if (a_pow < b_pow) {
            it_a++;
            if (it_a == a_end)
                return true;
            inside_a_p = false;
            inside_b_p = true;
            b_pow -= a_pow;
        } else {
            SASSERT(a_pow > b_pow);
            a_pow -= b_pow;
            it_b++;
            if (it_b == b_end)
                return false;
            inside_a_p = true;
            inside_b_p = false;
        }
    }
    return false;

}


bool nex_creator::less_than_on_var_nex(const nex_var* a, const nex* b) const {
    switch(b->type()) {
    case expr_type::SCALAR: return false;
    case expr_type::VAR:            
        return less_than(a->var() , to_var(b)->var());
    case expr_type::MUL:
        {
            if (b->get_degree() > 1)
                return true;
            auto it = to_mul(b)->children().begin();
            const nex_pow & c  = *it;
            const nex * f = c.e();
            return less_than_on_var_nex(a, f);
        }
            
    case expr_type::SUM:
        {
            nex_sum m;
            m.add_child(const_cast<nex_var*>(a));
            return lt(&m, to_sum(b));
        }
    default:
        UNREACHABLE();
        return false;
    }
}


bool nex_creator::less_than_on_mul_nex(const nex_mul* a, const nex* b) const {
    switch(b->type()) {
    case expr_type::SCALAR: return false;
    case expr_type::VAR:            
        {
            if (a->get_degree() > 1)
                return false;
            auto it = a->children().begin();
            const nex_pow & c  = *it;
            const nex * f = c.e();
            return lt(f, a);
        }
    case expr_type::MUL:
        return less_than_on_mul(a, to_mul(b));            
    case expr_type::SUM:
        {
            const nex* fc = *(to_sum(b)->children().begin());
            return lt(a, fc);
        }
    default:
        UNREACHABLE();
        return false;
    }    
}

bool nex_creator::lt(const nex* a, const nex* b) const {
    bool ret;
    switch (a->type()) {
    case expr_type::VAR: 
        ret = less_than_on_var_nex(to_var(a), b);
        break;
    case expr_type::SCALAR: {
        if (b->is_scalar())
            ret = to_scalar(a)->value() < to_scalar(b)->value();
        else
            ret = true; // the scalars are the smallest
        break;
    }        
    case expr_type::MUL: {
        ret = less_than_on_mul_nex(to_mul(a), b);
        break;
    }
    case expr_type::SUM: {
        UNREACHABLE();
        return false;
    }
    default:
        UNREACHABLE();
        return false;
    }

    TRACE("nla_cn_details_", tout << *a << (ret?" < ":" >= ") << *b << "\n";);
    
    return ret;

}

bool nex_creator::is_sorted(const nex_mul* e) const {
    for (unsigned j = 0; j < e->children().size() - 1; j++) {
        if (!(less_than_on_nex_pow(e->children()[j], e->children()[j+1])))
            return false;
    }
    return true;
}

 


bool nex_creator::mul_is_simplified(const nex_mul* e) const {
    if (e->size() == 1 && e->children().begin()->pow() == 1)
        return false;
    std::set<const nex*, nex_lt> s([this](const nex* a, const nex* b) {return lt(a, b); });
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
    if (e->size() == 1 && e->children()[0].pow() == 1) 
        return e->children()[0].e();
    TRACE("nla_cn_details", tout << *e << "\n";);
    SASSERT(is_simplified(e));
    return e;
}

nex* nex_creator::simplify_sum(nex_sum *e) {
    TRACE("nla_cn_details", tout << "was e = " << *e << "\n";);
    simplify_children_of_sum(e->children());
    nex *r = e->size() == 1? e->children()[0]: e;
    TRACE("nla_cn_details", tout << "became r = " << *r << "\n";);    
    return r;
}

bool nex_creator::sum_is_simplified(const nex_sum* e) const {
    TRACE("nla_cn_details",  tout << ++ lp::lp_settings::ddd << std::endl;);
    
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
    std::map<nex*, int, nex_lt> m([this](const nex* a, const nex* b) {return lt(a, b); });

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
    TRACE("nla_cn_details", tout << *e << ", coeff = " << coeff << "\n";);
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
        return mk_scalar(coeff);
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
// returns true if the key exists already
bool nex_creator::register_in_join_map(std::map<nex*, rational, nex_lt>& map, nex* e, const rational& r) const{
    TRACE("nla_cn_details",  tout << *e << ", r = " << r << std::endl;);
    auto map_it = map.find(e);
    if (map_it == map.end()) {
        map[e] = r;
        return false;
    } else {
        map_it->second += r;
        return true;
    }
}

// returns true if a simplificatian happens
bool nex_creator::process_mul_in_simplify_sum(nex_mul* em, std::map<nex*, rational, nex_lt> &map) {
    bool found = false;
    auto it = em->children().begin();
    if (it->e()->is_scalar()) {
        SASSERT(it->pow() == 1);
        rational r = to_scalar(it->e())->value();              
        auto end = em->children().end();
        if (em->children().size() == 2 && em->children()[1].pow() == 1) {
            found = register_in_join_map(map, em->children()[1].e(), r);
        } else {
            nex_mul * m = new nex_mul();
            for (it++; it != end; it++) {
                m->add_child_in_power(it->e(), it->pow());
            }
            found = register_in_join_map(map, m, r);
        } 
    } else {
        found = register_in_join_map(map, em, rational(1));
    }
    return found;
}

    // a + 3bc + 2bc => a + 5bc 
void nex_creator::sort_join_sum(ptr_vector<nex> & children) {
    TRACE("nla_cn_details", print_vector_of_ptrs(children, tout););
    std::map<nex*, rational, nex_lt> map([this](const nex *a , const nex *b)
                                       { return lt(a, b); });
    std::unordered_set<nex*> existing_nex; // handling (nex*) as numbers
    nex_scalar * common_scalar = nullptr;
    bool simplified = false;
    for (auto e : children) {
        if (e->is_scalar()) {
            nex_scalar * es = to_scalar(e);
            if (common_scalar == nullptr) {
                common_scalar = es;
            } else {
                simplified = true;
                common_scalar->value() += es->value();
            }
            continue;
        }
        existing_nex.insert(e);
        if (e->is_mul()) {
            simplified |= process_mul_in_simplify_sum(to_mul(e), map);
        } else {
            SASSERT(e->is_var());
            simplified |= register_in_join_map(map, e, rational(1));
        }
    }

    if (!simplified)
        return;

    TRACE("nla_cn_details", for (auto & p : map ) { tout << "(" << *p.first << ", " << p.second << ") ";});
    children.clear();
    if (common_scalar) {
        children.push_back(common_scalar);
    }
    for (auto& p : map) {
        nex *e = p.first;
        const rational & coeff = p.second;
        if (coeff.is_zero())
            continue;
        bool e_is_old = existing_nex.find(e) != existing_nex.end();
        if (e_is_old) {
            if (coeff.is_one()) {
                children.push_back(e);
            } else {
                if (e->is_var()) {
                    children.push_back(mk_mul(mk_scalar(coeff), e));
                } else {
                    SASSERT(e->is_mul());
                    nex* first = to_mul(e)->children()[0].e();
                    if (first->is_scalar()) {
                        to_scalar(first)->value() = coeff;
                        children.push_back(e);
                    } else {
                        e = simplify(mk_mul(mk_scalar(coeff), e));
                        children.push_back(e);
                    }
                }
            }                
        } else { // e is new
            if (coeff.is_one()) {
                m_allocated.push_back(e);
                children.push_back(e);
            } else {
                children.push_back(simplify(mk_mul(mk_scalar(coeff), e)));
            }
        }
    }
}

bool is_zero_scalar(nex *e) {
    return e->is_scalar() && to_scalar(e)->value().is_zero();
}

void nex_creator::simplify_children_of_sum(ptr_vector<nex> & children) {
    TRACE("nla_cn_details", print_vector_of_ptrs(children, tout););
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
    
    TRACE("nla_cn_details", print_vector_of_ptrs(children, tout););
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

nex* nex_creator::simplify(nex* e) {
    nex* es;
    TRACE("nla_cn_details", tout << *e << std::endl;);
    if (e->is_mul())
        es =  simplify_mul(to_mul(e));
    else if (e->is_sum())
        es =  simplify_sum(to_sum(e));
    else
        es = e;
    TRACE("nla_cn_details", tout << "simplified = " << *es << std::endl;);
    SASSERT(is_simplified(es));
    return es;
}

bool nex_creator::is_simplified(const nex *e) const 
{
    if (e->is_mul())
        return mul_is_simplified(to_mul(e));
    if (e->is_sum())
        return sum_is_simplified(to_sum(e));
    return true;
}
}
