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
    for (auto& p : *to_mul(a)) {
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
    if (pe->value().is_one())
        return true; // but do not change r here
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
        for (nex_pow& pp : *to_mul(p.e())) {
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
    auto it_a  = a->begin();
    auto it_b  = b->begin();
    auto a_end = a->end();
    auto b_end = b->end();
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
            auto it = to_mul(b)->begin();
            const nex_pow & c  = *it;
            const nex * f = c.e();
            return less_than_on_var_nex(a, f);
        }
            
    case expr_type::SUM:
        {
            return !lt((*to_sum(b))[0], a);
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
            auto it = a->begin();
            const nex_pow & c  = *it;
            const nex * f = c.e();
            return lt(f, a);
        }
    case expr_type::MUL:
        return less_than_on_mul(a, to_mul(b));            
    case expr_type::SUM:
        return lt(a, (*to_sum(b))[0]);
    default:
        UNREACHABLE();
        return false;
    }    
}

bool nex_creator::less_than_on_sum_sum(const nex_sum* a, const nex_sum* b) const {
    unsigned size = std::min(a->size(), b->size());
    for (unsigned j = 0; j < size; j++) {
        if (lt((*a)[j], (*b)[j]))
            return true;
        if (lt((*b)[j], (*a)[j]))
            return false;
    }
    return size < b->size();
            
}

bool nex_creator::lt(const nex* a, const nex* b) const {
    TRACE("nla_cn_details", tout << *a << " ^ " << *b << "\n";);
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
        if (b->is_sum())
            return less_than_on_sum_sum(to_sum(a), to_sum(b));
        return lt((*to_sum(a))[0], b);
    }
    default:
        UNREACHABLE();
        return false;
    }

    TRACE("nla_cn_details_", tout << *a << (ret?" < ":" >= ") << *b << "\n";);
    
    return ret;

}

bool nex_creator::is_sorted(const nex_mul* e) const {
    for (unsigned j = 0; j < e->size() - 1; j++) {
        if (!(less_than_on_nex_pow((*e)[j], (*e)[j+1]))) {
            TRACE("nla_cn_details", tout << "not sorted e " << * e << "\norder is incorrect " <<
                  (*e)[j] << " >= " << (*e)[j + 1]<< "\n";);

            return false;
        }
    }
    return true;
}

 


bool nex_creator::mul_is_simplified(const nex_mul* e) const {
    TRACE("nla_cn_details", tout <<  "e = " << *e << "\n";);
    if (e->size() == 1 && e->begin()->pow() == 1)
        return false;
    std::set<const nex*, nex_lt> s([this](const nex* a, const nex* b) {return lt(a, b); });
    for (const auto &p : *e) {
        const nex* ee = p.e();
        if (p.pow() == 0) {
            TRACE("nla_cn_details", tout << "not simplified " << *ee << "\n";);
            return false;
        }
        if (ee->is_mul()) {
            TRACE("nla_cn_details", tout << "not simplified " << *ee << "\n";);
            return false;
        }
        if (ee->is_scalar() && to_scalar(ee)->value().is_one()) {
            TRACE("nla_cn_details", tout << "not simplified " << *ee << "\n";);
            return false;
        }

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
    if (e->size() == 1 && (*e)[0].pow() == 1) 
        return (*e)[0].e();
    TRACE("nla_cn_details", tout << *e << "\n";);
    SASSERT(is_simplified(e));
    return e;
}

nex* nex_creator::simplify_sum(nex_sum *e) {
    TRACE("nla_cn_details", tout << "was e = " << *e << "\n";);
    simplify_children_of_sum(e->children());
    nex *r = e->size() == 1? (*e)[0]: e;
    TRACE("nla_cn_details", tout << "became r = " << *r << "\n";);    
    return r;
}

bool nex_creator::sum_is_simplified(const nex_sum* e) const {
    if (e->size() < 2) return false;
    bool scalar = false;
    for (nex * ee : *e) {
        if (ee->is_sum()) {
            TRACE("nla_cn", tout << "not simplified e = " << *e << "\n"
                  << " has a child which is a sum " << *ee << "\n";);
            return false;
        }
        if (ee->is_scalar()) {
            if (scalar) {
                TRACE("nla_cn", tout <<  "not simplified e = " << *e << "\n"
                      << " have more than one scalar " << *ee << "\n";);
                
                return false;
            }
            if (to_scalar(ee)->value().is_zero()) {
                if (scalar) {
                    TRACE("nla_cn", tout << "have a zero scalar " << *ee << "\n";);
                    
                    return false;
                }
                scalar = true;
            }
        }
        if (!is_simplified(ee))
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
        nex_pow *np = em->begin();
        if (np->e()->is_scalar()) {
            SASSERT(np->pow() == 1);
            to_scalar(np->e())->value() = coeff;
            return e;
        }
        em->add_child(mk_scalar(coeff));
        std::sort(em->begin(), em->end(), [this](const nex_pow& a,
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
    auto it = em->begin();
    if (it->e()->is_scalar()) {
        SASSERT(it->pow() == 1);
        rational r = to_scalar(it->e())->value();              
        auto end = em->end();
        if (em->size() == 2 && (*em)[1].pow() == 1) {
            found = register_in_join_map(map, (*em)[1].e(), r);
        } else {
            nex_mul * m = mk_mul();
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

bool nex_creator::fill_join_map_for_sum(ptr_vector<nex> & children,
                           std::map<nex*, rational, nex_lt>& map,
                           std::unordered_set<nex*>& existing_nex,
                           nex_scalar*& common_scalar) {
    
    common_scalar = nullptr;
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
    return simplified;
}
    // a + 3bc + 2bc => a + 5bc 
void nex_creator::sort_join_sum(ptr_vector<nex> & children) {
    TRACE("nla_cn_details", print_vector_of_ptrs(children, tout););
    std::map<nex*, rational, nex_lt> map([this](const nex *a , const nex *b)
                                       { return lt(a, b); });
    std::unordered_set<nex*> existing_nex; // handling (nex*) as numbers
    nex_scalar * common_scalar;
    fill_join_map_for_sum(children, map, existing_nex, common_scalar);

    TRACE("nla_cn_details", for (auto & p : map ) { tout << "(" << *p.first << ", " << p.second << ") ";});
    children.clear();
    if (common_scalar) {
        children.push_back(common_scalar);
    }
    for (auto& p : map) {
        process_map_pair(p.first, p.second, children, existing_nex);
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
    for (auto & p : *a)
        if (!p.e()->is_elementary())
            return false;

    return true;
}

bool have_no_scalars(const nex_mul* a) {
    for (auto & p : *a)
        if (p.e()->is_scalar() && !to_scalar(p.e())->value().is_one())
            return false;

    return true;
}

nex * nex_creator::mk_div_sum_by_mul(const nex_sum* m, const nex_mul* b) {
    nex_sum * r = mk_sum();
    for (auto e : *m) {
        r->add_child(mk_div_by_mul(e, b));
    }
    TRACE("nla_cn_details", tout << *r << "\n";);
    return r;
}

nex * nex_creator::mk_div_mul_by_mul(const nex_mul *a, const nex_mul* b) {
    SASSERT(all_factors_are_elementary(a) && all_factors_are_elementary(b));
    b->get_powers_from_mul(m_powers);
    nex_mul* ret = new nex_mul();
    for (auto& p_from_a : *a) {
        TRACE("nla_cn_details", tout << "p_from_a = " << p_from_a << "\n";);
        const nex* e = p_from_a.e();
        if (e->is_scalar()) {
            ret->add_child_in_power(clone(e), p_from_a.pow());
            TRACE("nla_cn_details", tout << "processed scalar\n";);
            continue;
        }
        SASSERT(e->is_var());
        lpvar j = to_var(e)->var();
        auto it = m_powers.find(j);
        if (it == m_powers.end()) {
            ret->add_child_in_power(clone(e), p_from_a.pow());
        } else {
            unsigned pa = p_from_a.pow(); 
            unsigned& pb = it->second;
            SASSERT(pa);
            if (pa > pb) {
                ret->add_child_in_power(mk_var(j), pa - pb);
                m_powers.erase(it); 
            } else if (pa == pb) {
                m_powers.erase(it);                 
            } else {
                SASSERT(pa < pb);
                // not adding the factor here, it was eaten by b,
                // but the key j in m_powers remains
                pb -= pa; 
            }
        }
        TRACE("nla_cn_details", tout << *ret << "\n";);            
    }
    SASSERT(m_powers.size() == 0);
    if (ret->size() == 0) {
        delete ret;
        TRACE("nla_cn_details", tout << "return 1\n";);
        return mk_scalar(rational(1));
    }
    add_to_allocated(ret);
    TRACE("nla_cn_details", tout << *ret << "\n";);        
    return ret;
}

nex * nex_creator::mk_div_by_mul(const nex* a, const nex_mul* b) {
    SASSERT(have_no_scalars(b));
    if (a->is_sum()) {
        return mk_div_sum_by_mul(to_sum(a), b);
    }
    
    if (a->is_var()) {
        SASSERT(b->get_degree() == 1 && get_vars_of_expr(a) == get_vars_of_expr(b));
        return mk_scalar(rational(1));
    }    
    return mk_div_mul_by_mul(to_mul(a), b);
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

void nex_creator::process_map_pair(nex *e, const rational& coeff, ptr_vector<nex> & children, std::unordered_set<nex*>& existing_nex) {
    // todo : break on shorter functions
    if (coeff.is_zero())
        return;
    bool e_is_old = existing_nex.find(e) != existing_nex.end();
    if (e_is_old) {
        if (coeff.is_one()) {
            children.push_back(e);
        } else {
            if (e->is_var()) {
                children.push_back(mk_mul(mk_scalar(coeff), e));
            } else {
                SASSERT(e->is_mul());
                nex* first = (*to_mul(e))[0].e();
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

bool nex_creator::is_simplified(const nex *e) const 
{
    if (e->is_mul())
        return mul_is_simplified(to_mul(e));
    if (e->is_sum())
        return sum_is_simplified(to_sum(e));
    return true;
}

#ifdef Z3DEBUG
unsigned nex_creator::find_sum_in_mul(const nex_mul* a) const {
    for (unsigned j = 0; j < a->size(); j++)
        if ((*a)[j].e()->is_sum())
            return j;

    return -1;
}
nex* nex_creator::canonize_mul(nex_mul *a) {    
    unsigned j = find_sum_in_mul(a);
    if (j + 1 == 0)
        return a;
    nex_pow& np = (*a)[j];
    SASSERT(np.pow());
    unsigned power = np.pow();
    nex_sum * s = to_sum(np.e()); // s is going to explode        
    nex_sum * r = mk_sum();
    nex *sclone = power > 1? clone(s) : nullptr;
    for (nex *e : *s) {
        nex_mul *m = mk_mul();
        if (power > 1)
            m->add_child_in_power(sclone, power - 1);
        m->add_child(e);
        for (unsigned k = 0; k < a->size(); k++) {
            if (k == j)
                continue;
            m->add_child_in_power(clone((*a)[k].e()), (*a)[k].pow());
        }
        r->add_child(m);
    }
    TRACE("nla_cn_details", tout << *r << "\n";);
    return canonize(r);
}


nex* nex_creator::canonize(const nex *a) {
    if (a->is_elementary())
        return clone(a);
    
    nex *t = simplify(clone(a));
    if (t->is_sum()) {
        nex_sum * s = to_sum(t);
        for (unsigned j = 0; j < s->size(); j++) {
            (*s)[j] = canonize((*s)[j]);
        }
        t = simplify(s);
        TRACE("nla_cn_details", tout << *t << "\n";);
        return t;
    }
    return canonize_mul(to_mul(t));
}

bool nex_creator::equal(const nex* a, const nex* b) {
    nex_creator cn;
    unsigned n = 0;
    for (lpvar j : get_vars_of_expr(a)) {
        n = std::max(j + 1, n);
    }
    for (lpvar j : get_vars_of_expr(b)) {
        n = std::max(j + 1, n);
    }
    cn.set_number_of_vars(n);
    for (lpvar j = 0; j < n; j++) {
        cn.set_var_weight(j, j);
    }
    nex * ca = cn.canonize(a);
    nex * cb = cn.canonize(b);
    TRACE("nla_cn_test", tout << "a = " << *a << ", canonized a = " << *ca << "\n";);
    TRACE("nla_cn_test", tout << "b = " << *b << ", canonized b = " << *cb << "\n";);
    return !(cn.lt(ca, cb) || cn.lt(cb, ca));
}
#endif

}
