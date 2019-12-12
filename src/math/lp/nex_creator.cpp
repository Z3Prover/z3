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
#include "util/lbool.h"
#include "math/lp/nex_creator.h"
#include <map>

using namespace nla;

// divides by variable j. A precondition is that a is a multiple of j.
nex * nex_creator::mk_div(const nex& a, lpvar j) {
    SASSERT(is_simplified(a));
    SASSERT(a.contains(j));
    SASSERT(a.is_mul() || (a.is_var() && a.to_var().var() == j));
    if (a.is_var())
        return mk_scalar(rational(1));
    vector<nex_pow> bv; 
    bool seenj = false;
    auto ma = a.to_mul();
    for (auto& p : ma) {
        const nex * c = p.e();
        int pow = p.pow();
        if (!seenj && c->contains(j)) {
            SASSERT(!c->is_var() || c->to_var().var() == j);
            if (!c->is_var()) {
                bv.push_back(nex_pow(mk_div(*c, j)));
            }
            if (pow != 1) {
                bv.push_back(nex_pow(clone(c), pow - 1));
            }
            seenj = true;
        } else {
            bv.push_back(nex_pow(clone(c), pow));
        }
    }
    if (bv.size() == 1 && bv.begin()->pow() == 1 && ma.coeff().is_one()) {
        return bv.begin()->e();
    }
    if (bv.empty()) {
        return mk_scalar(rational(ma.coeff()));
    }
    
    auto m = mk_mul(bv);
    m->coeff() = ma.coeff();
    return m;

}

// TBD: describe what this does
bool nex_creator::eat_scalar_pow(rational& r, const nex_pow& p, unsigned pow) {
    if (p.e()->is_mul()) {
        const nex_mul & m = p.e()->to_mul();
        if (m.size() == 0) {
            const rational& coeff = m.coeff();
            if (coeff.is_one())
                return true;
            r *= coeff.expt(p.pow() * pow);
            return true;
        }
        return false;
    }
    if (!p.e()->is_scalar())
        return false;
    const nex_scalar &pe = p.e()->to_scalar();
    if (pe.value().is_one())
        return true; // r does not change here
    r *= pe.value().expt(p.pow() * pow);
    return true;
}


void nex_creator::simplify_children_of_mul(vector<nex_pow> & children, rational& coeff) {
    TRACE("grobner_d", print_vector(children, tout););
    vector<nex_pow> to_promote;
    unsigned j = 0;
    for (nex_pow& p : children) {        
        if (eat_scalar_pow(coeff, p, 1)) {
            continue;
        }        
        p.e() = simplify(p.e());
        if (p.e()->is_mul()) {
            to_promote.push_back(p);
        } else {
            children[j++] = p;
        }
    }
    
    children.shrink(j);

    for (nex_pow & p : to_promote) {
        TRACE("grobner_d", tout << p << "\n";);
        nex_mul &pm = p.e()->to_mul();
        for (nex_pow& pp : pm) {
            TRACE("grobner_d", tout << pp << "\n";);
            if (!eat_scalar_pow(coeff, pp, p.pow()))
                children.push_back(nex_pow(pp.e(), pp.pow() * p.pow()));            
        }
        coeff *= pm.coeff().expt(p.pow());
    }

    mul_to_powers(children);
    
    TRACE("grobner_d", print_vector(children, tout););    
}

template <typename T>
bool nex_creator::gt_on_powers_mul_same_degree(const T& a, const nex_mul& b) const {
    bool ret = false;
    unsigned a_pow = a.begin()->pow();
    unsigned b_pow = b.begin()->pow();
    for (auto it_a = a.begin(), it_b = b.begin(); it_a != a.end() && it_b != b.end(); ) {
        if (gt(it_a->e(), it_b->e())){
            ret = true;
            break;
        }
        if (gt(it_b->e(), it_a->e())){
            ret = false;
            break;
        }
        if (a_pow > b_pow) { // b should be advanced
            b_pow -= a_pow;
            ++it_b;
            if (it_b != b.end()) b_pow = it_b->pow();
            ret = true;
        } 
        else if (a_pow < b_pow) { // a should be advanced
            b_pow -= a_pow;
            ++it_a;
            if (it_a != a.end()) a_pow = it_a->pow();
            ret = false;
        }
        else {
            ++it_a;
            ++it_b;
            if (it_a != a.end()) a_pow = it_a->pow();
            if (it_b != b.end()) b_pow = it_b->pow();
        }
    }
    TRACE("nex_gt", tout << "a = "; print_vector(a, tout) << (ret?" > ":" <= ") << b << "\n";);
    return ret;
}

bool nex_creator::children_are_simplified(const vector<nex_pow>& children) const {
    for (auto c : children) 
        if (!is_simplified(*c.e()) || c.pow() == 0)
            return false;
    return true;
}

bool nex_creator::gt_on_powers_mul(const vector<nex_pow>& children, const nex_mul& b) const {
    TRACE("nex_gt", tout << "children = "; print_vector(children, tout) << " , b = " << b << "\n";);
    SASSERT(children_are_simplified(children) && is_simplified(b));
    unsigned a_deg = get_degree_children(children);
    unsigned b_deg = b.get_degree();
    return a_deg == b_deg ? gt_on_powers_mul_same_degree(children, b) : a_deg > b_deg;
}

bool nex_creator::gt_on_mul_mul(const nex_mul& a, const nex_mul& b) const {
    TRACE("grobner_d", tout << "a = " << a << " , b = " << b << "\n";);
    SASSERT(is_simplified(a) && is_simplified(b));
    unsigned a_deg = a.get_degree();
    unsigned b_deg = b.get_degree();
    return a_deg == b_deg ? gt_on_powers_mul_same_degree(a, b) : a_deg > b_deg;
}

bool nex_creator::gt_on_var_nex(const nex_var* a, const nex* b) const {
    switch (b->type()) {
    case expr_type::SCALAR: 
        return true;
    case expr_type::VAR:            
        return gt(a->var() , to_var(b)->var());
    case expr_type::MUL: 
        return b->get_degree() <= 1 && gt_on_var_nex(a, (*to_mul(b))[0].e());
    case expr_type::SUM:
        SASSERT(b->size() > 1);
        return gt(a, (*to_sum(b))[0]);        
    default:
        UNREACHABLE();
        return false;
    }
}

bool nex_creator::gt_nex_powers(const vector<nex_pow>& children, const nex* b) const {
    switch (b->type()) {
    case expr_type::SCALAR: 
        return false;
    case expr_type::VAR: 
        if (get_degree_children(children) > 1)
            return true;
        SASSERT(children[0].pow() == 1);
        SASSERT(!children[0].e()->is_scalar());
        return gt(children[0].e(), b);    
    case expr_type::MUL:
        return gt_on_powers_mul(children, *to_mul(b));            
    case expr_type::SUM:
        return gt_nex_powers(children, (*to_sum(b))[0]);
    default:
        UNREACHABLE();
        return false;
    }    
}

bool nex_creator::gt_on_mul_nex(const nex_mul* a, const nex* b) const {
    switch (b->type()) {
    case expr_type::SCALAR: 
        return false;
    case expr_type::VAR: 
        if (a->get_degree() > 1)
            return true;
        SASSERT(a->begin()->pow() == 1);
        SASSERT(!a->begin()->e()->is_scalar());
        return gt(a->begin()->e(), b);    
    case expr_type::MUL:
        return gt_on_mul_mul(*a, *to_mul(b));            
    case expr_type::SUM:
        return gt(a, (*to_sum(b))[0]);
    default:
        UNREACHABLE();
        return false;
    }    
}

bool nex_creator::gt_on_sum_sum(const nex_sum* a, const nex_sum* b) const {
    unsigned size = std::min(a->size(), b->size());
    for (unsigned j = 0; j < size; j++) {
        if (gt((*a)[j], (*b)[j]))
            return true;
        if (gt((*b)[j], (*a)[j]))
            return false;
    }
    return a->size() > size;
}

// the only difference with gt() that it disregards the coefficient in nex_mul
bool nex_creator::gt_for_sort_join_sum(const nex* a, const nex* b) const {
    TRACE("grobner_d_", tout << *a << " ? " << *b <<  "\n";);
    if (a == b)
        return false;
    bool ret;
    switch (a->type()) {
    case expr_type::VAR: 
        ret = gt_on_var_nex(to_var(a), b);
        break;
    case expr_type::SCALAR: 
        if (b->is_scalar())
            ret = to_scalar(a)->value() > to_scalar(b)->value();
        else
            ret = false; // the scalars are the largest
        break;
    case expr_type::MUL: 
        ret = gt_nex_powers(to_mul(a)->children(), b);
        break;
    case expr_type::SUM: 
        if (b->is_sum())
            return gt_on_sum_sum(to_sum(a), to_sum(b));
        return gt((*to_sum(a))[0], b);
    default:
        UNREACHABLE();
        return false;
    }
    TRACE("grobner_d_", tout << *a << (ret?" < ":" >= ") << *b << "\n";);
    return ret;
}

bool nex_creator::gt(const nex* a, const nex* b) const {
    TRACE("grobner_d_", tout << *a << " ? " << *b <<  "\n";);
    if (a == b)
        return false;
    bool ret;
    switch (a->type()) {
    case expr_type::VAR: 
        ret = gt_on_var_nex(to_var(a), b);
        break;
    case expr_type::SCALAR: 
        ret = b->is_scalar() && to_scalar(a)->value() > to_scalar(b)->value();
        // the scalars are the largest
        break;
    case expr_type::MUL: 
        ret = gt_on_mul_nex(to_mul(a), b);
        break;
    case expr_type::SUM: 
        if (b->is_sum())
            return gt_on_sum_sum(to_sum(a), to_sum(b));
        return gt((*to_sum(a))[0], b);
    default:
        UNREACHABLE();
        return false;
    }
    TRACE("grobner_d_", tout << *a << (ret?" < ":" >= ") << *b << "\n";);
    return ret;
}

bool nex_creator::is_sorted(const nex_mul& e) const {
    for (unsigned j = 0; j < e.size() - 1; j++) {
        if (!(gt_on_nex_pow(e[j], e[j+1]))) {
            TRACE("grobner_d", tout << "not sorted e " << e << "\norder is incorrect " <<
                  e[j] << " >= " << e[j + 1]<< "\n";);

            return false;
        }
    }
    return true;
}

bool nex_creator::mul_is_simplified(const nex_mul& e) const {
    TRACE("nla_cn_", tout <<  "e = " << e << "\n";);
    if (e.size() == 0) {
        TRACE("nla_cn", );
        return false; // it has to be a scalar
    }
    if (e.size() == 1 && e.begin()->pow() == 1 && e.coeff().is_one()) { 
        TRACE("nla_cn", );
        return false;
    }
    std::set<const nex*, nex_lt> s([this](const nex* a, const nex* b) {return gt(a, b); });
    for (const auto &p : e) {
        const nex* ee = p.e();
        if (p.pow() == 0) {
            TRACE("nla_cn", tout << "not simplified " << *ee << "\n";);
            return false;
        }
        if (ee->is_mul()) {
            TRACE("nla_cn", tout << "not simplified " << *ee << "\n";);
            return false;
        }
        if (ee->is_scalar() && to_scalar(ee)->value().is_one()) {
            TRACE("nla_cn", tout << "not simplified " << *ee << "\n";);
            return false;
        }

        auto it = s.find(ee);
        if (it == s.end()) {
            s.insert(ee);
        } else {            
            TRACE("nla_cn", tout << "not simplified " << *ee << "\n";);
            return false;
        }
    }
    return is_sorted(e);
}

nex * nex_creator::simplify_mul(nex_mul *e) {
    TRACE("grobner_d", tout << *e << "\n";);
    rational& coeff = e->coeff();
    simplify_children_of_mul(e->children(), coeff);
    if (e->size() == 1 && (*e)[0].pow() == 1 && coeff.is_one()) 
        return (*e)[0].e();
    
    if (e->size() == 0 || e->coeff().is_zero())
        return mk_scalar(e->coeff());
    TRACE("grobner_d", tout << *e << "\n";);
    SASSERT(is_simplified(*e));
    return e;
}

nex* nex_creator::simplify_sum(nex_sum *e) {
    TRACE("grobner_d", tout << "was e = " << *e << "\n";);
    simplify_children_of_sum(e->children());
    nex *r;
    if (e->size() == 1) {
        r = (*e)[0];
    } else if (e->size() == 0) {
        r = mk_scalar(rational(0));
    } else {
        r = e;
    }
    TRACE("grobner_d", tout << "became r = " << *r << "\n";);    
    return r;
}

bool nex_creator::sum_is_simplified(const nex_sum& e) const {
    if (e.size() < 2)  return false;
    bool scalar = false;
    for (nex * ee : e) {
        TRACE("nla_cn_details", tout << "ee = " << *ee << "\n";);
        if (ee->is_sum()) {
            TRACE("nla_cn", tout << "not simplified e = " << e << "\n"
                  << " has a child which is a sum " << *ee << "\n";);
            return false;
        }
        if (ee->is_scalar()) {
            if (scalar) {
                TRACE("nla_cn", tout <<  "not simplified e = " << e << "\n"
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
        if (!is_simplified(*ee))
            return false;
    }
    return true;
}

void nex_creator::mul_to_powers(vector<nex_pow>& children) {
    std::map<nex*, int, nex_lt> m([this](const nex* a, const nex* b) { return gt(a, b); });

    for (auto & p : children) {
        auto it = m.find(p.e());
        if (it == m.end()) {
            m[p.e()] = p.pow();
        } else {
            it->second += p.pow();
        }
    }
    children.clear();
    for (auto & p : m) {
        children.push_back(nex_pow(p.first, p.second));
    }

    std::sort(children.begin(), children.end(), [this](const nex_pow& a, const nex_pow& b) {
                                                    return gt_on_nex_pow(a, b);
                                                });
}

nex* nex_creator::create_child_from_nex_and_coeff(nex *e,
                                                  const rational& coeff) {
    TRACE("grobner_d", tout << *e << ", coeff = " << coeff << "\n";);
    if (coeff.is_one())
        return e;
    SASSERT(is_simplified(*e));
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
                                                 const nex_pow& b) {return gt_on_nex_pow(a, b); });
        return em;
    }
    case expr_type::SUM: 
        return mk_mul(mk_scalar(coeff), e);
    default:
        UNREACHABLE();
        return nullptr;
    }
        
}
// returns true if the key exists already
bool nex_creator::register_in_join_map(std::map<nex*, rational, nex_lt>& map, nex* e, const rational& r) const{
    TRACE("grobner_d",  tout << *e << ", r = " << r << std::endl;);
    auto map_it = map.find(e);
    if (map_it == map.end()) {
        map[e] = r;
        TRACE("grobner_d",  tout << "inserting " << std::endl;);
        return false;
    } else {
        map_it->second += r;
        TRACE("grobner_d",  tout << "adding " << r << " , got " << map_it->second << std::endl;);
        return true;
    }
}

bool nex_creator::fill_join_map_for_sum(
    ptr_vector<nex> & children,
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
            nex_mul * m = to_mul(e);
            simplified |= register_in_join_map(map, m, m->coeff());
        } else {
            SASSERT(e->is_var());
            simplified |= register_in_join_map(map, e, rational(1));
        }
    }
    return simplified;
}
    // a + 3bc + 2bc => a + 5bc 
void nex_creator::sort_join_sum(ptr_vector<nex> & children) {
    TRACE("grobner_d", print_vector_of_ptrs(children, tout););
    std::map<nex*, rational, nex_lt> map([this](const nex *a , const nex *b)
                                       { return gt_for_sort_join_sum(a, b); });
    std::unordered_set<nex*> allocated_nexs; // handling (nex*) as numbers
    nex_scalar * common_scalar = nullptr;
    fill_join_map_for_sum(children, map, allocated_nexs, common_scalar);

    TRACE("grobner_d", for (auto & p : map ) { tout << "(" << *p.first << ", " << p.second << ") ";});
    children.clear();
    for (auto& p : map) {
        process_map_pair(p.first, p.second, children, allocated_nexs);
    }
    if (common_scalar && !common_scalar->value().is_zero()) {
        children.push_back(common_scalar);
    }
    TRACE("grobner_d",
          tout << "map=";
          for (auto & p : map ) tout << "(" << *p.first << ", " << p.second << ") "; 
          tout << "\nchildren="; print_vector_of_ptrs(children, tout) << "\n";);    
}

void nex_creator::simplify_children_of_sum(ptr_vector<nex> & children) {
    TRACE("grobner_d", print_vector_of_ptrs(children, tout););
    ptr_vector<nex> to_promote;
    unsigned k = 0; 
    for (unsigned j = 0; j < children.size(); j++) {
        nex* e = children[j] = simplify(children[j]);
        if (e->is_sum()) {
            to_promote.push_back(e);
        } else if (is_zero_scalar(e)) {
            continue;
        } else if (e->is_mul() && to_mul(e)->coeff().is_zero() ) {
            continue;
        } else {
            children[k++] = e;
        }
    }
    
    TRACE("grobner_d", print_vector_of_ptrs(children, tout););
    children.shrink(k);
    
    for (nex *e : to_promote) {
        for (nex *ee : *(e->to_sum().children_ptr())) {
            if (!is_zero_scalar(ee))
                children.push_back(ee);            
        }
    }

    sort_join_sum(children);
}


static bool have_no_scalars(const nex_mul& a) {
    for (auto & p : a)
        if (p.e()->is_scalar() && !to_scalar(p.e())->value().is_one())
            return false;
    return true;
}

bool nex_mul::all_factors_are_elementary() const {
    for (auto & p : *this)
        if (!p.e()->is_elementary())
            return false;
    return true;
}

nex * nex_creator::mk_div_sum_by_mul(const nex_sum& m, const nex_mul& b) {
    nex_sum * r = mk_sum();
    for (auto e : m) {
        r->add_child(mk_div_by_mul(*e, b));
    }
    TRACE("grobner_d", tout << *r << "\n";);
    return r;
}

nex * nex_creator::mk_div_mul_by_mul(const nex_mul& a, const nex_mul& b) {
    SASSERT(a.all_factors_are_elementary() && b.all_factors_are_elementary());
    b.get_powers_from_mul(m_powers);
    nex_mul* ret = new nex_mul();
    for (auto& p_from_a : a) {
        TRACE("grobner_d", tout << "p_from_a = " << p_from_a << "\n";);
        const nex* e = p_from_a.e();
        if (e->is_scalar()) {
            ret->add_child_in_power(clone(e), p_from_a.pow());
            TRACE("grobner_d", tout << "processed scalar\n";);
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
        TRACE("grobner_d", tout << *ret << "\n";);            
    }
    SASSERT(m_powers.size() == 0);
    if (ret->size() == 0) {
        delete ret;
        TRACE("grobner_d", tout << "return scalar\n";);
        return mk_scalar(a.coeff() / b.coeff());
    }
    ret->coeff() = a.coeff() / b.coeff();
    add_to_allocated(ret);
    TRACE("grobner_d", tout << *ret << "\n";);        
    return ret;
}

nex * nex_creator::mk_div_by_mul(const nex& a, const nex_mul& b) {
    SASSERT(have_no_scalars(b));
    SASSERT(!a.is_var() || (b.get_degree() == 1 && get_vars_of_expr(&a) == get_vars_of_expr(&b) && b.coeff().is_one()));
    if (a.is_sum()) {
        return mk_div_sum_by_mul(a.to_sum(), b);
    }    
    if (a.is_var()) {        
        return mk_scalar(rational(1));
    }    
    return mk_div_mul_by_mul(a.to_mul(), b);
}

nex * nex_creator::mk_div(const nex& a, const nex& b) {
    TRACE("grobner_d", tout << a <<" / " << b << "\n";);
    if (b.is_var()) {
        return mk_div(a, b.to_var().var());
    }
    return mk_div_by_mul(a, b.to_mul());
}

nex* nex_creator::simplify(nex* e) {
    nex* es;
    TRACE("grobner_d", tout << *e << std::endl;);
    if (e->is_mul())
        es = simplify_mul(to_mul(e));
    else if (e->is_sum())
        es = simplify_sum(to_sum(e));
    else
        es = e;
    TRACE("grobner_d", tout << "simplified = " << *es << std::endl;);
    SASSERT(is_simplified(*es));
    return es;
}

// adds to children the corrected expression and also adds to allocated the new expressions
void nex_creator::process_map_pair(nex *e, const rational& coeff, ptr_vector<nex> & children, std::unordered_set<nex*>& allocated_nexs) {
    TRACE("grobner_d", tout << "e=" << *e << " , coeff= " << coeff << "\n";);
    if (coeff.is_zero()) {
        TRACE("grobner_d", tout << "did nothing\n";);   
        return;
    }
    bool e_is_old = allocated_nexs.find(e) != allocated_nexs.end();
    if (!e_is_old) {
        m_allocated.push_back(e);
    }
    if (e->is_mul()) {
        e->to_mul().coeff() = coeff;
        children.push_back(simplify(e));
    } else {
        SASSERT(e->is_var());
        if (coeff.is_one()) {
            children.push_back(e);
        } else {
            children.push_back(mk_mul(mk_scalar(coeff), e));
        }
    }
}

bool nex_creator::is_simplified(const nex& e) const {
    TRACE("nla_cn_details", tout << "e = " << e << "\n";);
    if (e.is_mul())
        return mul_is_simplified(e.to_mul());
    if (e.is_sum())
        return sum_is_simplified(e.to_sum());
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
    TRACE("grobner_d", tout << "a = " << *a << "\n";);
    unsigned j = find_sum_in_mul(a);
    if (j + 1 == 0)
        return a;
    nex_pow& np = (*a)[j];
    SASSERT(np.pow());
    unsigned power = np.pow();
    nex_sum const& s = np.e()->to_sum(); // s is going to explode        
    nex_sum * r = mk_sum();
    nex *sclone = power > 1 ? clone(&s) : nullptr;
    for (nex *e : s) {
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
    TRACE("grobner_d", tout << "canonized a = " <<  *r << "\n";);
    return canonize(r);
}

nex* nex_creator::canonize(const nex *a) {
    if (a->is_elementary())
        return clone(a);
    
    nex *t = simplify(clone(a));
    if (t->is_sum()) {
        nex_sum & s = t->to_sum();
        for (unsigned j = 0; j < s.size(); j++) {
            s[j] = canonize(s[j]);
        }
        t = simplify(&s);
        TRACE("grobner_d", tout << *t << "\n";);
        return t;
    }
    return canonize_mul(to_mul(t));
}

bool nex_creator::equal(const nex* a, const nex* b) {
    TRACE("grobner_d", tout << *a << " against  " << *b << "\n";);
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
    TRACE("grobner_d", tout << "a = " << *a << ", canonized a = " << *ca << "\n";);
    TRACE("grobner_d", tout << "b = " << *b << ", canonized b = " << *cb << "\n";);
    return !(cn.gt(ca, cb) || cn.gt(cb, ca));
}
#endif

