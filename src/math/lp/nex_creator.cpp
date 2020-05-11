/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
   Lev Nachmanson (levnach)
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
    mul_factory mf(*this);
    bool seenj = false;
    auto ma = a.to_mul();
    for (auto& p : ma) {
        const nex * c = p.e();
        int pow = p.pow();
        if (!seenj && c->contains(j)) {
            SASSERT(!c->is_var() || c->to_var().var() == j);
            if (!c->is_var()) {
                mf *= nex_pow(mk_div(*c, j), 1);
            }
            if (pow != 1) {
                mf *= nex_pow(clone(c), pow - 1);
            }
            seenj = true;
        } else {
            mf *= nex_pow(clone(c), pow);
        }
    }
    mf *= ma.coeff();
    return mf.mk_reduced();
}

// return true if p is a constant, update r with value of p raised to pow.
bool nex_creator::eat_scalar_pow(rational& r, const nex_pow& p, unsigned pow) {
    if (p.e()->is_mul() && p.e()->to_mul().size() == 0) {
        auto const& m = p.e()->to_mul();
        if (!m.coeff().is_one()) {
            r *= m.coeff().expt(p.pow() * pow);
        }
        return true;
    }
    if (!p.e()->is_scalar())
        return false;
    const nex_scalar &pe = p.e()->to_scalar();
    if (!pe.value().is_one()) {
        r *= pe.value().expt(p.pow() * pow);
    }
    return true;
}


void nex_creator::simplify_children_of_mul(vector<nex_pow> & children, rational& coeff) {
    TRACE("grobner_d", print_vector(children, tout << "children_of_mul: "); tout << "\n";);
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
    auto it_a = a.begin();
    auto it_b = b.begin();
    for (; it_a != a.end() && it_b != b.end(); ) {
        if (gt(it_a->e(), it_b->e())){
            ret = true;
            break;
        }
        if (gt(it_b->e(), it_a->e())){
            ret = false;
            break;
        }
        if (a_pow > b_pow) {
            ret = true;
            break;
        } 
        if (a_pow < b_pow) {
            ret = false;
            break;
        }
        ++it_a;
        ++it_b;
        if (it_a != a.end()) a_pow = it_a->pow();
        if (it_b != b.end()) b_pow = it_b->pow();

    }
    TRACE("nex_gt", tout << "a = "; print_vector(a, tout) << (ret?" > ":" <= ") << b << "\n";);
    return ret;
}

bool nex_creator::gt_on_mul_mul(const nex_mul& a, const nex_mul& b) const {
    TRACE("grobner_d", tout << "a = " << a << " , b = " << b << "\n";);
    SASSERT(is_simplified(a) && is_simplified(b));
    unsigned a_deg = a.get_degree();
    unsigned b_deg = b.get_degree();
    return a_deg == b_deg ? gt_on_powers_mul_same_degree(a, b) : a_deg > b_deg;
}

bool nex_creator::gt_on_var_nex(const nex_var& a, const nex& b) const {
    switch (b.type()) {
    case expr_type::SCALAR: 
        return true;
    case expr_type::VAR:            
        return gt(a.var(), b.to_var().var());
    case expr_type::MUL: 
        return b.get_degree() <= 1 && gt_on_var_nex(a, *b.to_mul()[0].e());
    case expr_type::SUM:
        SASSERT(b.size() > 1);
        if(gt(&a, b.to_sum()[0]))
            return true;
        if (gt(b.to_sum()[0], &a ))
            return false;
        return true;
           
    default:
        UNREACHABLE();
        return false;
    }
}

bool nex_creator::gt_on_mul_nex(nex_mul const& m, nex const& b) const {
    switch (b.type()) {
    case expr_type::SCALAR: 
        return false;
    case expr_type::VAR: 
        if (m.get_degree() > 1)
            return true;
        SASSERT(m[0].pow() == 1);
        SASSERT(!m[0].e()->is_scalar());
        return gt(m[0].e(), &b);    
    case expr_type::MUL:
        return gt_on_mul_mul(m, b.to_mul());            
    case expr_type::SUM:
        return gt_on_mul_nex(m, *b.to_sum()[0]);
    default:
        UNREACHABLE();
        return false;
    }    
}

bool nex_creator::gt_on_sum_sum(const nex_sum& a, const nex_sum& b) const {
    unsigned size = std::min(a.size(), b.size());
    for (unsigned j = 0; j < size; j++) {
        if (gt(a[j], b[j]))
            return true;
        if (gt(b[j], a[j]))
            return false;
    }
    return a.size() > size;
}

// the only difference with gt() that it disregards the coefficient in nex_mul
bool nex_creator::gt_for_sort_join_sum(const nex* a, const nex* b) const {
    TRACE("grobner_d_", tout << *a << " ? " << *b <<  "\n";);
    if (a == b)
        return false;
    bool ret;
    switch (a->type()) {
    case expr_type::VAR: 
        ret = gt_on_var_nex(a->to_var(), *b);
        break;
    case expr_type::SCALAR: 
        if (b->is_scalar())
            ret = a->to_scalar().value() > b->to_scalar().value();
        else
            ret = false; // the scalars are the largest
        break;
    case expr_type::MUL: 
        ret = gt_on_mul_nex(a->to_mul(), *b);
        break;
    case expr_type::SUM: 
        if (b->is_sum())
            return gt_on_sum_sum(a->to_sum(), b->to_sum());
        return gt(a->to_sum()[0], b);
    default:
        UNREACHABLE();
        return false;
    }
    TRACE("grobner_d_", tout << *a << (ret?" < ":" >= ") << *b << "\n";);
    return ret;
}

bool nex_creator::gt(const nex& a, const nex& b) const {
    TRACE("grobner_d_", tout << a << " ? " << b <<  "\n";);
    if (&a == &b)
        return false;
    bool ret;
    switch (a.type()) {
    case expr_type::VAR: 
        ret = gt_on_var_nex(a.to_var(), b);
        break;
    case expr_type::SCALAR: 
        ret = b.is_scalar() && a.to_scalar().value() > b.to_scalar().value();
        // the scalars are the largest
        break;
    case expr_type::MUL: 
        ret = gt_on_mul_nex(a.to_mul(), b);
        break;
    case expr_type::SUM: 
        if (b.is_sum())
            return gt_on_sum_sum(a.to_sum(), b.to_sum());
        return gt(*a.to_sum()[0], b);
    default:
        UNREACHABLE();
        return false;
    }
    TRACE("grobner_d_", tout << a << (ret?" < ":" >= ") << b << "\n";);
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
    rational& coeff = e->m_coeff;
    simplify_children_of_mul(e->m_children, coeff);
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
    simplify_children_of_sum(*e);
    nex *r;
    if (e->size() == 1) {
        r = const_cast<nex*>((*e)[0]);
    } else if (e->size() == 0) {
        r = mk_scalar(rational(0));
    } else {
        r = const_cast<nex_sum*>(e);
    }
    TRACE("grobner_d", tout << "became r = " << *r << "\n";);    
    return r;
}

bool nex_creator::sum_is_simplified(const nex_sum& e) const {
    if (e.size() < 2)  return false;
    bool scalar = false;
    for (nex const* ee : e) {
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

// returns true if the key exists already
bool nex_creator::register_in_join_map(std::map<nex const*, rational, nex_lt>& map, nex const* e, const rational& r) const{
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
    nex_sum & sum,
    std::map<nex const*, rational, nex_lt>& map,
    std::unordered_set<nex const*>& existing_nex,
    rational& common_scalar) {
    bool simplified = false;
    for (auto e : sum) {
        if (e->is_scalar()) {
            simplified = true;
            common_scalar += e->to_scalar().value();           
            continue;
        }
        existing_nex.insert(e);
        if (e->is_mul()) {
            nex_mul const * m = to_mul(e);
            simplified |= register_in_join_map(map, m, m->coeff());
        } else {
            SASSERT(e->is_var());
            simplified |= register_in_join_map(map, e, rational(1));
        }
    }
    return simplified;
}
    // a + 3bc + 2bc => a + 5bc 
void nex_creator::sort_join_sum(nex_sum& sum) {
    TRACE("grobner_d", tout << sum << "\n";);
    std::map<nex const*, rational, nex_lt> map([this](const nex *a , const nex *b)
                                       { return gt_for_sort_join_sum(a, b); });
    std::unordered_set<nex const*> allocated_nexs; // handling (nex*) as numbers
    rational common_scalar(0);
    fill_join_map_for_sum(sum, map, allocated_nexs, common_scalar);

    TRACE("grobner_d", for (auto & p : map ) { tout << "(" << *p.first << ", " << p.second << ") ";});
    sum.m_children.reset();
    for (auto& p : map) {
        process_map_pair(const_cast<nex*>(p.first), p.second, sum, allocated_nexs);
    }
    if (!common_scalar.is_zero()) {
        sum.m_children.push_back(mk_scalar(common_scalar));
    }
    TRACE("grobner_d",
          tout << "map=";
          for (auto & p : map ) tout << "(" << *p.first << ", " << p.second << ") "; 
          tout << "\nchildren=" << sum << "\n";);    
}

void nex_creator::simplify_children_of_sum(nex_sum& s) {
    ptr_vector<nex> to_promote;
    unsigned k = 0;
    for (unsigned j = 0; j < s.size(); j++) {
        nex* e = s[j] = simplify(s[j]);
        if (e->is_sum()) {
            to_promote.push_back(e);
        } else if (is_zero_scalar(e)) {
            continue;
        } else if (e->is_mul() && to_mul(e)->coeff().is_zero() ) {
            continue;
        } else {
            s.m_children[k++] = e;
        }
    }
    s.m_children.shrink(k);
       
    for (nex *e : to_promote) {
        for (nex const*ee : e->to_sum()) {
            if (!is_zero_scalar(ee))
                s.m_children.push_back(const_cast<nex*>(ee));           
        }
    }
    
    sort_join_sum(s);
}

bool nex_mul::all_factors_are_elementary() const {
    for (auto & p : *this)
        if (!p.e()->is_elementary())
            return false;
    return true;
}

nex * nex_creator::mk_div_sum_by_mul(const nex_sum& m, const nex_mul& b) {
    sum_factory sf(*this);
    for (auto e : m) {
        sf += mk_div_by_mul(*e, b);
    }
    nex* r = sf.mk();
    TRACE("grobner_d", tout << *r << "\n";);
    return r;
}

nex * nex_creator::mk_div_mul_by_mul(const nex_mul& a, const nex_mul& b) {
    SASSERT(a.all_factors_are_elementary() && b.all_factors_are_elementary());
    b.get_powers_from_mul(m_powers);
    m_mk_mul.reset();
    for (auto& p_from_a : a) {
        TRACE("grobner_d", tout << "p_from_a = " << p_from_a << "\n";);
        const nex* e = p_from_a.e();
        if (e->is_scalar()) {
            m_mk_mul *= nex_pow(clone(e), p_from_a.pow());
            TRACE("grobner_d", tout << "processed scalar\n";);
            continue;
        }
        SASSERT(e->is_var());
        lpvar j = to_var(e)->var();
        auto it = m_powers.find(j);
        if (it == m_powers.end()) {
            m_mk_mul *= nex_pow(clone(e), p_from_a.pow());
        } else {
            unsigned pa = p_from_a.pow(); 
            unsigned& pb = it->second;
            SASSERT(pa);
            if (pa > pb) {
                m_mk_mul *= nex_pow(mk_var(j), pa - pb);
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
    }
    SASSERT(m_powers.size() == 0);
    m_mk_mul *= (a.coeff() / b.coeff());
    nex* ret = m_mk_mul.mk_reduced();
    TRACE("grobner_d", tout << *ret << "\n";);        
    return ret;
}

nex * nex_creator::mk_div_by_mul(const nex& a, const nex_mul& b) {
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
void nex_creator::process_map_pair(nex*e, const rational& coeff, nex_sum & sum, std::unordered_set<nex const*>& allocated_nexs) {
    TRACE("grobner_d", tout << "e=" << *e << " , coeff= " << coeff << "\n";);
    if (coeff.is_zero()) {
        TRACE("grobner_d", tout << "did nothing\n";);   
        return;
    }
    bool e_is_old = allocated_nexs.find(e) != allocated_nexs.end();
    if (!e_is_old) {
        add_to_allocated(e);
    }
    if (e->is_mul()) {
        e->to_mul().m_coeff = coeff;
        sum.m_children.push_back(simplify(e));
    } else {
        SASSERT(e->is_var());
        if (coeff.is_one()) {
            sum.m_children.push_back(e);
        } else {
            mul_factory mf(*this);
            mf *= coeff;
            mf *= e;
            sum.m_children.push_back(mf.mk());
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
    sum_factory sf(*this);
    nex *sclone = power > 1 ? clone(&s) : nullptr;
    for (nex const*e : s) {
        mul_factory mf(*this);
        if (power > 1)
            mf *= nex_pow(sclone, power - 1);
        mf *= nex_pow(e, 1);
        for (unsigned k = 0; k < a->size(); k++) {
            if (k == j)
                continue;
            mf *= nex_pow(clone((*a)[k].e()), (*a)[k].pow());
        }
        sf += mf.mk();
    }
    nex* r = sf.mk();
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

