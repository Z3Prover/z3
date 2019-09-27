/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Lev Nachmanson (levnach)

  Revision History:


  --*/

#include "math/lp/nex.h"
#include <map>
namespace nla {


bool is_zero_scalar(nex* e) {
    return e->is_scalar() && to_scalar(e)->value().is_zero();
}

void mul_to_powers(vector<nex_pow>& children, nex_lt lt) {
    std::map<nex*, int, nex_lt> m(lt);

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

    std::sort(children.begin(), children.end(), [lt](const nex_pow& a, const nex_pow& b) {
                                                    return less_than(a, b, lt);
                                                });
}

rational extract_coeff(const nex_mul* m) {
    const nex* e = m->children().begin()->e();
    if (e->is_scalar())
        return to_scalar(e)->value();
    return rational(1);
}


bool sum_simplify_lt(const nex_mul* a, const nex_mul* b, const nex_lt& lt) {
    NOT_IMPLEMENTED_YET();
}

// a + 3bc + 2bc => a + 5bc 
void sort_join_sum(ptr_vector<nex> & children, nex_lt& lt, std::function<nex_scalar*()> mk_scalar) {
    ptr_vector<nex> non_muls;
    std::map<nex_mul*, rational, std::function<bool(const nex_mul *a , const nex_mul *b)>>
             m([lt](const nex_mul *a , const nex_mul *b) { return sum_simplify_lt(a, b, lt); });
    for (nex* e : children) {
        SASSERT(e->is_simplified(lt));
        if (!e->is_mul()) {
            non_muls.push_back(e);
        } else {
            nex_mul * em = to_mul(e);
            rational r = extract_coeff(em);
            auto it = m.find(em);
            if (it == m.end()) {
                m[em] = r;
            } else {
                it->second += r;
            }
        }
    }
    NOT_IMPLEMENTED_YET();
}

void simplify_children_of_sum(ptr_vector<nex> & children, nex_lt lt, std::function<nex_scalar*()> mk_scalar ) {
    ptr_vector<nex> to_promote;
    int skipped = 0;
    for(unsigned j = 0; j < children.size(); j++) {
        nex** e = &(children[j]);
        (*e)->simplify(e, lt, mk_scalar);
        if ((*e)->is_sum()) {
            to_promote.push_back(*e);
        } else if (is_zero_scalar(*e)) {
            skipped ++;
            continue;
        } else {
            unsigned offset = to_promote.size() + skipped;
            if (offset) {
                children[j - offset] = *e;
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

    sort_join_sum(children, lt, mk_scalar);
}

bool eat_scalar_pow(nex_scalar *& r, nex_pow& p) {
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

void simplify_children_of_mul(vector<nex_pow> & children, nex_lt lt, std::function<nex_scalar*()> mk_scalar) {
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
        (p.e())->simplify(p.ee(), lt, mk_scalar );
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
        
    mul_to_powers(children, lt);
    
    TRACE("nla_cn_details", print_vector(children, tout););    
}

bool less_than_nex(const nex* a, const nex* b, lt_on_vars lt) {
    int r = (int)(a->type()) - (int)(b->type());
    if (r) {
        return r < 0;
    }
    SASSERT(a->type() == b->type());
    switch (a->type()) {
    case expr_type::VAR: {
        return lt(to_var(a)->var() , to_var(b)->var());
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

}
