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


bool ignored_child(nex* e, expr_type t) {
    switch(t) {
    case expr_type::MUL:
        return e->is_scalar() && to_scalar(e)->value().is_one();
    case expr_type::SUM:        
        return e->is_scalar() && to_scalar(e)->value().is_zero();
    default: return false;
    }
    return false;
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

void promote_children_of_sum(ptr_vector<nex> & children, nex_lt lt ) {
    ptr_vector<nex> to_promote;
    int skipped = 0;
    for(unsigned j = 0; j < children.size(); j++) {
        nex** e = &(children[j]);
        (*e)->simplify(e, lt);
        if ((*e)->is_sum()) {
            to_promote.push_back(*e);
        } else if (ignored_child(*e, expr_type::SUM)) {
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
            if (!ignored_child(ee, expr_type::SUM))
                children.push_back(ee);            
        }
    } 
}

bool eat_scalar(nex_scalar *& r, nex_pow& p) {
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

void simplify_children_of_mul(vector<nex_pow> & children, nex_lt lt) {
    nex_scalar* r = nullptr;
    TRACE("nla_cn_details", print_vector(children, tout););
    vector<nex_pow> to_promote;
    int skipped = 0;
    for(unsigned j = 0; j < children.size(); j++) {        
        nex_pow& p = children[j];
        if (eat_scalar(r, p)) {
            skipped++;
            continue;
        }
        (p.e())->simplify(p.ee(), lt);
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
            if (!eat_scalar(r, pp))
                children.push_back(nex_pow(pp.e(), pp.pow() * p.pow()));            
        }
    }

    if (r != nullptr) {
        children.push_back(nex_pow(r));
    }
        
    mul_to_powers(children, lt);
    
    TRACE("nla_cn_details", print_vector(children, tout););
    
}
}
