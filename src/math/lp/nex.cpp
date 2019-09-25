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



void promote_children_of_sum(ptr_vector<nex> & children,std::function<bool (const nex*, const nex*)> lt ) {
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

void promote_children_of_mul(vector<nex_pow> & children, std::function<bool (const nex*, const nex*)> lt) {
    TRACE("nla_cn_details", print_vector(children, tout););
    vector<nex_pow> to_promote;
    int skipped = 0;
    for(unsigned j = 0; j < children.size(); j++) {
        nex_pow& p = children[j];
        (p.e())->simplify(p.ee(), lt);
        if ((p.e())->is_mul()) {
            to_promote.push_back(p);
        } else if (ignored_child(p.e(), expr_type::MUL)) {
            skipped ++;
            continue;
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
            SASSERT(!ignored_child(pp.e(), expr_type::MUL));
            children.push_back(nex_pow(pp.e(), pp.pow() * p.pow()));            
        }
    }

    TRACE("nla_cn_details", print_vector(children, tout););
    
}
}
