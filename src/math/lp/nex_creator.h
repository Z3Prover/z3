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
#pragma once

namespace nla {

struct occ {
    unsigned m_occs; // number of occurences
    unsigned m_power; // min power in occurences
    occ() : m_occs(0), m_power(0) {}
    occ(unsigned k, unsigned p) : m_occs(k), m_power(p) {}
    // use the "name injection rule here"
    friend std::ostream& operator<<(std::ostream& out, const occ& c) {
        out << "(occs:" << c.m_occs <<", pow:" << c.m_power << ")";
        return out;
    }
};


// the purpose of this class is to create nex objects, keep them, and delete them

class nex_creator {

    ptr_vector<nex>                       m_allocated;
    std::unordered_map<lpvar, occ>        m_occurences_map;
    std::unordered_map<lpvar, unsigned>   m_powers;
public:
    const std::unordered_map<lpvar, occ>& occurences_map() const { return m_occurences_map; }
    std::unordered_map<lpvar, occ>& occurences_map() { return m_occurences_map; }
    const std::unordered_map<lpvar, unsigned> & powers() const { return m_powers; }
    std::unordered_map<lpvar, unsigned> & powers() { return m_powers; }
    
    void add_to_allocated(nex* r) { m_allocated.push_back(r); }

    void pop(unsigned sz) {
        for (unsigned j = sz; j < m_allocated.size(); j ++)
            delete m_allocated[j];
        m_allocated.resize(sz);
    }

    void clear() {
        for (auto e: m_allocated)
            delete e;
        m_allocated.clear();
    }
    
    unsigned size() const { return m_allocated.size(); }
    
    nex_sum* mk_sum() {
        auto r = new nex_sum();
        add_to_allocated(r);
        return r;
    }
    template <typename T>
    void add_children(T) { }
    
    template <typename T, typename K, typename ...Args>
    void add_children(T r, K e, Args ...  es) {
        r->add_child(e);
        add_children(r, es ...);
    }

    nex_sum* mk_sum(const ptr_vector<nex>& v) {
        auto r = new nex_sum();
        add_to_allocated(r);
        r->children() = v;
        return r;
    }

    nex_mul* mk_mul(const ptr_vector<nex>& v) {
        auto r = new nex_mul();
        add_to_allocated(r);
        r->children() = v;
        return r;
    }

    
    template <typename K, typename...Args>
    nex_sum* mk_sum(K e, Args... es) {
        auto r = new nex_sum();
        add_to_allocated(r);
        r->add_child(e);
        add_children(r, es...);
        return r;
    }
    nex_var* mk_var(lpvar j) {
        auto r = new nex_var(j);
        add_to_allocated(r);
        return r;
    }
    
    nex_mul* mk_mul() {
        auto r = new nex_mul();
        add_to_allocated(r);
        return r;
    }

    template <typename K, typename...Args>
    nex_mul* mk_mul(K e, Args... es) {
        auto r = new nex_mul();
        add_to_allocated(r);
        add_children(r, e, es...);
        return r;
    }
    
    nex_scalar* mk_scalar(const rational& v) {
        auto r = new nex_scalar(v);
        add_to_allocated(r);
        return r;
    }


    nex * mk_div(const nex* a, lpvar j) {
        TRACE("nla_cn_details", tout << "a=" << *a << ", v" << j << "\n";);
        SASSERT((a->is_mul() && a->contains(j)) || (a->is_var() && to_var(a)->var() == j));
        if (a->is_var())
            return mk_scalar(rational(1));
        ptr_vector<nex> bv;
        bool seenj = false;
        for (nex* c : to_mul(a)->children()) {
            if (!seenj) {
                if (c->contains(j)) {
                    if (!c->is_var())                     
                        bv.push_back(mk_div(c, j));
                    seenj = true;
                    continue;
                } 
            }
            bv.push_back(c);
        }
        if (bv.size() > 1) { 
            return mk_mul(bv);
        }
        if (bv.size() == 1) {
            return bv[0];
        }

        SASSERT(bv.size() == 0);
        return mk_scalar(rational(1));
    }

    nex * mk_div(const nex* a, const nex* b) {
        TRACE("nla_cn_details", tout << *a <<" / " << *b << "\n";);
        if (b->is_var()) {
            return mk_div(a, to_var(b)->var());
        }
        SASSERT(b->is_mul());
        const nex_mul *bm = to_mul(b);
        if (a->is_sum()) {
            nex_sum * r = mk_sum();
            const nex_sum * m = to_sum(a);
            for (auto e : m->children()) {
                r->add_child(mk_div(e, bm));
            }
            TRACE("nla_cn_details", tout << *r << "\n";);
            return r;
        }
        if (a->is_var() || (a->is_mul() && to_mul(a)->children().size() == 1)) {
            return mk_scalar(rational(1));
        }
        SASSERT(a->is_mul());
        const nex_mul* am = to_mul(a);
        bm->get_powers_from_mul(m_powers);
        nex_mul* ret = new nex_mul();
        for (auto e : am->children()) {
            TRACE("nla_cn_details", tout << "e=" << *e << "\n";);
            
            if (!e->is_var()) {
                SASSERT(e->is_scalar());
                ret->add_child(e);
                TRACE("nla_cn_details", tout << "continue\n";);
                continue;
            }
            SASSERT(e->is_var());
            lpvar j = to_var(e)->var();
            auto it = m_powers.find(j);
            if (it == m_powers.end()) {
                 ret->add_child(e);
            } else {
                it->second --;
                if (it->second == 0)
                    m_powers.erase(it);
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

};
}
