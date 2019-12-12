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
#include <map>
#include "util/map.h"
#include "math/lp/nex.h"
namespace nla {

struct occ {
    unsigned m_occs; // number of occurences
    unsigned m_power; // min power in occurences
    occ() : m_occs(0), m_power(0) {}
    occ(unsigned k, unsigned p) : m_occs(k), m_power(p) {}
    // use the "name injection rule here"
    friend std::ostream& operator<<(std::ostream& out, const occ& c) {
        return out << "(occs:" << c.m_occs <<", pow:" << c.m_power << ")";
    }
};

enum var_weight {
    FIXED = 0,
    QUOTED_FIXED =  1,
    BOUNDED    =    2,
    QUOTED_BOUNDED = 3,
    NOT_FREE      =  4,
    QUOTED_NOT_FREE = 5,
    FREE          =   6,
    QUOTED_FREE    = 7,
    MAX_DEFAULT_WEIGHT = 7
};


// the purpose of this class is to create nex objects, keep them,
// sort them, and delete them

class nex_creator {
    ptr_vector<nex>                              m_allocated;
    std::unordered_map<lpvar, occ>               m_occurences_map;
    std::unordered_map<lpvar, unsigned>          m_powers;
    unsigned_vector                              m_active_vars_weights;

public:
    static std::string ch(unsigned j) {
        std::stringstream s;
        s << "v" << j;        
        return s.str();
    }

    // assuming that every lpvar is less than this number
    void set_number_of_vars(unsigned k) {
        m_active_vars_weights.resize(k);
    }

    unsigned get_number_of_vars() const {
        return m_active_vars_weights.size();
    }
    
    void set_var_weight(unsigned j, unsigned weight) {
        m_active_vars_weights[j] = weight;
    }

private:
    svector<unsigned>& active_vars_weights() { return m_active_vars_weights;}
    const svector<unsigned>& active_vars_weights() const { return m_active_vars_weights;}
public:
    nex* simplify(nex* e);
    
    bool gt(lpvar j, lpvar k) const{
        unsigned wj = m_active_vars_weights[j];
        unsigned wk = m_active_vars_weights[k];
        return wj != wk ? wj > wk : j > k;
    }

    bool gt_on_nex_pow(const nex_pow & a, const nex_pow& b) const {
        return (a.pow() > b.pow()) || (a.pow() == b.pow() && gt(a.e(), b.e()));
    }
    
    void simplify_children_of_mul(vector<nex_pow> & children, rational&);

    nex * clone(const nex* a) {        
        switch (a->type()) {
        case expr_type::VAR: 
            return mk_var(to_var(a)->var());
        case expr_type::SCALAR: 
            return mk_scalar(to_scalar(a)->value());
        case expr_type::MUL: {
            auto m = to_mul(a);
            auto r = mk_mul();
            for (const auto& p : m->children()) {
                r->add_child_in_power(clone(p.e()), p.pow());
            }
            r->coeff() = m->coeff();
            return r;
        }
        case expr_type::SUM: {
            auto r = mk_sum();
            for (nex * e : *to_sum(a)) {
                r->add_child(clone(e));
            }
            return r;
        }
        default:
            UNREACHABLE();
            break;
        }
        return nullptr;
    }

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

    ~nex_creator() {
        clear();
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

    nex_mul* mk_mul(const vector<nex_pow>& v) {
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

    nex * mk_div(const nex& a, lpvar j);
    nex * mk_div(const nex& a, const nex& b);
    nex * mk_div_by_mul(const nex& a, const nex_mul& b);
    nex * mk_div_sum_by_mul(const nex_sum& a, const nex_mul& b);
    nex * mk_div_mul_by_mul(const nex_mul& a, const nex_mul& b);
    
    nex * simplify_mul(nex_mul *e);    
    bool is_sorted(const nex_mul & e) const;    

    nex* simplify_sum(nex_sum *e);

    bool is_simplified(const nex &e) const;
    bool sum_is_simplified(const nex_sum& e) const;
    bool mul_is_simplified(const nex_mul& e) const;
    
    void mul_to_powers(vector<nex_pow>& children);
    
    nex* create_child_from_nex_and_coeff(nex *e,
                                         const rational& coeff) ;

    void sort_join_sum(ptr_vector<nex> & children);
    bool fill_join_map_for_sum(ptr_vector<nex> & children,
                               std::map<nex*, rational, nex_lt>& map,
                               std::unordered_set<nex*>& existing_nex,
                               nex_scalar*& common_scalar);
    bool register_in_join_map(std::map<nex*, rational, nex_lt>&, nex*, const rational&) const;

    void simplify_children_of_sum(ptr_vector<nex> & children);
    
    bool eat_scalar_pow(rational& r, const nex_pow& p, unsigned);
    void simplify_children_of_mul(vector<nex_pow> & children, lt_on_vars, std::function<nex_scalar*()> mk_scalar);

    bool children_are_simplified(const vector<nex_pow>& children) const;
    bool gt(const nex* a, const nex* b) const;    
    bool gt_nex_powers(const vector<nex_pow>&, const nex* b) const;    
    bool gt_on_powers_mul(const vector<nex_pow>&, const nex_mul& b) const;
    template <typename T>
    bool gt_on_powers_mul_same_degree(const T&, const nex_mul& b) const;    
    bool gt_for_sort_join_sum(const nex* a, const nex* b) const;    
    bool gt_on_mul_mul(const nex_mul& a, const nex_mul& b) const;
    bool gt_on_var_nex(const nex_var* a, const nex* b) const;
    bool gt_on_mul_nex(const nex_mul* a, const nex* b) const;
    bool gt_on_sum_sum(const nex_sum* a, const nex_sum* b) const;
    void fill_map_with_children(std::map<nex*, rational, nex_lt> & m, ptr_vector<nex> & children);
    void process_map_pair(nex *e, const rational& coeff, ptr_vector<nex> & children, std::unordered_set<nex*>&);
#ifdef Z3DEBUG
    static
    bool equal(const nex*, const nex* );
    nex* canonize(const nex*);
    nex* canonize_mul(nex_mul*);
    unsigned find_sum_in_mul(const nex_mul* a) const;
#endif
};
}
