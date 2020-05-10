/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
   Lev Nachmanson (levnach)
   Nikolaj Bjorner (nbjorner)
  --*/
#pragma once
#include <map>
#include <set>
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
        s << "j" << j;
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
    svector<unsigned>& active_vars_weights() { return m_active_vars_weights; }
    const svector<unsigned>& active_vars_weights() const { return m_active_vars_weights; }

    nex_mul* mk_mul(const vector<nex_pow>& v) {
        auto r = alloc(nex_mul, rational::zero(), v);
        add_to_allocated(r);
        return r;
    }

    void mul_args() { }

    template <typename K>
    void mul_args(K e) { 
        m_mk_mul *= e;
    }
    
    template <typename K, typename ...Args>
    void mul_args(K e, Args ...  es) {   
        m_mk_mul *= e;
        mul_args(es...);
    }

    template <typename T>
    void add_sum(T) { }
    
    template <typename T, typename K, typename ...Args>
    void add_sum(T& r, K e, Args ...  es) {      
        r += e;
        add_sum(r, es ...);
    }



public:
    nex* simplify(nex* e);

    bool gt(lpvar j, lpvar k) const {
        unsigned wj = m_active_vars_weights[j];
        unsigned wk = m_active_vars_weights[k];
        return wj != wk ? wj > wk : j > k;
    }
   
    void simplify_children_of_mul(vector<nex_pow>& children, rational&);

    nex* clone(const nex* a) {
        switch (a->type()) {
        case expr_type::VAR:
            return mk_var(to_var(a)->var());
        case expr_type::SCALAR:
            return mk_scalar(to_scalar(a)->value());
        case expr_type::MUL: {
            mul_factory mf(*this);
            for (const auto& p : a->to_mul()) {
                mf *= nex_pow(clone(p.e()), p.pow());
            }
            mf *= a->to_mul().coeff();
            return mf.mk();
        }
        case expr_type::SUM: {
            sum_factory sf(*this);
            for (nex const* e : a->to_sum()) {
                sf += clone(e);
            }
            return sf.mk();
        }
        default:
            UNREACHABLE();
            break;
        }
        return nullptr;
    }

    const std::unordered_map<lpvar, occ>& occurences_map() const { return m_occurences_map; }
    std::unordered_map<lpvar, occ>& occurences_map() { return m_occurences_map; }
    const std::unordered_map<lpvar, unsigned>& powers() const { return m_powers; }
    std::unordered_map<lpvar, unsigned>& powers() { return m_powers; }

    void add_to_allocated(nex* r) {
        m_allocated.push_back(r);
        CTRACE("grobner_stats_d", m_allocated.size() % 1000 == 0, tout << "m_allocated.size() = " << m_allocated.size() << "\n";);
    }

    // NSB: we can use region allocation, but still need to invoke destructor 
    // because of 'rational' (and m_children in nex_mul unless we get rid of this)
    void pop(unsigned sz) {
        for (unsigned j = sz; j < m_allocated.size(); j++)
            dealloc(m_allocated[j]);
        m_allocated.resize(sz);
        TRACE("grobner_stats_d", tout << "m_allocated.size() = " << m_allocated.size() << "\n";);
    }

    void clear() {
        for (auto e : m_allocated)
            dealloc(e);
        m_allocated.clear();
    }

    nex_creator() : m_mk_mul(*this) {}

    ~nex_creator() {
        clear();
    }
    unsigned size() const { return m_allocated.size(); }
    
    class mul_factory {
        nex_creator& c;
        rational m_coeff;
        vector<nex_pow> m_args;
    public:
        mul_factory(nex_creator& c) :c(c), m_coeff(1) {}
        void reset() { m_coeff = rational::one();  m_args.reset();  }
        void operator*=(rational const& coeff) { m_coeff *= coeff;  }
        void operator*=(nex_pow const& p) { m_args.push_back(p); }
        void operator*=(nex const* n) { m_args.push_back(nex_pow(n, 1)); }
        bool empty() const { return m_args.empty(); }
        nex_mul* mk() {
            auto r = alloc(nex_mul, m_coeff, m_args);
            c.add_to_allocated(r); 
            return r;  
        }
        nex* mk_reduced() {
            if (m_args.empty()) return c.mk_scalar(m_coeff);
            if (m_coeff.is_one() && m_args.size() == 1 && m_args[0].pow() == 1) return m_args[0].e();
            return mk();
        }
    };

    class sum_factory {
        nex_creator& c;
        ptr_vector<nex> m_args;
    public:
        sum_factory(nex_creator& c) :c(c) {}
        void reset() { m_args.reset();  }
        void operator+=(nex const* n) { m_args.push_back(const_cast<nex*>(n)); }
        void operator+=(nex* n) { m_args.push_back(n); }
        bool empty() const { return m_args.empty(); }
        nex_sum* mk() { return c.mk_sum(m_args);  }
    };

    mul_factory m_mk_mul;

    nex_sum* mk_sum() {
        ptr_vector<nex> v0;
        return mk_sum(v0);
    }

    nex_sum* mk_sum(const ptr_vector<nex>& v) {  
        auto r = alloc(nex_sum, v);
        add_to_allocated(r);
        return r;
    }
    
    template <typename K, typename...Args>
    nex_sum* mk_sum(K e, Args... es) {
        sum_factory sf(*this);
        sf += e;
        add_sum(sf, es...);
        return sf.mk();
    }

    nex_var* mk_var(lpvar j) {
        auto r = alloc(nex_var, j);
        add_to_allocated(r);
        return r;
    }
    
    nex_mul* mk_mul() {
        auto r = alloc(nex_mul);
        add_to_allocated(r);
        return r;
    }

    template <typename K, typename...Args>
    nex_mul* mk_mul(K e, Args... es) {
        m_mk_mul.reset();    
        m_mk_mul *= e;
        mul_args(es...);
        return m_mk_mul.mk();
    }
    
    nex_scalar* mk_scalar(const rational& v) {
        auto r = alloc(nex_scalar, v);
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
    
    void sort_join_sum(nex_sum & sum);
    bool fill_join_map_for_sum(nex_sum & sum,
                               std::map<nex const*, rational, nex_lt>& map,
                               std::unordered_set<nex const*>& existing_nex,
                               rational& common_scalar);
    bool register_in_join_map(std::map<nex const*, rational, nex_lt>&, nex const*, const rational&) const;

    void simplify_children_of_sum(nex_sum & sum);
    
    bool eat_scalar_pow(rational& r, const nex_pow& p, unsigned);
    bool gt(const nex& a, const nex& b) const; 
    bool gt(const nex* a, const nex* b) const { return gt(*a, *b); }
    template <typename T>
    bool gt_on_powers_mul_same_degree(const T&, const nex_mul& b) const;    
    bool gt_for_sort_join_sum(const nex* a, const nex* b) const;    
    bool gt_on_mul_mul(const nex_mul& a, const nex_mul& b) const;    
    bool gt_on_sum_sum(const nex_sum& a, const nex_sum& b) const;
    bool gt_on_var_nex(const nex_var& a, const nex& b) const;
    bool gt_on_mul_nex(nex_mul const&, const nex& b) const;
    // just compare the underlying expressions
    bool gt_on_nex_pow(const nex_pow& a, const nex_pow& b) const {
        return gt(a.e(), b.e());
    }
    void process_map_pair(nex*e, const rational& coeff, nex_sum & sum, std::unordered_set<nex const*>&);
    static bool equal(const nex*, const nex* );
    nex* canonize(const nex*);
    nex* canonize_mul(nex_mul*);
    unsigned find_sum_in_mul(const nex_mul* a) const;
};
}
