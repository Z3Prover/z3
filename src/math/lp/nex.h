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
#pragma once
#include <initializer_list>
#include "math/lp/nla_defs.h"
#include <functional>
#include <set>
namespace nla {
class nex;
typedef std::function<bool (const nex*, const nex*)> nex_lt;

typedef std::function<bool (lpvar, lpvar)> lt_on_vars;

enum class expr_type { SCALAR, VAR, SUM, MUL, UNDEF };
inline std::ostream & operator<<(std::ostream& out, expr_type t) {
    switch (t) {
    case expr_type::SUM:
        out << "SUM";
        break;
    case expr_type::MUL:
        out << "MUL";
        break;
    case expr_type::VAR:
        out << "VAR";
        break;
    case expr_type::SCALAR:
        out << "SCALAR";
        break;
    default:
        out << "NN";
        break;
    }
    return out;
}

class nex;
bool less_than_nex_standard(const nex* a, const nex* b);

// This is the class of non-linear expressions 
class nex {
public:
    virtual expr_type type() const = 0;
    virtual std::ostream& print(std::ostream&) const = 0;
    nex() {}
    bool is_elementary() const {
        switch(type()) {
        case expr_type::SUM:
        case expr_type::MUL:
            return false;        
        default:
            return true;
        }
    }

    bool is_sum() const { return type() == expr_type::SUM; }
    bool is_mul() const { return type() == expr_type::MUL; }
    bool is_var() const { return type() == expr_type::VAR; }
    bool is_scalar() const { return type() == expr_type::SCALAR; }
    virtual bool is_pure_monomial() const { return false; }
    std::string str() const { std::stringstream ss; print(ss); return ss.str(); }
    virtual ~nex() {}
    virtual bool contains(lpvar j) const { return false; }
    virtual int get_degree() const = 0;
    // simplifies the expression and also assigns the address of "this" to *e
    virtual void simplify(nex** e, nex_lt) { *e = this; }
    void simplify(nex** e) { return simplify(e, less_than_nex_standard); }
    virtual bool is_simplified(nex_lt) const {
        return true;
    }
    
    virtual bool is_simplified() const { return is_simplified(less_than_nex_standard); }

    #ifdef Z3DEBUG
    virtual void sort() {};
    #endif
    bool virtual is_linear() const = 0;
};
#if Z3DEBUG
bool operator<(const nex& a , const nex& b);
inline bool operator ==(const nex& a , const nex& b) {
    return ! (a < b || b < a) ;
}
#endif
std::ostream& operator<<(std::ostream& out, const nex&);

class nex_var : public nex {
    lpvar m_j;
public:
    nex_var(lpvar j) : m_j(j) {}
    nex_var() {}
    expr_type type() const { return expr_type::VAR; }
    lpvar var() const {  return m_j; }
    lpvar& var() {  return m_j; } // the setter
    std::ostream & print(std::ostream& out) const {
        out << 'v' <<  m_j;
        return out;
    }    

    bool contains(lpvar j) const { return j == m_j; }
    int get_degree() const { return 1; }
    bool virtual is_linear() const { return true; }
};

class nex_scalar : public nex {
    rational m_v;
public:
    nex_scalar(const rational& v) : m_v(v) {}
    nex_scalar() {}
    expr_type type() const { return expr_type::SCALAR; }
    const rational& value() const {  return m_v; }
    rational& value() {  return m_v; } // the setter
    std::ostream& print(std::ostream& out) const {
        out << m_v;
        return out;
    }
    
    int get_degree() const { return 0; }
    bool is_linear() const { return true; }

};

const nex_scalar * to_scalar(const nex* a);
class nex_sum;
const nex_sum* to_sum(const nex*a);

void promote_children_of_sum(ptr_vector<nex> & children, nex_lt);
class nex_pow;
void promote_children_of_mul(vector<nex_pow> & children, nex_lt);

class nex_pow {
    nex* m_e;
    int  m_power;
public:
    explicit nex_pow(nex* e): m_e(e), m_power(1) {}
    explicit nex_pow(nex* e, int p): m_e(e), m_power(p) {}
    const nex * e() const { return m_e; }
    nex * e() { return m_e; }
    nex ** ee() { return & m_e; }
    int pow() const { return m_power; }
    int& pow() { return m_power; }
    std::string to_string() const {
        std::stringstream s;
        if (pow() == 1) {           
            s <<"(" <<  *e() << ")";
        } else {
            s << "(" << *e() << "^" << pow() << ")";
        }
        return s.str();
    }
    friend std::ostream& operator<<(std::ostream& out, const nex_pow & p) { out << p.to_string(); return out; }
};


inline bool less_than(const nex_pow & a, const nex_pow& b, nex_lt lt) {
    return (a.pow() < b.pow()) || (a.pow() == b.pow() && lt(a.e(), b.e()));
}


class nex_mul : public nex {
    vector<nex_pow> m_children;
public:
    nex_mul()  {}
    unsigned size() const { return m_children.size(); }
    expr_type type() const { return expr_type::MUL; }
    vector<nex_pow>& children() { return m_children;}
    const vector<nex_pow>& children() const { return m_children;}
    // A monomial is 'pure' if does not have a numeric coefficient.
    bool is_pure_monomial() const { return size() == 0 || (!m_children[0].e()->is_scalar()); }    
    std::ostream & print(std::ostream& out) const {
        
        bool first = true;
        for (const nex_pow& v : m_children) {            
            std::string s = v.to_string();
            if (first) {
                first = false;
                out << s;
            } else {
                out << "*" << s;                        
            }
        }
        return out;
    }

    void add_child(nex* e) {
        add_child_in_power(e, 1);
    }
    
    void add_child_in_power(nex* e, int power) { m_children.push_back(nex_pow(e, power)); }

    bool contains(lpvar j) const {
        for (const nex_pow& c : children()) {
            if (c.e()->contains(j))
                return true;
        }
        return false;
    }

    static const nex_var* to_var(const nex*a) {
        SASSERT(a->is_var());
        return static_cast<const nex_var*>(a);
    }

    void get_powers_from_mul(std::unordered_map<lpvar, unsigned> & r) const {
        TRACE("nla_cn_details", tout << "powers of " << *this << "\n";);
        r.clear();
        for (const auto & c : children()) {
            if (!c.e()->is_var()) {
                continue;
            }
            lpvar j = to_var(c.e())->var();
            SASSERT(r.find(j) == r.end());
            r[j] = c.pow();
        }
        TRACE("nla_cn_details", tout << "powers of " << *this << "\n"; print_vector(r, tout)<< "\n";);
    }

    int get_degree() const {
        int degree = 0;       
        for (const auto& p : children()) {
            degree +=  p.e()->get_degree() * p.pow();
        }
        return degree;
    }
    // the second argument is the comparison less than operator
    void simplify(nex **e, nex_lt lt) {
        TRACE("nla_cn_details", tout << *this << "\n";);
        TRACE("nla_cn_details", tout << "**e = " << **e << "\n";);
        *e = this;
        TRACE("nla_cn_details", tout << *this << "\n";);
        promote_children_of_mul(m_children, lt);
        if (size() == 1 && m_children[0].pow() == 1) 
            *e = m_children[0].e();
        TRACE("nla_cn_details", tout << *this << "\n";);
        SASSERT((*e)->is_simplified(lt));
    }

    bool is_sorted(nex_lt lt) const {
        for (unsigned j = 0; j < m_children.size() - 1; j++) {
            if (!(less_than(m_children[j], m_children[j+1], lt)))
                return false;
        }
        return true;
    }
    
    virtual bool is_simplified(nex_lt lt) const {
        if (size() == 1 && m_children.begin()->pow() == 1)
            return false;
        std::set<const nex*, nex_lt> s(lt);
        for (const auto &p : children()) {
            const nex* e = p.e();
            if (p.pow() == 0)
                return false;
            if (e->is_mul()) 
                return false;
            if (e->is_scalar() && to_scalar(e)->value().is_one())
                return false;

            auto it = s.find(e);
            if (it == s.end()) {
                s.insert(e);
            } else {
                TRACE("nla_cn_details", tout << "not simplified " << *e << "\n";);
                return false;
            }
        }
        return is_sorted(lt);
    }

    bool is_linear() const {
        //        SASSERT(is_simplified());
        return get_degree() < 2; // todo: make it more efficient
    }

// #ifdef Z3DEBUG
//     virtual void sort() {
//         for (nex * c : m_children) {
//             c->sort();
//         }
//         std::sort(m_children.begin(), m_children.end(), [](const nex* a, const nex* b) { return *a < *b; });
//     }
//     #endif

};


class nex_sum : public nex {
    ptr_vector<nex> m_children;
public:
    nex_sum()  {}
    expr_type type() const { return expr_type::SUM; }
    ptr_vector<nex>& children() { return m_children;}
    const ptr_vector<nex>& children() const { return m_children;}    
    const ptr_vector<nex>* children_ptr() const { return &m_children;}
    ptr_vector<nex>* children_ptr() { return &m_children;}
    unsigned size() const { return m_children.size(); }


    bool is_linear() const {
        TRACE("nex_details", tout << *this << "\n";);
        for (auto  e : children()) {
            if (!e->is_linear())
                return false;
        }
        TRACE("nex_details", tout << "linear\n";); 
        return true;
    }

    // we need a linear combination of at least two variables
    bool is_a_linear_term() const {
        TRACE("nex_details", tout << *this << "\n";);
        unsigned number_of_non_scalars = 0;
        for (auto  e : children()) {
            int d = e->get_degree();
            if (d == 0) continue;
            if (d > 1) return false;
            
            number_of_non_scalars++;
        }
        TRACE("nex_details", tout << (number_of_non_scalars > 1?"linear":"non-linear") << "\n";); 
        return number_of_non_scalars > 1;
    }
    
    std::ostream & print(std::ostream& out) const {
        bool first = true;
        for (const nex* v : m_children) {            
            std::string s = v->str();
            if (first) {
                first = false;
                if (v->is_elementary())
                    out << s;
                else 
                    out << "(" << s << ")";                            
            } else {
                if (v->is_elementary()) {
                    if (s[0] == '-') {
                        out << s;
                    } else {
                        out << "+" << s;
                    }
                } else {
                    out << "+" <<  "(" << s << ")";
                }
            }
        }
        return out;
    }

    void simplify(nex **e, nex_lt lt ) {
        *e = this;
        promote_children_of_sum(m_children, lt);
        if (size() == 1)
            *e = m_children[0];
    }
    
    virtual bool is_simplified() const {
        if (size() < 2) return false;
        for (nex * e : children()) {
            if (e->is_sum())
                return false;
            if (e->is_scalar() && to_scalar(e)->value().is_zero())
                return false;
        }
        return true;
    }
    
    int get_degree() const {
        int degree = 0;       
        for (auto  e : children()) {
            degree = std::max(degree, e->get_degree());
        }
        return degree;
    }
    
    void add_child(nex* e) { m_children.push_back(e); }
#ifdef Z3DEBUG
    virtual void sort() {
        NOT_IMPLEMENTED_YET();
        /*
        for (nex * c : m_children) {
            c->sort();
        }
        

        std::sort(m_children.begin(), m_children.end(), [](const nex* a, const nex* b) { return *a < *b; });
        */
    }
#endif
};

inline const nex_sum* to_sum(const nex*a) {
    SASSERT(a->is_sum());
    return static_cast<const nex_sum*>(a);
}

inline nex_sum* to_sum(nex * a) {
    SASSERT(a->is_sum());
    return static_cast<nex_sum*>(a);
}

    
inline const nex_var* to_var(const nex*a)  {
    SASSERT(a->is_var());
    return static_cast<const nex_var*>(a);
}

inline const nex_scalar* to_scalar(const nex*a)  {
    SASSERT(a->is_scalar());
    return static_cast<const nex_scalar*>(a);
}

inline const nex_mul* to_mul(const nex*a) {
    SASSERT(a->is_mul());
    return static_cast<const nex_mul*>(a);
}

inline nex_mul* to_mul(nex*a) {
    SASSERT(a->is_mul());
    return static_cast<nex_mul*>(a);
}

inline std::ostream& operator<<(std::ostream& out, const nex& e ) {
    return e.print(out);
}


inline bool less_than_nex(const nex* a, const nex* b, lt_on_vars lt) {
    int r = (int)(a->type()) - (int)(b->type());
    if (r) {
        return r < 0;
    }
    // here a and b have the same type
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

inline bool less_than_nex_standard(const nex* a, const nex* b) {
    return less_than_nex(a, b, [](lpvar j, lpvar k) { return j < k; });
}

#if Z3DEBUG

inline bool operator<(const ptr_vector<nex>&a , const ptr_vector<nex>& b) {
    int r = (int)a.size()  - (int)b.size();
    if (r)
        return r < 0;
    for (unsigned j = 0; j < a.size(); j++) {
        if (*a[j] < *b[j]) {
            return true;
        }
        if (*b[j] < *a[j]) {
            return false;
        }
    }
    return false;
}

#endif

}
    
