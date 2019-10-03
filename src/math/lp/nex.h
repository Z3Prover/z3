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

class nex_scalar;
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
      

    #ifdef Z3DEBUG
    virtual void sort() {};
    #endif
    bool virtual is_linear() const = 0;
};

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
        out <<  (char)('a' + m_j);
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

class nex_pow {
    nex* m_e;
    int  m_power;
public:
    explicit nex_pow(nex* e): m_e(e), m_power(1) {}
    explicit nex_pow(nex* e, int p): m_e(e), m_power(p) {}
    const nex * e() const { return m_e; }
    nex *& e() { return m_e; }
    
    nex ** ee() { return & m_e; }
    int pow() const { return m_power; }
    int& pow() { return m_power; }
    std::string to_string() const {
        std::stringstream s;
        if (pow() == 1) {
            if (e()->is_elementary()) {
                s << *e();
            } else {
                s <<"(" <<  *e() << ")";
            }
        } else {
            if (e()->is_elementary()){
                s << "(" << *e() << "^" << pow() << ")";
            } else {
                s << "((" << *e() << ")^" << pow() << ")";
            }
        }
        return s.str();
    }
    friend std::ostream& operator<<(std::ostream& out, const nex_pow & p) { out << p.to_string(); return out; }
};

bool less_than_nex(const nex* a, const nex* b, const lt_on_vars& lt);



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

    // returns true if the product of scalars gives a number different from 1
    bool has_a_coeff() const {
        rational r(1);
        for (auto & p : *this) {
            if (p.e()->is_scalar())
                r *= to_scalar(p.e())->value();
        }
        return !r.is_one();
    }

    const nex_pow& operator[](unsigned j) const { return m_children[j]; }
    nex_pow& operator[](unsigned j) { return m_children[j]; }
    const nex_pow* begin() const { return m_children.begin(); }
    const nex_pow* end() const { return m_children.end(); }
    nex_pow* begin() { return m_children.begin(); }
    nex_pow* end() { return m_children.end(); }
    
    void add_child_in_power(nex* e, int power) { m_children.push_back(nex_pow(e, power)); }

    bool contains(lpvar j) const {
        for (const nex_pow& c : *this) {
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
        for (const auto & c : *this) {
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
        for (const auto& p : *this) {
            degree +=  p.e()->get_degree() * p.pow();
        }
        return degree;
    }

    bool is_linear() const {
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
        for (auto  e : *this) {
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
        for (auto  e : *this) {
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

    int get_degree() const {
        int degree = 0;       
        for (auto  e : *this) {
            degree = std::max(degree, e->get_degree());
        }
        return degree;
    }
    const nex* operator[](unsigned j) const { return m_children[j]; }
    nex*& operator[](unsigned j) { return m_children[j]; }
    const ptr_vector<nex>::const_iterator begin() const { return m_children.begin(); }
    const ptr_vector<nex>::const_iterator end() const { return m_children.end(); }
    ptr_vector<nex>::iterator begin() { return m_children.begin(); }
    ptr_vector<nex>::iterator end() { return m_children.end(); }

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

inline nex_scalar* to_scalar(nex*a)  {
    SASSERT(a->is_scalar());
    return static_cast<nex_scalar*>(a);
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

inline bool less_than_nex_standard(const nex* a, const nex* b) {
    lt_on_vars lt = [](lpvar j, lpvar k) { return j < k; };
    return less_than_nex(a, b, lt);
}

inline std::unordered_set<lpvar> get_vars_of_expr(const nex *e ) {
        std::unordered_set<lpvar> r;
        switch (e->type()) {
        case expr_type::SCALAR:
            return r;
        case expr_type::SUM:
            {
                for (auto c: *to_sum(e))
                    for ( lpvar j : get_vars_of_expr(c))
                        r.insert(j);
            }
        case expr_type::MUL:
            {
                for (auto &c: *to_mul(e))
                    for ( lpvar j : get_vars_of_expr(c.e()))
                        r.insert(j);
            }
            return r;
        case expr_type::VAR:
            r.insert(to_var(e)->var());
            return r;
        default:
            TRACE("nla_cn_details", tout << e->type() << "\n";);
            SASSERT(false);
            return r;
        }
    }
}
    
