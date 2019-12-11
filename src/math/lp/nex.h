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

// forward definitions

class nex;
class nex_scalar;
class nex_pow; 
class nex_mul;
class nex_var;
class nex_sum;

// This is the class of non-linear expressions 

class nex {
public:
    // the scalar and the variable have size 1
    virtual unsigned size() const { return 1; }
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
    nex_mul& to_mul();
    nex_mul const& to_mul() const;

    nex_sum& to_sum();
    nex_sum const& to_sum() const;

    nex_var& to_var();
    nex_var const& to_var() const;

    nex_scalar& to_scalar();
    nex_scalar const& to_scalar() const;

    virtual unsigned number_of_child_powers() const { return 0; }    
    virtual const nex* get_child_exp(unsigned) const { return this; }
    virtual unsigned get_child_pow(unsigned) const { return 1; }
    virtual bool all_factors_are_elementary() const { return true; }
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
    virtual const rational& coeff() const { return rational::one(); }

    #ifdef Z3DEBUG
    virtual void sort() {};
    #endif
    bool virtual is_linear() const = 0;
};

std::ostream& operator<<(std::ostream& out, const nex&);

class nex_var : public nex {
    lpvar m_j;
public:
    unsigned number_of_child_powers() const { return 1; }
    nex_pow get_nex_pow(unsigned j);
    nex_var(lpvar j) : m_j(j) {}
    nex_var() {}
    expr_type type() const { return expr_type::VAR; }
    lpvar var() const {  return m_j; }
    lpvar& var() {  return m_j; } // the setter
    std::ostream & print(std::ostream& out) const {
        //        out <<  (char)('a' + m_j);
        return out << "v" << m_j;
    }    

    bool contains(lpvar j) const { return j == m_j; }
    int get_degree() const { return 1; }
    bool is_linear() const override { return true; }
};

class nex_scalar : public nex {
    rational m_v;
public:
    nex_scalar(const rational& v) : m_v(v) {}
    nex_scalar() {}
    expr_type type() const { return expr_type::SCALAR; }
    const rational& value() const {  return m_v; }
    rational& value() {  return m_v; } // the setter
    std::ostream& print(std::ostream& out) const { return out << m_v; }
    
    int get_degree() const { return 0; }
    bool is_linear() const { return true; }
};

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

    std::ostream& print(std::ostream& s) const {
        if (pow() == 1) {
            if (e()->is_elementary()) {
                s << *e();
            } else {
                s <<"(" <<  *e() << ")";
            }
        } 
        else {
            if (e()->is_elementary()){
                s << "(" << *e() << "^" << pow() << ")";
            } else {
                s << "((" << *e() << ")^" << pow() << ")";
            }
        }
        return s;
    }
    std::string to_string() const {
        std::stringstream s;
        print(s);
        return s.str();
    }
    friend std::ostream& operator<<(std::ostream& out, const nex_pow & p) { return p.print(out); }
};

inline unsigned get_degree_children(const vector<nex_pow>& children) {
    int degree = 0;       
    for (const auto& p : children) {
        degree +=  p.e()->get_degree() * p.pow();
    }
    return degree;
}

class nex_mul : public nex {
    rational        m_coeff;
    vector<nex_pow> m_children;
public:
    const nex* get_child_exp(unsigned j) const override { return m_children[j].e(); }
    unsigned get_child_pow(unsigned j) const override { return m_children[j].pow(); }

    unsigned number_of_child_powers() const { return m_children.size(); }

    nex_mul() : m_coeff(rational(1)) {}

    const rational& coeff() const {
        return m_coeff;
    }

    rational& coeff() {
        return m_coeff;
    }
    
    unsigned size() const { return m_children.size(); }
    expr_type type() const { return expr_type::MUL; }
    vector<nex_pow>& children() { return m_children;}
    const vector<nex_pow>& children() const { return m_children;}
    // A monomial is 'pure' if does not have a numeric coefficient.
    bool is_pure_monomial() const { return size() == 0 || (!m_children[0].e()->is_scalar()); }    

    std::ostream & print(std::ostream& out) const {        
        bool first = true;
        if (!m_coeff.is_one()) {
            out << m_coeff;
            first = false;
        }
        for (const nex_pow& v : m_children) {            
            if (first) {
                first = false;
                out << v;
            } else {
                out << "*" << v;                        
            }
        }
        return out;
    }

    void add_child(const rational& r) {
        m_coeff *= r;
    }
    
    void add_child(nex* e) {
        if (e->is_scalar()) {
            m_coeff *= e->to_scalar().value();
            return;
        }
        add_child_in_power(e, 1);
    }

    void add_child_in_power(nex_pow&  p) {
        add_child_in_power(p.e(), p.pow());
    }


    const nex_pow& operator[](unsigned j) const { return m_children[j]; }
    nex_pow& operator[](unsigned j) { return m_children[j]; }
    const nex_pow* begin() const { return m_children.begin(); }
    const nex_pow* end() const { return m_children.end(); }
    nex_pow* begin() { return m_children.begin(); }
    nex_pow* end() { return m_children.end(); }
    
    void add_child_in_power(nex* e, int power) {        
        if (e->is_scalar()) {
            m_coeff *= (e->to_scalar().value()).expt(power);
        }
        else {
            m_children.push_back(nex_pow(e, power));
        }
    }

    bool contains(lpvar j) const {
        for (const nex_pow& c : *this) {
            if (c.e()->contains(j))
                return true;
        }
        return false;
    }

    void get_powers_from_mul(std::unordered_map<lpvar, unsigned> & r) const {
        TRACE("nla_cn_details", tout << "powers of " << *this << "\n";);
        r.clear();
        for (const auto & c : *this) {
            if (!c.e()->is_var()) {
                continue;
            }
            lpvar j = c.e()->to_var().var();
            SASSERT(r.find(j) == r.end());
            r[j] = c.pow();
        }
        TRACE("nla_cn_details", tout << "powers of " << *this << "\n"; print_vector(r, tout)<< "\n";);
    }

    int get_degree() const {
        return get_degree_children(children());
    }    
    
    bool is_linear() const {
        return get_degree() < 2; // todo: make it more efficient
    }

     bool all_factors_are_elementary() const;

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
    void sort() override {
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

inline nex_sum& nex::to_sum() { SASSERT(is_sum()); return *static_cast<nex_sum*>(this); }
inline nex_sum const& nex::to_sum() const { SASSERT(is_sum()); return *static_cast<nex_sum const*>(this); }
inline nex_var& nex::to_var() { SASSERT(is_var()); return *static_cast<nex_var*>(this); }
inline nex_var const& nex::to_var() const { SASSERT(is_var()); return *static_cast<nex_var const*>(this); }
inline nex_mul& nex::to_mul() { SASSERT(is_mul()); return *static_cast<nex_mul*>(this); }
inline nex_mul const& nex::to_mul() const { SASSERT(is_mul()); return *static_cast<nex_mul const*>(this); }
inline nex_scalar& nex::to_scalar() { SASSERT(is_scalar()); return *static_cast<nex_scalar*>(this); }
inline nex_scalar const& nex::to_scalar() const { SASSERT(is_scalar()); return *static_cast<nex_scalar const*>(this); }

inline const nex_sum* to_sum(const nex* a) { return &(a->to_sum()); }
inline nex_sum* to_sum(nex * a) { return &(a->to_sum()); }
inline const nex_var* to_var(const nex* a) { return &(a->to_var()); }
inline nex_var* to_var(nex * a) { return &(a->to_var()); }
inline const nex_scalar* to_scalar(const nex* a) { return &(a->to_scalar()); }
inline nex_scalar* to_scalar(nex * a) { return &(a->to_scalar()); }
inline const nex_mul* to_mul(const nex* a) { return &(a->to_mul()); }
inline nex_mul* to_mul(nex * a) { return &(a->to_mul()); }
    

inline std::ostream& operator<<(std::ostream& out, const nex& e ) {
    return e.print(out);
}

// inline bool less_than_nex_standard(const nex* a, const nex* b) {
//     lt_on_vars lt = [](lpvar j, lpvar k) { return j < k; };
//     return less_than_nex(a, b, lt);
// }

inline rational get_nex_val(const nex* e, std::function<rational (unsigned)> var_val) {
    switch (e->type()) {
    case expr_type::SCALAR:
        return to_scalar(e)->value();
    case expr_type::SUM: {
        rational r(0);
        for (auto c: *to_sum(e)) {
            r += get_nex_val(c, var_val);
        }
        return r;
    }
    case expr_type::MUL: {
        auto & m = *to_mul(e);
        rational t = m.coeff();
        for (auto& c: m)
            t *= get_nex_val(c.e(), var_val).expt(c.pow());
        return t;
    }
    case expr_type::VAR:
        return var_val(to_var(e)->var());
    default:
        TRACE("nla_cn_details", tout << e->type() << "\n";);
        SASSERT(false);
        return rational();
    }
}

inline std::unordered_set<lpvar> get_vars_of_expr(const nex *e ) {
    std::unordered_set<lpvar> r;
    switch (e->type()) {
    case expr_type::SCALAR:
        return r;
    case expr_type::SUM: {
        for (auto c: *to_sum(e))
            for ( lpvar j : get_vars_of_expr(c))
                r.insert(j);
        return r;
    }
    case expr_type::MUL: {
        for (auto &c: *to_mul(e))
            for ( lpvar j : get_vars_of_expr(c.e()))
                r.insert(j);
        return r;
    }
    case expr_type::VAR:
        r.insert(to_var(e)->var());
        return r;
    default:
        TRACE("nla_cn_details", tout << e->type() << "\n";);
        SASSERT(false);
        return r;
    }
}

inline bool is_zero_scalar(nex *e) {
    return e->is_scalar() && to_scalar(e)->value().is_zero();
}
}
    
