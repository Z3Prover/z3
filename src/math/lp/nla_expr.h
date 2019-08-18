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
namespace nla {
enum class expr_type { VAR, SUM, MUL, SCALAR, UNDEF };
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
    case expr_type::UNDEF:
        out << "UNDEF";
        break;
    default:
        out << "NN";
        break;
    }
    return out;
}


// This class is needed in horner calculation with intervals
class nex {
public:
    virtual expr_type type() const = 0;
    virtual std::ostream& print(std::ostream&) const = 0;
    nex() {}
    bool is_simple() const {
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
    std::string str() const { std::stringstream ss; print(ss); return ss.str(); }
    virtual ~nex() {}
    virtual bool contains(lpvar j) const { return false; }
    virtual int get_degree() const = 0;
    virtual void simplify() {}
    virtual const ptr_vector<nex> * children_ptr() const {
        UNREACHABLE();
        return nullptr;
    }
    virtual ptr_vector<nex> * children_ptr() {
        UNREACHABLE();
        return nullptr;
    }
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
        out << 'v' <<  m_j;
        return out;
    }    

    bool contains(lpvar j) const { return j == m_j; }
    int get_degree() const { return 1; }
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

};

static void promote_children_by_type(ptr_vector<nex> * children, expr_type t) {
    ptr_vector<nex> to_promote;
    for(unsigned j = 0; j < children->size(); j++) {
        nex* e = (*children)[j];
        e->simplify();
        if (e->type() == t) {
            to_promote.push_back(e);
        } else {
            unsigned offset = to_promote.size();
            if (offset) {
                (*children)[j - offset] = e;
            }
        }
    }
    
    for (nex *e : to_promote) {
        for (nex *ee : *(e->children_ptr())) {
            children->push_back(ee);
        }
    }    
}

class nex_mul : public nex {
    ptr_vector<nex> m_children;
public:
    nex_mul()  {}
    unsigned size() const { return m_children.size(); }
    expr_type type() const { return expr_type::MUL; }
    ptr_vector<nex>& children() { return m_children;}
    const ptr_vector<nex>& children() const { return m_children;}
    const ptr_vector<nex>* children_ptr() const { return &m_children;}
    ptr_vector<nex>* children_ptr() { return &m_children;}
    
    std::ostream & print(std::ostream& out) const {
        bool first = true;
        for (const nex* v : m_children) {            
            std::string s = v->str();
            if (first) {
                first = false;
                if (v->is_simple())
                    out << s;
                else 
                    out << "(" << s << ")";                            
            } else {
                if (v->is_simple()) {
                    if (s[0] == '-') {
                        out << "*(" << s << ")";
                    } else {
                        out << "*" << s;
                    }
                } else {
                    out << "*(" << s << ")";
                }
            }
        }
        return out;
    }

    void add_child(nex* e) { m_children.push_back(e); }

    bool contains(lpvar j) const {
        for (const nex* c : children()) {
            if (c->contains(j))
                return true;
        }
        return false;
    }

    static const nex_var* to_var(const nex*a) {
        SASSERT(a->is_var());
        return static_cast<const nex_var*>(a);
    }

    void get_powers_from_mul(std::unordered_map<lpvar, unsigned> & r) const {
        r.clear();
        for (const auto & c : children()) {
            if (!c->is_var()) {
                continue;
            }
            lpvar j = to_var(c)->var();
            auto it = r.find(j);
            if (it == r.end()) {
                r[j] = 1;
            } else {
                it->second++;
            }
        }
        TRACE("nla_cn_details", tout << "powers of " << *this << "\n"; print_vector(r, tout)<< "\n";);
    }

    int get_degree() const {
        int degree = 0;       
        for (auto  e : children()) {
            degree +=  e->get_degree();
        }
        return degree;
    }
    
    void simplify() {
        promote_children_by_type(&m_children, expr_type::MUL);
    }

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
                if (v->is_simple())
                    out << s;
                else 
                    out << "(" << s << ")";                            
            } else {
                if (v->is_simple()) {
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

    void simplify() {
        promote_children_by_type(&m_children, expr_type::SUM);
    }
    
    int get_degree() const {
        int degree = 0;       
        for (auto  e : children()) {
            degree = std::max(degree, e->get_degree());
        }
        return degree;
    }
    
    void add_child(nex* e) { m_children.push_back(e); }
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

inline const nex_mul* to_mul(const nex*a) {
    SASSERT(a->is_mul());
    return static_cast<const nex_mul*>(a);
}

inline nex_mul* to_mul(nex*a) {
    SASSERT(a->is_mul());
    return static_cast<nex_mul*>(a);
}

inline const nex_scalar * to_scalar(const nex* a) {
    SASSERT(a->is_scalar());
    return static_cast<const nex_scalar*>(a);
}

inline std::ostream& operator<<(std::ostream& out, const nex& e ) {
    return e.print(out);
}


}
    
