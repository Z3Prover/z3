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
enum class expr_type { SUM, MUL, VAR, SCALAR, UNDEF };
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
template <typename T>
class nla_expr {
    // todo: use union
    expr_type       m_type;
    lpvar           m_j;
    T             m_v; // for the scalar
    vector<nla_expr> m_children;
public:
    bool is_sum() const { return m_type == expr_type::SUM; }
    bool is_var() const { return m_type == expr_type::VAR; }
    bool is_mul() const { return m_type == expr_type::MUL; }
    bool is_undef() const { return m_type == expr_type::UNDEF; }
    lpvar var() const { SASSERT(m_type == expr_type::VAR); return m_j; }
    expr_type type() const { return m_type; }
    expr_type& type() { return m_type; }
    const vector<nla_expr>& children() const { return m_children; }
    vector<nla_expr>& children() { return m_children; }
    const T& value() const { SASSERT(m_type == expr_type::SCALAR); return m_v; }
    std::string str() const { std::stringstream ss; ss << *this; return ss.str(); }
    std::ostream & print_sum(std::ostream& out) const {
        bool first = true;
        for (const nla_expr& v : m_children) {
            std::string s = v.str();
            if (first) {
                first = false;
                if (v.is_simple())
                    out << v;
                else 
                    out << "(" << s << ")";                            
            } else {
                if (v.is_simple()) {
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
    std::ostream & print_mul(std::ostream& out) const {
        bool first = true;
        for (const nla_expr& v : m_children) {
            std::string s = v.str();
            if (first) {
                first = false;
                if (v.is_simple())
                    out << s;
                else 
                    out << "(" << s << ")";                            
            } else {
                if (v.is_simple()) {
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
    std::ostream & print(std::ostream& out) const {
        switch(m_type) {
        case expr_type::SUM:
            return print_sum(out);
        case expr_type::MUL:
            return print_mul(out);
        case expr_type::VAR:
            out << static_cast<char>('a'+m_j);
            return out;
        case expr_type::SCALAR:
            out << m_v;
            return out;
        default:
            out << "undef";
            return out;
        }
    }

    bool is_simple() const {
        switch(m_type) {
        case expr_type::SUM:
        case expr_type::MUL:
            return m_children.size() <= 1;
        
        default:
            return true;
        }
    }

    unsigned size() {
        switch(m_type) {
        case expr_type::SUM:
        case expr_type::MUL:
            return m_children.size();
        
        default:
            return 1;
        }
    }
    nla_expr(expr_type t): m_type(t) {}
    nla_expr(): m_type(expr_type::UNDEF) {}
    
    void add_child(const nla_expr& e) {
        m_children.push_back(e);
    }

    void add_child(const T& k) {
        m_children.push_back(scalar(k));
    }

    void add_children() { }

    template <typename K, typename ...Args>
    void add_children(K e, Args ...  es) {
        add_child(e);
        add_children(es ...);
    }

    template <typename K, typename ... Args>
    static nla_expr sum(K e, Args ... es) {
        nla_expr r(expr_type::SUM);
        r.add_children(e, es...);
        return r;
    }

    template <typename K, typename ... Args>
    static nla_expr mul(K e, Args ... es) {
        nla_expr r(expr_type::MUL);
        r.add_children(e, es...);
        return r;
    }

    static nla_expr mul(const T& v, nla_expr & w) {
        if (v == 1)
            return w;
        nla_expr r(expr_type::MUL);
        r.add_child(scalar(v));
        r.add_child(w);
        return r;
    }

    static nla_expr mul(const T& v, lpvar j) {
        if (v == 1)
            return var(j);
        return mul(scalar(v), var(j));
    }

    static nla_expr scalar(const T& v)  {
        nla_expr r(expr_type::SCALAR);
        r.m_v = v;
        return r;
    }

    static nla_expr var(lpvar j)  {
        nla_expr r(expr_type::VAR);
        r.m_j = j;
        return r;
    }

    bool contains(lpvar j) const {
        if (is_var())
            return m_j == j;
        if (is_mul()) {
            for (const nla_expr<T>& c : children()) {
                if (c.contains(j))
                    return true;
            }
        }
        return false;
    }    
};
template <typename T> 
nla_expr<T> operator+(const nla_expr<T>& a, const nla_expr<T>& b) {
    if (a.is_sum()) {
        nla_expr<T> r(expr_type::SUM);
        r.children() = a.children();
        if (b.is_sum()) {
            for (auto& e: b.children())
                r.add_child(e);
        } else {
            r.add_child(b);
        }
        return r;
    }
    if (b.is_sum()) {
        nla_expr<T> r(expr_type::SUM);
        r.children() = b.children();
        r.add_child(a);
        return r;
    }
    return nla_expr<T>::sum(a, b);
}

template <typename T> 
nla_expr<T> operator*(const nla_expr<T>& a, const nla_expr<T>& b) {
    if (a.is_mul()) {
        nla_expr<T> r(expr_type::MUL);
        r.children() = a.children();
        if (b.is_mul()) {
            for (auto& e: b.children())
                r.add_child(e);
        } else {
            r.add_child(b);
        }
        return r;
    }
    if (b.is_mul()) {
        nla_expr<T> r(expr_type::MUL);
        r.children() = b.children();
        r.add_child(a);
        return r;
    }
    return nla_expr<T>::mul(a, b);
}


template <typename T> 
nla_expr<T> operator/(const nla_expr<T>& a, lpvar j) {
    SASSERT((a.is_mul() && a.contains(j)) || (a.is_var() && a.var() == j));
    if (a.is_var())
        return nla_expr<T>::scalar(T(1));
    nla_expr<T> b;
    bool seenj = false;
    for (const nla_expr<T>& c : a.children()) {
        if (!seenj) {
            if (c.contains(j)) {
                if (!c.is_var())                     
                    b.add_child(c / j);
                seenj = true;
                continue;
            } 
        }
        b.add_child(c);
    }
    if (b.children().size() > 1) {
        b.type() = expr_type::MUL;
    } else {
        b = b.children()[0];
    }
    return b;
}
template <typename T>
std::ostream& operator<<(std::ostream& out, const nla_expr<T>& e ) {
    return e.print(out);
}


}
    
