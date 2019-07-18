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
template <typename T>
class nla_expr {
    
    class sorted_children {
        std::vector<nla_expr> m_es;
        // m_order will be sorted according to the non-decreasing order of m_es
        svector<unsigned> m_order;
    public:
        const std::vector<nla_expr>& es() const { return m_es; }
        std::vector<nla_expr>& es() { return m_es; }
        void push_back(const nla_expr& e) {
            SASSERT(m_es.size() == m_order.size());
            m_order.push_back(m_es.size());
            m_es.push_back(e);
        }
        const svector<unsigned>& order() const { return m_order; }
        const nla_expr& back() const { return m_es.back(); }
        nla_expr& back() { return m_es.back(); }
        const nla_expr* begin() const { return m_es.begin(); }
        const nla_expr* end() const { return m_es.end(); }
        typename std::vector<nla_expr>::iterator begin() { return m_es.begin(); }
        typename std::vector<nla_expr>::iterator end() { return m_es.end(); }
        unsigned size() const { return m_es.size(); }
        void sort() {
            std::sort(m_order.begin(), m_order.end(), [this](unsigned i, unsigned j) { return m_es[i] < m_es[j]; });
        }
        bool operator<(const sorted_children& e) const {
            return compare(e) < 0;
        }

        int compare(const sorted_children& e) const {
            unsigned m = std::min(size(), e.size());
            for (unsigned j = 0; j < m; j++) {
                int r = m_es[m_order[j]].compare(e.m_es[e.m_order[j]]);
                TRACE("nla_cn_details", tout << "r=" << r << "\n";);
                if (r)
                    return r;
            }
            return static_cast<int>(size()) - static_cast<int>(e.size());
        }
        void reset_order() {
            m_order.clear();
            for( unsigned i = 0; i < m_es.size(); i++)
                m_order.push_back(i);
        }
    };

    // todo: use union
    expr_type       m_type;
    lpvar           m_j;
    T             m_v; // for the scalar
    sorted_children m_children;
public:
    bool is_sum() const { return m_type == expr_type::SUM; }
    bool is_var() const { return m_type == expr_type::VAR; }
    bool is_mul() const { return m_type == expr_type::MUL; }
    bool is_undef() const { return m_type == expr_type::UNDEF; }
    bool is_scalar() const { return m_type == expr_type::SCALAR; }
    lpvar var() const { SASSERT(m_type == expr_type::VAR); return m_j; }
    expr_type type() const { return m_type; }
    expr_type& type() { return m_type; }
    const std::vector<nla_expr>& children() const { return m_children.es(); }
    std::vector<nla_expr>& children() { return m_children.es(); }
    const sorted_children & s_children() const { return m_children; }
    sorted_children & s_children() { return m_children; }
    const T& value() const { SASSERT(m_type == expr_type::SCALAR); return m_v; }
    std::string str() const { std::stringstream ss; ss << *this; return ss.str(); }
    std::ostream & print_sum(std::ostream& out) const {
        bool first = true;
        for (unsigned j : m_children.order()) {            
            const nla_expr& v = m_children.es()[j];
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
    void sort () {
        if (is_sum() || is_mul()) {
            for (auto & e : m_children.es()) {
                e.sort();
            }
            m_children.sort();
        }            
    }

    void simplify() {
        if (is_simple()) return;
        bool has_sum = false;
        if (is_sum()) {
            for (auto & e : m_children) {
                e.simplify();
                has_sum |= e.is_sum();
            }
            if (has_sum) {
                nla_expr n(expr_type::SUM);
                for (auto &e : m_children.es()) {
                    n += e;
                }
                *this = n;
            }        
        } else if (is_mul()) {
            bool has_mul = false;
            for (auto & e : m_children) {
                e.simplify();
                has_mul |= e.is_mul();
            }
            if (has_mul) {
                nla_expr n(expr_type::MUL);
                for (auto &e : m_children.es()) {
                    n *= e;
                }
                *this = n;
            }
            TRACE("nla_cn", tout << "simplified " << *this << "\n";);
        }
    }

    std::ostream & print_mul(std::ostream& out) const {
        bool first = true;
        for (unsigned j : m_children.order()) {            
            const nla_expr& v = m_children.es()[j];
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
            out << 'v' << m_j;
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
            return false;
        
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

    static nla_expr mul() {
        return nla_expr(expr_type::MUL);
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

    int compare(const nla_expr& e) const {
        TRACE("nla_cn_details", tout << "this="<<*this<<", e=" << e << "\n";);
        if (type() != e.type())
            return (int)type() - (int)(e.type());

        switch(m_type) {
        case expr_type::SUM:
        case expr_type::MUL:
            return m_children.compare(e.m_children);
             
        case expr_type::VAR:
            return static_cast<int>(m_j) - static_cast<int>(e.m_j);
        case expr_type::SCALAR:
            return m_v < e.m_v? -1 : (m_v == e.m_v? 0 : 1);
        default:
            SASSERT(false);
            return 0;
        }
    }
    
    bool operator<(const nla_expr& e) const {
        TRACE("nla_cn_details", tout << "this=" << *this << ", e=" << e << "\n";);
        if (type() != (e.type()))
            return (int)type() < (int)(e.type());

        SASSERT(type() == (e.type()));

        switch(m_type) {
        case expr_type::SUM:
        case expr_type::MUL:
            return m_children < e.m_children;
             
        case expr_type::VAR:
            return m_j < e.m_j;
        case expr_type::SCALAR:
            return m_v < e.m_v;
        default:
            SASSERT(false);
            return false;
        }
    }

    nla_expr& operator*=(const nla_expr& b) {
        if (is_mul()) {
            if (b.is_mul()) {
                for (auto& e: b.children())
                    add_child(e);
            } else {
                add_child(b);
            }
            return *this;
        }
        SASSERT(false); // not impl
        return *this;
    }

    std::unordered_map<lpvar, int> get_powers_from_mul() const {
        SASSERT(is_mul());
        std::unordered_map<lpvar, int> r;
        for (const auto & c : children()) {
            if (!c.is_var()) {
                continue;
            }
            lpvar j = c.var();
            auto it = r.find(j);
            if (it == r.end()) {
                r[j] = 1;
            } else {
                it->second++;
            }
        }
        return r;
    }

    
    nla_expr& operator/=(const nla_expr& b) {
        TRACE("nla_cn_details", tout << *this <<", " << b << "\n";);
        if (b.is_var()) {
            *this = (*this) / b.var();
            return *this;
        }
        SASSERT(b.is_mul());
        if (is_sum()) {
            for (auto & e : children()) {
                e /= b;
            }
            return *this;
        }
        if (is_var()) {
            *this = scalar(T(1));
            return *this;
        }
        SASSERT(is_mul());
        auto powers = b.get_powers_from_mul();
        unsigned i = 0, k = 0;
        for (; i < children().size(); i++, k++) {
            auto & e = children()[i];
            if (!e.is_var()) {
                SASSERT(e.is_scalar());
                continue;
            }
            lpvar j = e.var();
            auto it = powers.find(j);
            if (it == powers.end()) {
                if (i != k)
                    children()[k] = children()[i];
            } else {
                it->second --;
                if (it->second == 0)
                    powers.erase(it);
                k--;
            }            
        }

        while(k ++ < i)
            children().pop_back();

        s_children().reset_order();
        
        return *this;
    }
        
    
    nla_expr& operator+=(const nla_expr& b) {
        if (is_sum()) {
            if (b.is_sum()) {
                for (auto& e: b.children())
                    add_child(e);
            } else {
                add_child(b);
            }
            return *this;
        }
        SASSERT(false); // not impl
        return *this;
    }

};
template <typename T> 
nla_expr<T> operator+(const nla_expr<T>& a, const nla_expr<T>& b) {
    if (a.is_sum()) {
        nla_expr<T> r(expr_type::SUM);
        r.s_children() = a.s_children();
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
        r.s_children() = b.s_children();
        r.add_child(a);
        return r;
    }
    return nla_expr<T>::sum(a, b);
}

template <typename T> 
nla_expr<T> operator*(const nla_expr<T>& a, const nla_expr<T>& b) {
    if (a.is_mul()) {
        nla_expr<T> r(expr_type::MUL);
        r.s_children() = a.s_children();
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
        r.s_children() = b.s_children();
        r.add_child(a);
        return r;
    }
    return nla_expr<T>::mul(a, b);
}


template <typename T> 
nla_expr<T> operator/(const nla_expr<T>& a, lpvar j) {
    TRACE("nla_cn_details", tout << "a=" << a << ", v" << j << "\n";);
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
    } else if (b.children().size() == 1) {
        auto t = b.children()[0];
        b = t;        
    } else {
        b = nla_expr<T>::scalar(T(1));
    }
    return b;
}
template <typename T>
std::ostream& operator<<(std::ostream& out, const nla_expr<T>& e ) {
    return e.print(out);
}


}
    
