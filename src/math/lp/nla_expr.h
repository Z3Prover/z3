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
#include "math/lp/nla_defs.h"
namespace nla {
enum class expr_type { SUM, MUL, VAR, SCALAR };
// This class is needed in horner calculation with intervals
template <typename T>
class nla_expr {
    expr_type       m_type;
    lpvar           m_j;
    T             m_v; // for the scalar
    vector<nla_expr> m_children;
public:
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
            out << "v" << m_j;
            return out;
        case expr_type::SCALAR:
            out << m_v;
            return out;
        default:
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

    nla_expr(expr_type t): m_type(t) {}
    
    void add_child(const nla_expr& e) {
        SASSERT(m_type == expr_type::SUM || m_type == expr_type::MUL);
        m_children.push_back(e);
    }

    
    static nla_expr sum(const nla_expr& v, const nla_expr & w) {
        nla_expr r(expr_type::SUM);
        r.add_child(v);
        r.add_child(w);
        return r;
    }
    static nla_expr mul(const nla_expr& v, const nla_expr & w) {
        nla_expr r(expr_type::MUL);
        r.add_child(v);
        r.add_child(w);
        return r;
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
    
    
};
template <typename T>
std::ostream& operator<<(std::ostream& out, const nla_expr<T>& e ) {
    return e.print(out);
}


}
    
