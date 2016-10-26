/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bound_manager.h

Abstract:

    Collect bounds.

Author:

    Leonardo (leonardo) 2011-05-16

Notes:

--*/
#ifndef BOUND_MANAGER_H_
#define BOUND_MANAGER_H_

#include"ast.h"
#include"arith_decl_plugin.h"

class goal;

class bound_manager {
public:
    typedef rational     numeral;
private:
    typedef std::pair<numeral, bool> limit;
    arith_util           m_util;
    obj_map<expr, limit> m_lowers;
    obj_map<expr, limit> m_uppers;
    obj_map<expr, expr_dependency*> m_lower_deps;
    obj_map<expr, expr_dependency*> m_upper_deps;
    ptr_vector<expr>     m_bounded_vars;
    bool is_disjunctive_bound(expr * f, expr_dependency * d);
    bool is_equality_bound(expr * f, expr_dependency * d);
    bool is_numeral(expr* v, rational& n, bool& is_int);
    void insert_lower(expr * v, bool strict, numeral const & n, expr_dependency * d);
    void insert_upper(expr * v, bool strict, numeral const & n, expr_dependency * d);
public:
    static decl_kind neg(decl_kind k);
    static void norm(numeral & n, decl_kind & k);

    bound_manager(ast_manager & m);
    ~bound_manager();
    
    ast_manager & m() const { return m_util.get_manager(); }
    
    void operator()(goal const & g);
    void operator()(expr * n, expr_dependency * d = 0);
    
    bool has_lower(expr * c, numeral & v, bool & strict) const {
        limit l;
        if (m_lowers.find(c, l)) {
            v = l.first;
            strict = l.second;
            return true;
        }
        return false;
    }

    bool has_upper(expr * c, numeral & v, bool & strict) const {
        limit l;
        if (m_uppers.find(c, l)) {
            v = l.first;
            strict = l.second;
            return true;
        }
        return false;
    }

    expr_dependency * lower_dep(expr * c) const {
        expr_dependency * d;
        if (m_lower_deps.find(c, d))
            return d;
        return 0;
    }

    expr_dependency * upper_dep(expr * c) const {
        expr_dependency * d;
        if (m_upper_deps.find(c, d))
            return d;
        return 0;
    }
    
    bool has_lower(expr * c) const {
        return m_lowers.contains(c);
    }

    bool has_upper(expr * c) const {
        return m_uppers.contains(c);
    }
    
    typedef ptr_vector<expr>::const_iterator iterator;
    
    /**
       \brief Iterator for all bounded constants.
    */
    iterator begin() const { return m_bounded_vars.begin(); }
    iterator end() const { return m_bounded_vars.end(); }
    
    void reset();

    // for debugging purposes
    void display(std::ostream & out) const;
};

#endif
