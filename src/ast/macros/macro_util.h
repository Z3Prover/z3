/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    macro_util.h

Abstract:

    Macro finding goodies.
    They are used during preprocessing (MACRO_FINDER=true), and model building.

Author:

    Leonardo de Moura (leonardo) 2010-12-15.

Revision History:

--*/
#ifndef MACRO_UTIL_H_
#define MACRO_UTIL_H_

#include"ast.h"
#include"obj_hashtable.h"
#include"simplifier.h"

class poly_simplifier_plugin;
class arith_simplifier_plugin;
class bv_simplifier_plugin;
class basic_simplifier_plugin;

class macro_util {
public:
    /**
       \brief See collect_macro_candidates.
    */
    class macro_candidates {
        ptr_vector<func_decl> m_fs;
        expr_ref_vector       m_defs;
        expr_ref_vector       m_conds;
        svector<bool>         m_ineq; // true if the macro is based on an inequality instead of equality.
        svector<bool>         m_satisfy;
        svector<bool>         m_hint; // macro did not contain all universal variables in the quantifier.
        friend class macro_util;
        ast_manager & get_manager() { return m_conds.get_manager(); }

    public:
        macro_candidates(ast_manager & m);
        ~macro_candidates() { reset(); }

        void reset();
        void insert(func_decl * f, expr * def, expr * cond, bool ineq, bool satisfy_atom, bool hint);
        bool empty() const { return m_fs.empty(); }
        unsigned size() const { return m_fs.size(); }
        func_decl * get_f(unsigned i) const { return m_fs[i]; }
        expr * get_def(unsigned i) const { return m_defs.get(i); }
        expr * get_cond(unsigned i) const { return m_conds.get(i); }
        bool ineq(unsigned i) const { return m_ineq[i]; }
        bool satisfy_atom(unsigned i) const { return m_satisfy[i]; }
        bool hint(unsigned i) const { return m_hint[i]; }
    };

private:
    ast_manager &               m_manager;
    simplifier &                m_simplifier;
    arith_simplifier_plugin *   m_arith_simp;
    bv_simplifier_plugin    *   m_bv_simp;
    basic_simplifier_plugin *   m_basic_simp;
    obj_hashtable<func_decl> *  m_forbidden_set;

    bool is_forbidden(func_decl * f) const { return m_forbidden_set != 0 && m_forbidden_set->contains(f); }
    bool poly_contains_head(expr * n, func_decl * f, expr * exception) const;

    void collect_arith_macros(expr * n, unsigned num_decls, unsigned max_macros, bool allow_cond_macros,
                              macro_candidates & r);

    void normalize_expr(app * head, expr * t, expr_ref & norm_t) const;
    void insert_macro(app * head, expr * def, expr * cond, bool ineq, bool satisfy_atom, bool hint, macro_candidates & r);
    void insert_quasi_macro(app * head, unsigned num_decls, expr * def, expr * cond, bool ineq, bool satisfy_atom, bool hint, 
                            macro_candidates & r);

    expr * m_curr_clause; // auxiliary var used in collect_macro_candidates.

    // Return true if m_curr_clause contains f in a literal different from except_lit
    bool rest_contains_decl(func_decl * f, expr * except_lit);
    // Store in extra_cond (and (not l_1) ... (not l_n)) where l_i's are the literals of m_curr_clause that are different from except_lit.
    void get_rest_clause_as_cond(expr * except_lit, expr_ref & extra_cond);
    void collect_poly_args(expr * n, expr * exception, ptr_buffer<expr> & args);
    void add_arith_macro_candidate(app * head, unsigned num_decls, expr * def, expr * atom, bool ineq, bool hint, macro_candidates & r);
    void collect_arith_macro_candidates(expr * lhs, expr * rhs, expr * atom, unsigned num_decls, bool ineq, macro_candidates & r);
    void collect_arith_macro_candidates(expr * atom, unsigned num_decls, macro_candidates & r);
    void collect_macro_candidates_core(expr * atom, unsigned num_decls, macro_candidates & r);
    bool is_poly_hint(expr * n, app * head, expr * exception);


public:
    macro_util(ast_manager & m, simplifier & s);
    void set_forbidden_set(obj_hashtable<func_decl> * s) { m_forbidden_set = s; }

    arith_simplifier_plugin * get_arith_simp() const;
    bv_simplifier_plugin * get_bv_simp() const;
    basic_simplifier_plugin * get_basic_simp() const;

    bool is_macro_head(expr * n, unsigned num_decls) const;
    bool is_left_simple_macro(expr * n, unsigned num_decls, app_ref & head, expr_ref & def) const;
    bool is_right_simple_macro(expr * n, unsigned num_decls, app_ref & head, expr_ref & def) const;
    bool is_simple_macro(expr * n, unsigned num_decls, app_ref& head, expr_ref & def) const {
        return is_left_simple_macro(n, num_decls, head, def) || is_right_simple_macro(n, num_decls, head, def); 
    }

    bool is_arith_macro(expr * n, unsigned num_decls, app_ref & head, expr_ref & def, bool & inv) const;
    bool is_arith_macro(expr * n, unsigned num_decls, app_ref & head, expr_ref & def) const {
        bool inv;
        return is_arith_macro(n, num_decls, head, def, inv);
    }
    
    bool is_pseudo_head(expr * n, unsigned num_decls, app_ref & head, app_ref & t);
    bool is_pseudo_predicate_macro(expr * n, app_ref & head, app_ref & t, expr_ref & def);

    bool is_quasi_macro_head(expr * n, unsigned num_decls) const;
    void quasi_macro_head_to_macro_head(app * qhead, unsigned num_decls, app_ref & head, expr_ref & cond) const;

    void mk_macro_interpretation(app * head, expr * def, expr_ref & interp) const;

    void collect_macro_candidates(expr * atom, unsigned num_decls, macro_candidates & r);
    void collect_macro_candidates(quantifier * q, macro_candidates & r);

    //
    // Auxiliary goodness that allows us to manipulate BV and Arith polynomials. 
    //
    bool is_bv(expr * n) const;
    bool is_bv_sort(sort * s) const;
    app * mk_zero(sort * s) const;
    bool is_add(expr * n) const;
    bool is_times_minus_one(expr * n, expr * & arg) const;
    bool is_le(expr * n) const;
    bool is_le_ge(expr * n) const;
    void mk_sub(expr * t1, expr * t2, expr_ref & r) const;
    void mk_add(expr * t1, expr * t2, expr_ref & r) const;
    void mk_add(unsigned num_args, expr * const * args, sort * s, expr_ref & r) const;
    poly_simplifier_plugin * get_poly_simp_for(sort * s) const;
};

#endif
