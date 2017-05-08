/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    static_features.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-16.

Revision History:

--*/
#ifndef STATIC_FEATURES_H_
#define STATIC_FEATURES_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"fpa_decl_plugin.h"
#include"seq_decl_plugin.h"
#include"map.h"

struct static_features {
    ast_manager &            m_manager;
    arith_util               m_autil;
    bv_util                  m_bvutil;
    array_util               m_arrayutil;
    fpa_util                 m_fpautil;
    seq_util                 m_sequtil;
    family_id                m_bfid;
    family_id                m_afid;
    family_id                m_lfid;    
    family_id                m_arrfid;
    ast_mark                 m_already_visited;
    bool                     m_cnf;
    unsigned                 m_num_exprs;             // 
    unsigned                 m_num_roots;             //
    unsigned                 m_max_depth;
    unsigned                 m_num_quantifiers;       //
    unsigned                 m_num_quantifiers_with_patterns; //
    unsigned                 m_num_quantifiers_with_multi_patterns; //
    unsigned                 m_num_clauses;
    unsigned                 m_num_bin_clauses;     // 
    unsigned                 m_num_units;           //
    unsigned                 m_sum_clause_size;
    unsigned                 m_num_nested_formulas; //
    unsigned                 m_num_bool_exprs;      // 
    unsigned                 m_num_bool_constants;  //
    unsigned                 m_num_formula_trees;
    unsigned                 m_max_formula_depth;
    unsigned                 m_sum_formula_depth;
    unsigned                 m_num_or_and_trees;
    unsigned                 m_max_or_and_tree_depth;
    unsigned                 m_sum_or_and_tree_depth;
    unsigned                 m_num_ite_trees;
    unsigned                 m_max_ite_tree_depth;
    unsigned                 m_sum_ite_tree_depth;
    unsigned                 m_num_ands;  //  
    unsigned                 m_num_ors;   // num nested ors
    unsigned                 m_num_iffs;  // 
    unsigned                 m_num_ite_formulas; //
    unsigned                 m_num_ite_terms;    //
    unsigned                 m_num_sharing;
    unsigned                 m_num_interpreted_exprs;       // doesn't include bool_exprs
    unsigned                 m_num_uninterpreted_exprs;     //
    unsigned                 m_num_interpreted_constants;   // doesn't include bool_consts
    unsigned                 m_num_uninterpreted_constants; //
    unsigned                 m_num_uninterpreted_functions; //
    unsigned                 m_num_eqs;         //
    bool                     m_has_rational;    //
    bool                     m_has_int;         //
    bool                     m_has_real;        //
    bool                     m_has_bv;          //
    bool                     m_has_fpa;         //
    bool                     m_has_str;         // has String-typed terms
    bool                     m_has_seq_non_str; // has non-String-typed Sequence terms
    bool                     m_has_arrays;      //
    rational                 m_arith_k_sum;     // sum of the numerals in arith atoms.
    unsigned                 m_num_arith_terms;
    unsigned                 m_num_arith_eqs;   // equalities of the form t = k where k is a numeral
    unsigned                 m_num_arith_ineqs;
    unsigned                 m_num_diff_terms;       // <= m_num_arith_terms
    unsigned                 m_num_diff_eqs;         // <= m_num_arith_eqs
    unsigned                 m_num_diff_ineqs;       // <= m_num_arith_ineqs
    unsigned                 m_num_simple_eqs;       // eqs of the form x = k
    unsigned                 m_num_simple_ineqs;     // ineqs of the form x <= k or x >= k
    unsigned                 m_num_non_linear;
    unsigned_vector          m_num_apps;             // mapping decl_id   -> num_apps;
    unsigned_vector          m_num_theory_terms;     // mapping family_id -> num_terms
    unsigned_vector          m_num_theory_atoms;     // mapping family_id -> num_atoms
    unsigned_vector          m_num_theory_constants; // mapping family_id -> num_exprs
    unsigned_vector          m_num_theory_eqs;       // mapping family_id -> num_eqs
    unsigned                 m_num_aliens;            //
    unsigned_vector          m_num_aliens_per_family; // mapping family_id -> num_alies exprs 
    
    unsigned_vector          m_expr2depth; // expr-id -> depth
    unsigned                 m_max_stack_depth;      // maximal depth of stack we are willing to walk.

    u_map<unsigned>          m_expr2or_and_depth; 
    u_map<unsigned>          m_expr2ite_depth;
    u_map<unsigned>          m_expr2formula_depth;

    unsigned                 m_num_theories; 
    svector<bool>            m_theories;       // mapping family_id -> bool

    symbol                   m_label_sym;
    symbol                   m_pattern_sym;
    symbol                   m_expr_list_sym;

    bool is_marked(ast * e) const { return m_already_visited.is_marked(e); }
    void mark(ast * e) { m_already_visited.mark(e, true); }
    bool is_bool(expr const * e) const { return m_manager.is_bool(e); }
    bool is_basic_expr(expr const * e) const { return is_app(e) && to_app(e)->get_family_id() == m_bfid; }
    bool is_arith_expr(expr const * e) const { return is_app(e) && to_app(e)->get_family_id() == m_afid; }
    bool is_numeral(expr const * e) const { return m_autil.is_numeral(e); }
    bool is_numeral(expr const * e, rational & r) const { return m_autil.is_numeral(e, r); }
    bool is_minus_one(expr const * e) const { rational r; return m_autil.is_numeral(e, r) && r.is_minus_one(); }
    bool is_diff_term(expr const * e, rational & r) const;
    bool is_diff_atom(expr const * e) const;
    bool is_gate(expr const * e) const;
    void mark_theory(family_id fid) { 
        if (fid != null_family_id && !m_manager.is_builtin_family_id(fid) && !m_theories.get(fid, false)) {
            m_theories.setx(fid, true, false);
            m_num_theories++; 
        }
    }
    
    void acc_num(rational const & r) {
        if (r.is_neg())
            m_arith_k_sum -= r;
        else
            m_arith_k_sum += r;
    }
    
    void acc_num(expr const * e) { 
        rational r; 
        if (is_numeral(e, r)) {
            acc_num(r);
        }
    }

    bool arith_k_sum_is_small() const { return m_arith_k_sum < rational(INT_MAX / 8); }

    void inc_num_apps(func_decl const * d) { unsigned id = d->get_decl_id(); m_num_apps.reserve(id+1, 0); m_num_apps[id]++; }
    void inc_theory_terms(family_id fid) { m_num_theory_terms.reserve(fid+1, 0); m_num_theory_terms[fid]++; }
    void inc_theory_atoms(family_id fid) { m_num_theory_atoms.reserve(fid+1, 0); m_num_theory_atoms[fid]++; }
    void inc_theory_constants(family_id fid) { m_num_theory_constants.reserve(fid+1, 0); m_num_theory_constants[fid]++; }
    void inc_theory_eqs(family_id fid) { m_num_theory_eqs.reserve(fid+1, 0); m_num_theory_eqs[fid]++; }
    void inc_num_aliens(family_id fid) { m_num_aliens_per_family.reserve(fid+1, 0); m_num_aliens_per_family[fid]++; }
    void update_core(expr * e);
    void update_core(sort * s);
    void process(expr * e, bool form_ctx, bool or_and_ctx, bool ite_ctx, unsigned stack_depth);
    void process_root(expr * e);
    unsigned get_depth(expr const * e) const { return m_expr2depth.get(e->get_id(), 1); }
    void set_depth(expr const * e, unsigned d) { m_expr2depth.setx(e->get_id(), d, 1); }
    unsigned get_or_and_depth(expr const * e) const { unsigned d = 0; m_expr2or_and_depth.find(e->get_id(), d); return d; }
    void set_or_and_depth(expr const * e, unsigned d) { m_expr2or_and_depth.insert(e->get_id(), d); }
    unsigned get_ite_depth(expr const * e) const { unsigned d = 0; m_expr2ite_depth.find(e->get_id(), d); return d; }
    void set_ite_depth(expr const * e, unsigned d) { m_expr2ite_depth.insert(e->get_id(), d); }
    unsigned get_form_depth(expr const * e) const { unsigned d = 0; m_expr2formula_depth.find(e->get_id(), d); return d; }
    void set_form_depth(expr const * e, unsigned d) { m_expr2formula_depth.insert(e->get_id(), d); }
    static_features(ast_manager & m);
    void reset();
    void flush_cache();
    void collect(unsigned num_formulas, expr * const * formulas);
    void collect(expr * f) { process_root(f); }
    bool internal_family(symbol const & f_name) const;
    void display_family_data(std::ostream & out, char const * prefix, unsigned_vector const & data) const;
    void display_primitive(std::ostream & out) const;
    void display(std::ostream & out) const;
    void get_feature_vector(vector<double> & result);
    bool has_uf() const;
    unsigned num_theories() const; 
    unsigned num_non_uf_theories() const; 

};

#endif /* STATIC_FEATURES_H_ */

