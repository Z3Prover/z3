/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_util.h

Abstract:

    Helper functions

Author:

    Leonardo de Moura (leonardo) 2007-06-08.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"

template<typename C>
void remove_duplicates(C & v) {
    expr_fast_mark1 visited;
    if (!v.empty()) {
        unsigned sz = v.size();
        unsigned j = 0;
        for (unsigned i = 0; i < sz; i++) {
            auto curr = v.get(i);
            if (!visited.is_marked(curr)) {
                visited.mark(curr);
                if (i != j)
                    v.set(j, curr);
                j++;
            }
        }
        v.shrink(j);
    }
}

app * mk_list_assoc_app(ast_manager & m, func_decl * f, unsigned num_args, expr * const * args);
app * mk_list_assoc_app(ast_manager & m, family_id fid, decl_kind k, unsigned num_args, expr * const * args);

bool is_well_formed_vars(ptr_vector<sort>& bound, expr* n);

inline bool args_are_vars(app const * n) {
    unsigned sz = n->get_num_args();
    for (unsigned i = 0; i < sz; i++) {
        if (!is_var(n->get_arg(i)))
            return false;
    }
    return true;
}

inline bool depth_leq_one(app * n) {
    unsigned sz = n->get_num_args();
    for (unsigned i = 0; i < sz; i++) {
        expr * arg = n->get_arg(i);
        if (is_app(arg) && to_app(arg)->get_num_args() > 0)
            return false;
    }
    return true;
}

template<typename AST>
void dec_ref(ast_manager & m, obj_hashtable<AST> & s) {
    for (auto a : s)
        m.dec_ref(a);
}

template<typename AST>
void inc_ref(ast_manager & m, obj_hashtable<AST> & s) {
    for (auto a : s) 
        m.inc_ref(a);
}

// -----------------------------------
//
// Clauses (as ASTs) support
//
// -----------------------------------
bool is_atom(ast_manager & m, expr * n);
bool is_literal(ast_manager & m, expr * n);
void get_literal_atom_sign(ast_manager & m, expr * n, expr * & atom, bool & sign);
bool is_clause(ast_manager & m, expr * n);
unsigned get_clause_num_literals(ast_manager & m, expr * cls);
expr * get_clause_literal(ast_manager & m, expr * cls, unsigned idx);

// -----------------------------------
//
// Goodies for creating Boolean expressions
//
// -----------------------------------

/**
   Return (and args[0] ... args[num_args-1]) if num_args >= 2
   Return args[0]                            if num_args == 1
   Return true                               if num_args == 0
 */
expr * mk_and(ast_manager & m, unsigned num_args, expr * const * args);
app  * mk_and(ast_manager & m, unsigned num_args, app * const * args);
inline expr * mk_and(ast_manager & m, expr* a, expr* b) { expr* args[2] = { a, b }; return mk_and(m, 2, args); }
inline app_ref mk_and(app_ref_vector const& args) { return app_ref(mk_and(args.get_manager(), args.size(), args.data()), args.get_manager()); }
inline expr_ref mk_and(expr_ref_vector const& args) { return expr_ref(mk_and(args.get_manager(), args.size(), args.data()), args.get_manager()); }

inline app_ref operator&(expr_ref& a, expr* b) { return app_ref(a.m().mk_and(a, b), a.m()); }
inline app_ref operator&(app_ref& a,  expr* b) { return app_ref(a.m().mk_and(a, b), a.m()); }
inline app_ref operator&(var_ref& a,  expr* b) { return app_ref(a.m().mk_and(a, b), a.m()); }
inline app_ref operator&(quantifier_ref& a,  expr* b) { return app_ref(a.m().mk_and(a, b), a.m()); }

inline app_ref operator|(expr_ref& a, expr* b) { return app_ref(a.m().mk_or(a, b), a.m()); }
inline app_ref operator|(app_ref& a,  expr* b) { return app_ref(a.m().mk_or(a, b), a.m()); }
inline app_ref operator|(var_ref& a,  expr* b) { return app_ref(a.m().mk_or(a, b), a.m()); }
inline app_ref operator|(quantifier_ref& a,  expr* b) { return app_ref(a.m().mk_or(a, b), a.m()); }
app_ref operator+(expr_ref& a, expr_ref& b);

/**
   Return (or args[0] ... args[num_args-1]) if num_args >= 2
   Return args[0]                           if num_args == 1
   Return false                             if num_args == 0
 */
expr * mk_or(ast_manager & m, unsigned num_args, expr * const * args);
app  * mk_or(ast_manager & m, unsigned num_args, app * const * args);
inline expr * mk_or(ast_manager & m, expr* a, expr* b) { expr* args[2] = { a, b }; return mk_or(m, 2, args); }
inline app_ref mk_or(app_ref_vector const& args) { return app_ref(mk_or(args.get_manager(), args.size(), args.data()), args.get_manager()); }
inline expr_ref mk_or(expr_ref_vector const& args) { return expr_ref(mk_or(args.get_manager(), args.size(), args.data()), args.get_manager()); }

/**
   Return a          if arg = (not a)
   Return (not arg)  otherwise
 */
expr * mk_not(ast_manager & m, expr * arg);

expr_ref mk_not(const expr_ref& e);

inline app_ref mk_not(const app_ref& e) { return app_ref(e.m().mk_not(e), e.m()); }


/**
   Negate and push over conjunction or disjunction.
 */
expr_ref push_not(const expr_ref& arg, unsigned limit = 8);

/**
   Return the expression (and (not (= args[0] args[1])) (not (= args[0] args[2])) ... (not (= args[num_args-2] args[num_args-1])))
*/
expr * expand_distinct(ast_manager & m, unsigned num_args, expr * const * args);

/**
   Create simplified distinct term. Binary distinct becomes a single disequality.
 */
expr * mk_distinct(ast_manager& m, unsigned num_args, expr * const * args);

expr_ref mk_distinct(expr_ref_vector const& args);

/**
   \brief Collect top-level conjunctions and disjunctions.
*/

void flatten_and(expr_ref_vector& result);

void flatten_and(expr_ref& fml);

void flatten_and(expr* fml, expr_ref_vector& result);

void flatten_or(expr_ref_vector& result);

void flatten_or(expr* fml, expr_ref_vector& result);

bool has_uninterpreted(ast_manager& m, expr* e);

