/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_quick_cheker.h

Abstract:

    Incomplete model checker.

Author:

    Leonardo de Moura (leonardo) 2008-06-20.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/obj_hashtable.h"

namespace smt {
    class context;

    /**
       \brief Simple object for finding quantifier instantiations that are falsified by the current model.
       
       \remark The code for selecting candidates is very naive.
    */
    class quick_checker {
        typedef obj_hashtable<enode> enode_set;
        
        /**
           \brief Functor for collecting candidates for quantifier instantiation.
        */
        class collector {
            context &            m_context;
            ast_manager &        m_manager;
            bool                 m_conservative;
            unsigned             m_num_vars;
            bool_vector        m_already_found;     // mapping from var_idx -> bool
            vector<enode_set>    m_candidates;        // mapping from var_idx -> set of candidates
            vector<enode_set>    m_tmp_candidates;    // auxiliary mapping from var_idx -> set of candidates

            struct entry {
                expr *      m_expr;
                func_decl * m_parent;
                unsigned    m_parent_pos;
                entry(expr * n = nullptr, func_decl * d = nullptr, unsigned p = 0):m_expr(n), m_parent(d), m_parent_pos(p) {}
                unsigned hash() const { return m_parent ? mk_mix(m_expr->get_id(), m_parent->get_id(), m_parent_pos) : m_expr->get_id(); }
                bool operator==(entry const & e) const { return m_expr == e.m_expr && m_parent == e.m_parent && m_parent_pos == e.m_parent_pos; }
            };
            
            typedef hashtable<entry, obj_hash<entry>, default_eq<entry> > cache;
            cache                m_cache;

            void init(quantifier * q);
            bool check_arg(enode * n, func_decl * f, unsigned i);
            void collect_core(app * n, func_decl * p, unsigned i);
            void collect(expr * n, func_decl * f, unsigned idx);
            void save_result(vector<enode_vector> & candidates);

        public:
            collector(context & c);
            void operator()(quantifier * q, bool conservative, vector<enode_vector> & candidates);
        };


        typedef std::pair<expr *, bool> expr_bool_pair;
        typedef pair_hash<obj_ptr_hash<expr>, int_hash> expr_bool_pair_hash;
        typedef map<expr_bool_pair, bool, expr_bool_pair_hash, default_eq<expr_bool_pair> > check_cache;
        typedef obj_map<expr, expr *> canonize_cache;

        context &            m_context;
        ast_manager &        m_manager;
        collector            m_collector;
        expr_ref_vector      m_new_exprs;
        vector<enode_vector> m_candidate_vectors; 
        check_cache          m_check_cache;
        canonize_cache       m_canonize_cache;
        unsigned             m_num_bindings;
        ptr_vector<enode>    m_bindings;
        
        bool all_args(app * a, bool is_true);
        bool any_arg(app * a, bool is_true);
        bool check_core(expr * n, bool is_true);
        bool check(expr * n, bool is_true);
        bool check_quantifier(quantifier * n, bool is_true);
        expr * canonize(expr * n);
        bool process_candidates(quantifier * q, bool unsat);
        
    public:
        quick_checker(context & c);
        bool instantiate_unsat(quantifier * q);
        bool instantiate_not_sat(quantifier * q);
        bool instantiate_not_sat(quantifier * q, unsigned num_candidates, expr * const * candidates);
    };
};


