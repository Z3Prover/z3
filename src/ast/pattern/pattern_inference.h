/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pattern_inference.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-12-08.

Revision History:

--*/
#ifndef PATTERN_INFERENCE_H_
#define PATTERN_INFERENCE_H_

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/pattern/pattern_inference_params.h"
#include "util/vector.h"
#include "util/uint_set.h"
#include "util/nat_set.h"
#include "util/obj_hashtable.h"
#include "util/obj_pair_hashtable.h"
#include "util/map.h"
#include "ast/pattern/expr_pattern_match.h"

/**
   \brief A pattern p_1 is smaller than a pattern p_2 iff 
   every instance of p_2 is also an instance of p_1.

   Example: f(X) is smaller than f(g(X)) because
   every instance of f(g(X)) is also an instance of f(X).
*/
class smaller_pattern {
    ast_manager &    m;
    ptr_vector<expr> m_bindings;

    typedef std::pair<expr *, expr *> expr_pair;
    typedef obj_pair_hashtable<expr, expr> cache;

    svector<expr_pair> m_todo;
    cache              m_cache;
    void save(expr * p1, expr * p2);
    bool process(expr * p1, expr * p2);

    smaller_pattern & operator=(smaller_pattern const &); 

public:

    smaller_pattern(ast_manager & m):
        m(m) {
    }

    bool operator()(unsigned num_bindings, expr * p1, expr * p2);
};

class pattern_inference_cfg :  public default_rewriter_cfg {
    ast_manager&               m;
    pattern_inference_params & m_params;
    family_id                  m_bfid;
    family_id                  m_afid;
    svector<family_id>         m_forbidden;
    obj_hashtable<func_decl>   m_preferred;        
    smaller_pattern            m_le;
    unsigned                   m_num_bindings;
    unsigned                   m_num_no_patterns;
    expr * const *             m_no_patterns;
    bool                       m_nested_arith_only;
    bool                       m_block_loop_patterns;

    struct info {
        uint_set m_free_vars;
        unsigned m_size;
        info(uint_set const & vars, unsigned size):
            m_free_vars(vars),
            m_size(size) {
        }
        info():
            m_free_vars(),
            m_size(0) {
        }
    };

    typedef obj_map<expr, info> expr2info;

    expr2info                 m_candidates_info; // candidate -> set of free vars + size
    app_ref_vector            m_candidates;

    ptr_vector<app>           m_tmp1;
    ptr_vector<app>           m_tmp2;
    ptr_vector<app>           m_todo;

    // Compare candidates patterns based on their usefulness
    // p1 < p2 if
    //  - p1 has more free variables than p2
    //  - p1 and p2 has the same number of free variables,
    //    and p1 is smaller than p2.
    struct pattern_weight_lt {
        expr2info & m_candidates_info;
        pattern_weight_lt(expr2info & i):
            m_candidates_info(i) {
        }
        bool operator()(expr * n1, expr * n2) const;
    };

    pattern_weight_lt          m_pattern_weight_lt;

    //
    // Functor for collecting candidates.
    //
    class collect {
        struct entry {
            expr *    m_node;
            unsigned  m_delta;
            entry():m_node(nullptr), m_delta(0) {}
            entry(expr * n, unsigned d):m_node(n), m_delta(d) {}
            unsigned hash() const { 
                return hash_u_u(m_node->get_id(), m_delta);
            }
            bool operator==(entry const & e) const { 
                return m_node == e.m_node && m_delta == e.m_delta; 
            }
        };
        
        struct info {
            expr_ref    m_node;
            uint_set    m_free_vars;
            unsigned    m_size;
            info(ast_manager & m, expr * n, uint_set const & vars, unsigned sz):
                m_node(n, m), m_free_vars(vars), m_size(sz) {}
        };
        
        ast_manager &            m;
        pattern_inference_cfg &     m_owner;
        family_id                m_afid;
        unsigned                 m_num_bindings;
        typedef map<entry, info *, obj_hash<entry>, default_eq<entry> > cache;
        cache                    m_cache;
        ptr_vector<info>         m_info;
        svector<entry>           m_todo;

        void visit(expr * n, unsigned delta, bool & visited);
        bool visit_children(expr * n, unsigned delta);
        void save(expr * n, unsigned delta, info * i);
        void save_candidate(expr * n, unsigned delta);
        void reset();
    public:
        collect(ast_manager & m, pattern_inference_cfg & o):m(m), m_owner(o), m_afid(m.mk_family_id("arith")) {}
        void operator()(expr * n, unsigned num_bindings);
    };

    collect                    m_collect;
    
    void add_candidate(app * n, uint_set const & s, unsigned size);

    void filter_looping_patterns(ptr_vector<app> & result);

    bool has_preferred_patterns(ptr_vector<app> & candidate_patterns, app_ref_buffer & result);

    void filter_bigger_patterns(ptr_vector<app> const & patterns, ptr_vector<app> & result);

    class contains_subpattern {
        pattern_inference_cfg & m_owner;
        nat_set              m_already_processed; 
        ptr_vector<expr>     m_todo;
        void save(expr * n);
    public:
        contains_subpattern(pattern_inference_cfg & owner):
            m_owner(owner) {}
        bool operator()(expr * n);
    };

    contains_subpattern        m_contains_subpattern;
        
    bool contains_subpattern(expr * n);
    
    struct pre_pattern {
        ptr_vector<app>  m_exprs;     // elements of the pattern.
        uint_set         m_free_vars; // set of free variables in m_exprs
        unsigned         m_idx;       // idx of the next candidate to process.
        pre_pattern():
            m_idx(0) {
        }
    };

    ptr_vector<pre_pattern>      m_pre_patterns;
    expr_pattern_match           m_database;

    void candidates2unary_patterns(ptr_vector<app> const & candidate_patterns,
                                   ptr_vector<app> & remaining_candidate_patterns,
                                   app_ref_buffer & result);
    
    void candidates2multi_patterns(unsigned max_num_patterns, 
                                   ptr_vector<app> const & candidate_patterns, 
                                   app_ref_buffer & result);
    
    void reset_pre_patterns();

    /**
       \brief All minimal unary patterns (i.e., expressions that
       contain all bound variables) are copied to result.  If there
       are unary patterns, then at most num_extra_multi_patterns multi
       patterns are created.  If there are no unary pattern, then at
       most 1 + num_extra_multi_patterns multi_patterns are created.
    */
    void mk_patterns(unsigned num_bindings,              // IN number of bindings.
                     expr * n,                           // IN node where the patterns are going to be extracted.
                     unsigned num_no_patterns,           // IN num. patterns that should not be used.
                     expr * const * no_patterns,         // IN patterns that should not be used.
                     app_ref_buffer & result);           // OUT result
    
public:
    pattern_inference_cfg(ast_manager & m, pattern_inference_params & params);
    
    void register_forbidden_family(family_id fid) {
        SASSERT(fid != m_bfid);
        m_forbidden.push_back(fid);
    }

    /**
       \brief Register f as a preferred function symbol. The inference algorithm
       gives preference to patterns rooted by this kind of function symbol.
    */
    void register_preferred(func_decl * f) {
        m_preferred.insert(f);
    }

    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr);

    void register_preferred(unsigned num, func_decl * const * fs) { for (unsigned i = 0; i < num; i++) register_preferred(fs[i]); }
    
    bool is_forbidden(func_decl const * decl) const {
        family_id fid = decl->get_family_id();
        if (fid == m_bfid && decl->get_decl_kind() != OP_TRUE && decl->get_decl_kind() != OP_FALSE) 
            return true;
        return std::find(m_forbidden.begin(), m_forbidden.end(), fid) != m_forbidden.end();
    }

    bool is_forbidden(app * n) const;
};

class pattern_inference_rw : public rewriter_tpl<pattern_inference_cfg> {
    pattern_inference_cfg m_cfg;
public:
    pattern_inference_rw(ast_manager& m, pattern_inference_params & params);
};

#endif /* PATTERN_INFERENCE_H_ */

