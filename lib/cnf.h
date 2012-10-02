/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cnf.h

Abstract:

    CNF translation

Author:

    Leonardo de Moura (leonardo) 2008-01-17.

Revision History:

--*/
#ifndef _CNF_H_
#define _CNF_H_

#include"cnf_params.h"
#include"pull_quant.h"
#include"nnf.h"
#include"approx_nat.h"

/**
   \brief Entry into the todo list of the CNF translator. It is also used as the key in the CNF cache.
*/
struct cnf_entry {
    expr *       m_node;
    bool         m_polarity:1;
    bool         m_in_q:1;
    cnf_entry():m_node(0), m_polarity(false), m_in_q(false) {}
    cnf_entry(expr * n, bool p, bool in_q):m_node(n), m_polarity(p), m_in_q(in_q) {}
    unsigned hash() const;
    bool operator==(cnf_entry const & k) const;
};

/**
   \brief Cache for CNF transformation. It is a mapping from (expr, polarity, in_q) -> (expr, proof)
*/
class cnf_cache {
public:
    typedef std::pair<expr *, proof *> expr_proof_pair;

    typedef map<cnf_entry, expr_proof_pair, obj_hash<cnf_entry>, default_eq<cnf_entry> > cache;
    
    ast_manager &   m_manager;
    cache  m_cache;
    
public:
    cnf_cache(ast_manager & m);
    ~cnf_cache() { reset(); }
    void insert(cnf_entry const & k, expr * r, proof * pr);
    bool contains(cnf_entry const & k) const { return m_cache.contains(k); }
    void get(cnf_entry const & k, expr * & r, proof * & pr) const { expr_proof_pair tmp; m_cache.find(k, tmp); r = tmp.first; pr = tmp.second; }
    void reset();
};

/**
   \brief Functor for converting expressions into CNF. The functor can
   optionally process subformulas nested in quantifiers. New names may be
   introduced for subformulas that are too expensive to be put into CNF.
   
   NNF translation must be applied before converting to CNF.
   
   - To use CNF_QUANT, we must use at least NNF_QUANT
   - To use CNF_OPPORTUNISTIC, we must use at least NNF_QUANT
   - To use CNF_FULL, we must use NNF_FULL
*/
class cnf {
    typedef std::pair<expr *, bool> expr_bool_pair;
    cnf_params &            m_params;
    ast_manager &           m_manager;
    defined_names &         m_defined_names;
    pull_quant              m_pull;
    cnf_cache               m_cache;
    svector<expr_bool_pair> m_todo;
    expr_ref_vector         m_todo_defs;
    proof_ref_vector        m_todo_proofs;
    ptr_vector<expr>        m_result_defs;
    ptr_vector<proof>       m_result_def_proofs;
    proof_ref_vector        m_coarse_proofs;

    void cache_result(expr * e, bool in_q, expr * r, proof * pr);
    void get_cached(expr * n, bool in_q, expr * & r, proof * & pr) const { m_cache.get(cnf_entry(n, true, in_q), r, pr); }
    bool is_cached(expr * n, bool in_q) const { return m_cache.contains(cnf_entry(n, true, in_q)); }

    void visit(expr * n, bool in_q, bool & visited);
    bool visit_children(expr * n, bool in_q);
    
    void get_args(app * n, bool in_q, ptr_buffer<expr> & new_args, ptr_buffer<proof> & new_arg_prs);
    void flat_args(func_decl * d, ptr_buffer<expr> const & args, ptr_buffer<expr> & flat_args);
    approx_nat approx_result_size_for_disj(ptr_buffer<expr> const & args);
    bool is_too_expensive(approx_nat approx_result_size, ptr_buffer<expr> const & args);
    void name_args(ptr_buffer<expr> const & args, expr_ref_buffer & new_args, proof_ref_buffer & new_arg_prs);
    void distribute(app * arg, app * & r, proof * & pr);
    void push_quant(quantifier * q, expr * & r, proof * & pr);
    void reduce1(expr * n, bool in_q);
    void reduce1_or(app * n, bool in_q);
    void reduce1_and(app * n, bool in_q);
    void reduce1_label(app * n, bool in_q);
    void reduce1_quantifier(quantifier * q, bool in_q);

    void reduce(expr * n, expr_ref & r, proof_ref & pr);
public:
    cnf(ast_manager & m, defined_names & n, cnf_params & params);
    ~cnf();
    void operator()(expr * n,                          // [IN] expression that should be put into CNF
                    expr_ref_vector & new_defs,        // [OUT] new definitions
                    proof_ref_vector & new_def_proofs, // [OUT] proofs of the new definitions 
                    expr_ref & r,                      // [OUT] resultant expression
                    proof_ref & p                      // [OUT] proof for (~ n r)
                    );

    void reset();
};

#endif /* _CNF_H_ */

