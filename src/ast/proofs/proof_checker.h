/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    proof_checker.h

Abstract:

    Proof checker.

Author:

    Nikolaj Bjorner (nbjorner) 2008-03-07.

Revision History:

--*/
#ifndef PROOF_CHECKER_H_
#define PROOF_CHECKER_H_

#include "ast/ast.h"
#include "util/map.h"

class proof_checker {
    ast_manager&     m;
    proof_ref_vector m_todo;
    expr_mark        m_marked;
    expr_ref_vector  m_pinned;
    obj_map<expr, expr*> m_hypotheses;
    family_id        m_hyp_fid;
    // family_id        m_spc_fid;
    app_ref          m_nil;
    bool             m_dump_lemmas;
    std::string      m_logic; 
    unsigned         m_proof_lemma_id;
    enum hyp_decl_kind {
        OP_CONS,
        OP_ATOM,
        OP_NIL
    };
    enum hyp_sort_kind {
        CELL_SORT
    };
    class hyp_decl_plugin : public decl_plugin {
    protected:
        func_decl* m_cons;
        func_decl* m_atom;
        func_decl* m_nil;
        sort*      m_cell;
        void set_manager(ast_manager * m, family_id id) override;
        func_decl * mk_func_decl(decl_kind k);
    public:
        hyp_decl_plugin();

        ~hyp_decl_plugin() override {}

        void finalize() override;
        
        decl_plugin * mk_fresh() override { return alloc(hyp_decl_plugin); }

        sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override;
        func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                 unsigned arity, sort * const * domain, sort * range) override;
        func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                 unsigned num_args, expr * const * args, sort * range) override;
        void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
        void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;
    };
public:
    proof_checker(ast_manager& m);
    void set_dump_lemmas(char const * logic = "AUFLIA") { m_dump_lemmas = true; m_logic = logic; } 
    bool check(proof* p, expr_ref_vector& side_conditions);
private:
    bool check1(proof* p, expr_ref_vector& side_conditions);
    bool check1_basic(proof* p, expr_ref_vector& side_conditions);
    bool check1_spc(proof* p, expr_ref_vector& side_conditions);
    bool check_arith_proof(proof* p);
    bool check_arith_literal(bool is_pos, app* lit, rational const& coeff, expr_ref& sum, bool& is_strict);
    bool match_fact(proof const* p, expr*& fact) const;
    void add_premise(proof* p);
    bool match_proof(proof const* p) const;
    bool match_proof(proof const* p, proof*& p0) const;
    bool match_proof(proof const* p, proof*& p0, proof*& p1) const;
    bool match_proof(proof const* p, proof_ref_vector& parents) const;
    bool match_binary(expr const* e, func_decl*& d, expr*& t1, expr*& t2) const;
    bool match_op(expr const* e, decl_kind k, expr*& t1, expr*& t2) const;
    bool match_op(expr const* e, decl_kind k, expr*& t) const;
    bool match_op(expr const* e, decl_kind k, ptr_vector<expr>& terms) const;
    bool match_iff(expr const* e, expr*& t1, expr*& t2) const;
    bool match_implies(expr const* e, expr*& t1, expr*& t2) const;
    bool match_eq(expr const* e, expr*& t1, expr*& t2) const;
    bool match_oeq(expr const* e, expr*& t1, expr*& t2) const;
    bool match_not(expr const* e, expr*& t) const;
    bool match_or(expr const* e, ptr_vector<expr>& terms) const;
    bool match_and(expr const* e, ptr_vector<expr>& terms) const;
    bool match_app(expr const* e, func_decl*& d, ptr_vector<expr>& terms) const;
    bool match_quantifier(expr const*, bool& is_univ, sort_ref_vector&, expr*& body) const;
    bool match_negated(expr const* a, expr* b) const;
    bool match_equiv(expr const* a, expr*& t1, expr*& t2) const;
    void get_ors(expr* e, expr_ref_vector& ors);
    void get_hypotheses(proof* p, expr_ref_vector& ante);

    bool match_nil(expr const* e) const;
    bool match_cons(expr const* e, expr*& a, expr*& b) const;
    bool match_atom(expr const* e, expr*& a) const;
    expr* mk_nil();
    expr* mk_cons(expr* a, expr* b);
    expr* mk_atom(expr* e);
    bool is_hypothesis(proof const* p) const;
    expr* mk_hyp(unsigned num_hyps, expr * const * hyps);
    void dump_proof(proof const* pr);
    void dump_proof(unsigned num_antecedents, expr * const * antecedents, expr * consequent);

    void set_false(expr_ref& e, unsigned idx, expr_ref& lit);
};

#endif
