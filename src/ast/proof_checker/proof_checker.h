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
#ifndef _PROOF_CHECKER_H_
#define _PROOF_CHECKER_H_

#include "ast.h"
#include "map.h"

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
        virtual void set_manager(ast_manager * m, family_id id);
        func_decl * mk_func_decl(decl_kind k);
    public:
        hyp_decl_plugin();

        virtual ~hyp_decl_plugin() {}

        virtual void finalize();
        
        virtual decl_plugin * mk_fresh() { return alloc(hyp_decl_plugin); }

        virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters);
        virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range);
        virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned num_args, expr * const * args, sort * range);
        virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
        virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);
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
    bool match_fact(proof* p, expr_ref& fact);
    void add_premise(proof* p);
    bool match_proof(proof* p);
    bool match_proof(proof* p, proof_ref& p0);
    bool match_proof(proof* p, proof_ref& p0, proof_ref& p1);
    bool match_proof(proof* p, proof_ref_vector& parents);
    bool match_binary(expr* e, func_decl_ref& d, expr_ref& t1, expr_ref& t2);
    bool match_op(expr* e, decl_kind k, expr_ref& t1, expr_ref& t2);
    bool match_op(expr* e, decl_kind k, expr_ref& t);
    bool match_op(expr* e, decl_kind k, expr_ref_vector& terms);
    bool match_iff(expr* e, expr_ref& t1, expr_ref& t2);
    bool match_implies(expr* e, expr_ref& t1, expr_ref& t2);
    bool match_eq(expr* e, expr_ref& t1, expr_ref& t2);
    bool match_oeq(expr* e, expr_ref& t1, expr_ref& t2);
    bool match_not(expr* e, expr_ref& t);
    bool match_or(expr* e, expr_ref_vector& terms);
    bool match_and(expr* e, expr_ref_vector& terms);
    bool match_app(expr* e, func_decl_ref& d, expr_ref_vector& terms);
    bool match_quantifier(expr*, bool& is_univ, sort_ref_vector&, expr_ref& body);
    bool match_negated(expr* a, expr* b);
    bool match_equiv(expr* a, expr_ref& t1, expr_ref& t2);
    void get_ors(expr* e, expr_ref_vector& ors);
    void get_hypotheses(proof* p, expr_ref_vector& ante);

    bool match_nil(expr* e) const;
    bool match_cons(expr* e, expr_ref& a, expr_ref& b) const;
    bool match_atom(expr* e, expr_ref& a) const;
    expr* mk_nil();
    expr* mk_cons(expr* a, expr* b);
    expr* mk_atom(expr* e);
    bool is_hypothesis(proof* p) const;
    expr* mk_hyp(unsigned num_hyps, expr * const * hyps);
    void dump_proof(proof * pr);
    void dump_proof(unsigned num_antecedents, expr * const * antecedents, expr * consequent);

    void set_false(expr_ref& e, unsigned idx, expr_ref& lit);
};

#endif
