#pragma once

#include <ostream>
#include "ast/ast.h"

namespace spacer {
typedef obj_hashtable<expr> expr_set;
typedef obj_hashtable<func_decl> func_decl_set;

/*
 * An iuc_proof is a proof together with information of the
 * coloring of the axioms.
 */
class iuc_proof
{
public:

    // Constructs an iuc_proof given an ast_manager, a proof, and a set of
    // literals core_lits that might be included in the unsat core
    iuc_proof(ast_manager& m, proof* pr, const expr_set& core_lits);
    iuc_proof(ast_manager& m, proof* pr, const expr_ref_vector &core_lits);

    // returns the proof object
    proof* get() {return m_pr.get();}

    // returns true if all uninterpreted symbols of e are from the core literals
    // requires that m_core_symbols has already been computed
    bool is_core_pure(expr* e) const;

    bool is_a_marked(proof* p) {return m_a_mark.is_marked(p);}
    bool is_b_marked(proof* p) {return m_b_mark.is_marked(p);}
    bool is_h_marked(proof* p) {return m_h_mark.is_marked(p);}

    bool is_b_pure (proof *p) {
        return !is_h_marked (p) && !this->is_a_marked(p) && is_core_pure(m.get_fact (p));
    }

    void display_dot(std::ostream &out);
    // debug method
    void dump_farkas_stats();
private:
    ast_manager& m;
    proof_ref m_pr;

    ast_mark m_a_mark;
    ast_mark m_b_mark;
    ast_mark m_h_mark;

    // -- literals that are part of the core
    expr_set m_core_lits;

    // symbols that occur in any literals in the core
    func_decl_set m_core_symbols;

    // collect symbols occurring in B (the core)
    void collect_core_symbols();

    // compute for each formula of the proof whether it derives
    // from A or from B
    void compute_marks();
};


}

