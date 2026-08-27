/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    witness_instantiation_simplifier.h

Abstract:

    Instantiate universally quantified assertions over sorts that have no
    ground witness term anywhere in the problem.

    Ordinary E-matching (and the polymorphism instantiation performed by
    theory_polymorphism, see ast/polymorphism_inst.h) only fires against
    ground terms that already occur in the (preprocessed) assertions: a
    quantifier whose trigger is an application at some sort S can only be
    instantiated once some ground term of sort S becomes a relevant enode.
    This is fine as long as some other assertion happens to mention a
    ground term of sort S; but some TPTP/THF problems state a fact as a
    plain "forall x : S. P(x)" where S is otherwise only ever used inside
    bound-variable positions (never as a ground term), so this axiom can
    never fire and its content is simply unavailable to the solver.

    Example (ANA068^1.p, monomorphic in the TPTP sort 'real'):

        FINITE_REAL_INTERVAL_1:  ! [A : real] : ~ FINITE(GSPEC(\A0. ...A...))

    Here 'real' never occurs as a ground term anywhere else in the problem
    (all other real-sorted axioms are themselves universally quantified, or
    polymorphic and instantiated at 'real' without ever producing a ground
    real value); as a result this axiom's crucial ground consequence for
    any concrete instantiation of A is never derived.

    Since every sort in the SMT semantics is non-empty, it is always sound
    to instantiate "forall x : S. P(x)" with a fresh, otherwise unconstrained
    constant c : S, obtaining "P(c)" as an additional (implied) fact: this is
    just ordinary universal instantiation, using a synthesized witness term
    instead of an existing ground term. Doing so exactly once per sort that
    is otherwise witness-less turns the missing-ground-term axiom above into
    an assertion that mentions a concrete (fresh) real value, which then
    seeds ordinary E-matching/congruence closure for the rest of the proof.

    To keep this conservative:
      - only uninterpreted (declared, non-builtin) sorts are considered:
        built-in sorts (Bool, Int, Real/Arith, BV, Array, ...) either have
        obvious ground terms available or are handled by dedicated theory
        solvers that do not depend on E-matching seeds this way;
      - a witness is synthesized once per witness-less sort (shared across
        all quantifiers ranging over that sort), not once per quantifier;
      - the original quantified formula is kept (this only adds an implied
        instance, it never removes or weakens anything).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"

class witness_instantiation_simplifier : public dependent_expr_simplifier {

    struct stats {
        unsigned m_num_witnesses = 0;
        void reset() { m_num_witnesses = 0; }
    };

    th_rewriter        m_rewriter;
    stats              m_stats;
    obj_map<sort, expr*> m_witness; // sort -> fresh witness constant (once instantiated, shared)
    expr_ref_vector     m_pinned;

    // collect the sorts of ground (variable- and quantifier-free) subterms
    // occurring anywhere in the current formula set.
    void collect_ground_sorts(obj_hashtable<sort>& ground_sorts);

    // return (creating if needed) a fresh ground witness constant of sort s.
    expr* get_witness(sort* s);

    // instantiate quantifier q (from formula de) at any of its declared
    // sorts that lack a ground witness, adding the resulting (implied)
    // instance(s) as new formulas.
    void try_instantiate(quantifier* q, dependent_expr const& de, obj_hashtable<sort> const& ground_sorts);

public:
    witness_instantiation_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m),
        m_pinned(m) {
        updt_params(p);
    }

    char const* name() const override { return "witness-instantiation"; }

    void reduce() override;

    void collect_statistics(statistics& st) const override {
        st.update("witness-instantiations", m_stats.m_num_witnesses);
    }

    void reset_statistics() override { m_stats.reset(); }

    void updt_params(params_ref const& p) override {
        m_rewriter.updt_params(p);
    }

    void collect_param_descrs(param_descrs& r) override {
        th_rewriter::get_param_descrs(r);
    }
};

/*
  ADD_SIMPLIFIER("witness-instantiation", "instantiate universally quantified assertions over sorts that have no ground witness term, using a fresh synthesized witness constant.", "alloc(witness_instantiation_simplifier, m, p, s)")
 */
