/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/proofs/proof_checker.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"

#define IS_EQUIV(_e_) m.is_eq(_e_)

#define SAME_OP(_d1_, _d2_) ((_d1_ == _d2_) || (IS_EQUIV(_d1_) && IS_EQUIV(_d2_)))

proof_checker::hyp_decl_plugin::hyp_decl_plugin() :
    m_cons(nullptr),
    m_atom(nullptr),
    m_nil(nullptr),
    m_cell(nullptr) {
}

void proof_checker::hyp_decl_plugin::finalize() {
    m_manager->dec_ref(m_cons);
    m_manager->dec_ref(m_atom);
    m_manager->dec_ref(m_nil);
    m_manager->dec_ref(m_cell);
}

void proof_checker::hyp_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m,id);
    m_cell = m->mk_sort(symbol("cell"), sort_info(id, CELL_SORT));
    m_cons = m->mk_func_decl(symbol("cons"), m_cell, m_cell, m_cell, func_decl_info(id, OP_CONS));
    m_atom = m->mk_func_decl(symbol("atom"), m->mk_bool_sort(), m_cell, func_decl_info(id, OP_ATOM));
    m_nil  = m->mk_const_decl(symbol("nil"), m_cell, func_decl_info(id, OP_NIL));
    m->inc_ref(m_cell);
    m->inc_ref(m_cons);
    m->inc_ref(m_atom);
    m->inc_ref(m_nil);
}

sort * proof_checker::hyp_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    SASSERT(k == CELL_SORT);
    return m_cell;
}

func_decl * proof_checker::hyp_decl_plugin::mk_func_decl(decl_kind k) {
    switch(k) {
    case OP_CONS: return m_cons;
    case OP_ATOM: return m_atom;
    case OP_NIL: return m_nil;
    default:
        UNREACHABLE();
        return nullptr;
    }
}

func_decl * proof_checker::hyp_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range) {
    return mk_func_decl(k);
}

func_decl * proof_checker::hyp_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned num_args, expr * const * args, sort * range) {
    return mk_func_decl(k);
}

void proof_checker::hyp_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name("cons", OP_CONS));
        op_names.push_back(builtin_name("atom", OP_ATOM));
        op_names.push_back(builtin_name("nil", OP_NIL));
    }
}

void proof_checker::hyp_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    if (logic == symbol::null) {
        sort_names.push_back(builtin_name("cell", CELL_SORT));
    }
}

proof_checker::proof_checker(ast_manager& m) : m(m), m_todo(m), m_marked(), m_pinned(m), m_nil(m),
                                               m_dump_lemmas(false), m_logic("AUFLIRA"), m_proof_lemma_id(0) {
    symbol fam_name("proof_hypothesis");
    if (!m.has_plugin(fam_name)) {
        m.register_plugin(fam_name, alloc(hyp_decl_plugin));
    }
    m_hyp_fid = m.mk_family_id(fam_name);
    // m_spc_fid = m.get_family_id("spc");
    m_nil = m.mk_const(m_hyp_fid, OP_NIL);
}

bool proof_checker::check(proof* p, expr_ref_vector& side_conditions) {
    proof_ref curr(m);
    m_todo.push_back(p);

    bool result = true;
    while (result && !m_todo.empty()) {
        curr = m_todo.back();
        m_todo.pop_back();
        result = check1(curr.get(), side_conditions);
        if (!result) {
            IF_VERBOSE(1, ast_ll_pp(verbose_stream() << "Proof check failed\n", m, curr.get()););
        }
    }

    m_hypotheses.reset();
    m_pinned.reset();
    m_todo.reset();
    m_marked.reset();

    return result;
}

bool proof_checker::check1(proof* p, expr_ref_vector& side_conditions) {
    if (p->get_family_id() == m.get_basic_family_id()) {
        return check1_basic(p, side_conditions);
    }
#if 0
    if (p->get_family_id() == m_spc_fid) {
        return check1_spc(p, side_conditions);
    }
#endif
    return false;
}

bool proof_checker::check1_spc(proof* p, expr_ref_vector& side_conditions) {
#if 0
    decl_kind k = p->get_decl_kind();
    bool is_univ = false;
    expr_ref fact(m), fml(m);
    expr_ref body(m), fml1(m), fml2(m);
    sort_ref_vector sorts(m);
    proof_ref p1(m), p2(m);
    proof_ref_vector proofs(m);

    if (match_proof(p, proofs)) {
        for (proof* pr : proofs) {
            add_premise(pr);
        }
    }
    switch(k) {
    case PR_DEMODULATION: {
        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1.get(), fml) &&
            match_quantifier(fml.get(), is_univ, sorts, body) &&
            is_univ) {
            // TBD: check that fml is an instance of body.
            return true;
        }
        return false;
    }
    case PR_SPC_REWRITE:
    case PR_SUPERPOSITION:
    case PR_EQUALITY_RESOLUTION:
    case PR_SPC_RESOLUTION:
    case PR_FACTORING:
    case PR_SPC_DER: {
        if (match_fact(p, fact)) {
            expr_ref_vector rewrite_eq(m);
            rewrite_eq.push_back(fact.get());
            for (unsigned i = 0; i < proofs.size(); ++i) {
                if (match_fact(proofs[i].get(), fml)) {
                    rewrite_eq.push_back(m.mk_not(fml.get()));
                }
            }
            expr_ref rewrite_cond(m);
            rewrite_cond = m.mk_or(rewrite_eq.size(), rewrite_eq.c_ptr());
            side_conditions.push_back(rewrite_cond.get());
            return true;
        }
        return false;
    }
    default:
        UNREACHABLE();
    }
    return false;
#else
    return true;
#endif
}

bool proof_checker::check1_basic(proof* p, expr_ref_vector& side_conditions) {
    decl_kind k = p->get_decl_kind();
    expr* fml0 = nullptr, *fml1 = nullptr, *fml2 = nullptr, *fml = nullptr;
    expr* t1 = nullptr, *t2 = nullptr;
    expr* s1 = nullptr, *s2 = nullptr;
    expr* u1 = nullptr, *u2 = nullptr;
    expr* fact = nullptr, *body1 = nullptr;
    expr* l1 = nullptr, *l2 = nullptr, *r1 = nullptr, *r2 = nullptr;
    func_decl* d1 = nullptr, *d2 = nullptr, *d3 = nullptr;
    proof* p0 = nullptr, *p1 = nullptr, *p2 = nullptr;
    proof_ref_vector proofs(m);
    func_decl* f1 = nullptr, *f2 = nullptr;
    ptr_vector<expr> terms1, terms2, terms;
    sort_ref_vector decls1(m), decls2(m);

    if (match_proof(p, proofs)) {
        for (proof* pr : proofs) {
            add_premise(pr);
        }
    }

    switch(k) {
    case PR_UNDEF:
        return true;
    case PR_TRUE:
        return true;
    case PR_ASSERTED:
        return true;
    case PR_GOAL:
        return true;
    case PR_MODUS_PONENS: {
        if (match_fact(p, fact) &&
            match_proof(p, p0, p1) &&
            match_fact(p0, fml0) &&
            match_fact(p1, fml1) &&
            (match_implies(fml1, t1, t2) || match_iff(fml1, t1, t2)) &&
            (fml0 == t1) &&
            (fact == t2)) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_REFLEXIVITY: {
        if (match_fact(p, fact) &&
            match_proof(p) &&
            (match_equiv(fact, t1, t2) || match_oeq(fact, t1, t2)) &&
            (t1 == t2)) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_SYMMETRY: {
        if (match_fact(p, fact) &&
            match_proof(p, p1) &&
            match_fact(p1, fml) &&
            match_binary(fact, d1, l1, r1) &&
            match_binary(fml, d2, l2, r2) &&
            SAME_OP(d1, d2) &&
            l1 == r2 &&
            r1 == l2) {
            // TBD d1, d2 is a symmetric predicate
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_TRANSITIVITY: {
        if (match_fact(p, fact) &&
            match_proof(p, p1, p2) &&
            match_fact(p1, fml1) &&
            match_fact(p2, fml2) &&
            match_binary(fact, d1, t1, t2) &&
            match_binary(fml1, d2, s1, s2) &&
            match_binary(fml2, d3, u1, u2) &&
            d1 == d2 &&
            d2 == d3 &&
            t1 == s1 &&
            s2 == u1 &&
            u2 == t2) {
            // TBD d1 is some transitive predicate.
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_TRANSITIVITY_STAR: {
        if (match_fact(p, fact) &&
            match_binary(fact, d1, t1, t2)) {
            u_map<bool> vertices;
            // TBD check that d1 is transitive, symmetric.
            for (proof* pr : proofs) {
                if (match_fact(pr, fml) &&
                    match_binary(fml, d2, s1, s2) &&
                    d1 == d2) {
                    unsigned id1 = s1->get_id();
                    unsigned id2 = s2->get_id();
#define INSERT(_id) if (vertices.contains(_id)) vertices.remove(_id); else vertices.insert(_id, true);
                    INSERT(id1);
                    INSERT(id2);
                }
                else {
                    UNREACHABLE();
                    return false;
                }
            }
            return
                vertices.size() == 2 &&
                vertices.contains(t1->get_id()) &&
                vertices.contains(t2->get_id());
        }
        UNREACHABLE();
        return false;
    }
    case PR_MONOTONICITY: {
        TRACE("proof_checker", tout << mk_bounded_pp(p, m, 3) << "\n";);
        if (match_fact(p, fact) &&
            match_binary(fact, d1, t1, t2) &&
            match_app(t1, f1, terms1) &&
            match_app(t2, f2, terms2) &&
            f1 == f2 &&
            terms1.size() == terms2.size()) {
            // TBD: d1 is monotone.
            for (unsigned i = 0; i < terms1.size(); ++i) {
                expr* term1 = terms1[i];
                expr* term2 = terms2[i];
                if (term1 != term2) {
                    bool found = false;
                    for (proof* pr : proofs) {
                        found |=
                            match_fact(pr, fml) &&
                            match_binary(fml, d2, s1, s2) &&
                            SAME_OP(d1, d2) &&
                            s1 == term1 &&
                            s2 == term2;
                    }
                    if (!found) {
                        UNREACHABLE();
                        return false;
                    }
                }
            }
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_QUANT_INTRO: {
        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml) &&
            (is_lambda(fact) || is_lambda(fml)))
            return true;

        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml) &&
            (match_iff(fact, t1, t2) || match_oeq(fact, t1, t2)) &&
            (match_iff(fml, s1, s2) || match_oeq(fml, s1, s2)) &&
            m.is_oeq(fact) == m.is_oeq(fml) &&
            is_quantifier(t1) &&
            is_quantifier(t2) &&
            to_quantifier(t1)->get_expr() == s1 &&
            to_quantifier(t2)->get_expr() == s2 &&
            to_quantifier(t1)->get_num_decls() == to_quantifier(t2)->get_num_decls() &&
            to_quantifier(t1)->get_kind() == to_quantifier(t2)->get_kind()) {
            quantifier* q1 = to_quantifier(t1);
            quantifier* q2 = to_quantifier(t2);
            for (unsigned i = 0; i < q1->get_num_decls(); ++i) {
                if (q1->get_decl_sort(i) != q2->get_decl_sort(i)) {
                    // term is not well-typed.
                    UNREACHABLE();
                    return false;
                }
            }
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_BIND:
        // it is a lambda expression returning a proof object.
        if (!is_lambda(to_app(p)->get_arg(0)))
            return false;
        // check that body is a proof object.
        return true;

    case PR_DISTRIBUTIVITY: {
        if (match_fact(p, fact) &&
            match_proof(p) &&
            match_equiv(fact, t1, t2)) {
            side_conditions.push_back(fact);
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_AND_ELIM: {
        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml) &&
            match_and(fml, terms)) {
            for (expr* t : terms)
                if (t == fact) return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_NOT_OR_ELIM: {

        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml) &&
            match_not(fml, fml1) &&
            match_or(fml1, terms)) {
            for (expr* t : terms) {
                if (match_negated(t, fact)) {
                    return true;
                }
            }
        }
        UNREACHABLE();
        return false;
    }
    case PR_REWRITE: {
        if (match_fact(p, fact) &&
            match_proof(p) &&
            match_equiv(fact, t1, t2)) {
            side_conditions.push_back(fact);
            return true;
        }
        IF_VERBOSE(0, verbose_stream() << "Expected proof of equality:\n" << mk_bounded_pp(p, m););
        return false;
    }
    case PR_REWRITE_STAR: {
        if (match_fact(p, fact) &&
            match_equiv(fact, t1, t2)) {
            expr_ref_vector rewrite_eq(m);
            rewrite_eq.push_back(fact);
            for (proof* pr : proofs) {
                if (match_fact(pr, fml)) {
                    rewrite_eq.push_back(m.mk_not(fml));
                }
            }
            expr_ref rewrite_cond(m);
            rewrite_cond = m.mk_or(rewrite_eq.size(), rewrite_eq.data());
            side_conditions.push_back(rewrite_cond.get());
            return true;
        }
        IF_VERBOSE(0, verbose_stream() << "Expected proof of equality:\n" << mk_bounded_pp(p, m););
        return false;
    }
    case PR_PULL_QUANT: {
        if (match_proof(p) &&
            match_fact(p, fact) &&
            match_iff(fact, t1, t2) &&
            is_quantifier(t2)) {
            // TBD: check the enchilada.
            return true;
        }
        IF_VERBOSE(0, verbose_stream() << "Expected proof of equivalence with a quantifier:\n" << mk_bounded_pp(p, m););
        return false;
    }
    case PR_PUSH_QUANT: {
        if (match_proof(p) &&
            match_fact(p, fact) &&
            match_iff(fact, t1, t2) &&
            is_quantifier(t1) &&
            match_and(to_quantifier(t1)->get_expr(), terms1) &&
            match_and(t2, terms2) &&
            terms1.size() == terms2.size()) {
            quantifier * q1 = to_quantifier(t1);
            for (unsigned i = 0; i < terms1.size(); ++i) {
                if (is_quantifier(terms2[i]) &&
                    to_quantifier(terms2[i])->get_expr() == terms1[i] &&
                    to_quantifier(terms2[i])->get_num_decls() == q1->get_num_decls()) {
                    // ok.
                }
                else {
                    return false;
                }
            }
        }
        UNREACHABLE();
        return false;
    }
    case PR_ELIM_UNUSED_VARS: {
        if (match_proof(p) &&
            match_fact(p, fact) &&
            match_iff(fact, t1, t2)) {
            // TBD:
            // match_quantifier(t1, is_forall1, decls1, body1)
            // filter out decls1 that occur in body1.
            // if list is empty, then t2 could be just body1.
            // otherwise t2 is also a quantifier.
            return true;
        }
        IF_VERBOSE(0, verbose_stream() << "does not match last rule: " << mk_pp(p, m) << "\n";);
        return false;
    }
    case PR_DER: {
        bool is_forall = false;
        if (match_proof(p) &&
            match_fact(p, fact) &&
            match_iff(fact, t1, t2) &&
            match_quantifier(t1, is_forall, decls1, body1) &&
            is_forall) {
            // TBD: check that terms are set of equalities.
            // t2 is an instance of a predicate in terms1
            return true;
        }
        IF_VERBOSE(0, verbose_stream() << "does not match last rule: " << mk_pp(p, m) << "\n";);
        return false;
    }
    case PR_HYPOTHESIS: {
        // TBD all branches with hypotheses must be closed by a later lemma.
        if (match_proof(p) &&
            match_fact(p, fml)) {
            return true;
        }
        return false;
    }
    case PR_LEMMA: {
        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml) &&
            m.is_false(fml)) {
            expr_ref_vector hypotheses(m);
            expr_ref_vector ors(m);
            get_hypotheses(p1, hypotheses);
            if (hypotheses.size() == 1 && match_negated(hypotheses.get(0), fact)) {
                // Suppose fact is (or a b c) and hypothesis is (not (or a b c))
                // That is, (or a b c) should be viewed as a 'quoted expression' and a unary clause,
                // instead of a clause with three literals.
                return true;
            }
            get_ors(fact, ors);
            for (unsigned i = 0; i < hypotheses.size(); ++i) {
                bool found = false;
                unsigned j;
                for (j = 0; !found && j < ors.size(); ++j) {
                    found = match_negated(ors[j].get(), hypotheses[i].get());
                }
                if (!found) {
                    TRACE("pr_lemma_bug",
                          tout << "i: " << i << "\n";
                          tout << "ORs:\n" << ors << "\n";
                          tout << "HYPOTHESIS:\n" << hypotheses << "\n";
                          );
                    UNREACHABLE();
                    return false;
                }
                TRACE("proof_checker", tout << "Matched:\n";
                      ast_ll_pp(tout, m, hypotheses[i].get());
                      ast_ll_pp(tout, m, ors[j-1].get()););
            }
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_UNIT_RESOLUTION: {
        if (match_fact(p, fact) &&
            proofs.size() == 2 &&
            match_fact(proofs[0].get(), fml1) &&
            match_fact(proofs[1].get(), fml2) &&
            m.is_complement(fml1, fml2) &&
            m.is_false(fact)) {
            return true;
        }
        if (match_fact(p, fact) &&
            proofs.size() > 1 &&
            match_fact(proofs.get(0), fml) &&
            match_or(fml, terms1)) {
            for (unsigned i = 1; i < proofs.size(); ++i) {
                if (!match_fact(proofs.get(i), fml2)) {
                    return false;
                }
                bool found = false;
                for (unsigned j = 0; !found && j < terms1.size(); ++j) {
                    if (m.is_complement(terms1.get(j), fml2)) {
                        found = true;
                        if (j + 1 < terms1.size()) {
                            terms1[j] = terms1.get(terms1.size()-1);
                        }
                        terms1.resize(terms1.size()-1);
                    }
                }
                if (!found) {
                    TRACE("pr_unit_bug",
                          tout << "Parents:\n";
                          for (unsigned i = 0; i < proofs.size(); i++) {
                              expr* p = nullptr;
                              match_fact(proofs.get(i), p);
                              tout << mk_pp(p, m) << "\n";
                          }
                          tout << "Fact:\n";
                          tout << mk_pp(fact, m) << "\n";
                          tout << "Clause:\n";
                          tout << mk_pp(fml, m) << "\n";
                          tout << "Could not find premise " << mk_pp(fml2, m) << "\n";
                          );

                    UNREACHABLE();
                    return false;
                }
            }
            switch(terms1.size()) {
            case 0:
                return m.is_false(fact);
            case 1:
                return fact == terms1[0];
            default: {
                if (match_or(fact, terms2)) {
                    for (expr* term1 : terms1) {
                        bool found = false;
                        for (expr* term2 : terms2) {
                            found = term1 == term2;
                            if (found) break;
                        }
                        if (!found) {
                            IF_VERBOSE(0, verbose_stream() << "Premise not found:" << mk_pp(term1, m) << "\n";);
                            return false;
                        }
                    }
                    return true;
                }
                IF_VERBOSE(0, verbose_stream() << "Conclusion is not a disjunction:\n";
                           verbose_stream() << mk_pp(fml, m) << "\n";
                           verbose_stream() << mk_pp(fact, m) << "\n";);

                return false;
            }

            }
        }
        UNREACHABLE();
        return false;
    }
    case PR_IFF_TRUE: {
        // iff_true(?rule(?p1, ?fml), (iff ?fml true))
        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml1) &&
            match_iff(fact, l1, r1) &&
            fml1 == l1 &&
            r1 == m.mk_true()) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_IFF_FALSE: {
        // iff_false(?rule(?p1, (not ?fml)), (iff ?fml false))
        if (match_proof(p, p1) &&
            match_fact(p, fact) &&
            match_fact(p1, fml1) &&
            match_iff(fact, l1, r1) &&
            match_not(fml1, t1) &&
            t1 == l1 &&
            r1 == m.mk_false()) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_COMMUTATIVITY: {
        // commutativity(= (?c ?t1 ?t2) (?c ?t2 ?t1))
        if (match_fact(p, fact) &&
            match_proof(p) &&
            match_equiv(fact, t1, t2) &&
            match_binary(t1, d1, s1, s2) &&
            match_binary(t2, d2, u1, u2) &&
            s1 == u2 &&
            s2 == u1 &&
            d1 == d2 &&
            d1->is_commutative()) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_DEF_AXIOM: {
        // axiom(?fml)
        if (match_fact(p, fact) &&
            match_proof(p) &&
            m.is_bool(fact)) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_DEF_INTRO: {
        // def_intro(?fml)
        //
        // ?fml: forall x . ~p(x) or e(x) and forall x . ~e(x) or p(x)
        //     : forall x . ~cond(x) or f(x) = then(x) and forall x . cond(x) or f(x) = else(x)
        //     : forall x . f(x) = e(x)
        //
        if (match_fact(p, fact) &&
            match_proof(p) &&
            m.is_bool(fact)) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_APPLY_DEF: {
        if (match_fact(p, fact) &&
            match_oeq(fact, t1, t2)) {
            // TBD: must definitions be in proofs?
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_IFF_OEQ: {
        // axiom(?rule(?p1,(iff ?t1 ?t2)), (~ ?t1 ?t2))
        if (match_fact(p, fact) &&
            match_proof(p, p1) &&
            match_oeq(fact, t1, t2) &&
            match_fact(p1, fml) &&
            match_iff(fml, s1, s2) &&
            s1 == t1 &&
            s2 == t2) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_NNF_POS: {
        // TBD:
        return true;
    }
    case PR_NNF_NEG: {
        // TBD:
        return true;
    }
    case PR_SKOLEMIZE: {
        // (exists ?x (p ?x y)) -> (p (sk y) y)
        // (not (forall ?x (p ?x y))) -> (not (p (sk y) y))
        if (match_fact(p, fact) &&
            match_oeq(fact, t1, t2)) {
            quantifier* q = nullptr;
            expr* e = t1;
            bool is_forall = false;
            if (match_not(t1, s1)) {
                e = s1;
                is_forall = true;
            }
            if (is_quantifier(e)) {
                SASSERT(!is_lambda(e));
                q = to_quantifier(e);
                // TBD check that quantifier is properly instantiated
                return is_forall == ::is_forall(q);
            }
        }
        UNREACHABLE();
        return false;
    }
    case PR_MODUS_PONENS_OEQ: {
        if (match_fact(p, fact) &&
            match_proof(p, p0, p1) &&
            match_fact(p0, fml0) &&
            match_fact(p1, fml1) &&
            match_oeq(fml1, t1, t2) &&
            fml0 == t1 &&
            fact == t2) {
            return true;
        }
        UNREACHABLE();
        return false;
    }
    case PR_TH_LEMMA: {
        SASSERT(p->get_decl()->get_num_parameters() > 0);
        SASSERT(p->get_decl()->get_parameter(0).is_symbol());
        if (symbol("arith") == p->get_decl()->get_parameter(0).get_symbol()) {
            return check_arith_proof(p);
        }
        dump_proof(p);
        return true;
    }
    case PR_QUANT_INST: {
        // TODO
        return true;
    }
    case PR_HYPER_RESOLVE: {
        proof_ref_vector premises(m);
        expr_ref_vector fmls(m);
        expr_ref conclusion(m), premise(m), premise0(m), premise1(m);
        svector<std::pair<unsigned, unsigned> > positions;
        vector<expr_ref_vector> substs;
        VERIFY(m.is_hyper_resolve(p, premises, conclusion, positions, substs));
        var_subst vs(m, false);
        for (unsigned i = 0; i < premises.size(); ++i) {
            expr_ref_vector const& sub = substs[i];
            premise = m.get_fact(premises[i].get());
            if (!sub.empty()) {
                if (is_forall(premise)) {
                    // SASSERT(to_quantifier(premise)->get_num_decls() == sub.size());
                    premise = to_quantifier(premise)->get_expr();
                }
                premise = vs(premise, sub.size(), sub.data());
            }
            fmls.push_back(premise.get());
            TRACE("proof_checker",
                  tout << mk_pp(premise.get(), m) << "\n";
                  for (unsigned j = 0; j < sub.size(); ++j) {
                      tout << mk_pp(sub[j], m) << " ";
                  }
                  tout << "\n";);
        }
        premise0 = fmls[0].get();
        for (unsigned i = 1; i < fmls.size(); ++i) {
            expr_ref lit1(m), lit2(m);
            expr* lit3 = nullptr;
            std::pair<unsigned, unsigned> pos = positions[i-1];
            premise1 = fmls[i].get();
            set_false(premise0, pos.first, lit1);
            set_false(premise1, pos.second, lit2);
            if (m.is_not(lit1, lit3) && lit3 == lit2) {
                // ok
            }
            else if (m.is_not(lit2, lit3) && lit3 == lit1) {
                // ok
            }
            else {
                IF_VERBOSE(0, verbose_stream() << "Could not establish complementarity for:\n" <<
                           mk_pp(lit1, m) << "\n" << mk_pp(lit2, m) << "\n" << mk_pp(p, m) << "\n";);
            }
            fmls[i] = premise1;
        }
        fmls[0] = premise0;
        premise0 = m.mk_or(fmls.size(), fmls.data());
        if (is_forall(conclusion)) {
            quantifier* q = to_quantifier(conclusion);
            premise0 = m.mk_iff(premise0, q->get_expr());
            premise0 = m.mk_forall(q->get_num_decls(), q->get_decl_sorts(), q->get_decl_names(), premise0);
        }
        else {
            premise0 = m.mk_iff(premise0, conclusion);
        }
        side_conditions.push_back(premise0);
        return true;
    }
    default:
        UNREACHABLE();
        return false;
    }
}

/**
   \brief Premises of the rules are of the form
      (or l0 l1 l2 .. ln)
   or
      (=> (and ln+1 ln+2 .. ln+m) l0)
   or in the most general (ground) form:
      (=> (and ln+1 ln+2 .. ln+m) (or l0 l1 .. ln-1))
   In other words we use the following (Prolog style) convention for Horn
   implications:
   The head of a Horn implication is position 0,
   the first conjunct in the body of an implication is position 1
   the second conjunct in the body of an implication is position 2

   Set the position provided in the argument to 'false'.
*/
void proof_checker::set_false(expr_ref& e, unsigned position, expr_ref& lit) {
    app* a = to_app(e);
    expr* head, *body;
    expr_ref_vector args(m);
    if (m.is_or(e)) {
        SASSERT(position < a->get_num_args());
        args.append(a->get_num_args(), a->get_args());
        lit = args[position].get();
        args[position] = m.mk_false();
        e = m.mk_or(args.size(), args.data());
    }
    else if (m.is_implies(e, body, head)) {
        expr* const* heads = &head;
        unsigned num_heads = 1;
        if (m.is_or(head)) {
            num_heads = to_app(head)->get_num_args();
            heads = to_app(head)->get_args();
        }
        expr*const* bodies = &body;
        unsigned num_bodies = 1;
        if (m.is_and(body)) {
            num_bodies = to_app(body)->get_num_args();
            bodies = to_app(body)->get_args();
        }
        if (position < num_heads) {
            args.append(num_heads, heads);
            lit = args[position].get();
            args[position] = m.mk_false();
            e = m.mk_implies(body, m.mk_or(args.size(), args.data()));
        }
        else {
            position -= num_heads;
            args.append(num_bodies, bodies);
            lit = m.mk_not(args[position].get());
            args[position] = m.mk_true();
            e = m.mk_implies(m.mk_and(args.size(), args.data()), head);
        }
    }
    else if (position == 0) {
        lit = e;
        e = m.mk_false();
    }
    else {
        IF_VERBOSE(0, verbose_stream() << position << "\n" << mk_pp(e, m) << "\n";);
        UNREACHABLE();
    }
}

bool proof_checker::match_fact(proof const* p, expr*& fact) const {
    if (m.is_proof(p) &&
        m.has_fact(p)) {
        fact = m.get_fact(p);
        return true;
    }
    return false;
}

void proof_checker::add_premise(proof* p) {
    if (!m_marked.is_marked(p)) {
        m_marked.mark(p, true);
        m_todo.push_back(p);
    }
}

bool proof_checker::match_proof(proof const* p) const {
    return
        m.is_proof(p) &&
        m.get_num_parents(p) == 0;
}

bool proof_checker::match_proof(proof const* p, proof*& p0) const {
    if (m.is_proof(p) &&
        m.get_num_parents(p) == 1) {
        p0 = m.get_parent(p, 0);
        return true;
    }
    return false;
}

bool proof_checker::match_proof(proof const* p, proof*& p0, proof*& p1) const {
    if (m.is_proof(p) &&
        m.get_num_parents(p) == 2) {
        p0 = m.get_parent(p, 0);
        p1 = m.get_parent(p, 1);
        return true;
    }
    return false;
}

bool proof_checker::match_proof(proof const* p, proof_ref_vector& parents) const {
    if (m.is_proof(p)) {
        for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
            parents.push_back(m.get_parent(p, i));
        }
        return true;
    }
    return false;
}


bool proof_checker::match_binary(expr const* e, func_decl*& d, expr*& t1, expr*& t2) const {
    if (e->get_kind() == AST_APP &&
        to_app(e)->get_num_args() == 2) {
        d = to_app(e)->get_decl();
        t1 = to_app(e)->get_arg(0);
        t2 = to_app(e)->get_arg(1);
        return true;
    }
    return false;
}


bool proof_checker::match_app(expr const* e, func_decl*& d, ptr_vector<expr>& terms) const {
    if (e->get_kind() == AST_APP) {
        d = to_app(e)->get_decl();
        for (expr* arg : *to_app(e)) {
            terms.push_back(arg);
        }
        return true;
    }
    return false;
}

bool proof_checker::match_quantifier(expr const* e, bool& is_univ, sort_ref_vector& sorts, expr*& body) const {
    if (is_quantifier(e)) {
        quantifier const* q = to_quantifier(e);
        is_univ = is_forall(q);
        body = q->get_expr();
        for (unsigned i = 0; i < q->get_num_decls(); ++i) {
            sorts.push_back(q->get_decl_sort(i));
        }
        return true;
    }
    return false;
}

bool proof_checker::match_op(expr const* e, decl_kind k, expr*& t1, expr*& t2) const {
    if (e->get_kind() == AST_APP &&
        to_app(e)->get_family_id() == m.get_basic_family_id() &&
        to_app(e)->get_decl_kind() == k &&
        to_app(e)->get_num_args() == 2) {
        t1 = to_app(e)->get_arg(0);
        t2 = to_app(e)->get_arg(1);
        return true;
    }
    return false;
}

bool proof_checker::match_op(expr const* e, decl_kind k, ptr_vector<expr>& terms) const {
    if (e->get_kind() == AST_APP &&
        to_app(e)->get_family_id() == m.get_basic_family_id() &&
        to_app(e)->get_decl_kind() == k) {
        for (expr* arg : *to_app(e))
            terms.push_back(arg);
        return true;
    }
    return false;
}


bool proof_checker::match_op(expr const* e, decl_kind k, expr*& t) const {
    if (e->get_kind() == AST_APP &&
        to_app(e)->get_family_id() == m.get_basic_family_id() &&
        to_app(e)->get_decl_kind() == k &&
        to_app(e)->get_num_args() == 1) {
        t = to_app(e)->get_arg(0);
        return true;
    }
    return false;
}

bool proof_checker::match_not(expr const* e, expr*& t) const {
    return match_op(e, OP_NOT, t);
}

bool proof_checker::match_or(expr const* e, ptr_vector<expr>& terms) const {
    return match_op(e, OP_OR, terms);
}

bool proof_checker::match_and(expr const* e, ptr_vector<expr>& terms) const {
    return match_op(e, OP_AND, terms);
}

bool proof_checker::match_iff(expr const* e, expr*& t1, expr*& t2) const {
    return match_op(e, OP_EQ, t1, t2) && m.is_bool(t1);
}

bool proof_checker::match_equiv(expr const* e, expr*& t1, expr*& t2) const {
    return match_oeq(e, t1, t2) || match_eq(e, t1, t2);
}

bool proof_checker::match_implies(expr const* e, expr*& t1, expr*& t2) const {
    return match_op(e, OP_IMPLIES, t1, t2);
}

bool proof_checker::match_eq(expr const* e, expr*& t1, expr*& t2) const {
    return match_op(e, OP_EQ, t1, t2);
}

bool proof_checker::match_oeq(expr const* e, expr*& t1, expr*& t2) const {
    return match_op(e, OP_OEQ, t1, t2);
}

bool proof_checker::match_negated(expr const* a, expr* b) const {
    expr* t = nullptr;
    return
        (match_not(a, t) && t == b) ||
        (match_not(b, t) && t == a);
}

void proof_checker::get_ors(expr* e, expr_ref_vector& ors) {
    ptr_buffer<expr> buffer;
    if (m.is_or(e)) {
        app* a = to_app(e);
        ors.append(a->get_num_args(), a->get_args());
    }
    else {
        ors.push_back(e);
    }
}


void proof_checker::get_hypotheses(proof* p, expr_ref_vector& ante) {
    ptr_vector<proof> stack;
    expr* h = nullptr, *hyp = nullptr;

    stack.push_back(p);
    while (!stack.empty()) {
        p = stack.back();
        SASSERT(m.is_proof(p));
        if (m_hypotheses.contains(p)) {
            stack.pop_back();
            continue;
        }
        if (is_hypothesis(p) && match_fact(p, hyp)) {
            hyp = mk_atom(hyp);
            m_pinned.push_back(hyp);
            m_hypotheses.insert(p, hyp);
            stack.pop_back();
            continue;
        }
        // in this system all hypotheses get bound by lemmas.
        if (m.is_lemma(p)) {
            m_hypotheses.insert(p, mk_nil());
            stack.pop_back();
            continue;
        }
        bool all_found = true;
        ptr_vector<expr> hyps;
        for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
            proof* p_i = m.get_parent(p, i);
            if (m_hypotheses.find(p_i, h)) {
                hyps.push_back(h);
            }
            else {
                stack.push_back(p_i);
                all_found = false;
            }
        }
        if (all_found) {
            h = mk_hyp(hyps.size(), hyps.data());
            m_pinned.push_back(h);
            m_hypotheses.insert(p, h);
            stack.pop_back();
        }
    }

    //
    // dis-assemble the set of obtained hypotheses.
    //
    if (!m_hypotheses.find(p, h)) {
        UNREACHABLE();
    }

    ptr_buffer<expr> hyps;
    ptr_buffer<expr> todo;
    expr_mark mark;
    todo.push_back(h);
    expr* a = nullptr, *b = nullptr;

    while (!todo.empty()) {
        h = todo.back();

        todo.pop_back();
        if (mark.is_marked(h)) {
            continue;
        }
        mark.mark(h, true);
        if (match_cons(h, a, b)) {
            todo.push_back(a);
            todo.push_back(b);
        }
        else if (match_atom(h, a)) {
            ante.push_back(a);
        }
        else {
            SASSERT(match_nil(h));
        }
    }
    TRACE("proof_checker",
          {
              ast_ll_pp(tout << "Getting hypotheses from: ", m, p);
              tout << "Found hypotheses:\n";
              for (unsigned i = 0; i < ante.size(); ++i) {
                  ast_ll_pp(tout, m, ante[i].get());
              }
          });

}

bool proof_checker::match_nil(expr const* e) const {
    return
        is_app(e) &&
        to_app(e)->get_family_id() == m_hyp_fid &&
        to_app(e)->get_decl_kind() == OP_NIL;
}

bool proof_checker::match_cons(expr const* e, expr*& a, expr*& b) const {
    if (is_app(e) &&
        to_app(e)->get_family_id() == m_hyp_fid &&
        to_app(e)->get_decl_kind() == OP_CONS) {
        a = to_app(e)->get_arg(0);
        b = to_app(e)->get_arg(1);
        return true;
    }
    return false;
}


bool proof_checker::match_atom(expr const* e, expr*& a) const {
    if (is_app(e) &&
        to_app(e)->get_family_id() == m_hyp_fid &&
        to_app(e)->get_decl_kind() == OP_ATOM) {
        a = to_app(e)->get_arg(0);
        return true;
    }
    return false;
}

expr* proof_checker::mk_atom(expr* e) {
    return m.mk_app(m_hyp_fid, OP_ATOM, e);
}

expr* proof_checker::mk_cons(expr* a, expr* b) {
    return m.mk_app(m_hyp_fid, OP_CONS, a, b);
}

expr* proof_checker::mk_nil() {
    return m_nil.get();
}

bool proof_checker::is_hypothesis(proof const* p) const {
    return
        m.is_proof(p) &&
        p->get_decl_kind() == PR_HYPOTHESIS;
}

expr* proof_checker::mk_hyp(unsigned num_hyps, expr * const * hyps) {
    expr* result = nullptr;
    for (unsigned i = 0; i < num_hyps; ++i) {
        if (!match_nil(hyps[i])) {
            if (result) {
                result = mk_cons(result, hyps[i]);
            }
            else {
                result = hyps[i];
            }
        }
    }
    if (result == nullptr) {
        return mk_nil();
    }
    else {
        return result;
    }
}

void proof_checker::dump_proof(proof const* pr) {
    if (!m_dump_lemmas)
        return;
    SASSERT(m.has_fact(pr));
    expr * consequent = m.get_fact(pr);
    unsigned num      = m.get_num_parents(pr);
    ptr_buffer<expr> antecedents;
    for (unsigned i = 0; i < num; i++) {
        proof * a = m.get_parent(pr, i);
        SASSERT(m.has_fact(a));
        antecedents.push_back(m.get_fact(a));
    }
    dump_proof(antecedents.size(), antecedents.data(), consequent);
}

void proof_checker::dump_proof(unsigned num_antecedents, expr * const * antecedents, expr * consequent) {
    char buffer[128];
#ifdef _WINDOWS
    sprintf_s(buffer, Z3_ARRAYSIZE(buffer), "proof_lemma_%d.smt2", m_proof_lemma_id);
#else
    sprintf(buffer, "proof_lemma_%d.smt2", m_proof_lemma_id);
#endif
    std::ofstream out(buffer);
    ast_smt_pp pp(m);
    pp.set_benchmark_name("lemma");
    pp.set_status("unsat");
    pp.set_logic(symbol(m_logic.c_str()));
    for (unsigned i = 0; i < num_antecedents; i++)
        pp.add_assumption(antecedents[i]);
    expr_ref n(m);
    n = m.mk_not(consequent);
    pp.display_smt2(out, n);
    out.close();
    m_proof_lemma_id++;
}

bool proof_checker::check_arith_literal(bool is_pos, app* lit0, rational const& coeff, expr_ref& sum, bool& is_strict) {
    arith_util a(m);
    app* lit = lit0;

    if (m.is_not(lit)) {
        lit = to_app(lit->get_arg(0));
        is_pos = !is_pos;
    }
    if (!a.is_le(lit) && !a.is_lt(lit) && !a.is_ge(lit) && !a.is_gt(lit) && !m.is_eq(lit)) {
        IF_VERBOSE(2, verbose_stream() << "Not arith literal: " << mk_pp(lit, m) << "\n";);
        return false;
    }
    SASSERT(lit->get_num_args() == 2);
    sort* s = lit->get_arg(0)->get_sort();
    bool is_int = a.is_int(s);
    if (!is_int && a.is_int_expr(lit->get_arg(0))) {
        is_int = true;
        s = a.mk_int();
    }

    if (!is_int && is_pos && (a.is_gt(lit) || a.is_lt(lit))) {
        is_strict = true;
    }
    if (!is_int && !is_pos && (a.is_ge(lit) || a.is_le(lit))) {
        is_strict = true;
    }


    SASSERT(a.is_int(s) || a.is_real(s));
    expr_ref sign1(m), sign2(m), term(m);
    sign1 = a.mk_numeral(m.is_eq(lit)?coeff:abs(coeff), s);
    sign2 = a.mk_numeral(m.is_eq(lit)?-coeff:-abs(coeff), s);
    if (!sum.get()) {
        sum = a.mk_numeral(rational(0), s);
    }

    expr* a0 = lit->get_arg(0);
    expr* a1 = lit->get_arg(1);

    if (is_pos && (a.is_ge(lit) || a.is_gt(lit))) {
        std::swap(a0, a1);
    }
    if (!is_pos && (a.is_le(lit) || a.is_lt(lit))) {
        std::swap(a0, a1);
    }

    //
    // Multiplying by coefficients over strict
    // and non-strict inequalities:
    //
    // (a <= b) * 2
    // (a - b <= 0) * 2
    // (2a - 2b <= 0)

    // (a < b) * 2       <=>
    // (a +1 <= b) * 2   <=>
    // 2a + 2 <= 2b      <=>
    // 2a+2-2b <= 0

    bool strict_ineq =
        is_pos?(a.is_gt(lit) || a.is_lt(lit)):(a.is_ge(lit) || a.is_le(lit));

    if (is_int && strict_ineq) {
        sum = a.mk_add(sum, sign1);
    }

    term = a.mk_mul(sign1, a0);
    sum = a.mk_add(sum, term);
    term = a.mk_mul(sign2, a1);
    sum = a.mk_add(sum, term);

#if 1
    {
        th_rewriter rw(m);
        rw(sum);
    }

    IF_VERBOSE(2, verbose_stream() << "coeff,lit,sum " << coeff << "\n" << mk_pp(lit0, m) << "\n" << mk_pp(sum, m) << "\n";);
#endif

    return true;
}

bool proof_checker::check_arith_proof(proof* p) {
    func_decl* d = p->get_decl();
    SASSERT(PR_TH_LEMMA == p->get_decl_kind());
    SASSERT(d->get_parameter(0).get_symbol() == "arith");
    unsigned num_params = d->get_num_parameters();
    arith_util autil(m);

    SASSERT(num_params > 0);
    if (num_params == 1) {
        dump_proof(p);
        return true;
    }
    expr* fact = nullptr;
    proof_ref_vector proofs(m);

    if (!match_fact(p, fact)) {
        UNREACHABLE();
        return false;
    }

    if (d->get_parameter(1).get_symbol() != symbol("farkas")) {
        dump_proof(p);
        return true;
    }
    expr_ref sum(m);
    bool is_strict = false;
    unsigned offset = 0;
    vector<rational> coeffs;
    rational lc(1);
    for (unsigned i = 2; i < d->get_num_parameters(); ++i) {
        parameter const& p = d->get_parameter(i);
        if (!p.is_rational()) {
            UNREACHABLE();
            return false;
        }
        coeffs.push_back(p.get_rational());
        lc = lcm(lc, denominator(coeffs.back()));
    }
    if (!lc.is_one()) {
        for (unsigned i = 0; i < coeffs.size(); ++i) {
            coeffs[i] = lc*coeffs[i];
        }
    }

    unsigned num_parents = m.get_num_parents(p);
    for (unsigned i = 0; i < num_parents; i++) {
        proof * a = m.get_parent(p, i);
        SASSERT(m.has_fact(a));
        if (!check_arith_literal(true, to_app(m.get_fact(a)), coeffs[offset++], sum, is_strict)) {
            return false;
        }
    }
    TRACE("proof_checker", 
          for (unsigned i = 0; i < num_parents; i++) 
              tout << coeffs[i] << " * " << mk_bounded_pp(m.get_fact(m.get_parent(p, i)), m) << "\n";
          tout << "fact:" << mk_bounded_pp(fact, m) << "\n";);
    
    if (m.is_or(fact)) {
        app* disj = to_app(fact);
        unsigned num_args = disj->get_num_args();
        for (unsigned i = 0; i < num_args; ++i) {
            app* lit = to_app(disj->get_arg(i));
            if (!check_arith_literal(false, lit,  coeffs[offset++], sum, is_strict)) {
                return false;
            }
        }
    }
    else if (!m.is_false(fact)) {
        if (!check_arith_literal(false, to_app(fact),  coeffs[offset++], sum, is_strict)) {
            return false;
        }
    }

    if (!sum.get()) {
        return false;
    }

    sort* s = sum->get_sort();


    if (is_strict) {
        sum = autil.mk_lt(sum, autil.mk_numeral(rational(0), s));
    }
    else {
        sum = autil.mk_le(sum, autil.mk_numeral(rational(0), s));
    }

    th_rewriter rw(m);
    rw(sum);

    if (!m.is_false(sum)) {
        IF_VERBOSE(1, verbose_stream() << "Arithmetic proof check failed: " << mk_pp(sum, m) << "\n";);
        m_dump_lemmas = true;
        dump_proof(p);
        return false;
    }

    return true;
}
