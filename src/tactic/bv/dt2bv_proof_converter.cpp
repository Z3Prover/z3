/*++
Copyright (c) 2026 Microsoft Corporation
--*/

#include "tactic/bv/dt2bv_proof_converter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/converters/replace_proof_converter.h"
#include "ast/expr_functors.h"
#include "ast/for_each_expr.h"
#include "ast/proofs/proof_utils.h"
#include "params/smt_params.h"
#include "smt/smt_kernel.h"
#include "tactic/tactic.h"

namespace {

class close_encoding_lemmas : public map_proc {
public:
    close_encoding_lemmas(ast_manager& m): map_proc(m) {}
    void operator()(var* v) { visit(v); }
    void operator()(quantifier* q) { visit(q); }
    void operator()(app* a) {
        if (get_expr(a))
            return;
        reconstruct(a);
        app* result = to_app(get_expr(a));
        if (!m.is_lemma(result))
            return;
        expr* conclusion = m.get_fact(result);
        ptr_vector<expr> literals;
        if (m.is_or(conclusion))
            for (expr* literal : *to_app(conclusion))
                literals.push_back(literal);
        else
            literals.push_back(conclusion);
        ptr_vector<proof> todo;
        proof_ref_vector hypotheses(m);
        expr_ref_vector disjuncts(m), residual(m);
        expr_mark visited;
        for (expr* literal : literals) {
            disjuncts.push_back(literal);
            residual.push_back(literal);
        }
        bool quoted = false;
        todo.push_back(m.get_parent(result, 0));
        while (!todo.empty()) {
            proof* current = todo.back();
            todo.pop_back();
            if (visited.is_marked(current))
                continue;
            visited.mark(current, true);
            if (m.is_lemma(current))
                continue;
            if (m.is_hypothesis(current)) {
                expr* fact = m.get_fact(current);
                expr_ref complement(m);
                if (m.is_not(fact))
                    complement = to_app(fact)->get_arg(0);
                else
                    complement = m.mk_not(fact);
                bool covered = false;
                for (expr* literal : literals)
                    covered |= literal == complement;
                if (m.is_or(conclusion) && complement == conclusion) {
                    covered = true;
                    if (!quoted) {
                        quoted = true;
                        disjuncts.push_back(conclusion);
                        residual.push_back(conclusion);
                    }
                }
                if (!covered) {
                    hypotheses.push_back(current);
                    disjuncts.push_back(complement);
                }
            }
            else
                for (unsigned i = 0; i < m.get_num_parents(current); ++i)
                    todo.push_back(m.get_parent(current, i));
        }
        if (hypotheses.empty() && !quoted)
            return;
        expr_ref clause(m.mk_or(disjuncts.size(), disjuncts.data()), m);
        proof_ref closed(m.mk_lemma(m.get_parent(result, 0), clause), m);
        expr_ref restored(quoted ? m.mk_or(residual.size(), residual.data()) : conclusion, m);
        proof_ref_vector premises(m);
        premises.push_back(closed);
        premises.append(hypotheses);
        proof_ref value(hypotheses.empty() ? closed.get() :
                        m.mk_unit_resolution(premises.size(), premises.data(), restored), m);
        if (quoted) {
            proof_ref absorption(m.mk_rewrite(restored, conclusion), m);
            value = m.mk_modus_ponens(value, absorption);
        }
        m_map.insert(a, value, nullptr);
    }
};

// Instantiation arguments live in proof declaration parameters, not AST children.
class substitute_proof_parameters : public map_proc {
    expr_safe_replace& m_substitution;
public:
    substitute_proof_parameters(ast_manager& m, expr_safe_replace& substitution):
        map_proc(m), m_substitution(substitution) {}

    void operator()(var* v) { visit(v); }
    void operator()(quantifier* q) { visit(q); }
    void operator()(app* a) {
        if (get_expr(a))
            return;
        reconstruct(a);
        app* result = to_app(get_expr(a));
        if (!m.is_proof(result))
            return;
        func_decl* f = result->get_decl();
        vector<parameter> parameters;
        expr_ref_vector refs(m);
        bool changed = false;
        for (parameter const& p : f->parameters()) {
            if (p.is_ast() && is_expr(p.get_ast())) {
                expr_ref value(m);
                m_substitution(to_expr(p.get_ast()), value);
                changed |= value.get() != p.get_ast();
                refs.push_back(value);
                parameters.push_back(parameter(value.get()));
            }
            else {
                if (p.is_ast() && is_func_decl(p.get_ast()) &&
                    to_func_decl(p.get_ast())->get_arity() == 0) {
                    expr_ref constant(m.mk_const(to_func_decl(p.get_ast())), m), value(m);
                    m_substitution(constant, value);
                    if (constant != value)
                        throw tactic_exception("dt2bv cannot substitute a declaration-valued encoding parameter");
                }
                parameters.push_back(p);
            }
        }
        if (changed) {
            app* value = m.mk_app(f->get_family_id(), f->get_decl_kind(),
                                 parameters.size(), parameters.data(),
                                 result->get_num_args(), result->get_args());
            m_map.insert(a, value, nullptr);
        }
    }
};

}

dt2bv_proof_converter::dt2bv_proof_converter(ast_manager& m):
    m(m), m_substitution(m), m_sources(m), m_encodings(m), m_proofs(m) {}

void dt2bv_proof_converter::insert_enum(func_decl* original, func_decl* fresh) {
    datatype_util dt(m);
    bv_util bv(m);
    if (original->get_arity() != 0 || fresh->get_arity() != 0 ||
        !dt.is_enum_sort(original->get_range()) || !bv.is_bv_sort(fresh->get_range()))
        throw tactic_exception("dt2bv proof converter requires enumeration and bit-vector constants");
    auto const& constructors = *dt.get_datatype_constructors(original->get_range());
    unsigned width = bv.get_bv_size(fresh->get_range());
    if (!m_proofs.empty() || rational(constructors.size()) > rational::power_of_two(width))
        throw tactic_exception("dt2bv proof converter requires a complete, non-wrapping encoding");
    expr_ref subject(m.mk_const(original), m);
    expr_ref encoding(bv.mk_numeral(rational(constructors.size() - 1), width), m);
    for (unsigned i = constructors.size() - 1; i-- > 0;) {
        expr_ref constructor(m.mk_const(constructors[i]), m);
        expr_ref condition(m.mk_eq(subject, constructor), m);
        expr_ref numeral(bv.mk_numeral(rational(i), width), m);
        encoding = m.mk_ite(condition, numeral, encoding);
    }
    expr_ref source(m.mk_const(fresh), m);
    for (expr* previous : m_sources)
        if (previous == source)
            throw tactic_exception("dt2bv proof converter has a duplicate bit-vector constant");
    m_sources.push_back(source);
    m_encodings.push_back(encoding);
    m_substitution.insert(source, encoding);
}

proof_ref dt2bv_proof_converter::prove(expr* fact) {
    ast_manager certificates(PGM_ENABLED);
    scoped_limits limits(m.limit());
    limits.push_child(&certificates.limit());
    ast_translation to_certificate(m, certificates);
    expr_ref target(to_certificate(fact), certificates);
    smt_params params;
    smt::kernel kernel(certificates, params);
    expr_ref negation(certificates.mk_not(target), certificates);
    proof_ref hypothesis(certificates.mk_hypothesis(negation), certificates);
    kernel.assert_expr(negation, hypothesis);
    if (kernel.check() != l_false)
        throw tactic_exception("dt2bv failed to certify an encoding lemma");
    proof_ref refutation(kernel.get_proof(), certificates);
    if (!refutation || !certificates.is_false(certificates.get_fact(refutation)))
        throw tactic_exception("dt2bv encoding lemma has no refutation certificate");
    // Keep nested PR_LEMMA nodes closed; resolution restores the ambient hypothesis.
    close_encoding_lemmas close(certificates);
    for_each_expr(close, refutation);
    refutation = to_app(close.get_expr(refutation));
    auto check_assertions = [&](expr* e) {
        if (certificates.is_asserted(e))
            throw tactic_exception("dt2bv encoding certificate contains an asserted premise");
    };
    for_each_expr(check_assertions, refutation);
    proof_ref certificate(certificates.mk_lemma(refutation, target), certificates);
    if (!proof_utils::is_closed(certificates, certificate))
        throw tactic_exception("dt2bv encoding certificate contains an open hypothesis");
    ast_translation from_certificate(certificates, m, false);
    auto seed = [&](expr* e) { from_certificate.seed(to_certificate(e), e); };
    for_each_expr(seed, fact);
    return proof_ref(from_certificate(certificate.get()), m);
}

void dt2bv_proof_converter::insert(proof* original, expr* translated) {
    expr_ref fact(m);
    m_substitution(translated, fact);
    expr* before = m.get_fact(original);
    if (before == fact)
        m_proofs.push_back(original);
    else {
        expr_ref equivalence(m.mk_eq(before, fact), m);
        proof_ref certificate = prove(equivalence);
        m_proofs.push_back(m.mk_modus_ponens(original, certificate));
    }
    auto collect_assertions = [&](expr* e) {
        if (m.is_asserted(e))
            m_assertions.insert(m.get_fact(to_app(e)));
    };
    for_each_expr(collect_assertions, original);
}

void dt2bv_proof_converter::insert_bound(expr* bound) {
    expr_ref fact(m);
    m_substitution(bound, fact);
    m_proofs.push_back(prove(fact));
}

proof_ref dt2bv_proof_converter::operator()(ast_manager& manager, unsigned num_source,
                                           proof* const* source) {
    if (&manager != &m || num_source != 1 || !source[0] || !m.is_false(m.get_fact(source[0])))
        throw tactic_exception("dt2bv proof converter requires one refutation in its own context");
    expr_ref result(m);
    m_substitution(source[0], result);
    substitute_proof_parameters parameters(m, m_substitution);
    for_each_expr(parameters, result);
    result = parameters.get_expr(result);
    replace_proof_converter replacements(m);
    for (proof* p : m_proofs)
        replacements.insert(p);
    proof* refutation = to_app(result);
    proof_ref converted = replacements(m, 1, &refutation);
    auto check_assertions = [&](expr* e) {
        if (m.is_asserted(e) && !m_assertions.contains(m.get_fact(to_app(e))))
            throw tactic_exception("dt2bv converted proof contains an unoriginal assertion");
    };
    for_each_expr(check_assertions, converted);
    return converted;
}

proof_converter* dt2bv_proof_converter::translate(ast_translation& translator) {
    auto* result = alloc(dt2bv_proof_converter, translator.to());
    for (unsigned i = 0; i < m_sources.size(); ++i) {
        expr_ref source(translator(m_sources.get(i)), translator.to());
        expr_ref encoding(translator(m_encodings.get(i)), translator.to());
        result->m_sources.push_back(source);
        result->m_encodings.push_back(encoding);
        result->m_substitution.insert(source, encoding);
    }
    for (proof* p : m_proofs)
        result->m_proofs.push_back(translator(p));
    for (expr* assertion : m_assertions)
        result->m_assertions.insert(translator(assertion));
    return result;
}

void dt2bv_proof_converter::display(std::ostream& out) {
    out << "(dt2bv-proof-converter)\n";
}
