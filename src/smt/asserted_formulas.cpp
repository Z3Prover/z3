/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    asserted_formulas.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-11.

Revision History:

--*/
#include "util/warning.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/normal_forms/nnf.h"
#include "ast/pattern/pattern_inference.h"
#include "ast/macros/quasi_macros.h"
#include "smt/asserted_formulas.h"

asserted_formulas::asserted_formulas(ast_manager & m, smt_params & sp, params_ref const& p):
    m(m),
    m_smt_params(sp),
    m_params(p),
    m_rewriter(m),
    m_substitution(m),
    m_scoped_substitution(m_substitution),
    m_defined_names(m),
    m_static_features(m),
    m_qhead(0),
    m_macro_manager(m),
    m_bv_sharing(m),
    m_inconsistent(false),
    m_has_quantifiers(false),
    m_reduce_asserted_formulas(*this),
    m_distribute_forall(*this),
    m_pattern_inference(*this),
    m_refine_inj_axiom(*this),
    m_max_bv_sharing_fn(*this),
    m_elim_term_ite(*this),
    m_pull_nested_quantifiers(*this),
    m_elim_bvs_from_quantifiers(*this),
    m_cheap_quant_fourier_motzkin(*this),
    m_apply_bit2int(*this),
    m_lift_ite(*this),
    m_ng_lift_ite(*this),
    m_find_macros(*this),
    m_propagate_values(*this),
    m_nnf_cnf(*this),
    m_apply_quasi_macros(*this) {

    m_macro_finder = alloc(macro_finder, m, m_macro_manager);

    m_elim_and = true;
    set_eliminate_and(false);

}

void asserted_formulas::setup() {
    switch (m_smt_params.m_lift_ite) {
    case LI_FULL:
        m_smt_params.m_ng_lift_ite = LI_NONE;
        break;
    case LI_CONSERVATIVE:
        if (m_smt_params.m_ng_lift_ite == LI_CONSERVATIVE)
            m_smt_params.m_ng_lift_ite = LI_NONE;
        break;
    default:
        break;
    }

    if (m_smt_params.m_relevancy_lvl == 0)
        m_smt_params.m_relevancy_lemma = false;
}


asserted_formulas::~asserted_formulas() {
}

void asserted_formulas::push_assertion(expr * e, proof * pr, vector<justified_expr>& result) {
    if (inconsistent()) {
        return;
    }
    expr* e1 = nullptr;
    if (m.is_false(e)) {
        result.push_back(justified_expr(m, e, pr));
        m_inconsistent = true;
    }
    else if (m.is_true(e)) {
        // skip
    }
    else if (m.is_and(e)) {
        for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i) {
            expr* arg = to_app(e)->get_arg(i);
            proof_ref _pr(m.proofs_enabled() ? m.mk_and_elim(pr, i) : nullptr, m);
            push_assertion(arg, _pr, result);
        }
    }
    else if (m.is_not(e, e1) && m.is_or(e1)) {
        for (unsigned i = 0; i < to_app(e1)->get_num_args(); ++i) {
            expr* arg = to_app(e1)->get_arg(i);
            proof_ref _pr(m.proofs_enabled() ? m.mk_not_or_elim(pr, i) : nullptr, m);
            expr_ref  narg(mk_not(m, arg), m);
            push_assertion(narg, _pr, result);
        }
    }
    else {
        result.push_back(justified_expr(m, e, pr));
    }
}

void asserted_formulas::updt_params(params_ref const& p) {
    m_params.append(p);
}

void asserted_formulas::set_eliminate_and(bool flag) {
    if (flag == m_elim_and) return;
    m_elim_and = flag;
    if (m_smt_params.m_pull_cheap_ite) m_params.set_bool("pull_cheap_ite", true);
    m_params.set_bool("elim_and", flag);
    m_params.set_bool("arith_ineq_lhs", true);
    m_params.set_bool("sort_sums", true);
    m_params.set_bool("rewrite_patterns", true);
    m_params.set_bool("eq2ineq", m_smt_params.m_arith_eq2ineq);
    m_params.set_bool("gcd_rounding", true);
    m_params.set_bool("expand_select_store", true);
    m_params.set_bool("bv_sort_ac", true);
    m_params.set_bool("som", true);
    m_rewriter.updt_params(m_params);
    flush_cache();
}


void asserted_formulas::assert_expr(expr * e, proof * _in_pr) {
    proof_ref  in_pr(_in_pr, m), pr(_in_pr, m);
    expr_ref   r(e, m);

    if (inconsistent())
        return;

    if (m_smt_params.m_preprocess) {
        TRACE("assert_expr_bug", tout << r << "\n";);
        set_eliminate_and(false); // do not eliminate and before nnf.
        m_rewriter(e, r, pr);
        if (m.proofs_enabled()) {
            if (e == r)
                pr = in_pr;
            else
                pr = m.mk_modus_ponens(in_pr, pr);
        }
        TRACE("assert_expr_bug", tout << "after...\n" << r << "\n";);
    }

    m_has_quantifiers |= ::has_quantifiers(e);

    push_assertion(r, pr, m_formulas);
    TRACE("asserted_formulas_bug", tout << "after assert_expr\n"; display(tout););
}

void asserted_formulas::assert_expr(expr * e) {
    assert_expr(e, m.proofs_enabled() ? m.mk_asserted(e) : nullptr);
}

void asserted_formulas::get_assertions(ptr_vector<expr> & result) const {
    for (justified_expr const& je : m_formulas) result.push_back(je.get_fml());
}

void asserted_formulas::push_scope() {
    SASSERT(inconsistent() || m_qhead == m_formulas.size() || m.canceled());
    TRACE("asserted_formulas_scopes", tout << "before push: " << m_scopes.size() << "\n";);
    m_scoped_substitution.push();
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_formulas_lim = m_formulas.size();
    SASSERT(inconsistent() || s.m_formulas_lim == m_qhead || m.canceled());
    s.m_inconsistent_old = m_inconsistent;
    m_defined_names.push();
    m_bv_sharing.push_scope();
    m_macro_manager.push_scope();
    commit();
    TRACE("asserted_formulas_scopes", tout << "after push: " << m_scopes.size() << "\n";);
}

void asserted_formulas::pop_scope(unsigned num_scopes) {
    TRACE("asserted_formulas_scopes", tout << "before pop " << num_scopes << " of " << m_scopes.size() << "\n";);
    m_bv_sharing.pop_scope(num_scopes);
    m_macro_manager.pop_scope(num_scopes);
    unsigned new_lvl    = m_scopes.size() - num_scopes;
    scope & s           = m_scopes[new_lvl];
    m_inconsistent      = s.m_inconsistent_old;
    m_defined_names.pop(num_scopes);
    m_scoped_substitution.pop(num_scopes);
    m_formulas.shrink(s.m_formulas_lim);
    m_qhead    = s.m_formulas_lim;
    m_scopes.shrink(new_lvl);
    flush_cache();
    TRACE("asserted_formulas_scopes", tout << "after pop " << num_scopes << "\n";);
}

void asserted_formulas::reset() {
    m_defined_names.reset();
    m_qhead = 0;
    m_formulas.reset();
    m_macro_manager.reset();
    m_bv_sharing.reset();
    m_rewriter.reset();
    m_inconsistent = false;
}

bool asserted_formulas::check_well_sorted() const {
    for (justified_expr const& je : m_formulas) {
        if (!is_well_sorted(m, je.get_fml())) return false;
    }
    return true;
}

void asserted_formulas::reduce() {
    if (inconsistent())
        return;
    if (canceled())
        return;
    if (m_qhead == m_formulas.size())
        return;
    if (!m_smt_params.m_preprocess)
        return;
    if (m_macro_manager.has_macros())
        invoke(m_find_macros);

    TRACE("before_reduce", display(tout););
    CASSERT("well_sorted", check_well_sorted());

    set_eliminate_and(false); // do not eliminate and before nnf.
    if (!invoke(m_propagate_values)) return;
    if (!invoke(m_find_macros)) return;
    if (!invoke(m_nnf_cnf)) return;
    set_eliminate_and(true);
    if (!invoke(m_reduce_asserted_formulas)) return;
    if (!invoke(m_pull_nested_quantifiers)) return;
    if (!invoke(m_lift_ite)) return;
    if (!invoke(m_ng_lift_ite)) return;
    if (!invoke(m_elim_term_ite)) return;
    if (!invoke(m_refine_inj_axiom)) return;
    if (!invoke(m_distribute_forall)) return;
    if (!invoke(m_find_macros)) return;
    if (!invoke(m_apply_quasi_macros)) return;
    if (!invoke(m_apply_bit2int)) return;
    if (!invoke(m_cheap_quant_fourier_motzkin)) return;
    if (!invoke(m_pattern_inference)) return;
    if (!invoke(m_max_bv_sharing_fn)) return;
    if (!invoke(m_elim_bvs_from_quantifiers)) return;
    if (!invoke(m_reduce_asserted_formulas)) return;

    IF_VERBOSE(10, verbose_stream() << "(smt.simplifier-done)\n";);
    TRACE("after_reduce", display(tout););
    TRACE("after_reduce_ll", ast_mark visited; display_ll(tout, visited););
    TRACE("macros", m_macro_manager.display(tout););
    flush_cache();
    CASSERT("well_sorted",check_well_sorted());
}


unsigned asserted_formulas::get_formulas_last_level() const {
    if (m_scopes.empty()) {
        return 0;
    }
    else {
        return m_scopes.back().m_formulas_lim;
    }
}

bool asserted_formulas::invoke(simplify_fmls& s) {
    if (!s.should_apply()) return true;
    IF_VERBOSE(10, verbose_stream() << "(smt." << s.id() << ")\n";);
    s();
    IF_VERBOSE(10000, verbose_stream() << "total size: " << get_total_size() << "\n";);
    TRACE("reduce_step_ll", ast_mark visited; display_ll(tout, visited););
    CASSERT("well_sorted",check_well_sorted());
    if (inconsistent() || canceled()) {
        TRACE("after_reduce", display(tout););
        TRACE("after_reduce_ll", ast_mark visited; display_ll(tout, visited););
        return false;
    }
    else {
        return true;
    }
}

void asserted_formulas::display(std::ostream & out) const {
    out << "asserted formulas:\n";
    for (unsigned i = 0; i < m_formulas.size(); i++) {
        if (i == m_qhead)
            out << "[HEAD] ==>\n";
        out << mk_pp(m_formulas[i].get_fml(), m) << "\n";
    }
    out << "inconsistent: " << inconsistent() << "\n";
}

void asserted_formulas::display_ll(std::ostream & out, ast_mark & pp_visited) const {
    if (!m_formulas.empty()) {
        for (justified_expr const& f : m_formulas)
            ast_def_ll_pp(out, m, f.get_fml(), pp_visited, true, false);
        out << "asserted formulas:\n";
        for (justified_expr const& f : m_formulas)
            out << "#" << f.get_fml()->get_id() << " ";
        out << "\n";
    }
}

void asserted_formulas::collect_statistics(statistics & st) const {
}


void asserted_formulas::swap_asserted_formulas(vector<justified_expr>& formulas) {
    SASSERT(!inconsistent() || !formulas.empty());
    m_formulas.shrink(m_qhead);
    m_formulas.append(formulas);
}


void asserted_formulas::find_macros_core() {
    vector<justified_expr> new_fmls;
    unsigned sz = m_formulas.size();
    (*m_macro_finder)(sz - m_qhead, m_formulas.c_ptr() + m_qhead, new_fmls);
    swap_asserted_formulas(new_fmls);
    reduce_and_solve();
}


void asserted_formulas::apply_quasi_macros() {
    TRACE("before_quasi_macros", display(tout););
    vector<justified_expr> new_fmls;
    quasi_macros proc(m, m_macro_manager);
    while (proc(m_formulas.size() - m_qhead,
                m_formulas.c_ptr() + m_qhead,
                new_fmls)) {
        swap_asserted_formulas(new_fmls);
        new_fmls.reset();
    }
    TRACE("after_quasi_macros", display(tout););
    reduce_and_solve();
}

void asserted_formulas::nnf_cnf() {
    nnf              apply_nnf(m, m_defined_names);
    vector<justified_expr> new_fmls;
    expr_ref_vector  push_todo(m);
    proof_ref_vector push_todo_prs(m);

    unsigned i  = m_qhead;
    unsigned sz = m_formulas.size();
    TRACE("nnf_bug", tout << "i: " << i << " sz: " << sz << "\n";);
    for (; i < sz; i++) {
        expr * n    = m_formulas[i].get_fml();
        TRACE("nnf_bug", tout << "processing:\n" << mk_pp(n, m) << "\n";);
        proof * pr  = m_formulas[i].get_proof();
        expr_ref   r1(m);
        proof_ref  pr1(m);
        push_todo.reset();
        push_todo_prs.reset();
        CASSERT("well_sorted", is_well_sorted(m, n));
        apply_nnf(n, push_todo, push_todo_prs, r1, pr1);
        CASSERT("well_sorted",is_well_sorted(m, r1));
        pr = m.proofs_enabled() ? m.mk_modus_ponens(pr, pr1) : nullptr;
        push_todo.push_back(r1);
        push_todo_prs.push_back(pr);

        if (canceled()) {
            return;
        }
        unsigned sz2 = push_todo.size();
        for (unsigned k = 0; k < sz2; k++) {
            expr * n   = push_todo.get(k);
            pr = nullptr;
            m_rewriter(n, r1, pr1);
            CASSERT("well_sorted",is_well_sorted(m, r1));
            if (canceled()) {
                return;
            }
            if (m.proofs_enabled())
                pr = m.mk_modus_ponens(push_todo_prs.get(k), pr1);
            push_assertion(r1, pr, new_fmls);
        }
    }
    swap_asserted_formulas(new_fmls);
}

void asserted_formulas::simplify_fmls::operator()() {
    vector<justified_expr> new_fmls;
    unsigned sz = af.m_formulas.size();
    for (unsigned i = af.m_qhead; i < sz; i++) {
        auto& j = af.m_formulas[i];
        expr_ref result(m);
        proof_ref result_pr(m);
        simplify(j, result, result_pr);
        if (m.proofs_enabled()) {
            if (!result_pr) result_pr = m.mk_rewrite(j.get_fml(), result);
            result_pr = m.mk_modus_ponens(j.get_proof(), result_pr);
        }
        if (j.get_fml() == result) {
            new_fmls.push_back(j);
        }
        else {
            af.push_assertion(result, result_pr, new_fmls);
        }
        if (af.canceled()) return;
    }
    af.swap_asserted_formulas(new_fmls);
    TRACE("asserted_formulas", af.display(tout););
    post_op();
}


void asserted_formulas::reduce_and_solve() {
    IF_VERBOSE(10, verbose_stream() << "(smt.reducing)\n";);
    flush_cache(); // collect garbage
    m_reduce_asserted_formulas();
}


void asserted_formulas::commit() {
    commit(m_formulas.size());
}

void asserted_formulas::commit(unsigned new_qhead) {
    m_macro_manager.mark_forbidden(new_qhead - m_qhead, m_formulas.c_ptr() + m_qhead);
    m_expr2depth.reset();
    for (unsigned i = m_qhead; i < new_qhead; ++i) {
        justified_expr const& j = m_formulas[i];
        update_substitution(j.get_fml(), j.get_proof());
    }
    m_qhead = new_qhead;
}

void asserted_formulas::propagate_values() {
    flush_cache();

    unsigned num_prop = 0;
    unsigned num_iterations = 0;
    while (!inconsistent() && ++num_iterations < 2) {
        m_expr2depth.reset();
        m_scoped_substitution.push();
        unsigned prop = num_prop;
        TRACE("propagate_values", tout << "before:\n"; display(tout););
        unsigned i  = m_qhead;
        unsigned sz = m_formulas.size();
        for (; i < sz; i++) {
            prop += propagate_values(i);
        }
        flush_cache();
        m_scoped_substitution.pop(1);
        m_expr2depth.reset();
        m_scoped_substitution.push();
        TRACE("propagate_values", tout << "middle:\n"; display(tout););
        i = sz;
        while (i > m_qhead) {
            --i;
            prop += propagate_values(i);
        }
        m_scoped_substitution.pop(1);
        flush_cache();
        TRACE("propagate_values", tout << "after:\n"; display(tout););
        if (num_prop == prop) {
            break;
        }
        num_prop = prop;
    }
    if (num_prop > 0)
        m_reduce_asserted_formulas();
}

unsigned asserted_formulas::propagate_values(unsigned i) {
    expr_ref n(m_formulas[i].get_fml(), m);
    expr_ref new_n(m);
    proof_ref new_pr(m);
    m_rewriter(n, new_n, new_pr);
    if (m.proofs_enabled()) {
        proof * pr  = m_formulas[i].get_proof();
        new_pr = m.mk_modus_ponens(pr, new_pr);
    }
    justified_expr j(m, new_n, new_pr);
    m_formulas[i] = j;
    if (m_formulas[i].get_fml() != new_n) {
        std::cout << "NOT updated\n";
    }
    if (m.is_false(j.get_fml())) {
        m_inconsistent = true;
    }
    update_substitution(new_n, new_pr);
    return n != new_n ? 1 : 0;
}

void asserted_formulas::update_substitution(expr* n, proof* pr) {
    expr* lhs, *rhs, *n1;
    proof_ref pr1(m);
    if (is_ground(n) && m.is_eq(n, lhs, rhs)) {
        compute_depth(lhs);
        compute_depth(rhs);
        if (is_gt(lhs, rhs)) {
            TRACE("propagate_values", tout << "insert " << mk_pp(lhs, m) << " -> " << mk_pp(rhs, m) << "\n";);
            m_scoped_substitution.insert(lhs, rhs, pr);
            return;
        }
        if (is_gt(rhs, lhs)) {
            TRACE("propagate_values", tout << "insert " << mk_pp(rhs, m) << " -> " << mk_pp(lhs, m) << "\n";);
            pr1 = m.proofs_enabled() ? m.mk_symmetry(pr) : nullptr;
            m_scoped_substitution.insert(rhs, lhs, pr1);
            return;
        }
        TRACE("propagate_values", tout << "incompatible " << mk_pp(n, m) << "\n";);
    }
    if (m.is_not(n, n1)) {
        pr1 = m.proofs_enabled() ? m.mk_iff_false(pr) : nullptr;
        m_scoped_substitution.insert(n1, m.mk_false(), pr1);
    }
    else {
        pr1 = m.proofs_enabled() ? m.mk_iff_true(pr) : nullptr;
        m_scoped_substitution.insert(n, m.mk_true(), pr1);
    }
}


/**
   \brief implement a Knuth-Bendix ordering on expressions.
*/

bool asserted_formulas::is_gt(expr* lhs, expr* rhs) {
    if (lhs == rhs) {
        return false;
    }
    // values are always less in ordering than non-values.
    bool v1 = m.is_value(lhs);
    bool v2 = m.is_value(rhs);
    if (!v1 && v2) {
        return true;
    }
    if (v1 && !v2) {
        return false;
    }
    SASSERT(is_ground(lhs) && is_ground(rhs));
    if (depth(lhs) > depth(rhs)) {
        return true;
    }
    if (depth(lhs) == depth(rhs) && is_app(lhs) && is_app(rhs)) {
        app* l = to_app(lhs);
        app* r = to_app(rhs);
        if (l->get_decl()->get_id() != r->get_decl()->get_id()) {
            return l->get_decl()->get_id() > r->get_decl()->get_id();
        }
        if (l->get_num_args() != r->get_num_args()) {
            return l->get_num_args() > r->get_num_args();
        }
        for (unsigned i = 0; i < l->get_num_args(); ++i) {
            if (l->get_arg(i) != r->get_arg(i)) {
                return is_gt(l->get_arg(i), r->get_arg(i));
            }
        }
        UNREACHABLE();
    }

    return false;
}

void asserted_formulas::compute_depth(expr* e) {
    ptr_vector<expr> todo;
    todo.push_back(e);
    while (!todo.empty()) {
        e = todo.back();
        unsigned d = 0;
        if (m_expr2depth.contains(e)) {
            todo.pop_back();
            continue;
        }
        if (is_app(e)) {
            app* a = to_app(e);
            bool visited = true;
            for (expr* arg : *a) {
                unsigned d1 = 0;
                if (m_expr2depth.find(arg, d1)) {
                    d = std::max(d, d1);
                }
                else {
                    visited = false;
                    todo.push_back(arg);
                }
            }
            if (!visited) {
                continue;
            }
        }
        todo.pop_back();
        m_expr2depth.insert(e, d + 1);
    }
}

proof * asserted_formulas::get_inconsistency_proof() const {
    if (!inconsistent())
        return nullptr;
    if (!m.proofs_enabled())
        return nullptr;
    for (justified_expr const& j : m_formulas) {
        if (m.is_false(j.get_fml()))
            return j.get_proof();
    }
    UNREACHABLE();
    return nullptr;
}

void asserted_formulas::refine_inj_axiom_fn::simplify(justified_expr const& j, expr_ref& n, proof_ref& p) {
    expr* f = j.get_fml();
    if (is_quantifier(f) && simplify_inj_axiom(m, to_quantifier(f), n)) {
        TRACE("inj_axiom", tout << "simplifying...\n" << mk_pp(f, m) << "\n" << n << "\n";);
    }
    else {
        n = j.get_fml();
    }
}


unsigned asserted_formulas::get_total_size() const {
    expr_mark visited;
    unsigned r  = 0;
    for (justified_expr const& j : m_formulas)
        r += get_num_exprs(j.get_fml(), visited);
    return r;
}


#ifdef Z3DEBUG
void pp(asserted_formulas & f) {
    f.display(std::cout);
}
#endif
