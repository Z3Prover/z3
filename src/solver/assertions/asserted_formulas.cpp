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
#include <vector>
#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/recfun_replace.h"
#include "ast/rewriter/func_decl_replace.h"
#include "ast/rewriter/var_subst.h"
#include "ast/occurs.h"
#include "ast/for_each_expr.h"
#include "ast/occurs.h"
#include "ast/bv_decl_plugin.h"
#include "solver/assertions/asserted_formulas.h"


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
    m_qe_lite(*this),
    m_pull_nested_quantifiers(*this),
    m_elim_bvs_from_quantifiers(*this),
    m_cheap_quant_fourier_motzkin(*this),
    m_apply_bit2int(*this),
    m_bv_size_reduce(*this),
    m_lift_ite(*this),
    m_ng_lift_ite(*this),
    m_find_macros(*this),
    m_find_recfuns(*this),
    m_propagate_values(*this),
    m_nnf_cnf(*this),
    m_apply_quasi_macros(*this),
    m_flatten_clauses(*this),
    m_lazy_scopes(0) {

    m_macro_finder = alloc(macro_finder, m, m_macro_manager);

    m_elim_and = true;
    set_eliminate_and(false);

}

void asserted_formulas::setup() {
    switch (m_smt_params.m_lift_ite) {
    case lift_ite_kind::LI_FULL:
        m_smt_params.m_ng_lift_ite = lift_ite_kind::LI_NONE;
        break;
    case lift_ite_kind::LI_CONSERVATIVE:
        if (m_smt_params.m_ng_lift_ite == lift_ite_kind::LI_CONSERVATIVE)
            m_smt_params.m_ng_lift_ite = lift_ite_kind::LI_NONE;
        break;
    default:
        break;
    }

    if (m_smt_params.m_relevancy_lvl == 0)
        m_smt_params.m_relevancy_lemma = false;
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
    //m_params.set_bool("expand_nested_stores", true);
    m_params.set_bool("bv_sort_ac", true);
    // seq theory solver keeps terms in normal form and has to interact with side-effect of rewriting
    m_params.set_bool("coalesce_chars", m_smt_params.m_string_solver != symbol("seq"));
    m_params.set_bool("som", true);
    if (m_smt_params.m_arith_mode == arith_solver_id::AS_OLD_ARITH)
        m_params.set_bool("flat", true);
    m_rewriter.updt_params(m_params);
    flush_cache();
}


void asserted_formulas::assert_expr(expr * e, proof * _in_pr) {
    force_push();
    proof_ref  in_pr(_in_pr, m), pr(_in_pr, m);
    expr_ref   e_ref(e, m);
    expr_ref   r(e, m);
    SASSERT(m.is_bool(e));

    if (inconsistent())
        return;

    if (m.is_true(e))
        return;

    if (m_smt_params.m_preprocess) {
        TRACE(assert_expr_bug, tout << r << "\n";);
        set_eliminate_and(false); // do not eliminate and before nnf.
        m_rewriter(e_ref, r, pr);
        if (m.proofs_enabled()) {
            if (e_ref == r)
                pr = in_pr;
            else
                pr = m.mk_modus_ponens(in_pr, pr);
        }
        TRACE(assert_expr_bug, tout << "after...\n" << r << "\n" << pr << "\n";);
    }

    m_has_quantifiers |= ::has_quantifiers(e_ref);

    push_assertion(r, pr, m_formulas);
    TRACE(asserted_formulas_bug, tout << "after assert_expr\n"; display(tout););
}

void asserted_formulas::assert_expr(expr * e) {
    assert_expr(e, m.proofs_enabled() ? m.mk_asserted(e) : nullptr);
}

void asserted_formulas::get_assertions(ptr_vector<expr> & result) const {
    for (justified_expr const& je : m_formulas) result.push_back(je.fml());
}

void asserted_formulas::push_scope() {
    ++m_lazy_scopes;
}

void asserted_formulas::push_scope_core() {
    reduce();
    commit();
    SASSERT(inconsistent() || m_qhead == m_formulas.size() || m.limit().is_canceled());
    TRACE(asserted_formulas_scopes, tout << "before push: " << m_scopes.size() << "\n");
    m_scoped_substitution.push();
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_formulas_lim = m_formulas.size();
    SASSERT(inconsistent() || s.m_formulas_lim == m_qhead || m.limit().is_canceled());
    s.m_inconsistent_old = m_inconsistent;
    m_defined_names.push();
    m_elim_term_ite.push();
    m_bv_sharing.push_scope();
    m_macro_manager.push_scope();
    m_bv_size_reduce.push_scope();
    commit();
    TRACE(asserted_formulas_scopes, tout << "after push: " << m_scopes.size() << "\n");
}

void asserted_formulas::force_push() {
    for (; m_lazy_scopes > 0; --m_lazy_scopes)
        push_scope_core();
}

void asserted_formulas::pop_scope(unsigned num_scopes) {
    if (num_scopes <= m_lazy_scopes) {
        m_lazy_scopes -= num_scopes;
        return;
    }
    num_scopes -= m_lazy_scopes;
    m_lazy_scopes = 0;
    
    TRACE(asserted_formulas_scopes, tout << "before pop " << num_scopes << " of " << m_scopes.size() << "\n";);
    m_bv_sharing.pop_scope(num_scopes);
    m_macro_manager.pop_scope(num_scopes);
    m_bv_size_reduce.pop_scope(num_scopes);
    unsigned new_lvl    = m_scopes.size() - num_scopes;
    scope & s           = m_scopes[new_lvl];
    m_inconsistent      = s.m_inconsistent_old;
    m_defined_names.pop(num_scopes);
    m_elim_term_ite.pop(num_scopes);
    m_scoped_substitution.pop(num_scopes);
    m_formulas.shrink(s.m_formulas_lim);
    m_qhead    = s.m_formulas_lim;
    m_scopes.shrink(new_lvl);
    flush_cache();
    TRACE(asserted_formulas_scopes, tout << "after pop " << num_scopes << "\n";);
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

void asserted_formulas::finalize() {
    reset();
    m_substitution.cleanup();
}

bool asserted_formulas::check_well_sorted() const {
    for (justified_expr const& je : m_formulas) {
        if (!is_well_sorted(m, je.fml())) return false;
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
    if (!m_has_quantifiers && !m_smt_params.m_preprocess)
        return;
    if (m_macro_manager.has_macros())
        invoke(m_find_macros);

    TRACE(before_reduce, display(tout););
    CASSERT("well_sorted", check_well_sorted());

    IF_VERBOSE(10, verbose_stream() << "(smt.simplify-begin :num-exprs " << get_total_size() << ")\n";);

    set_eliminate_and(false); // do not eliminate and before nnf.
    if (!invoke(m_find_recfuns)) return;
    if (!invoke(m_propagate_values)) return;
    if (!invoke(m_find_macros)) return;
    if (!invoke(m_nnf_cnf)) return;
    set_eliminate_and(true);
    if (!invoke(m_reduce_asserted_formulas)) return;
    if (!invoke(m_pull_nested_quantifiers)) return;
    if (!invoke(m_lift_ite)) return;
    m_lift_ite.m_functor.set_conservative(m_smt_params.m_lift_ite == lift_ite_kind::LI_CONSERVATIVE);
    m_ng_lift_ite.m_functor.set_conservative(m_smt_params.m_ng_lift_ite == lift_ite_kind::LI_CONSERVATIVE);
    if (!invoke(m_ng_lift_ite)) return;
    if (!invoke(m_elim_term_ite)) return;
    if (!invoke(m_qe_lite)) return;
    if (!invoke(m_refine_inj_axiom)) return;
    if (!invoke(m_distribute_forall)) return;
    if (!invoke(m_find_macros)) return;
    if (!invoke(m_apply_quasi_macros)) return;
    if (!invoke(m_apply_bit2int)) return;
    if (!invoke(m_bv_size_reduce)) return;
    if (!invoke(m_cheap_quant_fourier_motzkin)) return;
    if (!invoke(m_pattern_inference)) return;
    if (!invoke(m_max_bv_sharing_fn)) return;
    if (!invoke(m_elim_bvs_from_quantifiers)) return;
    if (!invoke(m_reduce_asserted_formulas)) return;
    if (!invoke(m_flatten_clauses)) return;
//    if (!invoke(m_propagate_values)) return;

    IF_VERBOSE(10, verbose_stream() << "(smt.simplifier-done :num-exprs " << get_total_size() << ")\n";);
    TRACE(after_reduce, display(tout););
    TRACE(after_reduce_ll, ast_mark visited; display_ll(tout, visited););
    TRACE(macros, m_macro_manager.display(tout););
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
    s();
    IF_VERBOSE(10, verbose_stream() << "(smt." << s.id() << " :num-exprs " << get_total_size() << ")\n";);
    IF_VERBOSE(10000, verbose_stream() << "total size: " << get_total_size() << "\n";);
    TRACE(reduce_step_ll, ast_mark visited; display_ll(tout, visited););
    CASSERT("well_sorted",check_well_sorted());
    TRACE(after_reduce, display(tout << s.id() << "\n"););
    if (inconsistent() || canceled()) {
        TRACE(after_reduce_ll, ast_mark visited; display_ll(tout, visited););
        return false;
    }
    else {
        return true;
    }
}

void asserted_formulas::display(std::ostream & out) const {
    out << "asserted formulas:\n";
    for (unsigned i = 0; i < m_formulas.size(); ++i) {
        if (i == m_qhead)
            out << "[HEAD] ==>\n";
        out << mk_pp(m_formulas[i].fml(), m) << "\n";
    }
    out << "inconsistent: " << inconsistent() << "\n";
}

void asserted_formulas::display_ll(std::ostream & out, ast_mark & pp_visited) const {
    if (!m_formulas.empty()) {
        for (justified_expr const& f : m_formulas)
            ast_def_ll_pp(out, m, f.fml(), pp_visited, true, false);
        out << "asserted formulas:\n";
        for (justified_expr const& f : m_formulas)
            out << "#" << f.fml()->get_id() << " ";
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



/**
   \brief Detect (mutually) recursive function definitions among the asserted axioms and
   register them as recursive function definitions (as if declared with define-funs-rec).

   A candidate is an axiom of the form
        (forall X (= (f X) body))        or        (forall X (= body (f X)))
   where f is uninterpreted, is applied to exactly the bound variables (each once), and has
   exactly one such axiom.  If body is (g X) for a recursive function g (a "mirror"
   definition whose own body refers back to uninterpreted candidates), g is inlined one step,
   so the recursion that goes through the axioms becomes visible.

   The candidates form a call graph; every strongly connected component that contains a
   cycle is turned into one group of recursive definitions f' over fresh recfun symbols.
   f is then treated as the macro f(X) = f'(X): the axiom is removed, f is replaced by f'
   in all asserted formulas, and the macro provides the model interpretation of f.

   This is always sound for unsat (every unfolding is an instance of the axiom).  It is
   sound for sat only when the definitions are terminating, which z3 cannot check; the
   transformation is therefore controlled by smt.recfun_finder (off by default).
*/
namespace {
    // does e contain an application of one of the symbols in syms?
    bool contains_sym(ast_manager& m, expr* e, obj_hashtable<func_decl> const& syms) {
        for (expr* t : subterms::all(expr_ref(e, m)))
            if (is_app(t) && syms.contains(to_app(t)->get_decl()))
                return true;
        return false;
    }

    // The simplifier turns Boolean (ite c t true) into (or (not c) t) and (ite c t false) into
    // (and c t). Recursive definitions need their recursive calls guarded by ite so that they are
    // unfolded lazily, case by case. Rebuild the guards: in an or/and, the disjuncts/conjuncts
    // without recursive calls become the condition.
    expr_ref guard_recursion(ast_manager& m, expr* e, obj_hashtable<func_decl> const& syms) {
        expr_ref r(e, m);
        if (!contains_sym(m, e, syms))
            return r;
        if (m.is_ite(e)) {
            app* a = to_app(e);
            expr_ref t = guard_recursion(m, a->get_arg(1), syms);
            expr_ref el = guard_recursion(m, a->get_arg(2), syms);
            r = m.mk_ite(a->get_arg(0), t, el);
            return r;
        }
        if (m.is_not(e)) {
            r = m.mk_not(guard_recursion(m, to_app(e)->get_arg(0), syms));
            return r;
        }
        if (m.is_or(e) || m.is_and(e)) {
            bool is_or = m.is_or(e);
            expr_ref_vector guards(m), recs(m);
            for (expr* arg : *to_app(e))
                (contains_sym(m, arg, syms) ? recs : guards).push_back(guard_recursion(m, arg, syms));
            if (guards.empty())
                return r;
            expr_ref g(m), rest(m);
            g = is_or ? mk_or(guards) : mk_and(guards);
            rest = is_or ? mk_or(recs) : mk_and(recs);
            r = is_or ? m.mk_ite(g, m.mk_true(), rest) : m.mk_ite(g, rest, m.mk_false());
            return r;
        }
        return r;
    }

    // every recursive call must be below an ite
    bool recursion_guarded(ast_manager& m, expr* e, obj_hashtable<func_decl> const& syms) {
        if (m.is_ite(e))
            return true;
        if (is_app(e)) {
            app* a = to_app(e);
            if (syms.contains(a->get_decl()))
                return false;
            for (expr* arg : *a)
                if (!recursion_guarded(m, arg, syms))
                    return false;
        }
        return true;
    }
}

void asserted_formulas::find_recfuns_core() {
    if (!m.has_plugin(symbol("recfun")))
        m.register_plugin(symbol("recfun"), alloc(recfun::decl::plugin));
    recfun::util ru(m);
    recfun::decl::plugin& plugin = ru.get_plugin();
    macro_util& mu = m_macro_manager.get_util();
    unsigned sz = m_formulas.size();

    // function symbols occurring in committed formulas cannot be redefined here
    obj_hashtable<func_decl> committed;
    {
        struct proc {
            obj_hashtable<func_decl>& s;
            proc(obj_hashtable<func_decl>& s): s(s) {}
            void operator()(app* a) { s.insert(a->get_decl()); }
            void operator()(var*) {}
            void operator()(quantifier*) {}
        };
        proc p(committed);
        expr_mark visited;
        for (unsigned i = 0; i < m_qhead; ++i)
            for_each_expr(p, visited, m_formulas[i].fml());
    }

    struct candidate {
        quantifier* q;
        app*        head;
        expr_ref    def;
        func_decl*  mirror;
        unsigned    fml_idx;
    };
    vector<candidate> cands;
    obj_map<func_decl, unsigned> f2c;
    obj_hashtable<func_decl> ambiguous;

    for (unsigned i = m_qhead; i < sz; ++i) {
        expr* fml = m_formulas[i].fml();
        if (!is_forall(fml))
            continue;
        quantifier* q = to_quantifier(fml);
        IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :axiom " << mk_pp(q->get_expr(), m) << ")\n";);
        unsigned nd = q->get_num_decls();
        app_ref head(m);
        expr_ref defr(m);
        // Recognize a definitional axiom for a head f(X) where f is applied to exactly the
        // bound variables. Unlike macro_util::is_simple_macro, the head is allowed to occur in
        // the body (that is what makes it recursive). The body itself can be any expression:
        //   (= (f X) body) / (= body (f X))            [also iff, since eq==iff for Bool]
        //   (not (= (f X) body)) / (not (= body (f X))) [Boolean head, negated form]
        //   arithmetic normal form (= (+ (f X) t) c)   [is_arith_macro]
        {
            expr* n = q->get_expr();
            expr *a = nullptr, *b = nullptr;
            bool neg = m.is_not(n, n);
            if (m.is_eq(n, a, b) && (!neg || m.is_bool(a))) {
                if (mu.is_macro_head(a, nd))
                    head = to_app(a), defr = neg ? m.mk_not(b) : expr_ref(b, m);
                else if (mu.is_macro_head(b, nd))
                    head = to_app(b), defr = neg ? m.mk_not(a) : expr_ref(a, m);
            }
            if (!head) {
                app_ref ahead(m);
                expr_ref adef(m);
                bool inv = false;
                if (!neg && mu.is_arith_macro(n, nd, ahead, adef, inv))
                    head = ahead, defr = adef;
            }
        }
        if (!head) {
            IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :no-head)\n";);
            continue;
        }
        app* head_app = head.get();
        expr* def = defr.get();
        func_decl* f = head_app->get_decl();
        if (committed.contains(f) || m_macro_manager.is_forbidden(f) || m_macro_manager.contains(f))
            continue;
        if (f2c.contains(f)) {
            ambiguous.insert(f);
            continue;
        }
        expr_ref d(def, m);
        // z3's recfun theory does not support lambdas in a recursive body (def::compute_cases
        // throws). Leave such an axiom untouched rather than abort the solve. A recursive call
        // that appears under a lambda (a binder that shifts de Bruijn indices) is likewise not
        // handled: is_macro_head would not recognise the shifted variables, so it is skipped here.
        {
            bool has_lam = false;
            for (expr* e : subterms::all(d))
                if (is_lambda(e)) { has_lam = true; break; }
            if (has_lam) {
                IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :lambda-in-body " << f->get_name() << ")\n";);
                continue;
            }
        }
        func_decl* mirror = nullptr;
        // mirror: def is g(X) with the same argument variables, g a recursive definition
        if (is_app(def) && ru.is_defined(to_app(def)->get_decl()) && ru.has_def(to_app(def)->get_decl()) &&
            to_app(def)->get_num_args() == head_app->get_num_args()) {
            app* ga = to_app(def);
            bool same = !committed.contains(ga->get_decl());
            for (unsigned k = 0; same && k < ga->get_num_args(); ++k)
                same = ga->get_arg(k) == head_app->get_arg(k);
            recfun::def& gd = ru.get_def(ga->get_decl());
            if (same && gd.get_rhs() && gd.get_vars().size() == ga->get_num_args()) {
                unsigned max_idx = 0;
                for (var* v : gd.get_vars())
                    max_idx = std::max(max_idx, v->get_idx() + 1);
                expr_ref_vector sub(m);
                for (unsigned k = 0; k < max_idx; ++k)
                    sub.push_back(m.mk_var(k, m.mk_bool_sort()));
                for (unsigned k = 0; k < ga->get_num_args(); ++k)
                    sub[gd.get_vars()[k]->get_idx()] = ga->get_arg(k);
                var_subst vs(m, false);
                d = vs(gd.get_rhs(), sub.size(), sub.data());
                mirror = ga->get_decl();
            }
        }
        f2c.insert(f, cands.size());
        IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :candidate " << f->get_name() << (mirror ? " :mirror " : "") << (mirror ? mirror->get_name().str() : std::string()) << ")\n";);
        cands.push_back(candidate{q, head_app, d, mirror, i});
    }

    IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :candidates " << cands.size() << " :ambiguous " << ambiguous.size() << ")\n";);
    // symbol -> candidate index (heads and their mirrors)
    obj_map<func_decl, unsigned> sym2c;
    for (unsigned i = 0; i < cands.size(); ++i) {
        if (ambiguous.contains(cands[i].head->get_decl()))
            continue;
        sym2c.insert(cands[i].head->get_decl(), i);
        if (cands[i].mirror)
            sym2c.insert(cands[i].mirror, i);
    }

    // call graph
    unsigned n = cands.size();
    vector<unsigned_vector> succ(n);
    for (unsigned i = 0; i < n; ++i) {
        if (ambiguous.contains(cands[i].head->get_decl()))
            continue;
        for (expr* e : subterms::all(expr_ref(cands[i].def.get(), m))) {
            unsigned j;
            if (is_app(e) && sym2c.find(to_app(e)->get_decl(), j))
                succ[i].push_back(j);
        }
    }

    // Tarjan's SCC
    unsigned_vector index, low, stack;
    svector<bool> on_stack;
    index.resize(n, UINT_MAX);
    low.resize(n, 0);
    on_stack.resize(n, false);
    vector<unsigned_vector> comps;
    unsigned counter = 0;
    std::function<void(unsigned)> strong = [&](unsigned v) {
        index[v] = low[v] = counter++;
        stack.push_back(v);
        on_stack[v] = true;
        for (unsigned w : succ[v]) {
            if (index[w] == UINT_MAX) {
                strong(w);
                low[v] = std::min(low[v], low[w]);
            }
            else if (on_stack[w])
                low[v] = std::min(low[v], index[w]);
        }
        if (low[v] == index[v]) {
            unsigned_vector comp;
            unsigned w;
            do {
                w = stack.back();
                stack.pop_back();
                on_stack[w] = false;
                comp.push_back(w);
            }
            while (w != v);
            comps.push_back(comp);
        }
    };
    for (unsigned v = 0; v < n; ++v)
        if (index[v] == UINT_MAX && !ambiguous.contains(cands[v].head->get_decl()))
            strong(v);

    IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :components " << comps.size() << ")\n"; for (auto const& comp : comps) { verbose_stream() << "  ("; for (unsigned i : comp) verbose_stream() << cands[i].head->get_decl()->get_name() << " "; verbose_stream() << ")\n"; });
    // keep the components that are actually recursive
    vector<unsigned_vector> rec_comps;
    for (auto const& comp : comps) {
        bool rec = comp.size() > 1;
        if (!rec)
            for (unsigned w : succ[comp[0]])
                rec |= w == comp[0];
        if (rec)
            rec_comps.push_back(comp);
    }
    // A head must not occur in a recursive definition that survives the transformation:
    // the macro f(X) = f'(X) could not be applied inside such a body (see macro_manager::insert).
    // Mirrors of accepted components are redefined as aliases, so they do not count.
    // Rejecting a component keeps its mirrors, which may block others: iterate to a fixpoint.
    svector<bool> accepted;
    accepted.resize(rec_comps.size(), true);
    bool changed = true;
    while (changed) {
        changed = false;
        obj_hashtable<func_decl> mirrors;
        for (unsigned c = 0; c < rec_comps.size(); ++c)
            if (accepted[c])
                for (unsigned i : rec_comps[c])
                    if (cands[i].mirror)
                        mirrors.insert(cands[i].mirror);
        for (unsigned c = 0; c < rec_comps.size(); ++c) {
            if (!accepted[c])
                continue;
            bool blocked = false;
            for (func_decl* g : ru.get_rec_funs()) {
                if (mirrors.contains(g) || !ru.has_def(g))
                    continue;
                if (ru.get_def(g).is_macro()) // define-fun: applications are expanded by the parser
                    continue;
                expr* rhs = ru.get_def(g).get_rhs();
                for (unsigned i : rec_comps[c])
                    if (rhs && occurs(cands[i].head->get_decl(), rhs)) {
                        blocked = true;
                        IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :blocked-by " << g->get_name() << " :head " << cands[i].head->get_decl()->get_name() << ")\n";);
                    }
            }
            if (blocked) {
                accepted[c] = false;
                changed = true;
                IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :blocked " << cands[rec_comps[c][0]].head->get_decl()->get_name() << ")\n";);
            }
        }
    }
    {
        vector<unsigned_vector> kept;
        for (unsigned c = 0; c < rec_comps.size(); ++c)
            if (accepted[c])
                kept.push_back(rec_comps[c]);
        rec_comps.swap(kept);
    }

    unsigned num_defs = 0;
    func_decl_replace replace(m);
    std::vector<std::pair<unsigned, recfun::promise_def>> pdefs;
    func_decl_ref_vector new_decls(m);
    uint_set removed;

    obj_hashtable<func_decl> rec_syms;
    for (auto const& comp : rec_comps)
        for (unsigned i : comp) {
            rec_syms.insert(cands[i].head->get_decl());
            if (cands[i].mirror)
                rec_syms.insert(cands[i].mirror);
        }
    // Recursive calls have to be guarded by ite, otherwise a definition is unfolded eagerly
    // (as an unconditional macro) and unfolding may not terminate. A definition without guards
    // is fine as long as every cycle of recursive calls passes through a guarded definition,
    // i.e. the unguarded definitions of a component form an acyclic subgraph.
    {
        vector<unsigned_vector> kept;
        for (auto const& comp : rec_comps) {
            uint_set unguarded, in_comp;
            for (unsigned i : comp) {
                in_comp.insert(i);
                cands[i].def = guard_recursion(m, cands[i].def, rec_syms);
                if (!recursion_guarded(m, cands[i].def, rec_syms))
                    unguarded.insert(i);
            }
            // cycle detection on the unguarded subgraph (colors: 0 white, 1 gray, 2 black)
            unsigned_vector color;
            color.resize(n, 0);
            bool cyclic = false;
            std::function<void(unsigned)> dfs = [&](unsigned v) {
                color[v] = 1;
                for (unsigned w : succ[v]) {
                    if (!in_comp.contains(w) || !unguarded.contains(w))
                        continue;
                    if (color[w] == 1)
                        cyclic = true;
                    else if (color[w] == 0)
                        dfs(w);
                }
                color[v] = 2;
            };
            for (unsigned i : comp)
                if (unguarded.contains(i) && color[i] == 0)
                    dfs(i);
            if (cyclic) {
                IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :unguarded-cycle " << cands[comp[0]].head->get_decl()->get_name() << ")\n";);
                continue;
            }
            kept.push_back(comp);
        }
        rec_comps.swap(kept);
    }

    // phase 1: declare the new recursive function symbols
    for (auto const& comp : rec_comps) {
        for (unsigned i : comp) {
            func_decl* f = cands[i].head->get_decl();
            recfun::promise_def pd = plugin.ensure_def(f->get_name(), f->get_arity(), f->get_domain(), f->get_range(), false);
            func_decl* f1 = pd.get_def()->get_decl();
            new_decls.push_back(f1);
            replace.insert(f, f1);
            if (cands[i].mirror)
                replace.insert(cands[i].mirror, f1);
            pdefs.push_back(std::make_pair(i, pd));
        }
    }

    // phase 2: define them
    for (auto& [i, pd] : pdefs) {
        candidate& c = cands[i];
        unsigned nargs = c.head->get_num_args();
        // canonicalize bound variables: argument k of the head becomes variable nargs-1-k
        expr_ref_vector sub(m);
        var_ref_vector vars(m);
        for (unsigned k = 0; k < nargs; ++k)
            sub.push_back(nullptr);
        for (unsigned k = 0; k < nargs; ++k) {
            var* v = to_var(c.head->get_arg(k));
            var* w = m.mk_var(nargs - 1 - k, v->get_sort());
            sub[v->get_idx()] = w;
            vars.push_back(w);
        }
        var_subst vs(m, false);
        expr_ref body = vs(c.def, sub.size(), sub.data());
        body = replace(body);
        recfun_replace rr(m);
        plugin.set_definition(rr, pd, false, vars.size(), vars.data(), body);
        IF_VERBOSE(11, verbose_stream() << "(smt.recfun-finder :define " << pd.get_def()->get_decl()->get_name() << " := " << body << ")\n";);
        ++num_defs;
    }

    // phase 3: mirrors g(X) become aliases g(X) = f'(X), so their bodies no longer mention f
    for (auto& [i, pd] : pdefs) {
        candidate& c = cands[i];
        if (!c.mirror)
            continue;
        func_decl* g = c.mirror;
        func_decl* f1 = pd.get_def()->get_decl();
        unsigned nargs = g->get_arity();
        var_ref_vector vars(m);
        expr_ref_vector args(m);
        for (unsigned k = 0; k < nargs; ++k) {
            var* w = m.mk_var(nargs - 1 - k, g->get_domain(k));
            vars.push_back(w);
            args.push_back(w);
        }
        recfun::promise_def gpd = plugin.ensure_def(g->get_name(), nargs, g->get_domain(), g->get_range(), false);
        expr_ref alias(m.mk_app(f1, args.size(), args.data()), m);
        recfun_replace rr(m);
        plugin.set_definition(rr, gpd, true, vars.size(), vars.data(), alias);
    }

    // phase 4: f(X) = f'(X) as macros (model interpretation of f, expansion in later formulas)
    for (auto& [i, pd] : pdefs) {
        candidate& c = cands[i];
        func_decl* f = c.head->get_decl();
        func_decl* f1 = pd.get_def()->get_decl();
        expr_ref rhs(m.mk_app(f1, c.head->get_num_args(), c.head->get_args()), m);
        quantifier_ref q1(m.update_quantifier(c.q, m.mk_eq(c.head, rhs)), m);
        proof_ref pr(m);
        if (m.proofs_enabled())
            pr = m.mk_def_intro(q1);
        if (m_macro_manager.insert(f, q1, pr))
            removed.insert(c.fml_idx);
        else
            IF_VERBOSE(1, verbose_stream() << "(smt.recfun-finder :warning \"could not register " << f->get_name() << " as a macro\")\n";);
    }

    if (num_defs == 0 && !m_macro_manager.has_macros())
        return;

    // rewrite the asserted formulas
    vector<justified_expr> new_fmls;
    for (unsigned i = m_qhead; i < sz; ++i) {
        if (removed.contains(i))
            continue;
        expr* fml = m_formulas[i].fml();
        proof* pr = m_formulas[i].pr();
        expr_ref new_fml(fml, m);
        proof_ref new_pr(pr, m);
        if (m_macro_manager.has_macros()) {
            expr_dependency_ref new_dep(m);
            m_macro_manager.expand_macros(fml, pr, nullptr, new_fml, new_pr, new_dep);
        }
        if (num_defs > 0) {
            expr_ref r = replace(new_fml);
            if (r != new_fml) {
                if (m.proofs_enabled())
                    new_pr = m.mk_modus_ponens(new_pr, m.mk_rewrite(new_fml, r));
                new_fml = r;
            }
        }
        new_fmls.push_back(justified_expr(m, new_fml, new_pr));
    }
    if (num_defs > 0)
        IF_VERBOSE(10, verbose_stream() << "(smt.recfun-finder :num-defs " << num_defs << ")\n";);
    swap_asserted_formulas(new_fmls);
    reduce_and_solve();
}

void asserted_formulas::find_macros_core() {
    vector<justified_expr> new_fmls;
    unsigned sz = m_formulas.size();
    (*m_macro_finder)(sz - m_qhead, m_formulas.data() + m_qhead, new_fmls);
    swap_asserted_formulas(new_fmls);
    reduce_and_solve();
}

/**
   \brief rewrite (a or (b & c)) to (a or b), (a or c) if the reference count of (b & c) is 1.
   This avoids the literal for (b & c)
*/
void asserted_formulas::flatten_clauses() {
    if (m.proofs_enabled()) return;
    bool change = true;
    vector<justified_expr> new_fmls;
    auto mk_not = [this](expr* e) { return m.is_not(e, e) ? e : m.mk_not(e); };
    auto is_literal = [this](expr *e) { m.is_not(e, e); return !is_app(e) || to_app(e)->get_num_args() == 0; };
    expr *a = nullptr, *b = nullptr, *c = nullptr;
    while (change) {
        change = false;        
        new_fmls.reset();
        unsigned sz = m_formulas.size();
        for (unsigned i = m_qhead; i < sz; ++i) {
            auto const& j = m_formulas.get(i);
            expr* f = j.fml();
            bool decomposed = false;
            if (m.is_or(f, a, b) && m.is_not(b, b) && m.is_or(b) && (b->get_ref_count() == 1 || is_literal(a))) {
                decomposed = true;
            }
            else if (m.is_or(f, b, a) && m.is_not(b, b) && m.is_or(b) && (b->get_ref_count() == 1 || is_literal(a))) {
                decomposed = true;
            }            
            if (decomposed) {
                for (expr* arg : *to_app(b)) {
                    justified_expr j1(m, m.mk_or(a, mk_not(arg)), nullptr);
                    new_fmls.push_back(j1);
                }
                change = true;
                continue;
            }
            if (m.is_ite(f, a, b, c)) {
                new_fmls.push_back(justified_expr(m, m.mk_or(mk_not(a), b), nullptr));
                new_fmls.push_back(justified_expr(m, m.mk_or(a, c), nullptr));
                change = true;
                continue;
            }
            new_fmls.push_back(j);            
        }
        swap_asserted_formulas(new_fmls);
    }
}


void asserted_formulas::apply_quasi_macros() {
    TRACE(before_quasi_macros, display(tout););
    vector<justified_expr> new_fmls;
    quasi_macros proc(m, m_macro_manager);
    while (m_qhead == 0 && 
           proc(m_formulas.size() - m_qhead,
                m_formulas.data() + m_qhead,
                new_fmls)) {
        swap_asserted_formulas(new_fmls);
        new_fmls.reset();
    }
    TRACE(after_quasi_macros, display(tout););
    reduce_and_solve();
}

void asserted_formulas::nnf_cnf() {
    nnf              apply_nnf(m, m_defined_names);
    vector<justified_expr> new_fmls;
    expr_ref_vector  push_todo(m);
    proof_ref_vector push_todo_prs(m);

    unsigned i  = m_qhead;
    unsigned sz = m_formulas.size();
    TRACE(nnf_bug, tout << "i: " << i << " sz: " << sz << "\n";);
    for (; i < sz; ++i) {
        expr * n    = m_formulas[i].fml();
        TRACE(nnf_bug, tout << "processing:\n" << mk_pp(n, m) << "\n";);
        proof_ref pr(m_formulas[i].pr(), m);
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
        for (unsigned k = 0; k < sz2; ++k) {
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
    for (unsigned i = af.m_qhead; i < sz; ++i) {
        auto& j = af.m_formulas[i];
        expr_ref result(m);
        proof_ref result_pr(m);
        simplify(j, result, result_pr);
        SASSERT(is_well_sorted(m, j.fml()));
        if (m.proofs_enabled()) {
            if (!result_pr) result_pr = m.mk_rewrite(j.fml(), result);
            result_pr = m.mk_modus_ponens(j.pr(), result_pr);
        }
        if (j.fml() == result) {
            new_fmls.push_back(j);
        }
        else {
            af.push_assertion(result, result_pr, new_fmls);
        }
        if (af.canceled())
            return;
    }
    af.swap_asserted_formulas(new_fmls);
    TRACE(asserted_formulas, af.display(tout););
    post_op();
}


void asserted_formulas::reduce_and_solve() {
    flush_cache(); // collect garbage
    m_reduce_asserted_formulas();
    IF_VERBOSE(10, verbose_stream() << "(smt.reduced " << get_total_size() << ")\n";);
}


void asserted_formulas::commit() {
    commit(m_formulas.size());
}

void asserted_formulas::commit(unsigned new_qhead) {
    m_macro_manager.mark_forbidden(new_qhead - m_qhead, m_formulas.data() + m_qhead);
    for (unsigned i = m_qhead; i < new_qhead; ++i) {
        justified_expr const& j = m_formulas[i];
        update_substitution(j.fml(), j.pr());
    }
    m_qhead = new_qhead;
}

void asserted_formulas::propagate_values() {
    if (m.proofs_enabled())
        return;
    flush_cache();

    unsigned num_prop = 0;
    unsigned sz = m_formulas.size();
    unsigned delta_prop = sz;
    while (!inconsistent() && sz/20 < delta_prop) {
        m_scoped_substitution.push();
        unsigned prop = num_prop;
        TRACE(propagate_values, display(tout << "before:\n"););
        unsigned i  = m_qhead;
        for (; i < sz; ++i) {
            prop += propagate_values(i);
        }
        flush_cache();
        m_scoped_substitution.pop(1);
        m_scoped_substitution.push();
        TRACE(propagate_values, tout << "middle:\n"; display(tout););
        i = sz;
        while (i > m_qhead) {
            --i;
            prop += propagate_values(i);
        }
        m_scoped_substitution.pop(1);
        flush_cache();
        TRACE(propagate_values, tout << "after:\n"; display(tout););
        delta_prop = prop - num_prop;
        num_prop = prop;
        if (sz <= m_formulas.size())
            break;
        sz = m_formulas.size();
    }
    TRACE(asserted_formulas, tout << num_prop << "\n";);
    if (num_prop > 0)
        m_reduce_asserted_formulas();
}

unsigned asserted_formulas::propagate_values(unsigned i) {
    expr_ref n(m_formulas[i].fml(), m);
    expr_ref new_n(m);
    proof_ref new_pr(m);
    m_rewriter(n, new_n, new_pr);
    if (m.proofs_enabled()) {
        proof * pr  = m_formulas[i].pr();
        new_pr = m.mk_modus_ponens(pr, new_pr);
    }
    justified_expr j(m, new_n, new_pr);
    m_formulas[i] = j;
    if (m.is_false(j.fml())) {
        m_inconsistent = true;
    }
    update_substitution(new_n, new_pr);
    return (n != new_n) ? 1 : 0;
}

bool asserted_formulas::update_substitution(expr* n, proof* pr) {
    expr* lhs, *rhs, *n1;
    proof_ref pr1(m);
    if (is_ground(n) && m.is_eq(n, lhs, rhs)) {
        if (is_gt(lhs, rhs)) {
            TRACE(propagate_values, tout << "insert " << mk_pp(lhs, m) << " -> " << mk_pp(rhs, m) << "\n";);
            m_scoped_substitution.insert(lhs, rhs, pr);
            return true;
        }
        if (is_gt(rhs, lhs)) {
            TRACE(propagate_values, tout << "insert " << mk_pp(rhs, m) << " -> " << mk_pp(lhs, m) << "\n";);
            pr1 = m.proofs_enabled() ? m.mk_symmetry(pr) : nullptr;
            m_scoped_substitution.insert(rhs, lhs, pr1);
            return true;
        }
        TRACE(propagate_values, tout << "incompatible " << mk_pp(n, m) << "\n";);
    }
    if (m.is_not(n, n1)) {
        pr1 = m.proofs_enabled() ? m.mk_iff_false(pr) : nullptr;
        m_scoped_substitution.insert(n1, m.mk_false(), pr1);
    }
    else {
        pr1 = m.proofs_enabled() ? m.mk_iff_true(pr) : nullptr;
        m_scoped_substitution.insert(n, m.mk_true(), pr1);
    }
    return false;
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

proof * asserted_formulas::get_inconsistency_proof() const {
    if (!inconsistent())
        return nullptr;
    if (!m.proofs_enabled())
        return nullptr;
    if (!m.inc())
        return nullptr;
    for (justified_expr const& j : m_formulas) {
        if (m.is_false(j.fml()))
            return j.pr();
    }
    return nullptr;
}

void asserted_formulas::refine_inj_axiom_fn::simplify(justified_expr const& j, expr_ref& n, proof_ref& p) {
    expr* f = j.fml();
    if (is_quantifier(f) && simplify_inj_axiom(m, to_quantifier(f), n)) {
        TRACE(inj_axiom, tout << "simplifying...\n" << mk_pp(f, m) << "\n" << n << "\n";);
    }
    else {
        n = j.fml();
    }
}


void asserted_formulas::bv_size_reduce_fn::simplify(justified_expr const& j, expr_ref& n, proof_ref& p) {
    bv_util bv(m);
    expr* f = j.fml();
    expr* a, *b, *x;
    unsigned lo, hi;
    rational r;
    expr_ref new_term(m);
    auto check_reduce = [&](expr* a, expr* b) {
        if (bv.is_extract(a, lo, hi, x) && lo > 0 && hi + 1 == bv.get_bv_size(x) && bv.is_numeral(b, r) && r == 0) {
            // insert x -> x[0,lo-1] ++ n into sub
            new_term = bv.mk_concat(b, bv.mk_extract(lo - 1, 0, x));
            m_sub.insert(x, new_term);
            n = j.fml();
            return true;
        }
        return false;
    };
    if (m.is_eq(f, a, b) && (check_reduce(a, b) || check_reduce(b, a))) {
        // done
    }
    else {
        n = j.fml();
        m_sub(n);
    }
}

void asserted_formulas::bv_size_reduce_fn::push_scope() {
    m_sub.push_scope();
}

void asserted_formulas::bv_size_reduce_fn::pop_scope(unsigned n) {
    m_sub.pop_scope(n);
}

unsigned asserted_formulas::get_total_size() const {
    expr_mark visited;
    unsigned r  = 0;
    for (justified_expr const& j : m_formulas)
        r += get_num_exprs(j.fml(), visited);
    return r;
}


#ifdef Z3DEBUG
#include <iostream>
void pp(asserted_formulas & f) {
    f.display(std::cout);
}
#endif
