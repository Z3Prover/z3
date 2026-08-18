/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    seq_regex.cpp

Abstract:

    Solver for regexes 

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-22
    Margus Veanes 2021

--*/

#include "smt/seq_regex.h"
#include "smt/theory_seq.h"
#include "ast/expr_abstract.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/seq_regex_bisim.h"
#include "ast/rewriter/expr_safe_replace.h"
#include <numeric>

namespace smt {

    static seq::transition_mode monadic_transition_mode(symbol const& s) {
        if (s == "light-ant")
            return seq::transition_mode::light_antimirov_tm;
        if (s == "brz")
            return seq::transition_mode::brzozowski_tm;
        throw default_exception("invalid seq.regex_transition_mode, use 'light-ant' or 'brz'");
    }

    static seq_monadic::orientation monadic_orientation(symbol const& s) {
        if (s == "forward")
            return seq_monadic::orientation::forward;
        if (s == "reversed")
            return seq_monadic::orientation::reversed;
        if (s == "retry")
            return seq_monadic::orientation::retry;
        throw default_exception("invalid seq.regex_orientation, use 'forward', 'reversed' or 'retry'");
    }

    seq_regex::seq_regex(theory_seq& th):
        th(th),
        ctx(th.get_context()),
        m(th.get_manager()),
        m_monadic(seq_rw(), ctx.get_trail_stack(),
                  monadic_transition_mode(ctx.get_fparams().m_seq_regex_transition_mode)),
        m_monadic_model(th.get_manager()),
        m_live_states(seq_rw(), seq::transition_mode::brzozowski_tm, 10000) {
        m_monadic.set_is_var([&th](expr *e) { return th.is_var(e); });
        m_monadic.set_budget(ctx.get_fparams().m_seq_regex_budget);
        m_monadic.set_orientation(monadic_orientation(ctx.get_fparams().m_seq_regex_orientation));
        m_monadic.set_split_rounds(ctx.get_fparams().m_seq_regex_split);
    }

    seq_util& seq_regex::u() { return th.m_util; }
    class seq_util::rex& seq_regex::re() { return th.m_util.re; }
    class seq_util::str& seq_regex::str() { return th.m_util.str; }
    seq_rewriter& seq_regex::seq_rw() { return th.m_seq_rewrite; }
    seq::skolem& seq_regex::sk() { return th.m_sk; }
    arith_util& seq_regex::a() { return th.m_autil; }
    void seq_regex::rewrite(expr_ref& e) { th.m_rewrite(e); }

    expr_ref seq_regex::expand_shallow(expr* e, void*& deps, unsigned depth) {
        expr* elem = nullptr;
        if (depth > 40)
            return expr_ref(e, m);                // guard against pathological chains
        if (str().is_concat(e)) {
            expr_ref_vector args(m);
            for (expr* arg : *to_app(e))
                args.push_back(expand_shallow(arg, deps, depth + 1));
            return expr_ref(str().mk_concat(args, e->get_sort()), m);
        }
        if (str().is_empty(e) || str().is_string(e))
            return expr_ref(e, m);                // parseable constant leaf
        if (str().is_unit(e, elem) && m.is_value(elem))
            return expr_ref(e, m);                // seq.unit of a constant element
        // A variable or a defined term: substitute through the solution map, but only keep
        // the substitution if it stays monadic-decidable.  A free variable whose only
        // definition is its seq.unit(nth ..) length representation is thus kept atomic.
        theory_seq::dependency* d = nullptr;
        expr* r = th.m_rep.find(e, d);
        if (r == e)
            return expr_ref(e, m);                // no defining equation: atomic leaf
        void* sub = d;
        expr_ref er = expand_shallow(r, sub, depth + 1);
        if (m_monadic.can_decide_term(er)) {
            deps = th.m_dm.mk_join(static_cast<theory_seq::dependency*>(deps),
                                   static_cast<theory_seq::dependency*>(sub));
            return er;
        }
        return expr_ref(e, m);                     // keep atomic; drop the polluted expansion
    }

    expr_ref seq_regex::compute_expansion(expr* s, void*& dep) {
        dep = nullptr;
        // Prefer full canonization: it collapses a variable defined by a word equation
        // (and any variable pinned to a constant) down to constants/variables, which is
        // what lets the monadic solver decide the real structure.  If that yields a form
        // the solver cannot decide -- typically because theory_seq has replaced a free
        // variable by its seq.unit(nth ..) length representation -- fall back to a shallow
        // expansion that keeps such variables atomic, and finally to the atomic term.
        theory_seq::dependency* cdep = nullptr;
        expr_ref full(m);
        if (th.canonize(s, cdep, full) && full && m_monadic.can_decide_term(full)) {
            dep = cdep;
            return full;
        }
        void* sdep = nullptr;
        expr_ref shallow = expand_shallow(s, sdep, 0);
        if (shallow && m_monadic.can_decide_term(shallow)) {
            dep = sdep;
            return shallow;
        }
        dep = nullptr;
        return expr_ref(s, m);
    }

    void seq_regex::add_monadic_membership(literal lit, expr* s, expr* r) {
        for (auto const& membership : m_monadic_memberships)
            if (membership.m_lit == lit)
                return;
        // Decide the membership over the concatenation of variables/constants that define s
        // (see compute_expansion) rather than over the atomic term s.  Deciding s atomically
        // yields witnesses that ignore s's defining word equation (e.g. x = x8 ++ "/" ++ s9),
        // which then conflict on assume_eq and livelock.  The equalities used are captured in
        // `dep` and folded into any unsat core for soundness.
        void* dep = nullptr;
        expr_ref s_expanded = compute_expansion(s, dep);
        unsigned idx = m_monadic_memberships.size();
        m_monadic_memberships.push_back(monadic_membership(m, lit, s, r, s_expanded, dep));
        ctx.push_trail(push_back_vector(m_monadic_memberships));
        m_monadic.add(s_expanded, r, dep_of_membership(idx));
        ctx.push_trail(value_trail<unsigned>(m_monadic_generation));
        ++m_monadic_generation;
        TRACE(seq_regex, tout << "monadic add " << lit << ": "
                             << mk_pp(s_expanded, m) << " in " << mk_pp(r, m) << "\n";);
    }

    void seq_regex::refresh_expansions() {
        for (unsigned idx = 0; idx < m_monadic_memberships.size(); ++idx) {
            monadic_membership& mem = m_monadic_memberships[idx];
            void* dep = nullptr;
            expr_ref s_expanded = compute_expansion(mem.m_s, dep);
            // Always resync: m_s_expanded/m_dep are not trailed, so after a backtrack they
            // may be stale while the monadic term (which IS trailed) was restored.
            // set_term itself no-ops when the monadic term already matches.
            mem.m_s_expanded = s_expanded;
            mem.m_dep = dep;
            m_monadic.set_term(dep_of_membership(idx), s_expanded);
            TRACE(seq_regex, tout << "monadic expand " << mk_pp(mem.m_s, m)
                                 << " -> " << mk_pp(s_expanded, m) << "\n";);
        }
    }

    void seq_regex::collect_vars(expr* s, ptr_vector<expr>& vars) {
        // View s as a concatenation of string constants and variables (the same shape the
        // monadic solver decomposes internally) and gather the distinct variables.
        ptr_vector<expr> todo;
        todo.push_back(s);
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            if (str().is_concat(t)) {
                for (expr* arg : *to_app(t))
                    todo.push_back(arg);
                continue;
            }
            if (th.is_var(t) && !vars.contains(t))
                vars.push_back(t);
        }
    }

    void seq_regex::collect_candidate_bounds(vector<candidate_bound>& out) {
        // add_lo/add_hi/add_len build a length regex .{lo}.* / .{0,hi} / .{len}; keep the
        // bound small so the extra membership never itself blows past the monadic solver's
        // state cap (a too-large bound would only turn a solvable case into a give-up).
        const unsigned MAX_BOUND = 1000;
        // Record whatever arithmetic length bounds currently hold for term t as candidate
        // length regexes for the monadic solver.
        auto add_term = [&](expr* t) {
            expr_ref len = th.mk_len(t);
            rational lo, hi;
            bool has_lo = th.lower_bound(len, lo) && lo.is_unsigned() && lo.get_unsigned() > 0;
            bool has_hi = th.upper_bound(len, hi) && hi.is_unsigned();
            if (has_lo && has_hi && lo == hi) {
                if (lo.get_unsigned() <= MAX_BOUND)
                    out.push_back(candidate_bound(m, t, len, bound_constraint::LEN, lo.get_unsigned()));
                return;
            }
            if (has_lo && lo.get_unsigned() <= MAX_BOUND)
                out.push_back(candidate_bound(m, t, len, bound_constraint::LO, lo.get_unsigned()));
            if (has_hi && hi.get_unsigned() <= MAX_BOUND)
                out.push_back(candidate_bound(m, t, len, bound_constraint::HI, hi.get_unsigned()));
        };
        ptr_vector<expr> vars;
        for (auto const& mem : m_monadic_memberships) {
            // Use the expanded term: it is what the monadic solver actually decides, so its
            // variables (and their lengths) are the ones a witness must respect.  Bounding
            // the original atomic term would reintroduce it as a fresh monadic variable.
            expr* s = mem.m_s_expanded;
            // The whole-term bound constrains the sum of the atom lengths.
            add_term(s);
            // Decompose s into constants and variables and bound each variable directly:
            // per-variable bounds prune the monadic search for that variable's value,
            // whereas the whole-term bound only constrains the total length.
            vars.reset();
            collect_vars(s, vars);
            for (expr* v : vars)
                add_term(v);
        }
    }

    bool seq_regex::model_len(expr* t, unsigned& len) {
        expr_substitution& model = m_monadic_model;
        ptr_vector<expr> todo;
        todo.push_back(t);
        len = 0;
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            expr* a = nullptr, *b = nullptr;
            zstring s;
            if (str().is_concat(e, a, b)) {
                todo.push_back(a);
                todo.push_back(b);
                continue;
            }
            if (str().is_empty(e))
                continue;
            if (str().is_unit(e)) {
                ++len;
                continue;
            }
            if (str().is_string(e, s)) {
                len += s.length();
                continue;
            }
            expr* w = model.find(e);
            if (w && w != e) {                    // variable: replace by its witness
                todo.push_back(w);
                continue;
            }
            return false;                         // unassigned variable / unsupported shape
        }
        return true;
    }

    bool seq_regex::model_satisfies_bound(candidate_bound const& cb) {
        unsigned len = 0;
        if (!model_len(cb.m_term, len))
            return true;                          // cannot evaluate -> leave to arithmetic
        switch (cb.m_kind) {
        case bound_constraint::LO:  return len >= cb.m_value;
        case bound_constraint::HI:  return len <= cb.m_value;
        case bound_constraint::LEN: return len == cb.m_value;
        }
        return true;
    }

    void seq_regex::record_bound(expr* s, expr* len, bound_constraint::kind_t k, unsigned v) {
        for (auto const& b : m_monadic_bounds)
            if (b.m_len.get() == len && b.m_kind == k && b.m_value == v)
                return;                           // already asserted at this scope
        unsigned idx = m_monadic_bounds.size();
        m_monadic_bounds.push_back(bound_constraint(m, k, len, v));
        ctx.push_trail(push_back_vector(m_monadic_bounds));
        void* dep = dep_of_bound(idx);
        switch (k) {
        case bound_constraint::LO:  m_monadic.add_lo(s, v, dep); break;
        case bound_constraint::HI:  m_monadic.add_hi(s, v, dep); break;
        case bound_constraint::LEN: m_monadic.add_len(s, v, dep); break;
        }
        TRACE(seq_regex, tout << "monadic bound " << mk_pp(len, m)
                             << (k == bound_constraint::LO ? " >= " :
                                 k == bound_constraint::HI ? " <= " : " = ") << v << "\n";);
    }

    bool seq_regex::all_true(literal_vector const& lits) const {
        return all_of(lits, [this](literal lit) { return l_true == ctx.get_assignment(lit); });
    }

    void seq_regex::add_core_literal(void* dep, literal_vector& lits, void*& deps) {
        size_t enc = reinterpret_cast<size_t>(dep);
        if ((enc & 1) == 0) {                     // even: a monadic membership (by index)
            monadic_membership const& mem = m_monadic_memberships[static_cast<unsigned>((enc >> 1) - 1)];
            lits.push_back(mem.m_lit);
            if (mem.m_dep)                         // include the equalities used to expand its term
                deps = th.m_dm.mk_join(static_cast<theory_seq::dependency*>(deps),
                                       static_cast<theory_seq::dependency*>(mem.m_dep));
            return;
        }
        // odd: a length bound; materialize its justifying arithmetic literal(s) now.
        bound_constraint const& b = m_monadic_bounds[static_cast<unsigned>((enc - 1) >> 1)];
        switch (b.m_kind) {
        case bound_constraint::LO:
            lits.push_back(th.m_ax.mk_ge(b.m_len, b.m_value));
            break;
        case bound_constraint::HI:
            lits.push_back(th.m_ax.mk_le(b.m_len, b.m_value));
            break;
        case bound_constraint::LEN:
            lits.push_back(th.m_ax.mk_ge(b.m_len, b.m_value));
            lits.push_back(th.m_ax.mk_le(b.m_len, b.m_value));
            break;
        }
    }

    void seq_regex::propagate_accept_legacy(literal lit, expr* s, expr* r) {
        if (is_string_equality(lit))
            return;
        expr_ref regex(r, m);
        if (!m.is_value(s)) {
            expr_ref s_approx = get_overapprox_regex(s);
            if (!re().is_full_seq(s_approx)) {
                regex = re().mk_inter(regex, s_approx);
                TRACE(seq_regex, tout
                    << "get_overapprox_regex(" << mk_pp(s, m)
                    << ") = " << mk_pp(s_approx, m) << std::endl;);
                STRACE(seq_regex_brief, tout
                    << "overapprox=" << state_str(regex) << " ";);
            }
        }

        expr_ref zero(a().mk_int(0), m);
        expr_ref acc(sk().mk_accept(s, zero, regex), m);
        literal acc_lit = th.mk_literal(acc);

        TRACE(seq, tout << "propagate " << acc << "\n";);
        th.add_axiom(~lit, acc_lit);
    }

    void seq_regex::enable_legacy_fallback() {
        if (m_monadic_fallback_generation == m_monadic_generation)
            return;
        for (auto const& membership : m_monadic_memberships)
            propagate_accept_legacy(membership.m_lit, membership.m_s, membership.m_re);
        ctx.push_trail(value_trail<unsigned>(m_monadic_fallback_generation));
        m_monadic_fallback_generation = m_monadic_generation;
        ++th.m_stats.m_regex_monadic_fallbacks;
    }

    final_check_status seq_regex::final_check() {
        if (!th.use_monadic_regex() || m_monadic_memberships.empty())
            return FC_DONE;
        if (m_monadic_fallback_generation == m_monadic_generation)
            return FC_DONE;

        if (m_monadic_assumption_generation == m_monadic_generation) {
            for (auto const& assumption : m_monadic_assumptions) {
                if (assumption.m_generation != m_monadic_generation)
                    continue;
                if (assumption.m_var->get_root() != assumption.m_witness->get_root()) {
                    enable_legacy_fallback();
                    return FC_CONTINUE;
                }
            }
            return FC_DONE;
        }

        // Re-canonize membership terms now that theory_seq's solution map is populated:
        // a variable defined by a word equation (x = x8 ++ "/" ++ s9) is decided over its
        // expanded concatenation, so the monadic witness assigns the real subvariables
        // consistently instead of inventing a value for the atomic term.
        refresh_expansions();

        // Lazy length-constraint enforcement: first decide the memberships WITHOUT any
        // length regexes.  If the resulting model already respects every candidate length
        // bound, keep it; otherwise add exactly the violated bounds and re-solve.  Each
        // round enforces at least one new bound (finite set), so the loop terminates.
        vector<candidate_bound> candidates;
        collect_candidate_bounds(candidates);
        lbool result = l_undef;
        unsigned guard = candidates.size() + 1;
        m_monadic_model.reset();
        while (true) {
            ++th.m_stats.m_regex_monadic_checks;
            result = m_monadic.check();
            if (result != l_true)
                break;
            // the bound checks below need values, and every round has a new solution
            m_monadic_model.reset();
            if (m_monadic.materialize_all(m_monadic_model) != l_true) {
                result = l_undef;
                break;
            }
            bool progressed = false;
            for (auto const& cb : candidates) {
                if (model_satisfies_bound(cb))
                    continue;
                record_bound(cb.m_term, cb.m_len, cb.m_kind, cb.m_value);
                progressed = true;
            }
            if (!progressed || guard-- == 0)
                break;
        }

        TRACE(seq, tout << "monadic solver returned " << result << "\n";
        m_monadic.display(tout););

        if (result == l_false) {
            ++th.m_stats.m_regex_monadic_unsat;
            literal_vector lits;
            void* deps = nullptr;
            for (void* core_dep : m_monadic.core())
                add_core_literal(core_dep, lits, deps);
            if (all_true(lits)) {
                // Every core literal is assigned true, so the negated core (together with the
                // equalities collected while canonizing membership terms, carried in deps) is a
                // legitimate theory conflict.
                th.set_conflict(static_cast<theory_seq::dependency*>(deps), lits);
            }
            else {
                // Some core literal is not currently assigned true, so this is not a legitimate
                // theory conflict (see #10398): raising one would justify it with non-true
                // literals. Assert the blocking clause instead -- the negation of the literals
                // and canonization equalities that the monadic solver refuted.
                for (unsigned i = 0; i < lits.size(); ++i)
                    lits[i] = ~lits[i];
                enode_pair_vector eqs;
                literal_vector dep_lits;
                th.linearize(static_cast<theory_seq::dependency*>(deps), eqs, dep_lits);
                for (literal l : dep_lits)
                    lits.push_back(~l);
                for (auto const& [a, b] : eqs)
                    lits.push_back(~th.mk_eq(a->get_expr(), b->get_expr(), false));
                th.add_axiom(lits);
            }
            return FC_CONTINUE;
        }
        if (result == l_undef) {
            ++th.m_stats.m_regex_monadic_undef;
            enable_legacy_fallback();
            return FC_CONTINUE;
        }

        ++th.m_stats.m_regex_monadic_sat;
        ctx.push_trail(value_trail<unsigned>(m_monadic_assumption_generation));
        m_monadic_assumption_generation = m_monadic_generation;
        for (auto const& [var, witness] : m_monadic_model.sub()) {
            enode* var_node = th.ensure_enode(var);
            enode* witness_node = th.ensure_enode(witness);
            if (var_node->get_root() == witness_node->get_root())
                continue;
            ctx.assume_eq(var_node, witness_node);
            m_monadic_assumptions.push_back({ m_monadic_generation, var_node, witness_node });
            ctx.push_trail(push_back_vector(m_monadic_assumptions));
            ++th.m_stats.m_regex_monadic_assumptions;
            TRACE(seq_regex, tout << "monadic assume "
                                  << mk_pp(var, m) << " = " << mk_pp(witness, m) << "\n";);
        }
        return FC_CONTINUE;
    }

    /**
     * is_string_equality holds of str.in_re s R, 
     * 
     * s in (all ++ x ++ all ++ y ++ all)
     * => 
     * s = fresh1 ++ x ++ fresh2 ++ y ++ fresh3
     * 
     * TBD General rewrite possible:
     *
     * s in (R ++ Q)
     * =>
     * s = x ++ y and x in R and y in Q
     */

    bool seq_regex::is_string_equality(literal lit) {
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        expr_ref id(a().mk_int(e->get_id()), m);
        VERIFY(str().is_in_re(e, s, r));
        sort* seq_sort = s->get_sort();
        vector<expr_ref_vector> patterns;
        auto mk_cont = [&](unsigned idx) { 
            return sk().mk("seq.cont", id, a().mk_int(idx), seq_sort);
        };
        unsigned idx = 0;
        if (seq_rw().is_re_contains_pattern(r, patterns)) {
            expr_ref_vector ts(m);
            ts.push_back(mk_cont(idx));
            for (auto const& p : patterns) {
                ts.append(p);
                ts.push_back(mk_cont(++idx));
            }
            expr_ref t = th.mk_concat(ts, seq_sort);
            th.propagate_eq(lit, s, t, true);
            return true;
        }
        return false;
    }

    /**
     * Propagate the atom (str.in_re s r)
     * 
     * Propagation implements the following inference rules
     * 
     * (not (str.in_re s r)) => (str.in_re s (complement r))
     * (str.in_re s r) => r != {}
     * 
     * (str.in_re s r) => (accept s 0 r)
     */

    void seq_regex::propagate_in_re(literal lit) {
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));

        TRACE(seq_regex, tout << "propagate in RE: " << lit.sign() << " " << mk_pp(e, m) << std::endl;);
        STRACE(seq_regex_brief, tout << "PIR(" << mk_pp(s, m) << ","
                                       << state_str(r) << ") ";);

        if (unfold_complement(lit, s, r))
            return;

        if (unfold_prefix(lit, s, r)) 
            return;        

        if (factor_ite(lit, s, r))
            return;

        if (coallesce_in_re(lit)) 
            return;

        propagate_length_residue(lit, s, r);

        if (th.use_monadic_regex())
            add_monadic_membership(lit, s, r);
        else
            propagate_accept_legacy(lit, s, r);
    }

    void seq_regex::propagate_length_residue(literal lit, expr* s, expr* r) {
        if (lit.sign())
            return;
        if (!u().can_be_member(s, r)) {
            th.add_axiom(~lit);
            return;
        }
        auto info = re().get_info(r);
        if (!info.is_known() || info.period <= 1)
            return;
        
        if (!lengths_are_live(s))
            return;

        unsigned num = 0;
        for (unsigned i = 0; i < info.period; ++i)
            if (info.residues & (1ull << i))
                ++num;
        if (num == 0 || num > 4)
            return;
        expr_ref len(th.mk_len(s), m);
        expr_ref mod(a().mk_mod(len, a().mk_int(info.period)), m);
        literal_vector lits;
        lits.push_back(~lit);
        for (unsigned i = 0; i < info.period; ++i)
            if (info.residues & (1ull << i))
                lits.push_back(th.mk_eq(mod, a().mk_int(i), false));
        th.add_axiom(lits);
    }



    bool seq_regex::lengths_are_live(expr* s) {
        if (th.has_length(s))
            return true;
        ptr_vector<expr> todo;
        todo.push_back(s);
        bool has_var = false;
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            expr* a1 = nullptr, *a2 = nullptr;
            if (str().is_concat(e, a1, a2)) {
                todo.push_back(a1);
                todo.push_back(a2);
                continue;
            }
            if (str().is_empty(e) || str().is_unit(e) || str().is_string(e))
                continue;
            if (!th.has_length(e))
                return false;
            has_var = true;
        }
        return has_var;
    }

    bool seq_regex::unfold_complement(literal lit, expr *s, expr *r) {
        if (!lit.sign())
            return false;
        // convert negative negative membership literals to positive
        // ~(s in R) => s in C(R)
        expr_ref fml(re().mk_in_re(s, re().mk_complement(r)), m);
        rewrite(fml);
        literal nlit = th.mk_literal(fml);
        if (lit == nlit) {
            // is-nullable doesn't simplify for regexes with uninterpreted subterms
            th.add_unhandled_expr(fml);
        }
        th.propagate_lit(nullptr, 1, &lit, nlit);
        return true;
    }
    
    bool seq_regex::unfold_prefix(literal lit, expr *s, expr *r) {
        expr_ref_vector prefix(m);
        expr *hd, *v, *tl = s, *tl1;
        while (str().is_concat(tl, hd, tl1) && str().is_unit(hd, v))
            prefix.push_back(v), tl = tl1;

        if (prefix.empty())
            return false;

        expr_ref q(r, m);
        for (expr *v : prefix) {
            q = seq_rw().mk_derivative(v, q);
            if (re().is_empty(q)) {
                enode_pair_vector eqs;
                literal_vector lits;
                lits.push_back(lit);
                th.set_conflict(eqs, lits);
                return true;
            }
        }
        expr_ref fml(re().mk_in_re(tl, q), m);
        rewrite(fml);
        literal nlit = th.mk_literal(fml);
        th.propagate_lit(nullptr, 1, &lit, nlit);
        TRACE(seq_regex, tout << "unfolded prefix\n");
        return true;
    }

    bool seq_regex::factor_ite(literal lit, expr *s, expr *r) {
        bool_rewriter br(m);
        expr_ref c(m), t(m), e(m);
        if (!br.decompose_ite(r, c, t, e))
            return false;
        auto c_lit = th.mk_literal(c);
        switch (ctx.get_assignment(c_lit)) {
        case l_true: {
            literal lits[2] = {lit, c_lit};
            th.propagate_lit(nullptr, 2, lits, th.mk_literal(re().mk_in_re(s, t)));
            break;
        }
        case l_false: {
            literal lits[2] = {lit, ~c_lit};
            th.propagate_lit(nullptr, 2, lits, th.mk_literal(re().mk_in_re(s, e)));
            break;
        }
        case l_undef: {
            ctx.mark_as_relevant(c_lit);
            // The membership literal is asserted only once, so preserve both
            // branches until the condition receives an assignment.
            literal in_t = th.mk_literal(re().mk_in_re(s, t));
            literal in_e = th.mk_literal(re().mk_in_re(s, e));
            th.add_axiom(~lit, ~c_lit, in_t);
            th.add_axiom(~lit, c_lit, in_e);
            break;
        }
        }
        return true;
    }

    /**
    * Gets an overapproximating regex s_approx for the input string expression s.
    * such that for any valuation v(s) of s, v(s) in L(s_approx).
    * If the overapproximation is trivial then dotstar is returned.
    */
    expr_ref seq_regex::get_overapprox_regex(expr* s) {
        expr_ref s_to_re(re().mk_to_re(s), m);
        expr_ref dotstar(re().mk_full_seq(s_to_re->get_sort()), m);
        if (m.is_value(s)) 
            return s_to_re;
        
        if (str().is_concat(s)) {
            expr_ref_vector es(m);
            str().get_concat(s, es);            
            expr_ref s_approx(m), e_approx(m), last(m);
            for (expr* e : es) {
                e_approx = get_overapprox_regex(e);
                if (!s_approx)
                    s_approx = e_approx;
                else if (last != dotstar || e_approx != dotstar)
                    s_approx = re().mk_concat(s_approx, e_approx);
                last = e_approx;
            }
            if (!s_approx)
                s_approx = re().mk_epsilon(s->get_sort());
        
            return s_approx;
        }

        expr* c = nullptr, *r1 = nullptr, *r2 = nullptr;
        if (m.is_ite(s, c, r1, r2)) {
            // if either branch approximates to .* then the result is also .*

            expr_ref s_approx1 = get_overapprox_regex(r1);
            if (re().is_full_seq(s_approx1))
                return s_approx1;

            expr_ref s_approx2 = get_overapprox_regex(r2);
            if (re().is_full_seq(s_approx2)) 
                return s_approx2;
        
            return expr_ref(re().mk_union(s_approx1, s_approx2), m);
        }

        // TBD: other app expressions that can be approximated
        return dotstar;
    
    }

    bool seq_regex::block_if_empty(expr* r, literal lit) {
        auto info = re().get_info(r);

        //if the minlength of the regex is UINT_MAX then the regex is a deadend
        if (re().is_empty(r) || info.min_length == UINT_MAX) {
            STRACE(seq_regex_brief, tout << "(empty) ";);
            th.add_axiom(~lit);
            return true;
        }

        if (info.interpreted) {
            auto live = m_live_states.reachable_live(r);
            if (live.is_dead()) {
                STRACE(seq_regex_brief, tout << "(dead) ";);
                th.add_axiom(~lit);
                return true;
            }
            // Fall back to antimirov NFA reachability.  The lazy state graph
            // keys states by AST identity and cannot close on intersections /
            // complements whose derivative product states do not canonicalize,
            // so it never detects their emptiness.  re_is_empty decides
            // emptiness directly (the same procedure propagate_eq already uses
            // for re.none equalities).
            if (re_is_empty(r) == l_true) {
                STRACE(seq_regex_brief, tout << "(empty:re) ";);
                th.add_axiom(~lit);
                return true;
            }
        }
        return false;
    }


    /**
     * Propagate the atom (accept s i r)
     *
     * Propagation triggers derivative reachability for dead state detection:
     * (accept s i r) & dead(r) => false
     *
     * Propagation is also blocked under certain conditions to throttle
     * state space exploration past a certain point: see block_unfolding
     *
     * Otherwise, propagation implements the following inference rules:
     *
     * Rule 1. (accept s i r) => len(s) >= i + min_len(r)
     * Rule 2. (accept s i r) & len(s) <= i => nullable(r)
     *     (only necessary if min_len fails and returns 0 for non-nullable r)
     * Rule 3. (accept s i r) and len(s) > i =>
     *             (accept s (i + 1) (derivative s[i] r)
     *
     * Acceptance of a derivative is unfolded into a disjunction over
     * all derivatives. Effectively, this implements the following rule:
     * (accept s i (ite c r1 r2)) => (ite c (accept s i r1) (accept s i r2))
     */
     void seq_regex::propagate_accept(literal lit) {
        SASSERT(!lit.sign());

        expr* s = nullptr, *i = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        unsigned idx = 0;
        VERIFY(sk().is_accept(e, s, i, idx, r));

        TRACE(seq_regex, tout << "propagate accept: "
                                << mk_pp(e, m) << std::endl;);
        STRACE(seq_regex_brief, tout << std::endl
                                       << "PA(" << mk_pp(s, m) << "@" << idx
                                       << "," << state_str(r) << ") ";);

        if (block_if_empty(r, lit))
            return;

        if (block_unfolding(lit, idx)) {
            STRACE(seq_regex_brief, tout << "(blocked) ";);
            return;
        }

        STRACE(seq_regex_brief, tout << "(unfold) ";);

        // Rule 1: use min_length to prune search
        unsigned min_len = re().min_length(r);
        unsigned min_len_plus_i = add_truncate(min_len, idx);
        literal len_s_ge_min = th.m_ax.mk_ge(th.mk_len(s), min_len_plus_i);
        // Acc(s,i,r) ==> |s| >= i + minlength(r)
        th.propagate_lit(nullptr, 1, &lit, len_s_ge_min);
        // Axiom equivalent to the above: th.add_axiom(~lit, len_s_ge_min);

        // Rule 2: nullable check
        literal len_s_le_i = th.m_ax.mk_le(th.mk_len(s), idx);
        if (min_len == 0) {
            expr_ref is_nullable = is_nullable_wrapper(r);
            if (m.is_false(is_nullable)) {
                STRACE(seq_regex, tout
                    << "Warning: min_length returned 0 for non-nullable regex"
                    << std::endl;);
                STRACE(seq_regex_brief, tout
                    << " (Warning: min_length returned 0 for"
                    << " non-nullable regex)";);
                // since nullable(r) = false:
                // Acc(s,i,r) ==> |s|>i
                th.propagate_lit(nullptr, 1, &lit, ~len_s_le_i);
            }
            else if (!m.is_true(is_nullable)) {
                // is_nullable did not simplify
                STRACE(seq_regex, tout
                    << "Warning: is_nullable did not simplify to true or false"
                    << std::endl;);
                STRACE(seq_regex_brief, tout
                    << " (Warning: is_nullable did not simplify)";);
                literal is_nullable_lit = th.mk_literal(is_nullable);
                ctx.mark_as_relevant(is_nullable_lit);
                // Acc(s,i,r) & |s|<=i  ==> nullable(r)
                th.add_axiom(~lit, ~len_s_le_i, is_nullable_lit);
                //TODO: what if is_nullable contains an in_re 
                if (str().is_in_re(is_nullable))
                    th.add_unhandled_expr(is_nullable);
            }
        }

        // Rule 3: derivative unfolding
        literal_vector accept_next;
        expr_ref s_i = th.mk_nth(s, i);
        expr_ref deriv(m);
        deriv = mk_derivative_wrapper(s_i, r);
        STRACE(seq_regex, tout
            << "mk_derivative_wrapper: " << re().to_str(deriv) << std::endl;);
        expr_ref accept_deriv(m);
        accept_deriv = mk_deriv_accept(s, idx + 1, deriv);
        accept_next.push_back(~lit);
        accept_next.push_back(len_s_le_i);
        accept_next.push_back(th.mk_literal(accept_deriv));
        // Acc(s, i, r) => (|s|<=i or Acc(s, i+1, D(s_i,r)))
        // where Acc(s, i+1, ite(c, t, f)) = ite(c, Acc(s, i+1, t), Acc(s, i+1, t))
        // and Acc(s, i+1, r U s) = Acc(s, i+1, r) or Acc(s, i+1, s)
        th.add_axiom(accept_next);
    }

    /**
     * Put a limit to the unfolding of s. 
     */
    bool seq_regex::block_unfolding(literal lit, unsigned i) {
        if (i <= th.m_max_unfolding_depth)
            return false;
        if (th.m_max_unfolding_lit == null_literal)
            return false;
        if (ctx.get_assignment(th.m_max_unfolding_lit) != l_true)
            return false;
        if (ctx.at_base_level())
            return false;
        th.propagate_lit(nullptr, 1, &lit, ~th.m_max_unfolding_lit);
        return true;
    }

    /**
     * Combine a conjunction of membership relations for the same string
     * within the same Regex.
     */
    bool seq_regex::coallesce_in_re(literal lit) {
        return false; // disabled
        expr* s = nullptr, *r = nullptr;
        expr* e = ctx.bool_var2expr(lit.var());
        VERIFY(str().is_in_re(e, s, r));
        expr_ref regex(r, m);
        literal_vector lits;    
        for (unsigned i = 0; i < m_s_in_re.size(); ++i) {
            auto const& entry = m_s_in_re[i];
            if (!entry.m_active)
                continue;
            enode* n1 = th.ensure_enode(entry.m_s);
            enode* n2 = th.ensure_enode(s);
            if (n1->get_root() != n2->get_root())
                continue;
            if (entry.m_re == regex) 
                continue;

            th.m_trail_stack.push(vector_value_trail<s_in_re, true>(m_s_in_re, i));
            m_s_in_re[i].m_active = false;
            IF_VERBOSE(11, verbose_stream() << "Intersect " << regex << " " << 
                       mk_pp(entry.m_re, m) << " " << mk_pp(s, m) << " " << mk_pp(entry.m_s, m) << std::endl;);
            regex = re().mk_inter(entry.m_re, regex);
            rewrite(regex);
            lits.push_back(~entry.m_lit);
            if (n1 != n2) 
                lits.push_back(~th.mk_eq(n1->get_expr(), n2->get_expr(), false));
        }
        m_s_in_re.push_back(s_in_re(lit, s, regex));
        th.get_trail_stack().push(push_back_vector<vector<s_in_re>>(m_s_in_re));
        if (lits.empty())
            return false;
        lits.push_back(~lit);
        lits.push_back(th.mk_literal(re().mk_in_re(s, regex)));
        th.add_axiom(lits);
        return true;
    }

    expr_ref seq_regex::symmetric_diff(expr* r1, expr* r2) {
        expr_ref r(m);
        if (r1 == r2)
            r = re().mk_empty(r1->get_sort());
        else if (re().is_empty(r1)) 
            r = r2;
        else if (re().is_empty(r2))
            r = r1;
        else 
            r = re().mk_union(re().mk_diff(r1, r2), re().mk_diff(r2, r1));
        rewrite(r);
        return r;
    }

    /*
        Wrapper around calls to is_nullable from the seq rewriter.

        TODO: clean up the following:
        Note: the is_nullable_wrapper and mk_derivative_wrapper actually use
        different sequence rewriters; these are at:
            m_seq_rewrite
                (returned by seq_rw())
            th.m_rewrite.m_imp->m_cfg.m_seq_rw
                (private, can't be accessed directly)
        As a result operations are cached separately for the nullable
        and derivative calls. 
    */
    expr_ref seq_regex::is_nullable_wrapper(expr* r) {
        STRACE(seq_regex, tout << "nullable: " << mk_pp(r, m) << std::endl;);

        expr_ref result = seq_rw().is_nullable(r);
        //TODO: rewrite seems unnecessary here
        rewrite(result);

        STRACE(seq_regex, tout << "nullable result: " << mk_pp(result, m) << std::endl;);
        STRACE(seq_regex_brief, tout << "n(" << state_str(r) << ")="
                                       << mk_pp(result, m) << " ";);

        return result;
    }

    /*
       First creates a derivatrive of r wrt x=(:var 0) and then replaces x by ele.
       This will create a cached entry for the generic derivative of r that is independent of ele.
    */
    expr_ref seq_regex::mk_derivative_wrapper(expr* ele, expr* r) {
        STRACE(seq_regex, tout << "derivative(" << mk_pp(ele, m) << "): " << mk_pp(r, m) << std::endl;);

        // Uses canonical variable (:var 0) for the derivative element
        // Substitute (:var 0) with the actual element
        expr_ref der = seq_rw().mk_derivative(r);
        var_subst subst(m);
        der = subst(der, ele);

        STRACE(seq_regex, tout << "derivative result: " << mk_pp(der, m) << std::endl;);
        STRACE(seq_regex_brief, tout << "d(" << state_str(r) << ")="
                                       << state_str(der) << " ";);

        //TODO: simplify der further, if ele implies further simplifications
        //e.g. if ele='b' then de(ite (x='a') t f) simplifies to t
        return der;
    }

    void seq_regex::propagate_eq(expr* r1, expr* r2) {
        TRACE(seq_regex, tout << "propagate EQ: " << mk_pp(r1, m) << ", " << mk_pp(r2, m) << std::endl;);
        STRACE(seq_regex_brief, tout << "PEQ ";);

        sort* seq_sort = nullptr;
        VERIFY(u().is_re(r1, seq_sort));
        expr_ref r = symmetric_diff(r1, r2);
        if (re().is_empty(r))
            //trivially true
            return;
        // When one side is re.none the equation is a pure emptiness check on
        // the other regex (symmetric_diff already returned it as r).  Decide
        // it directly by antimirov NFA reachability instead of running the
        // bisimulation/XOR closure, which would build large un-canonicalized
        // product states for intersections of contains-patterns.
        if ((re().is_empty(r1) || re().is_empty(r2)) && re().is_ground(r)) {
            switch (re_is_empty(r)) {
            case l_true:
                STRACE(seq_regex_brief, tout << "empty:eq ";);
                return; // languages equal (both empty): trivially true
            case l_false:
                STRACE(seq_regex_brief, tout << "empty:neq ";);
                th.add_axiom(~th.mk_eq(r1, r2, false), false_literal);
                return;
            case l_undef:
                break;
            }
        }
        // Try the bisimulation procedure on ground regexes first.  If it
        // returns a definite answer, dispatch the corresponding axiom and
        // bypass the symbolic emptiness/derivative closure.
        if (re().is_ground(r1) && re().is_ground(r2)) {
            seq::regex_bisim bisim(seq_rw());
            switch (bisim.are_equivalent(r1, r2)) {
            case l_true:
                STRACE(seq_regex_brief, tout << "bisim:eq ";);
                return; // trivially true
            case l_false:
                STRACE(seq_regex_brief, tout << "bisim:neq ";);
                th.add_axiom(~th.mk_eq(r1, r2, false), false_literal);
                return;
            case l_undef:
                break;
            }
        }
        th.add_unhandled_expr(r1);
        th.add_unhandled_expr(r2);
    }
    
    void seq_regex::propagate_ne(expr* r1, expr* r2) {
        TRACE(seq_regex, tout << "propagate NEQ: " << mk_pp(r1, m) << ", " << mk_pp(r2, m) << std::endl;);
        STRACE(seq_regex_brief, tout << "PNEQ ";);
        sort* seq_sort = nullptr;
        VERIFY(u().is_re(r1, seq_sort));
        expr_ref r = symmetric_diff(r1, r2);
        if (re().is_ground(r1) && re().is_ground(r2)) {
            seq::regex_bisim bisim(seq_rw());
            switch (bisim.are_equivalent(r1, r2)) {
            case l_true:
                STRACE(seq_regex_brief, tout << "bisim:eq ";);
                th.add_axiom(th.mk_eq(r1, r2, false), false_literal);
                return;
            case l_false:
                STRACE(seq_regex_brief, tout << "bisim:neq ";);
                return; // trivially satisfied
            case l_undef:
                break;
            }
        }
        th.add_unhandled_expr(r1);
        th.add_unhandled_expr(r2);
    }

    bool seq_regex::is_member(expr* r, expr* u) {
        expr* u2 = nullptr;
        while (re().is_union(u, u, u2)) {
            if (r == u2)
                return true;
        }
        return r == u;        
    }

    /**
     * is_non_empty(r, u) => nullable or \/_i (c_i and is_non_empty(r_i, u union r))
     *
     * for each (c_i, r_i) in cofactors (min-terms)
     *
     * is_non_empty(r_i, u union r) := false if r_i in u
     *
     */
    void seq_regex::propagate_is_non_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r = nullptr, *u = nullptr, *n = nullptr;
        VERIFY(sk().is_is_non_empty(e, r, u, n));

        if (block_if_empty(r, lit)) 
            return;
        

        TRACE(seq_regex, tout << "propagate nonempty: " << mk_pp(e, m) << std::endl;);
        STRACE(seq_regex_brief, tout
            << std::endl << "PNE(" << expr_id_str(e) << "," << state_str(r)
            << "," << expr_id_str(u) << "," << expr_id_str(n) << ") ";);

        expr_ref is_nullable = is_nullable_wrapper(r);
        if (m.is_true(is_nullable)) 
            return;


        literal null_lit = th.mk_literal(is_nullable);
        expr_ref hd = mk_first(r, n);
        expr_ref d(m);
        d = mk_derivative_wrapper(hd, r);

        literal_vector lits;
        lits.push_back(~lit);
        if (null_lit != false_literal) 
            lits.push_back(null_lit);

        expr_ref_pair_vector cofactors(m);
        seq_rw().get_cofactors(hd, d, cofactors);
        for (auto const& [c, r] : cofactors) {
            if (is_member(r, u)) 
                continue;            
            expr_ref cond(c, m);
            seq_rw().elim_condition(hd, cond);
            rewrite(cond);
            if (m.is_false(cond))
                continue;            
            expr_ref next_non_empty = sk().mk_is_non_empty(r, re().mk_union(u, r), n);
            if (!m.is_true(cond))
                next_non_empty = m.mk_and(cond, next_non_empty);
            lits.push_back(th.mk_literal(next_non_empty));
        }

        th.add_axiom(lits);
    }

    /*
        Given a string s, index i, and a derivative r, return an
        expression that is equivalent to
            accept s i r
        but which pushes accept s i r into the leaves 

        Input r is of type regex; output is of type bool.

        Example:
            mk_deriv_accept(s, i, (ite a r1 r2) u (ite b r3 r4))
            = (or (ite a (accept s i r1) (accept s i r2))
                  (ite b (accept s i r3) (accept s i r4)))
    */
    expr_ref seq_regex::mk_deriv_accept(expr* s, unsigned i, expr* r) {
        vector<expr*> to_visit;
        to_visit.push_back(r);
        obj_map<expr, expr*> re_to_accept;
        expr_ref_vector _temp_bool_owner(m); // temp owner for bools we create

        bool s_is_longer_than_i = str().min_length(s) > i;
        expr* i_int = a().mk_int(i);
        _temp_bool_owner.push_back(i_int);

        // DFS, avoids duplicating derivative construction that has already been done
        while (!to_visit.empty()) {
            expr* e = to_visit.back();
            expr* econd = nullptr, *e1 = nullptr, *e2 = nullptr;
            if (!re_to_accept.contains(e)) {
                // First visit: add children
                STRACE(seq_regex_verbose, tout << "1";);
                if (m.is_ite(e, econd, e1, e2) ||
                    re().is_union(e, e1, e2)) {
                    to_visit.push_back(e1);
                    to_visit.push_back(e2);
                }
                // Mark first visit by adding nullptr to the map
                re_to_accept.insert(e, nullptr);
            }
            else if (re_to_accept.find(e) == nullptr) {
                // Second visit: set value
                STRACE(seq_regex_verbose, tout << "2";);
                to_visit.pop_back();
                if (m.is_ite(e, econd, e1, e2)) {
                    expr* b1 = re_to_accept.find(e1);
                    expr* b2 = re_to_accept.find(e2);
                    expr* b;
                    if (m.is_true(econd) || b1 == b2)
                        b = b1;
                    else if (m.is_false(econd))
                        b = b2;
                    else
                        b = m.mk_ite(econd, b1, b2);
                    _temp_bool_owner.push_back(b);
                    re_to_accept.find(e) = b;
                }
                else if (re().is_empty(e) || (s_is_longer_than_i && re().is_epsilon(e)))
                {
                    // s[i..] in [] <==> false, also: s[i..] in () <==> false when |s|>i
                    re_to_accept.find(e) = m.mk_false();
                }
                else if (re().is_full_seq(e) || (s_is_longer_than_i && re().is_dot_plus(e)))
                {
                    // s[i..] in .* <==> true, also: s[i..] in .+ <==> true when |s|>i
                    re_to_accept.find(e) = m.mk_true();
                }
                else if (re().is_union(e, e1, e2)) {
                    expr* b1 = re_to_accept.find(e1);
                    expr* b2 = re_to_accept.find(e2);
                    expr* b;
                    if (m.is_false(b1) || b1 == b2)
                        b = b2;
                    else if (m.is_false(b2))
                        b = b1;
                    else
                        b = m.mk_or(b1, b2);
                    _temp_bool_owner.push_back(b);
                    re_to_accept.find(e) = b;
                }
                else {
                    expr_ref acc_leaf = sk().mk_accept(s, i_int, e);
                    _temp_bool_owner.push_back(acc_leaf);
                    re_to_accept.find(e) = acc_leaf;

                    STRACE(seq_regex_verbose, tout
                        << "mk_deriv_accept: added accept leaf: "
                        << mk_pp(acc_leaf, m) << std::endl;);
                }
            }
            else {
                STRACE(seq_regex_verbose, tout << "3";);
                // Remaining visits: skip
                to_visit.pop_back();
            }
        }

        // Finalize
        expr_ref result(m);
        result = re_to_accept.find(r); // Assigns ownership of all exprs in
                                       // re_to_accept for after this completes
        rewrite(result);
        return result;
    }

    /*
        Decide emptiness of a ground regex r via antimirov-mode NFA
        reachability.

        The symbolic derivative engine runs in antimirov mode, so the
        derivative of an intersection distributes into a *set* of individual
        product states inter(A_i, B_j) (each a small, ground regex) rather
        than one giant union-of-intersections term.  get_derivative_targets
        enumerates these NFA successor states.

        We short-circuit to l_false (non-empty) as soon as a reachable state
        is nullable (accepts the empty word) or classical (a regex built only
        from to_re/all/union/concat/star/plus/opt/loop, hence non-empty).  An
        intersection itself is never classical, but once one operand reduces
        to Σ* the intersection collapses (via the derivative's subset
        simplification) to the other, classical, operand.

        If the worklist is exhausted with no such state, r is empty (l_true).
        Returns l_undef if a step bound is hit, so callers can fall back to
        the general procedure.
    */
    lbool seq_regex::re_is_empty(expr* r) {
        if (re().is_empty(r))
            return l_true;
        expr_ref_vector pinned(m);
        obj_hashtable<expr> visited;
        ptr_vector<expr> work;
        work.push_back(r);
        visited.insert(r);
        pinned.push_back(r);
        unsigned const bound = 100000;
        unsigned steps = 0;
        while (!work.empty()) {
            if (++steps > bound)
                return l_undef;
            expr* s = work.back();
            work.pop_back();
            auto info = re().get_info(s);
            if (!info.is_known())
                return l_undef;
            // ε ∈ L(s) or s is a non-empty classical regex ⇒ L(r) non-empty.
            if (info.nullable == l_true || info.classical)
                return l_false;
            // Dead state: prune (min_length == UINT_MAX means no word is
            // accepted from here).
            if (info.min_length == UINT_MAX)
                continue;
            expr_ref_vector targets(m);
            get_derivative_targets(s, targets);
            for (expr* t : targets) {
                if (visited.contains(t))
                    continue;
                visited.insert(t);
                pinned.push_back(t);
                work.push_back(t);
            }
        }
        return l_true;
    }


    /*
        Return a list of all reachable target regexes in the derivative of a
        regex r.

        The derivative is taken wrt (:var 0) and its reachable leaves are
        enumerated with the path-aware cofactor engine, which conjoins the
        ITE-path conditions and prunes infeasible character-range combinations
        (e.g. a nested branch requiring elem = 'a' and elem = 'B').  Each leaf
        is re-normalized with the path-aware smart constructors so that
        semantically equal states stay syntactically identical (essential for
        state dedup in the emptiness closure).

        Without this pruning the naive ITE-tree DFS would reach infeasible
        leaves; an infeasible classical (intersection/complement-free) leaf
        would then be misjudged as a non-empty residual.
    */
    void seq_regex::get_derivative_targets(expr* r, expr_ref_vector& targets) {
        expr_ref_pair_vector cofactors(m);
        seq_rw().brz_derivative_cofactors(r, cofactors);
        for (auto const& [c, t] : cofactors) {
            if (!re().is_empty(t))
                targets.push_back(t);
        }
    }

    /*
        Return a list of all (cond, leaf) pairs in a given derivative
        expression r, where elem is the character symbol the derivative was
        taken with respect to.

        The transition regexes produced by the symbolic derivative engine are
        ITE-trees over character predicates ci on elem (equalities such as
        elem = 'A', and ranges such as 'a' <= elem <= 'z').  These predicates
        are typically mutually exclusive, so the number of feasible truth
        assignments to {c1,..,ck} ("minterms") is small.

        The enumeration is delegated to seq::derive (via seq_rw().get_cofactors)
        so it reuses the very same path/interval context that the derivative
        engine uses while hoisting ITEs: each feasible path through the ITE-tree
        yields one (path_condition, leaf) cofactor, infeasible character-range
        combinations are pruned, and the leaf is simplified with the path-aware
        smart constructors.

        This is used by:
            propagate_is_empty
            propagate_is_non_empty
    */

    /*
      is_empty(r, u) => ~is_nullable(r)
      is_empty(r, u) => (forall x . ~cond(x)) or is_empty(r1, u union r)    for (cond, r) in min-terms(D(x,r))      

      is_empty(r, u) is true if r is a member of u
     */
    void seq_regex::propagate_is_empty(literal lit) {
        expr* e = ctx.bool_var2expr(lit.var()), *r = nullptr, *u = nullptr, *n = nullptr;
        VERIFY(sk().is_is_empty(e, r, u, n));
        expr_ref is_nullable = is_nullable_wrapper(r);

        TRACE(seq_regex, tout << "propagate empty: " << mk_pp(e, m) << std::endl;);
        STRACE(seq_regex_brief, tout
            << std::endl << "PE(" << expr_id_str(e) << "," << state_str(r)
            << "," << expr_id_str(u) << "," << expr_id_str(n) << ") ";);

        if (m.is_true(is_nullable)) {
            th.add_axiom(~lit);
            return;
        }
        th.add_axiom(~lit, ~th.mk_literal(is_nullable));
        expr_ref hd = mk_first(r, n);
        expr_ref d(m);
        d = mk_derivative_wrapper(hd, r);
        literal_vector lits;
        expr_ref_pair_vector cofactors(m);
        seq_rw().get_cofactors(hd, d, cofactors);        
        for (auto const& [c, r] : cofactors) {
            if (is_member(r, u))
                continue;
            expr_ref cond(c, m);
            seq_rw().elim_condition(hd, cond);
            rewrite(cond);
            if (m.is_false(cond))
                continue;
            lits.reset();
            lits.push_back(~lit);
            if (!m.is_true(cond)) {
                expr_ref ncond(mk_not(m, cond), m);
                expr_ref facond = mk_forall(m, hd, ncond);
                ctx.internalize(facond, true); // make sure fa is internalized, and assumed in positive polarity only.
                lits.push_back(th.mk_literal(facond));
            }
            expr_ref is_empty1 = sk().mk_is_empty(r, re().mk_union(u, r), n);    
            lits.push_back(th.mk_literal(is_empty1)); 
            th.add_axiom(lits);
        }        
    }

    expr_ref seq_regex::mk_first(expr* r, expr* n) {
        sort* elem_sort = nullptr, *seq_sort = nullptr;
        VERIFY(u().is_re(r, seq_sort));
        VERIFY(u().is_seq(seq_sort, elem_sort));
        return sk().mk("re.first", n, a().mk_int(r->get_id()), elem_sort);
    }

    std::string seq_regex::state_str(expr* e) {
        if (m_live_states.contains(e))
            return std::to_string(m_live_states.state_id(e));
        return expr_id_str(e);
    }
    std::string seq_regex::expr_id_str(expr* e) {
        return std::string("id") + std::to_string(e->get_id());
    }

}
