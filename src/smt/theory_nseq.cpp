/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.cpp

Abstract:

    Implementation of theory_nseq: see theory_nseq.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#include "smt/theory_nseq.h"
#include "smt/seq_nseq_ambient_context.h"
#include "smt/smt_context.h"
#include "smt/smt_justification.h"
#include "ast/expr_substitution.h"
#include "smt/smt_model_generator.h"
#include "util/trail.h"
#include "ast/ast_ll_pp.h"
#include <functional>
#include <fstream>

namespace smt {

    // Model-value builder for a seq-sorted enode. Unlike the previous
    // implementation (which eagerly substituted a *fresh* value for any
    // non-value, non-unit token and then ran m_th_rewriter over the
    // whole concatenation - discarding the actual dependency on that
    // token's real model value), this walks the token list once in
    // get_dependencies() to record every token that still needs a value
    // computed for it (any unit() argument, or any other still-unresolved
    // subterm) as a proper model_value_dependency, and only then, in
    // mk_value(), splices each dependency's already-materialized value
    // back into its slot before concatenating - so unit(x) where x is a
    // shared variable receives the *same* character value assigned to x
    // elsewhere, and any other non-value token found (e.g. the model_subst-
    // rewritten forms) is also asked for its own value rather than being
    // discarded in favor of an unrelated fresh one.
    class theory_nseq::seq_model_value_proc : public model_value_proc {
        theory_nseq&       th;
        sort*              m_sort;
        // Each slot is either a literal (already-final) token, recorded
        // directly, or a placeholder standing for the i'th dependency in
        // m_dep_enodes/m_dep_units (resolved from `values` in mk_value).
        struct slot {
            expr* m_literal = nullptr; // non-null: use this token as-is
            bool  m_is_unit = false;   // true: dependency's value must be wrapped via str.mk_unit
        };
        vector<slot>                      m_slots;
        ptr_vector<enode>                 m_dep_enodes;
        svector<bool>                     m_dep_is_unit;
    public:
        seq_model_value_proc(theory_nseq& th, sort* s) : th(th), m_sort(s) {}

        // Append a token already known to be a final value/constant
        // (values, or units wrapping a value char) - no dependency
        // needed.
        void add_literal(expr* t) {
            slot sl;
            sl.m_literal = t;
            m_slots.push_back(sl);
        }

        // Append a token that still needs its model value computed:
        // `n` is the enode whose value should be substituted in; if
        // `is_unit` holds, `n`'s own value is the character payload of a
        // unit() token (str.unit(value-of-n) is spliced in), otherwise
        // `n`'s value is spliced in directly (n is itself seq-sorted).
        void add_dependency(enode* n, bool is_unit) {
            slot sl;
            sl.m_is_unit = is_unit;
            m_slots.push_back(sl);
            m_dep_enodes.push_back(n);
            m_dep_is_unit.push_back(is_unit);
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            for (enode* n : m_dep_enodes)
                result.push_back(model_value_dependency(n));
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            SASSERT(values.size() == m_dep_enodes.size());
            ast_manager& m = th.m;
            expr_ref_vector final_toks(m);
            // runs of constant tokens become one string literal (a power's model may repeat its base thousands of times)
            svector<unsigned> chars;
            auto flush = [&]() {
                if (!chars.empty())
                    final_toks.push_back(th.m_seq.str.mk_string(zstring(chars.size(), chars.data())));
                chars.reset();
            };
            auto add = [&](expr* t) {
                expr_ref_vector units(m);
                th.m_seq.str.get_concat_units(t, units); // flattens concats, splits string literals into units
                for (expr* u : units) {
                    expr* ch = nullptr;
                    unsigned code;
                    if (th.m_seq.str.is_unit(u, ch) && th.m_seq.is_const_char(ch, code))
                        chars.push_back(code);
                    else {
                        flush();
                        final_toks.push_back(u);
                    }
                }
            };
            unsigned j = 0;
            for (slot const& sl : m_slots) {
                if (sl.m_literal) {
                    add(sl.m_literal);
                    continue;
                }
                expr* v = values.get(j++);
                add(sl.m_is_unit ? th.m_seq.str.mk_unit(v) : v);
            }
            flush();
            expr_ref result(m);
            result = final_toks.empty() ? th.m_seq.str.mk_empty(m_sort)
                                        : th.m_seq.str.mk_concat(final_toks.size(), final_toks.data(), m_sort);
            th.m_factory->add_trail(result);
            return to_app(result);
        }
    };

    theory_nseq::theory_nseq(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("seq")),
        m_seq(m),
        m_autil(m),
        m_rewriter(m),
        m_th_rewriter(m),
        m_arith_value(m),
        m_pin(m),
        m_ax(*this, m_th_rewriter),
        m_sk(m, m_th_rewriter),
        m_axioms(m),
        m_tree(ctx.get_trail_stack(), m.limit()),
        m_root(m_tree.mk_root()),
        m_solver(m, m_autil, m_tree.dep_mgr()),
        m_model_pin(m)
    {
        m_ambient = alloc(seq::theory_nseq_ambient_context, *this);
        m_tree.set_ambient_context(m_ambient.get());

        m_tree.register_facet_bound<seq::eq_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_eq_id(id); }, m, m_seq, m_tree.dep_mgr());
        m_tree.register_facet_bound<seq::deq_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_deq_id(id); }, m, m_seq, m_tree.dep_mgr());
        m_tree.register_facet_bound<seq::solver_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_arith_id(id); }, m, m_seq, m_solver);
        m_tree.register_facet_bound<seq::power_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_pow_id(id); }, m, m_seq, m_autil, m_tree.dep_mgr());
        m_tree.register_facet_bound<seq::mem_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_mem_id(id); }, m, m_seq, m_tree.dep_mgr(), m_rewriter);
        m_tree.register_facet_bound<seq::ncontains_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_ncontains_id(id); }, m, m_seq, m_tree.dep_mgr());
        m_tree.register_facet_bound<seq::assumption_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_assumption_id(id); }, m);
        m_tree.register_facet_bound<seq::req_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_req_id(id); }, m, m_seq, m_tree.dep_mgr());
        m_tree.register_facet_bound<seq::lex_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_lex_id(id); }, m, m_seq, m_tree.dep_mgr());
        m_tree.register_facet_bound<seq::stoi_facet>(*m_root, [&](stx::facet_id id) { m_ambient->set_stoi_id(id); }, m, m_seq, m_autil);
        m_tree.register_facet_bound<seq::ho_facet>(
            *m_root,
            [&](stx::facet_id id) { m_ambient->set_ho_id(id); },
            m,
            m_seq,
            m_rewriter,
            [this](expr* lhs, expr* rhs) { return add_ho_eq(lhs, rhs); },
            [this](expr* term, expr*& elaboration) { return find_ho_elaboration(term, elaboration); });
        m_ambient->stoi_facet(*m_root).set_instantiate([this](expr* e, unsigned k) { m_ax.add_stoi_axiom(e, k); });

        // deterministic propagation plugins (order among these does not
        // matter: the engine iterates every propagation plugin to
        // fixpoint before ever consulting a split plugin). Each plugin
        // is heap-allocated and handed to `m_tree`, which owns it from
        // here on (stored in its own `scoped_ptr_vector`, deallocated
        // with the tree) - see stx_search_tree.h's
        // `add_propagation_plugin`/`add_split_plugin`.
        m_tree.add_propagation_plugin(alloc(seq::eq_propagation, m, m_seq));
        m_tree.add_propagation_plugin(alloc(seq::deq_propagation, m, m_seq));
        m_tree.add_propagation_plugin(alloc(seq::arith_propagation, m, m_seq));
        m_tree.add_propagation_plugin(alloc(seq::power_propagation, m, m_seq, m_autil));
        m_tree.add_propagation_plugin(alloc(seq::mem_propagation, m, m_seq, m_rewriter));
        m_tree.add_propagation_plugin(alloc(seq::mem_bounds_propagation, m, m_seq, m_autil, *m_ambient));
        m_tree.add_propagation_plugin(alloc(seq::ncontains_propagation, m, m_seq, m_autil));
        m_tree.add_propagation_plugin(alloc(seq::req_propagation, m, m_seq, m_rewriter));
        m_tree.add_propagation_plugin(alloc(seq::lex_propagation, m, m_seq));

        // split plugins: registration order mostly mirrors the priority
        // order of the c3 branch's nielsen_graph::generate_extensions
        // (see theory_nseq.h's module comment for the mapping table),
        // with one deliberate deviation: mem_monadic_split (regex
        // membership landing, c3 priority 5d) is registered ahead of
        // eq_split/word_eq_split (equality splitting, c3 priorities 5
        // and 8b/12) instead of between them, so that at cost 0 the
        // engine always tries a regex-membership split before it tries
        // any word-equation split. This was found experimentally to
        // avoid needless equation case-splitting on nodes that a regex
        // split alone can already close.
        m_tree.add_split_plugin(alloc(seq::power_fixed_exp, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::eq_approx_split, m, m_seq, m_rewriter));
        m_tree.add_split_plugin(alloc(seq::mem_parikh_split, m, m_seq));
        m_mem_leaf = alloc(seq::mem_leaf_split, m, m_seq, m_rewriter, *m_ambient);
        m_tree.add_split_plugin(m_mem_leaf);
        m_tree.add_split_plugin(alloc(seq::mem_monadic_split, m, m_seq, m_rewriter, *m_ambient));
        m_tree.add_split_plugin(alloc(seq::power_split_elim, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_fine_wilf, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_decompose, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_peel, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::eq_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::power_gpower_intro, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::word_eq_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::power_split, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_peel_mem, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::deq_split, m, m_seq));

        m_tree.set_max_search_depth(100);

        // Diagnostics only: NSEQ_DOT_FILE=<path>, if set, enables
        // stx::search_tree's dot-trace recording (see stx_search_tree.h's
        // m_dot_nodes comment). The file is kept live-updated throughout
        // the search (throttled, see set_dot_live_file) rather than only
        // dumped after m_tree.solve() returns, since a real -T: timeout
        // is enforced by the shell calling _Exit() directly from a
        // background thread once the deadline elapses - that never
        // unwinds back to a post-solve() dump point, so a live file is
        // the only way to see anything for a run that actually times
        // out. Mirrors z3-tacas's nielsen_graph::to_dot() debugging
        // facility, reusable via e.g. `dot -Tsvg <path> -o out.svg`.
        if (const char* dot_path = getenv("NSEQ_DOT_FILE")) {
            m_tree.enable_dot_trace(true);
            m_tree.set_dot_live_file(dot_path);
            if (const char* max_nodes = getenv("NSEQ_DOT_MAX_NODES"))
                m_tree.set_max_dot_nodes(static_cast<unsigned>(atoi(max_nodes)));
        }
    }

    void theory_nseq::init() {
        m_arith_value.init(&get_context());
        std::function<void(literal, literal, literal, literal, literal)> add_ax =
            [&](literal l1, literal l2, literal l3, literal l4, literal l5) {
                literal_vector lits;
                if (l1 == true_literal || l2 == true_literal || l3 == true_literal ||
                    l4 == true_literal || l5 == true_literal)
                    return;
                if (l1 != null_literal && l1 != false_literal) lits.push_back(l1);
                if (l2 != null_literal && l2 != false_literal) lits.push_back(l2);
                if (l3 != null_literal && l3 != false_literal) lits.push_back(l3);
                if (l4 != null_literal && l4 != false_literal) lits.push_back(l4);
                if (l5 != null_literal && l5 != false_literal) lits.push_back(l5);
                for (literal lit : lits)
                    if (ctx.get_assignment(lit) == l_true && ctx.get_assign_level(lit) == 0)
                        return;
                for (literal lit : lits)
                    ctx.mark_as_relevant(lit);
                ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
            };
        std::function<literal(expr*, bool)> mk_eq_emp = [&](expr* e, bool phase) {
            expr_ref emp(m_seq.str.mk_empty(e->get_sort()), m);
            literal lit = mk_eq(e, emp, false);
            ctx.force_phase(phase ? lit : ~lit);
            ctx.mark_as_relevant(lit);
            return lit;
        };
        m_ax.add_axiom5 = add_ax;
        m_ax.mk_eq_empty2 = mk_eq_emp;
    }

    // -----------------------------------------------------------------------
    // Internalization
    // -----------------------------------------------------------------------

    bool theory_nseq::internalize_atom(app* atom, bool /*gate_ctx*/) {
        if (m_seq.str.is_in_re(atom)) {
            expr* str_arg = atom->get_arg(0);
            mk_var(ensure_enode(str_arg));
            if (!ctx.e_internalized(atom->get_arg(1)))
                ctx.internalize(atom->get_arg(1), false);
            if (!ctx.b_internalized(atom)) {
                bool_var bv = ctx.mk_bool_var(atom);
                ctx.set_var_theory(bv, get_id());
                ctx.mark_as_relevant(bv);
            }
            return true;
        }
        return internalize_term(atom);
    }

    theory_var theory_nseq::mk_var(enode* n) {
        expr* o = n->get_expr();
        if (!m_seq.is_seq(o) && !m_seq.is_re(o))
            return null_theory_var;
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        get_context().attach_th_var(n, this, v);
        get_context().mark_as_relevant(n);
        return v;
    }

    bool theory_nseq::internalize_term(app* term) {
        for (auto arg : *term)
            mk_var(ensure_enode(arg));

        if (ctx.e_internalized(term)) {
            mk_var(ctx.get_enode(term));
            return true;
        }

        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode* en = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, m.is_bool(term), true);
        mk_var(en);
        return true;
    }

    void theory_nseq::apply_sort_cnstr(enode* n, sort* /*s*/) {
        mk_var(n);
    }

    // -----------------------------------------------------------------------
    // Equality / disequality notifications
    // -----------------------------------------------------------------------

    void theory_nseq::new_eq_eh(theory_var v1, theory_var v2) {
        enode* n1 = get_enode(v1);
        enode* n2 = get_enode(v2);
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        unsigned idx = mk_dep(assumption(n1, n2));
        seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
        if (m_seq.is_re(e1)) {
            m_ambient->req_facet(*m_root).add_req(e1, e2, true, dep);
        }
        if (m_seq.is_seq(e1)) {
            expr_ref_vector lhs = m_ambient->tokenize(e1);
            expr_ref_vector rhs = m_ambient->tokenize(e2);
            m_ambient->eq_facet(*m_root).add_equation(lhs, rhs, dep);
        }
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        enode *n1 = get_enode(v1);
        enode *n2 = get_enode(v2);
        expr *e1 = n1->get_expr();
        expr *e2 = n2->get_expr();
        unsigned idx = mk_dep(assumption(n1, n2, true));
        seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
        if (m_seq.is_re(e1)) {
            m_ambient->req_facet(*m_root).add_req(e1, e2, false, dep);
        }
        if (m_seq.is_seq(e1)) {
            expr_ref_vector lhs = m_ambient->tokenize(e1);
            expr_ref_vector rhs = m_ambient->tokenize(e2);
            m_ambient->deq_facet(*m_root).add_disequation(lhs, rhs, dep);
        }
    }

    // -----------------------------------------------------------------------
    // Boolean assignment notification: str.in_re, prefix/suffix/contains
    // -----------------------------------------------------------------------

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        literal lit(v, !is_true);
        expr* e1 = nullptr, *e2 = nullptr;

        // Any other assignment invalidates the sat snapshot final_check_eh is waiting
        // on; the pending assumption literals themselves are what it is waiting for.
        if (!any_of(m_pending_assumptions, [&](literal l) { return l.var() == v; }))
            m_pending_assumptions.reset();
        if (m_seq.str.is_in_re(e, e1, e2)) {
            ensure_enode(e1);
            ensure_enode(e2);
            unsigned idx = mk_dep(assumption(lit));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            expr* re = is_true ? e2 : m_seq.re.mk_complement(e2);
            seq::view mv = seq::view::membership(re, m);
            expr_ref_vector ts = m_ambient->tokenize(e1);
            // str_mem itself pins m_view's regex (m_regex, an expr_ref)
            // for as long as the membership is live, so no separate
            // theory_nseq::pin() call is needed here even though the
            // complement is freshly built and not owned elsewhere.
            m_ambient->mem_facet(*m_root).add(seq::str_mem(m, ts, mv, dep));
            return;
        }

        if (m_seq.str.is_prefix(e, e1, e2)) {
            // prefix(e1,e2) <=> exists f. e2 = e1 ++ f  in the true case;
            // the false case - "e1 is not a prefix of e2" - has no
            // eq_facet/ncontains_facet analog, so it is axiomatized
            // directly (following theory_seq::propagate_not_prefix, minus
            // the canonize-based short-circuit which relies on solved-form
            // machinery theory_nseq doesn't have): the disjunctive axiom
            // `!prefix(e1,e2) => len(e1) > len(e2) or e1=xcy & e2=xdz & c!=d`
            // is emitted via m_ax.add_prefix_axiom, which internally calls
            // back into add_axiom5/mk_eq_empty2 (wired in init()) to create
            // ordinary theory-axiom clauses in the ambient SMT context.
            if (is_true) {
                unsigned idx = mk_dep(assumption(lit));
                seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
                expr* f = m_ambient->eq_facet(*m_root).mk_fresh_var(e2->get_sort());
                expr_ref_vector lhs = m_ambient->tokenize(e2);
                expr_ref_vector rhs = m_ambient->tokenize(e1);
                rhs.push_back(f); // fresh existential, kept alive by rhs's own ref (add_equation copies it into the stored equation)
                m_ambient->eq_facet(*m_root).add_equation(lhs, rhs, dep);
            }
            else
                m_ax.add_prefix_axiom(e);
            return;
        }

        if (m_seq.str.is_suffix(e, e1, e2)) {
            // suffix(e1,e2) <=> exists f. e2 = f ++ e1 in the true case;
            // the false case is axiomatized directly, mirroring the
            // prefix case above (theory_seq::propagate_not_suffix).
            if (is_true) {
                unsigned idx = mk_dep(assumption(lit));
                seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
                expr* f = m_ambient->eq_facet(*m_root).mk_fresh_var(e2->get_sort());
                expr_ref_vector lhs = m_ambient->tokenize(e2);
                expr_ref_vector rhs(m);
                rhs.push_back(f); // fresh existential, kept alive by rhs's own ref
                rhs.append(m_ambient->tokenize(e1));
                m_ambient->eq_facet(*m_root).add_equation(lhs, rhs, dep);
            }
            else
                m_ax.add_suffix_axiom(e);
            return;
        }

        if (m_seq.str.is_contains(e, e1, e2)) {
            unsigned idx = mk_dep(assumption(lit));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            if (is_true) {
                // contains(e1,e2) <=> exists x,y. e1 = x ++ e2 ++ y
                expr* x = m_ambient->eq_facet(*m_root).mk_fresh_var(e1->get_sort());
                expr* y = m_ambient->eq_facet(*m_root).mk_fresh_var(e1->get_sort());
                expr_ref_vector lhs = m_ambient->tokenize(e1);
                expr_ref_vector rhs(m);
                rhs.push_back(x); // fresh existentials, kept alive by rhs's own ref
                rhs.append(m_ambient->tokenize(e2));
                rhs.push_back(y);
                m_ambient->eq_facet(*m_root).add_equation(lhs, rhs, dep);
            }
            else {
                // not contains(e1,e2): a universal obligation, not reducible
                // to an equation - accumulate it on ncontains_facet.
                m_ambient->ncontains_facet(*m_root).add_ncontains(e1, e2, dep);
            }
            return;
        }

        if (m_seq.str.is_lt(e, e1, e2) || m_seq.str.is_le(e, e1, e2)) {
            // Lexicographic comparison: route into lex_facet instead of
            // m_ax.add_lt_axiom/add_le_axiom's disjunctive Skolem
            // axiomatization (see seq_lex_facet.h's module comment).
            // Negation flips both the operator and the operand order:
            // !(e1 < e2) <=> e2 <= e1, !(e1 <= e2) <=> e2 < e1.
            bool strict = m_seq.str.is_lt(e);
            unsigned idx = mk_dep(assumption(lit));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            expr_ref_vector lhs = m_ambient->tokenize(is_true ? e1 : e2);
            expr_ref_vector rhs = m_ambient->tokenize(is_true ? e2 : e1);
            m_ambient->lex_facet(*m_root).add_lex(lhs, rhs, is_true ? strict : !strict, dep);
            return;
        }

        if (m_sk.is_eq(e, e1, e2)) {
            // Internal equality-atom skolem (see seq::skolem::mk_eq):
            // theory_seq's own mechanism for deferring an
            // internally-derived equality until the atom itself is
            // asserted true - mirror theory_seq::assign_eh's
            // m_sk.is_eq branch by propagating the equality straight
            // into the SMT core (propagate_eq/ctx.assign_eq), rather
            // than merely recording it as an ordinary eq_facet
            // equation (this is not currently created by any
            // theory_nseq call site, but assign_eh must still handle it
            // correctly if any future code path - or a shared skolem
            // instance - ever creates one).
            if (is_true)
                propagate_eq(lit, e1, e2);
            return;
        }

        // No handler recognized this atom: log it so gaps in assign_eh's
        // dispatch are visible rather than silently ignored.
        TRACE(seq, tout << "unhandled assign_eh: " << (is_true ? "" : "not ") << mk_bounded_pp(e, m) << "\n";);
    }

    // -----------------------------------------------------------------------
    // Axiomatization queue: string operations reducible to more basic
    // arithmetic/sequence constraints (length/index/replace/extract/at/
    // nth/itos/stoi/lt/le/unit/is_digit/from_code/to_code). Follows
    // theory_seq's relevant_eh/enque_axiom/deque_axiom pattern, but is
    // drained eagerly (can_propagate/propagate) rather than at
    // final_check_eh, matching theory_nseq's "apply as soon as noticed"
    // style; the axioms themselves are solver-independent term rewrites,
    // so eager draining is sound.
    // -----------------------------------------------------------------------

    void theory_nseq::relevant_eh(expr* n) {
        seq::ho_facet& hf = m_ambient->ho_facet(*m_root);
        expr* s = nullptr;
        if (hf.is_ho_term(n, s)) {
            hf.add_term(n);
            ensure_length_var(s);
        }
        // s^k: register the power obligation; the facet's rules assume k >= 0 (s^k = s^max(k,0))
        expr* pow_base = nullptr, *k = nullptr;
        if (m_seq.str.is_power(n, pow_base, k)) {
            expr* k0 = m_autil.is_numeral(k) ? k : m.mk_ite(m_autil.mk_ge(k, m_autil.mk_int(0)), k, m_autil.mk_int(0));
            m_ambient->power_facet(*m_root).add_power(n, pow_base, k0);
        }
        if (m_seq.str.is_length(n)      ||
            m_seq.str.is_index(n)       ||
            m_seq.str.is_last_index(n)  ||
            m_seq.str.is_replace(n)     ||
            m_seq.str.is_replace_all(n) ||
            m_seq.str.is_extract(n)     ||
            m_seq.str.is_at(n)          ||
            m_seq.str.is_nth_i(n)       ||
            m_seq.str.is_itos(n)        ||
            m_seq.str.is_stoi(n)        ||
            m_seq.str.is_unit(n)        ||
            m_seq.str.is_is_digit(n)    ||
            m_seq.str.is_from_code(n)   ||
            m_seq.str.is_to_code(n))
            enqueue_axiom(n);
    }

    void theory_nseq::enqueue_axiom(expr* e) {
        if (!m_axiom_set.contains(e)) {
            m_axioms.push_back(e);
            m_axiom_set.insert(e);
            ctx.push_trail(push_back_vector(m_axioms));
            ctx.push_trail(insert_obj_trail<expr>(m_axiom_set, e));
        }
    }

    void theory_nseq::dequeue_axiom(expr* n) {
        if (m_seq.str.is_length(n))
            m_ax.add_length_axiom(n);
        else if (m_seq.str.is_index(n))
            m_ax.add_indexof_axiom(n);
        else if (m_seq.str.is_last_index(n))
            m_ax.add_last_indexof_axiom(n);
        else if (m_seq.str.is_replace(n))
            m_ax.add_replace_axiom(n);
        else if (m_seq.str.is_replace_all(n))
            m_ax.add_replace_all_axiom(n);
        else if (m_seq.str.is_extract(n))
            m_ax.add_extract_axiom(n);
        else if (m_seq.str.is_at(n))
            m_ax.add_at_axiom(n);
        else if (m_seq.str.is_nth_i(n))
            m_ax.add_nth_axiom(n);
        else if (m_seq.str.is_itos(n))
            m_ax.add_itos_axiom(n);
        else if (m_seq.str.is_stoi(n)) {
            m_ax.add_stoi_axiom_re(n);
            m_ambient->stoi_facet(*m_root).add_term(n);
        }
        else if (m_seq.str.is_unit(n))
            m_ax.add_unit_axiom(n);
        else if (m_seq.str.is_is_digit(n))
            m_ax.add_is_digit_axiom(n);
        else if (m_seq.str.is_from_code(n))
            m_ax.add_str_from_code_axiom(n);
        else if (m_seq.str.is_to_code(n))
            m_ax.add_str_to_code_axiom(n);
    }

    bool theory_nseq::can_propagate() {
        return m_axioms_head < m_axioms.size();
    }

    void theory_nseq::propagate() {
        while (m_axioms_head < m_axioms.size() && !ctx.inconsistent()) {
            expr* e = m_axioms.get(m_axioms_head);
            dequeue_axiom(e);
            ctx.push_trail(value_trail<unsigned>(m_axioms_head));
            ++m_axioms_head;
        }
    }

    unsigned theory_nseq::mk_dep(assumption const& a) {
        unsigned j = m_assumptions.size();
        m_assumptions.push_back(a);
        ctx.push_trail(push_back_vector(m_assumptions));
        return 2 * j + 1;
    }

    // See theory_nseq.h's module comment on flush_assigned_literals for
    // the full rationale.
    void theory_nseq::flush_assigned_literals() {
        seq::solver_facet_i& sf = m_ambient->solver_facet(*m_root);
        literal_vector const& lits = ctx.assigned_literals();
        ctx.push_trail(value_trail<unsigned>(m_lits_qhead));
        for (; m_lits_qhead < lits.size(); ++m_lits_qhead) {
            literal lit = lits[m_lits_qhead];
            if (!ctx.is_relevant(lit))
                continue;
            expr* atom = ctx.bool_var2expr(lit.var());
            expr_ref e(lit.sign() ? m.mk_not(atom) : atom, m);
            unsigned idx = mk_dep(assumption(lit));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            sf.add_constraint(e, dep);
        }
    }

    // Mirrors theory_seq::propagate_eq: assign e1 = e2 directly into the
    // SMT core, justified by lit (already true - the caller is the
    // m_sk.is_eq branch of assign_eh, called only when is_true holds).
    bool theory_nseq::propagate_eq(literal lit, expr* e1, expr* e2) {
        enode* n1 = ensure_enode(e1);
        enode* n2 = ensure_enode(e2);
        if (n1->get_root() == n2->get_root())
            return false;
        ctx.mark_as_relevant(n1);
        ctx.mark_as_relevant(n2);
        justification* js =
            ctx.mk_justification(
                ext_theory_eq_propagation_justification(
                    get_id(), ctx, 1, &lit, 0, nullptr, n1, n2));
        ctx.assign_eq(n1, n2, eq_justification(js));
        return true;
    }

    void theory_nseq::report_conflict(seq::eq_tree::dep_tracker dep) {
        vector<unsigned, false> idxs;
        m_tree.dep_mgr().linearize(dep, idxs);
        literal_vector clause;
        for (unsigned idx : idxs) {
            if ((idx & 1) == 0) {
                expr* e = m_ambient->conditional_dep_expr(idx / 2);
                clause.push_back(~mk_literal(e));
                continue;
            }
            assumption const& a = m_assumptions[idx / 2];
            if (a.lit != null_literal) {
                SASSERT(ctx.get_assignment(a.lit) == l_true);
                clause.push_back(~a.lit);
            }
            else if (a.is_diseq) {
                // n1, n2 were distinct in the ambient context - the
                // equality literal is only created now, lazily, since
                // the disequality is actually needed to justify this
                // conflict.
                SASSERT(a.n1->get_root() != a.n2->get_root());
                clause.push_back(mk_eq(a.n1->get_expr(), a.n2->get_expr(), false));
            }
            else {
                SASSERT(a.n1->get_root() == a.n2->get_root());
                clause.push_back(~mk_eq(a.n1->get_expr(), a.n2->get_expr(), false));
            }
        }
        for (literal lit : clause)
            ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), clause.size(), clause.data());
        ++m_num_conflicts;
    }

    void theory_nseq::init_model(model_generator& mg) {
        m_factory = alloc(seq_factory, get_manager(), get_family_id(), mg.get_model());
        mg.register_factory(m_factory);
        for (enode* n : ctx.enodes()) {
            expr* e = n->get_expr();
            if (m_seq.is_seq(e) && m.is_value(e))
                m_factory->register_value(e);
        }
        seq::eq_tree::node const* snap = m_tree.sat_snapshot();
        if (!snap)
            return;
        auto& mf = m_ambient->mem_facet(const_cast<seq::eq_tree::node&>(*snap));
        mf.get_witness_model(m_model_subst, m_model_pin);
    }

    void theory_nseq::finalize_model(model_generator&) {
        m_factory = nullptr; // owned by the model's plugin_manager; do not delete here
        m_model_subst.reset();
        m_model_pin.reset();
    }

    model_value_proc* theory_nseq::mk_value(enode* n, model_generator&) {
        expr* e = n->get_expr();
        if (m_seq.is_re(e))
            return alloc(expr_wrapper_proc, to_app(e));
        SASSERT (m_seq.is_seq(e));
        seq::eq_tree::node const* snap = m_tree.sat_snapshot();
        expr_ref_vector resolved(m);
        if (snap)
            m_ambient->eq_facet(const_cast<seq::eq_tree::node&>(*snap)).eliminate(e, resolved);
        else
            m_seq.str.get_concat_units(e, resolved);

        seq_model_value_proc* proc = alloc(seq_model_value_proc, *this, e->get_sort());
        seq::solver_facet_i const* sf = snap ? &m_ambient->solver_facet(const_cast<seq::eq_tree::node&>(*snap)) : nullptr;

        // Append token `t` to `proc`: literal tokens (values, units over
        // a value char, or any token that has no enode yet - nothing to
        // depend on) are recorded as-is; anything else that is already
        // internalized records an actual dependency so its real,
        // already-materialized model value is spliced in later by
        // seq_model_value_proc::mk_value, instead of being thrown away
        // for an unrelated fresh value.
        std::function<void(expr*)> add_token = [&](expr* t) {
            expr* sub = nullptr, *s = nullptr, *k = nullptr;
            rational count;
            if (m_model_subst.find(t, sub)) {
                expr_ref_vector toks(m);
                m_seq.str.get_concat_units(sub, toks);
                for (expr* t2 : toks)
                    add_token(t2);
                return;
            }
            expr* ch = nullptr;
            if (m_seq.str.is_unit(t, ch)) {
                if (m.is_value(ch) || !ctx.e_internalized(ch))
                    proc->add_literal(t);
                else {
                    enode* en = ctx.get_enode(ch);
                    // model_generator only builds a model_value_proc for
                    // enodes it deems relevant (see mk_value_procs); a
                    // dependency on a non-relevant enode's root would
                    // never be found in root2proc, crashing top-sort/
                    // mk_values. Rather than forcing it relevant, fall
                    // back to a default character - non-relevant enodes
                    // are free to take an arbitrary value.
                    if (ctx.is_relevant(en))
                        proc->add_dependency(en, true);
                    else
                        proc->add_literal(m_seq.str.mk_unit(m_seq.str.mk_char(0)));
                }
            }
            else if (sf && m_seq.str.is_power(t, s, k) && sf->value(k, count) && count.is_unsigned()) {
                // the base, repeated as often as the sat leaf's arithmetic model says
                for (unsigned c = 0; c < count.get_unsigned(); ++c)
                    add_token(s);
            }
            else if (m.is_value(t) || !ctx.e_internalized(t)) {
                proc->add_literal(t);
            }
            else {
                enode* en = ctx.get_enode(t);
                // eliminate() may fail to resolve `t` any further than
                // `e` itself (e.g. an unconstrained seq variable), in
                // which case en->get_root() == n: recording that as a
                // dependency would be a self-dependency on the very
                // enode this model_value_proc is building the value
                // for, which model_generator::mk_values (see
                // smt_model_generator.cpp) cannot satisfy (its value
                // isn't in m_root2value yet) - fall back to a fresh
                // value for such an irreducible token instead.
                if (en->get_root() == n) {
                    proc->add_literal(to_app(m_factory->get_fresh_value(t->get_sort())));
                    return;
                }
                // Any other still-unresolved seq-sorted subterm that is
                // already internalized: record a dependency on its own
                // enode so its (separately computed) model value is
                // spliced in here, rather than being replaced by an
                // unrelated fresh value - unless it is not relevant, in
                // which case there is no model_value_proc for it to
                // depend on; fall back to the empty sequence instead.
                if (ctx.is_relevant(en))
                    proc->add_dependency(en, false);
                else
                    proc->add_literal(m_seq.str.mk_empty(t->get_sort()));
            }
        };
        for (expr* t : resolved)
            add_token(t);
        return proc;
    }

    final_check_status theory_nseq::final_check_eh(unsigned) {
        ++m_num_final_checks;

        if (m_ambient->ho_facet(*m_root).propagate())
            return FC_CONTINUE;

        if (!m_pending_assumptions.empty()) {

            if (all_of(m_pending_assumptions, [&](literal lit) { return ctx.get_assignment(lit) == l_true; })) 
                return FC_DONE;

            SASSERT(all_of(m_pending_assumptions, [&](literal lit) { return ctx.get_assignment(lit) != l_undef; }));

            // At least one hypothesis turned out false: it never held,
            // so the tree state it came from cannot be trusted as a
            // model. Discard it and fall through to re-run the tree
            // search below from scratch.
            m_pending_assumptions.reset();
        }

        m_ambient->reset_conditional_deps();
        flush_assigned_literals();
        // Instantiate any inductive stoi coherence axioms now made
        // available by the arithmetic sub-solver committing to concrete
        // lengths (see check_stoi_coherence's declaration). Doing this
        // before m_tree.solve() lets a `str.to_int` unfolding feed
        // straight into the very same search; `stoi_progress` also lets
        // any later FC_GIVEUP in this call fall back to FC_CONTINUE
        // instead, since new axioms are now available for the core to
        // reconsider, so giving up here would be premature.
        bool stoi_progress = !check_stoi_coherence();
        if (m_mem_leaf)
            m_mem_leaf->reset_root_ask();
        stx::search_result res;
        try {
            res = m_tree.solve();
        }
        catch (const std::exception&) {
            // Diagnostics only: on cancellation/timeout (thrown from
            // deep within m_tree.solve() via the async -T timeout event
            // handler), dump whatever dot-trace state was recorded so
            // far, since the normal post-solve() dump point below is
            // never reached in that case.
            if (m_tree.dot_trace_enabled()) {
                if (char const* path = getenv("NSEQ_DOT_FILE")) {
                    std::ofstream dot(path);
                    if (dot)
                        m_tree.to_dot(dot);
                }
            }
            throw;
        }
        if (m_tree.dot_trace_enabled()) {
            if (char const* path = getenv("NSEQ_DOT_FILE")) {
                std::ofstream dot(path);
                if (dot)
                    m_tree.to_dot(dot);
            }
        }
        switch (res) {
        case stx::search_result::sat: {
            seq::eq_tree::node const* snap = m_tree.sat_snapshot();
            if (snap) {
                auto& node = const_cast<seq::eq_tree::node&>(*snap);
                expr_ref_vector assumptions(m);
                for (auto const& assumption : m_ambient->assumption_facet(node).assumptions())
                    assumptions.push_back(assumption.first);
                // the core must agree with the leaf's arithmetic model on every exponent it may see
                rational v;
                for (auto const& p : m_ambient->power_facet(node).powers())
                    if (m_ambient->solver_facet(node).value(p.m_n, v))
                        assumptions.push_back(m.mk_eq(p.m_n, m_autil.mk_numeral(v, true)));
                for (expr* a : assumptions) {
                    literal lit = mk_literal(a);
                    bool_var bv = lit.var();
                    if (ctx.get_var_theory(bv) == null_theory_var)
                        ctx.set_var_theory(bv, get_id());
                    auto r = ctx.get_assignment(lit);
                    if (r == l_true)
                        continue;
                    if (r == l_false) {
                        m_pending_assumptions.reset();
                        return FC_CONTINUE;
                    }
                    if (r == l_undef)
                        ctx.force_phase(lit);
                    m_pending_assumptions.push_back(lit);
                }
                if (!m_pending_assumptions.empty()) {
                    ctx.push_trail(restore_vector<literal_vector>(m_pending_assumptions, 0));
                    return FC_CONTINUE;
                }
            }
            return FC_DONE;
        }

        case stx::search_result::unsat: {
            seq::eq_tree::dep_tracker dep = m_root->conflict_dep();
            if (dep) {
                report_conflict(dep);
                return FC_CONTINUE;
            }
            return stoi_progress ? FC_CONTINUE : FC_GIVEUP;
        }
        default:
            if (stoi_progress)
                return FC_CONTINUE;
            if (getenv("NSEQ_DUMP_UNKNOWN")) {
                std::cerr << "theory_nseq: giving up (" << (res == stx::search_result::unknown ? "unknown" : "depth_cutoff") << ")\n";
                for (unsigned id = 0; id < m_root->num_facets(); ++id)
                    if (m_root->has_facet(id))
                        m_root->facet(id).display(std::cerr) << "\n";
            }
            return FC_GIVEUP;
        }
    }

    void theory_nseq::push_scope_eh() {
        theory::push_scope_eh();
        m_tree.push_facets();
    }

    void theory_nseq::pop_scope_eh(unsigned num_scopes) {
        for (unsigned i = 0; i < num_scopes; ++i)
            m_tree.pop_facets();
        theory::pop_scope_eh(num_scopes);
    }

    theory* theory_nseq::mk_fresh(context* new_ctx) {
        return alloc(theory_nseq, *new_ctx);
    }

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq: " << m_num_final_checks << " final checks, " << m_num_conflicts << " conflicts\n";
        out << "  ho terms: " << m_ambient->ho_facet(*m_root).terms().size() << "\n";
        m_tree.display(out);
    }

    void theory_nseq::collect_statistics(::statistics& st) const {
        st.update("nseq final checks", m_num_final_checks);
        st.update("nseq conflicts", m_num_conflicts);
        seq::ho_facet const& hf = m_ambient->ho_facet(*m_root);
        st.update("nseq length axioms", hf.num_length_axioms());
        st.update("nseq ho unfolds", hf.num_ho_unfolds());
        m_tree.collect_statistics(st);
    }

    void theory_nseq::ensure_length_var(expr* e) const {
        SASSERT(e && m_seq.is_seq(e));
        expr_ref len(m_seq.str.mk_length(e), m);
        if (!ctx.e_internalized(len))
            ctx.internalize(len, false);
    }

    bool theory_nseq::add_ho_eq(expr* lhs, expr* rhs) {
        if (!ctx.e_internalized(lhs))
            ctx.internalize(lhs, false);
        if (!ctx.e_internalized(rhs))
            ctx.internalize(rhs, false);
        if (ctx.get_enode(lhs)->get_root() == ctx.get_enode(rhs)->get_root())
            return false;

        expr_ref eq(m.mk_eq(lhs, rhs), m);
        if (!ctx.b_internalized(eq))
            ctx.internalize(eq, true);
        literal lit = ctx.get_literal(eq);
        if (ctx.get_assignment(lit) == l_true)
            return false;
        ctx.mk_th_axiom(get_id(), 1, &lit);
        TRACE(seq, tout << "nseq ho equality: "
                        << mk_bounded_pp(lhs, m, 3) << " = "
                        << mk_bounded_pp(rhs, m, 3) << "\n";);
        return true;
    }

    bool theory_nseq::find_ho_elaboration(expr* term, expr*& elaboration) const {
        elaboration = nullptr;
        if (!ctx.e_internalized(term))
            return false;
        enode* root = ctx.get_enode(term)->get_root();
        enode* curr = root;
        do {
            expr* e = curr->get_expr();
            expr* a1 = nullptr, *a2 = nullptr;
            if (m_seq.str.is_empty(e) ||
                m_seq.str.is_unit(e, a1) ||
                m_seq.str.is_concat(e, a1, a2)) {
                elaboration = e;
                return true;
            }
            curr = curr->get_next();
        }
        while (curr != root);
        return false;
    }

    bool theory_nseq::get_num_value(expr* e, rational& val) {
        expr_ref e2(m);
        m_th_rewriter(e, e2);
        return m_arith_value.get_value_equiv(e2, val) && val.is_int();
    }

    bool theory_nseq::lower_bound(expr* e, rational& lo) {
        if (!m_autil.is_int(e))
            return false;
        expr_ref e2(m);
        m_th_rewriter(e, e2);
        bool is_strict = true;
        return m_arith_value.get_lo_equiv(e2, lo, is_strict) && !is_strict && lo.is_int();
    }

    bool theory_nseq::upper_bound(expr* e, rational& hi) {
        if (!m_autil.is_int(e))
            return false;
        expr_ref e2(m);
        m_th_rewriter(e, e2);
        bool is_strict = true;
        return m_arith_value.get_up_equiv(e2, hi, is_strict) && !is_strict && hi.is_int();
    }

    // Thin forwarder: the actual coherence-checking control logic now
    // lives on the facet itself (see seq::stoi_facet::check_stoi_coherence,
    // ast/seq/seq_stoi_facet.h) - it consults `*m_ambient` (for
    // `current_value`/`add_axiom`) and the `m_instantiate` callback wired
    // up at construction time, rather than touching `ctx`/`m_ax` here
    // directly.
    bool theory_nseq::check_stoi_coherence() {
        return m_ambient->stoi_facet(*m_root).check_stoi_coherence(*m_ambient);
    }

}
