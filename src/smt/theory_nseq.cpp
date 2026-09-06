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
            unsigned j = 0;
            for (slot const& sl : m_slots) {
                if (sl.m_literal) {
                    final_toks.push_back(sl.m_literal);
                    continue;
                }
                expr* v = values.get(j++);
                final_toks.push_back(sl.m_is_unit ? th.m_seq.str.mk_unit(v) : v);
            }
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
        m_solver(m, m_autil, m_tree.dep_mgr())
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

        // split plugins: registration order mirrors the priority order of
        // the c3 branch's nielsen_graph::generate_extensions (see
        // theory_nseq.h's module comment for the mapping table).
        m_tree.add_split_plugin(alloc(seq::eq_approx_split, m, m_seq, m_rewriter));
        m_tree.add_split_plugin(alloc(seq::mem_parikh_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::power_num_cmp, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_split_elim, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_fine_wilf, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_peel, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::eq_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::mem_monadic_split, m, m_seq, m_rewriter, *m_ambient));
        m_tree.add_split_plugin(alloc(seq::power_gpower_intro, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::word_eq_split, m, m_seq));
        m_tree.add_split_plugin(alloc(seq::power_split, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_decompose, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::power_var_peel_mem, m, m_seq, m_autil));
        m_tree.add_split_plugin(alloc(seq::deq_split, m, m_seq));

        m_tree.set_max_search_depth(30);
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
        if (m_seq.is_re(e1)) {
            unsigned idx = mk_dep(assumption(n1, n2));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            m_ambient->req_facet(*m_root).add_req(e1, e2, true, dep);
            return;
        }
        if (!m_seq.is_seq(e1))
            return;
        unsigned idx = mk_dep(assumption(n1, n2));
        seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
        expr_ref_vector lhs = m_ambient->purify(e1);
        expr_ref_vector rhs = m_ambient->purify(e2);
        m_ambient->eq_facet(*m_root).add_equation(lhs, rhs, dep);
    }

    void theory_nseq::new_diseq_eh(theory_var v1, theory_var v2) {
        enode* n1 = get_enode(v1);
        enode* n2 = get_enode(v2);
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        if (m_seq.is_re(e1)) {
            unsigned idx = mk_dep(assumption(n1, n2, true));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            m_ambient->req_facet(*m_root).add_req(e1, e2, false, dep);
            return;
        }
        if (!m_seq.is_seq(e1))
            return;
        unsigned idx = mk_dep(assumption(n1, n2, true));
        seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
        expr_ref_vector lhs = m_ambient->purify(e1);
        expr_ref_vector rhs = m_ambient->purify(e2);
        m_ambient->deq_facet(*m_root).add_disequation(lhs, rhs, dep);
    }

    // -----------------------------------------------------------------------
    // Boolean assignment notification: str.in_re, prefix/suffix/contains
    // -----------------------------------------------------------------------

    void theory_nseq::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx.bool_var2expr(v);
        literal lit(v, !is_true);
        expr* e1 = nullptr, *e2 = nullptr;

        if (m_seq.str.is_in_re(e, e1, e2)) {
            ensure_enode(e1);
            ensure_enode(e2);
            unsigned idx = mk_dep(assumption(lit));
            seq::eq_tree::dep_tracker dep = m_tree.dep_mgr().mk_leaf(idx);
            expr* re = is_true ? e2 : m_seq.re.mk_complement(e2);
            seq::view mv = seq::view::membership(re);
            expr_ref_vector ts = m_ambient->purify(e1);
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
                expr_ref_vector lhs = m_ambient->purify(e2);
                expr_ref_vector rhs = m_ambient->purify(e1);
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
                expr_ref_vector lhs = m_ambient->purify(e2);
                expr_ref_vector rhs(m);
                rhs.push_back(f); // fresh existential, kept alive by rhs's own ref
                rhs.append(m_ambient->purify(e1));
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
                expr_ref_vector lhs = m_ambient->purify(e1);
                expr_ref_vector rhs(m);
                rhs.push_back(x); // fresh existentials, kept alive by rhs's own ref
                rhs.append(m_ambient->purify(e2));
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
            expr_ref_vector lhs = m_ambient->purify(is_true ? e1 : e2);
            expr_ref_vector rhs = m_ambient->purify(is_true ? e2 : e1);
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
        else if (m_seq.str.is_stoi(n))
            m_ax.add_stoi_axiom(n);
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
        unsigned idx = m_assumptions.size();
        m_assumptions.push_back(a);
        ctx.push_trail(push_back_vector(m_assumptions));
        return idx;
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
            assumption const& a = m_assumptions[idx];
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
        m_model_subst.reset();
        m_factory = alloc(seq_factory, get_manager(), get_family_id(), mg.get_model());
        mg.register_factory(m_factory.get());
        for (enode* n : ctx.enodes()) {
            expr* e = n->get_expr();
            if (m_seq.is_seq(e) && m.is_value(e))
                m_factory->register_value(e);
        }
        seq::eq_tree::node const* snap = m_tree.sat_snapshot();
        if (!snap)
            return;
        auto const& mf = m_ambient->mem_facet(const_cast<seq::eq_tree::node&>(*snap));
        seq_monadic mon(m_rewriter, ctx.get_trail_stack(), seq::transition_mode::brzozowski_tm);
        mon.set_gen_solution(true);
        for (auto const& sm : mf.memberships()) {
            sort* s = m_seq.re.to_seq(sm.m_view.m_state->get_sort());
            expr_ref term(m_seq.str.mk_concat(sm.m_str.size(), sm.m_str.data(), s), m);
            mon.add(term, sm.m_view.m_state, sm.m_dep);
        }
        expr_substitution model(m);
        if (mon.materialize_all(model) == l_true) {
            for (auto const& kv : model.sub())
                m_model_subst.insert(kv.m_key, kv.m_value);
        }
    }

    void theory_nseq::finalize_model(model_generator&) {
        m_factory = nullptr;
        m_model_subst.reset();
    }

    model_value_proc* theory_nseq::mk_value(enode* n, model_generator&) {
        expr* e = n->get_expr();
        if (m_seq.is_re(e))
            // Regexes are not sequence values to be synthesized token by
            // token - just return the regex term itself as its own
            // model value (no fresh value needed/possible).
            return alloc(expr_wrapper_proc, to_app(e));
        if (!m_seq.is_seq(e))
            return alloc(expr_wrapper_proc, to_app(m_factory->get_fresh_value(e->get_sort())));
        seq::eq_tree::node const* snap = m_tree.sat_snapshot();
        expr_ref_vector resolved(m);
        if (snap)
            m_ambient->eq_facet(const_cast<seq::eq_tree::node&>(*snap)).eliminate(e, resolved);
        else
            m_seq.str.get_concat_units(e, resolved);

        seq_model_value_proc* proc = alloc(seq_model_value_proc, *this, e->get_sort());

        // Append token `t` to `proc`: literal tokens (values, units over
        // a value char, or any token that has no enode yet - nothing to
        // depend on) are recorded as-is; anything else that is already
        // internalized records an actual dependency so its real,
        // already-materialized model value is spliced in later by
        // seq_model_value_proc::mk_value, instead of being thrown away
        // for an unrelated fresh value.
        std::function<void(expr*)> add_token = [&](expr* t) {
            expr* sub = nullptr;
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
                else
                    proc->add_dependency(ctx.get_enode(ch), true);
            }
            else if (m.is_value(t) || !ctx.e_internalized(t)) {
                proc->add_literal(t);
            }
            else {
                // Any other still-unresolved seq-sorted subterm that is
                // already internalized: record a dependency on its own
                // enode so its (separately computed) model value is
                // spliced in here, rather than being replaced by an
                // unrelated fresh value.
                proc->add_dependency(ctx.get_enode(t), false);
            }
        };
        for (expr* t : resolved)
            add_token(t);
        return proc;
    }

    final_check_status theory_nseq::final_check_eh(unsigned) {
        ++m_num_final_checks;
        stx::search_result res = m_tree.solve();
        switch (res) {
        case stx::search_result::sat: {
            // Assumptions accumulated along the satisfying branch (e.g.
            // word_eq_split's symbolic char-equality substitutions, see
            // seq::assumption_facet's class comment) must also hold in
            // the ambient SMT context for the tree's model to be valid:
            // check each is already an internalized literal assigned
            // true, and if not, internalize it and force it true so the
            // core re-checks with that requirement in place.
            seq::eq_tree::node const* snap = m_tree.sat_snapshot();
            if (snap) {
                auto const& af = m_ambient->assumption_facet(const_cast<seq::eq_tree::node&>(*snap));
                for (expr* a : af.assumptions()) {
                    if (!ctx.b_internalized(a))
                        ctx.internalize(a, false);
                    bool_var bv = ctx.get_bool_var(a);
                    ctx.set_var_theory(bv, get_id());
                    literal lit(bv);
                    if (ctx.get_assignment(lit) == l_true)
                        continue;
                    ctx.mark_as_relevant(lit);
                    if (ctx.get_assignment(lit) == l_false)
                        // Already refuted by the ambient context: force a
                        // fresh final check to re-derive/propagate the
                        // conflict through the ordinary channels next
                        // round, rather than asserting a unit clause that
                        // would immediately contradict it.
                        return FC_CONTINUE;
                    ctx.mk_th_axiom(get_id(), 1, &lit);
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
            // No precise dependency recorded: fall back to a giveup rather
            // than asserting an unjustified conflict.
            return FC_GIVEUP;
        }
        default:
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
        theory_nseq* result = alloc(theory_nseq, *new_ctx);
        // Cross-manager clone: `new_ctx` may use a different ast_manager
        // than `this` (e.g. portfolio/parallel solving), so the facets'
        // own `clone(trail_stack&)` (a same-manager deep-copy, used by
        // stx::search_tree::clone_state_from for e.g. hot-restart
        // snapshots) is not safe here - it copies expr* members verbatim,
        // which are only valid in *this*'s manager. Instead, translate
        // each facet's AST-typed state directly into `result`'s
        // already-constructed facets (registered by result's own
        // constructor, in the same order/types as `this`'s), via each
        // facet's `clone(src, ast_translation&)` method.
        ast_translation tr(m, result->m);
        result->m_ambient->eq_facet(*result->m_root).clone(m_ambient->eq_facet(*m_root), tr);
        result->m_ambient->deq_facet(*result->m_root).clone(m_ambient->deq_facet(*m_root), tr);
        result->m_ambient->power_facet(*result->m_root).clone(m_ambient->power_facet(*m_root), tr);
        result->m_ambient->mem_facet(*result->m_root).clone(m_ambient->mem_facet(*m_root), tr);
        result->m_ambient->ncontains_facet(*result->m_root).clone(m_ambient->ncontains_facet(*m_root), tr);
        result->m_ambient->assumption_facet(*result->m_root).clone(m_ambient->assumption_facet(*m_root), tr);
        result->m_ambient->req_facet(*result->m_root).clone(m_ambient->req_facet(*m_root), tr);
        result->m_ambient->lex_facet(*result->m_root).clone(m_ambient->lex_facet(*m_root), tr);
        // solver_facet: intentionally not translated - see
        // seq::solver_facet::clone(solver_facet const&, ast_translation&)'s
        // comment (a cloned node's own constraint set is meaningless
        // without the very same shared incremental backend it was
        // asserted against, and `result` has its own fresh sub_solver).
        return result;
    }

    void theory_nseq::display(std::ostream& out) const {
        out << "theory_nseq: " << m_num_final_checks << " final checks, " << m_num_conflicts << " conflicts\n";
        m_tree.display(out);
    }

    void theory_nseq::collect_statistics(::statistics& st) const {
        st.update("nseq final checks", m_num_final_checks);
        st.update("nseq conflicts", m_num_conflicts);
        m_tree.collect_statistics(st);
    }

    bool theory_nseq::get_num_value(expr* e, rational& val) const {
        expr_ref e2(m);
        const_cast<th_rewriter&>(m_th_rewriter)(e, e2);
        return m_arith_value.get_value_equiv(e2, val) && val.is_int();
    }

    bool theory_nseq::lower_bound(expr* e, rational& lo) const {
        if (!m_autil.is_int(e))
            return false;
        expr_ref e2(m);
        const_cast<th_rewriter&>(m_th_rewriter)(e, e2);
        bool is_strict = true;
        return m_arith_value.get_lo(e2, lo, is_strict) && !is_strict && lo.is_int();
    }

    bool theory_nseq::upper_bound(expr* e, rational& hi) const {
        if (!m_autil.is_int(e))
            return false;
        expr_ref e2(m);
        const_cast<th_rewriter&>(m_th_rewriter)(e, e2);
        bool is_strict = true;
        return m_arith_value.get_up(e2, hi, is_strict) && !is_strict && hi.is_int();
    }

}
