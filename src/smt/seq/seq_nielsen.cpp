/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen.cpp

Abstract:

    Nielsen graph: constraint/node/edge data structures, graph
    construction, length-expression and length-constraint generation,
    and the bridge to the arithmetic sub-solver.

    The algorithm itself is split across seq_nielsen_simplify.cpp
    (constraint simplification), seq_nielsen_search.cpp (iterative
    deepening DFS), seq_nielsen_modifiers.cpp / seq_nielsen_regex.cpp
    (the apply_* rules) and seq_nielsen_automaton.cpp (partial DFA,
    land-state views, synchronous product).

NSB review:

   ostrich\substring2b.smt2, ostrich\substring.smt2
   - We are missing rewrites for unit(x) = unit('a') that would eliminate x by a.

Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen_internal.h"

namespace seq {

    void deps_to_lits(dep_manager &dep_mgr, const dep_tracker deps,
        svector<enode_pair> &eqs, svector<sat::literal> &lits) {
        
        vector<dep_source, false> vs;
        dep_mgr.linearize(deps, vs);
        for (dep_source const &d : vs) {
            if (std::holds_alternative<enode_pair>(d)) {
                eqs.push_back(std::get<enode_pair>(d));
            }
            else if (std::holds_alternative<sat::literal>(d))
                lits.push_back(std::get<sat::literal>(d));
            else
                UNREACHABLE();
        }
    }

    // -----------------------------------------------
    // str_eq
    // -----------------------------------------------

    void str_eq::sort() {
        if (m_lhs && m_rhs && m_lhs->id() > m_rhs->id()) {
            std::swap(m_lhs, m_rhs);
        }
        SASSERT(!m_lhs || !m_rhs || m_lhs->id() <= m_rhs->id());
    }

    bool str_eq::is_trivial() const {
        return m_lhs == m_rhs || (m_lhs && m_rhs && m_lhs->is_empty() && m_rhs->is_empty());
    }

    bool str_eq::contains_var(euf::snode const* var) const {
        if (!var)
            return false;
        return (m_lhs && snode_contains_var(m_lhs, var))
            || (m_rhs && snode_contains_var(m_rhs, var));
    }

    // -----------------------------------------------
    // str_mem
    // -----------------------------------------------

    bool str_mem::is_primitive() const {
        // A still-unresolved symbolic-derivative residual (ite) is not a settled
        // primitive — apply_regex_if_split must resolve it first.
        return m_str && m_str->length() == 1 && m_str->is_var() && m_regex->is_ground()
            && m_regex->kind() != euf::snode_kind::s_ite;
    }

    bool str_mem::is_trivial(nielsen_node const* n) const {
        SASSERT(m_str && m_regex);
        if (m_kind == mem_kind::stab_view)
            // The plain full-seq shortcut below does NOT apply to a view: its
            // language L_{Q,{s}}(state) is about *landing* at s, not membership
            // in L(state) — a view whose run state is Σ* with s ≠ Σ* denotes ∅
            // (see is_contradiction), so treating it as trivial would silently
            // drop the constraint.
            // ε ∈ L_{Q,{s}}(state) iff current state ≡ acceptance state s (=m_root).
            return m_str->is_empty() && m_regex == m_root;
        if (m_regex->is_full_seq())
            return true;
        if (!m_str->is_empty())
            return false;
        return n->graph().sg().re_nullable(m_regex) == l_true;
    }

    bool str_mem::is_contradiction(nielsen_node const* n) const {
        if (!(m_str && m_regex))
            return false;
        if (m_kind == mem_kind::stab_view) {
            // δ_a(Σ*) = Σ* for every a: once the run state is Σ*, it stays
            // there, so no continuation can land at a different acceptance
            // state — the view denotes ∅ regardless of the remaining string.
            if (m_regex->is_full_seq() && m_regex != m_root)
                return true;
            // An unresolved symbolic residual (ite / non-ground state, produced
            // by consume_view stepping over a symbolic unit) is not a settled
            // state: apply_regex_if_split may still resolve it to m_root, so no
            // ε-verdict is possible yet.  (The plain branch below is guarded
            // the same way implicitly: re_nullable is l_undef on such states.)
            if (!m_regex->is_ground() || m_regex->kind() == euf::snode_kind::s_ite)
                return false;
            // ε ∉ view when current state ≢ acceptance s
            return m_str->is_empty() && m_regex != m_root;
        }
        if (!m_str->is_empty())
            return false;
        return n->graph().sg().re_nullable(m_regex) == l_false;
    }

    bool str_mem::contains_var(euf::snode const* var) const {
        SASSERT(var);
        return m_str && snode_contains_var(m_str, var);
    }

    // -----------------------------------------------
    // nielsen_subst
    // -----------------------------------------------

    bool nielsen_subst::is_eliminating() const {
        SASSERT(m_var && m_replacement);
        // check if var appears in replacement - deep, so that an occurrence
        // buried in a power base is not mistaken for an eliminating substitution
        return !deep_contains_var(m_replacement, m_var);
    }

    bool nielsen_subst::is_char_subst() const {
        SASSERT(m_var && m_replacement);
        SASSERT(!m_var->is_unit() || m_replacement->is_char_or_unit());
        return m_var->is_unit();
    }

    // -----------------------------------------------
    // nielsen_edge
    // -----------------------------------------------

    nielsen_edge::nielsen_edge(nielsen_node* src, nielsen_node* tgt, const char* rule, const bool is_progress):
        m_src(src), m_tgt(tgt), m_rule_name(rule),
        m_is_progress(is_progress) { }

    void nielsen_edge::add_subst(nielsen_subst const& s) {
        m_subst.push_back(s);
    }

    // -----------------------------------------------
    // nielsen_node
    // -----------------------------------------------

    nielsen_node::nielsen_node(nielsen_graph& graph, const unsigned id):
        m_id(id), m_graph(graph), m_is_progress(true) { }

    void nielsen_node::set_conflict(const backtrack_reason r, const dep_tracker confl) {
        // Keep the FIRST internal conflict.  Key the guard on m_reason, not on
        // m_conflict_internal: nullptr is a legal dep tracker (the empty
        // dependency set), so a dep-based guard would let a later, weaker
        // conflict silently overwrite a dep-free one.  An external conflict may
        // still be upgraded to an internal one (we prefer internal conflicts —
        // they are needed as justification for general conflicts).
        if (m_reason != backtrack_reason::unevaluated && m_conflict_external_literal == sat::null_literal)
            return;
        // We prefer internal conflicts (we need it as a justification for general conflicts)
        TRACE(seq, tout << "internal conflict " << (unsigned)r << "\n");
        m_reason = r;
        m_conflict_internal = confl;
        m_conflict_external_literal = sat::null_literal;
    }

    void nielsen_node::set_external_conflict(const sat::literal lit, dep_tracker confl) {
        if (m_reason != backtrack_reason::unevaluated)
            return;
        TRACE(seq, tout << "external conflict " << lit << "\n");
        m_reason = backtrack_reason::external;
        m_conflict_external_literal = ~lit;
        m_conflict_internal = confl;
    }

    void nielsen_node::clone_from(nielsen_node const& parent) {
        m_str_eq.reset();
        m_str_deq.reset();
        m_str_mem.reset();
        m_constraints.reset();
        m_char_ranges.reset();
        m_fw_applied.reset();
        m_str_eq.append(parent.m_str_eq);
        m_fw_applied.append(parent.m_fw_applied);
        m_str_deq.append(parent.m_str_deq);
        m_str_mem.append(parent.m_str_mem);
        m_constraints.append(parent.m_constraints);

        // clone character ranges
        for (auto const &[k, v] : parent.m_char_ranges)
            m_char_ranges.insert(k, std::make_pair(v.first.clone(), v.second));

        SASSERT(m_str_eq.size() == parent.m_str_eq.size());
        SASSERT(m_str_deq.size() == parent.m_str_deq.size());
        SASSERT(m_str_mem.size() == parent.m_str_mem.size());
        SASSERT(m_constraints.size() == parent.m_constraints.size());
    }

    void nielsen_node::add_str_eq(const str_eq& eq) {
        SASSERT(eq.m_lhs != nullptr);
        SASSERT(eq.m_rhs != nullptr);
        if (eq.is_trivial())
            return;
        // check if root node contains this equation already
        if (std::ranges::any_of(str_eqs(),
            [&](const str_eq &e) { return e.m_lhs == eq.m_lhs && e.m_rhs == eq.m_rhs; }))
            // already present, no need to add again
            return;
        m_simplify_stamp = 0;
        m_str_eq.push_back(eq);
    }

    void nielsen_node::add_str_deq(const str_deq& deq) {
        SASSERT(deq.m_lhs != nullptr);
        SASSERT(deq.m_rhs != nullptr);
        // check if root node contains this equation already
        if (std::ranges::any_of(str_deqs(),
        [&](const str_deq &e) { return e.m_lhs == deq.m_lhs && e.m_rhs == deq.m_rhs; }))
            // already present, no need to add again
            return;
        m_simplify_stamp = 0;
        m_str_deq.push_back(deq);
    }

    void nielsen_node::add_str_mem(str_mem const& mem) {
        SASSERT(mem.m_str != nullptr);
        SASSERT(mem.m_regex != nullptr);
        if (mem.is_trivial(this))
            return;
        // Skip only a FULLY identical membership.  The dedup must compare the
        // whole membership (kind/root/ν), not just (m_str,m_regex): a land-state
        // view (paper §5.3) shares (m_str,m_regex) with a plain membership on the
        // same variable+state, and two land-views on the same state differ only
        // in their acceptance root / ν.  Deduping on (m_str,m_regex) alone would
        // silently drop such a view and lose the constraint (→ unsound leaf).
        if (std::ranges::any_of(str_mems(), [&](const str_mem &e) { return e == mem; }))
            return; // already present
        m_simplify_stamp = 0;
        m_str_mem.push_back(mem);
    }

    bool nielsen_node::lower_bound(expr *e, rational &lo, dep_tracker &dep) {
        literal_vector lits;
        enode_pair_vector eqs;
        if (m_graph.a.is_numeral(e, lo))
            return true;
        if (!m_graph.m_context_solver.lower_bound(e, lo, lits, eqs))
            return false;
        for (auto lit : lits) {
            dep = m_graph.dep_mgr().mk_join(dep, m_graph.dep_mgr().mk_leaf(lit));
        }
        for (auto eq : eqs) {
            dep = m_graph.dep_mgr().mk_join(dep, m_graph.dep_mgr().mk_leaf(eq));
        }

        const expr_ref lo_expr(m_graph.a.mk_int(lo), m_graph.m);
        m_graph.add_le_dependency(dep, this, lo_expr, e);
        return true;
    }

    bool nielsen_node::upper_bound(expr *e, rational &up, dep_tracker &dep) {
        literal_vector lits;
        enode_pair_vector eqs;
        if (m_graph.a.is_numeral(e, up))
            return true;
        if (!m_graph.m_context_solver.upper_bound(e, up, lits, eqs))
            return false;
        for (auto lit : lits) {
            dep = m_graph.dep_mgr().mk_join(dep, m_graph.dep_mgr().mk_leaf(lit));
        }
        for (auto eq : eqs) {
            dep = m_graph.dep_mgr().mk_join(dep, m_graph.dep_mgr().mk_leaf(eq));
        }
        const expr_ref up_expr(m_graph.a.mk_int(up), m_graph.m);
        m_graph.add_le_dependency(dep, this, e, up_expr);
        return true;
    }

    void nielsen_node::add_constraint(constraint const &c) {
        auto& m = graph().get_manager();
        if (m.is_true(c.fml))
            return;
        // TODO: Is it possible that we miss a conflict if we decompose?
        if (m.is_and(c.fml)) {
            // We have to add all - even if some of it conflict
            // [otw. we would leave the node partially initialized]
            for (const auto f : *to_app(c.fml)) {
                add_constraint(constraint(f, c.dep, m));
            }
            return;
        }
        // Exprs are hash-consed, so pointer equality identifies duplicates.
        // The bound queries in simplify_and_init (upper_bound/lower_bound via
        // add_le_dependency) re-derive the same formula on every fixpoint
        // sweep and on every re-simplification epoch; without this check the
        // duplicates accumulate and each copy is re-asserted to the subsolver.
        // Keeping the FIRST dep is sound: any recorded dep set entails its
        // constraint, independently of the current outer assignment.
        if (std::ranges::any_of(m_constraints,
            [&](constraint const& e) { return e.fml.get() == c.fml.get(); }))
            return;
        m_simplify_stamp = 0;
        m_constraints.push_back(c);
    }

    void nielsen_node::apply_subst(euf::sgraph& sg, nielsen_subst const& s) {
        SASSERT(!s.m_var->is_char_or_unit() || s.m_replacement->is_char_or_unit());
        SASSERT(s.m_var);
        SASSERT(s.m_replacement != nullptr);
        m_simplify_stamp = 0;
        for (auto &eq : m_str_eq) {
            const auto new_lhs = sg.subst(eq.m_lhs, s.m_var, s.m_replacement);
            const auto new_rhs = sg.subst(eq.m_rhs, s.m_var, s.m_replacement);
            if (new_lhs != eq.m_lhs || new_rhs != eq.m_rhs) {
                 eq.m_lhs = new_lhs;
                 eq.m_rhs = new_rhs;
                 eq.m_dep = m_graph.dep_mgr().mk_join(eq.m_dep, s.m_dep);
                 eq.sort();
            }
        }

        for (auto &deq : m_str_deq) {
            const auto new_lhs = sg.subst(deq.m_lhs, s.m_var, s.m_replacement);
            const auto new_rhs = sg.subst(deq.m_rhs, s.m_var, s.m_replacement);
            if (new_lhs != deq.m_lhs || new_rhs != deq.m_rhs) {
                 deq.m_lhs = new_lhs;
                 deq.m_rhs = new_rhs;
                 deq.m_dep = m_graph.dep_mgr().mk_join(deq.m_dep, s.m_dep);
                 deq.sort();
            }
        }

        for (auto &mem : m_str_mem) {
            const auto new_str = sg.subst(mem.m_str, s.m_var, s.m_replacement);
            const auto new_regex = sg.subst(mem.m_regex, s.m_var, s.m_replacement);
            if (new_str != mem.m_str || new_regex != mem.m_regex) {
                mem.m_str = new_str;
                mem.m_regex = new_regex;
                mem.m_dep = m_graph.dep_mgr().mk_join(mem.m_dep, s.m_dep);
            }
        }

        const unsigned var_id = s.m_var->id();

        ast_manager& m = graph().get_manager();

        if (s.is_char_subst()) {
            expr* var_c_expr = s.m_var->arg0()->get_expr();
            expr* repl_c_expr = s.m_replacement->arg0()->get_expr();
            add_constraint(
                constraint(m.mk_eq(var_c_expr, repl_c_expr), s.m_dep, m));

            if (m_char_ranges.contains(var_id)) {
                const auto range = m_char_ranges.find(var_id); // copy exactly
                m_char_ranges.remove(var_id);
                add_char_range(s.m_replacement, range.first, m_graph.dep_mgr().mk_join(range.second, s.m_dep));
            }
        }
    }

    unsigned nielsen_node::canonize_and_compute_node_hash() {
        unsigned hash = 457260179;
        // Restore the lhs/rhs orientation invariant first: the simplify passes
        // rewrite constraint sides in place without re-sorting, and both the
        // hash and the elementwise sibling comparison are orientation-sensitive
        // — a stale orientation only costs missed sibling/unsat-cache hits, but
        // this is the single choke point before hashing, so fix it here.
        for (auto& e : str_eqs()) {
            e.sort();
        }
        for (auto& e : str_deqs()) {
            e.sort();
        }
        std::sort(str_eqs().begin(), str_eqs().end());
        for (auto const& e : str_eqs()) {
            hash += 433867097 * e.hash();
        }
        std::sort(str_deqs().begin(), str_deqs().end());
        for (auto const& e : str_deqs()) {
            hash += 982048589 * e.hash();
        }
        std::sort(str_mems().begin(), str_mems().end());
        for (auto const& e : str_mems()) {
            hash += 736051237 * e.hash();
        }

        for (auto const& [uid, cr] : char_ranges()) {
            // not sorted; computation needs to be commutative
            for (auto const& rg : cr.first.ranges()) {
                hash += 473672767 * (750753749 * rg.m_lo + rg.m_hi) + uid;
            }
        }
        return hash;
    }

    bool nielsen_node::is_node_sibling(nielsen_node const* n) {
        if (n->str_eqs().size() != str_eqs().size())
            return false;
        if (n->str_deqs().size() != str_deqs().size())
            return false;
        if (n->str_mems().size() != str_mems().size())
            return false;
        if (n->char_ranges().size() != char_ranges().size())
            return false;
        for (unsigned i = 0; i < str_eqs().size(); i++) {
            if (str_eqs()[i] != n->str_eqs()[i])
                return false;
        }
        for (unsigned i = 0; i < str_deqs().size(); i++) {
            if (str_deqs()[i] != n->str_deqs()[i])
                return false;
        }
        for (unsigned i = 0; i < str_mems().size(); i++) {
            if (str_mems()[i] != n->str_mems()[i])
                return false;
        }
        // char_ranges is a u_map keyed by the symbolic-char snode id (NOT a vector),
        // so it must be compared by key lookup, not by position.  Sizes are equal
        // (checked above), so a one-directional key+value match is a full match.
        // Compare only the char_set (the constraint); deps differ between siblings,
        // exactly as canonize_and_compute_node_hash hashes ranges+uid and ignores dep.
        for (auto const& [uid, cr] : char_ranges()) {
            if (!n->char_ranges().contains(uid))
                return false;
            if (cr.first != n->char_ranges().find(uid).first)
                return false;
        }
        return true;
    }

    void nielsen_node::add_char_range(euf::snode const* sym_char, char_set const& range, dep_tracker dep) {
        // An empty class admits no character at all.  Handle it here rather than
        // falling through: the fresh-key branch below would insert it silently
        // and the generated mk_or over zero ranges is just `false`, i.e. an
        // arithmetic conflict with the wrong reason and no general conflict.
        if (range.is_empty()) {
            set_conflict(backtrack_reason::character_range, dep);
            set_general_conflict();
            return;
        }
        if (sym_char->is_char()) {
            // for a concrete character just check if it matches
            const expr * val = sym_char->get_expr();
            unsigned ch = 0;
            expr* ch_expr = nullptr;
            VERIFY(graph().seq().str.is_unit(val, ch_expr));
            VERIFY(graph().seq().is_const_char(ch_expr, ch));
            if (range.contains(ch))
                return; // matches, no conflict
            set_conflict(backtrack_reason::character_range, dep);
            set_general_conflict();
            return;
        }
        SASSERT(sym_char && sym_char->is_unit());
        m_simplify_stamp = 0;
        const unsigned id = sym_char->id();
        if (m_char_ranges.contains(id)) {
            auto& existing = m_char_ranges.find(id);
            char_set inter = existing.first.intersect_with(range);
            existing = std::make_pair(inter, graph().dep_mgr().mk_join(existing.second, dep));
            if (inter.is_empty()) {
                set_conflict(backtrack_reason::character_range, existing.second);
                set_general_conflict();
            }
        }
        else
            m_char_ranges.insert(id, std::make_pair(range.clone(), dep));

        auto& ranges = range.ranges();
        auto& m = graph().get_manager();
        const auto & seq = graph().seq();
        expr* var = sym_char->get_expr();
        SASSERT(seq.str.is_unit(var));
        var = to_app(var)->get_arg(0);
        ptr_vector<expr> cases;
        cases.reserve(ranges.size());

        for (unsigned i = 0; i < ranges.size(); ++i) {
            cases[i] = m.mk_and(
                seq.mk_le(seq.mk_char(ranges[i].m_lo), var),
                seq.mk_le(var, seq.mk_char(ranges[i].m_hi - 1)));
        }
        add_constraint(constraint(m.mk_or(cases), dep, m));
    }
    // -----------------------------------------------
    // nielsen_graph
    // -----------------------------------------------

    nielsen_graph::nielsen_graph(euf::sgraph &sg, sub_solver_i &solver, context_solver_i &ctx_solver) :
        m(sg.get_manager()), a(sg.get_manager()), m_seq(sg.get_seq_util()), m_sg(sg), m_rw(m), m_a_rw(m),
        m_sk(m, m_rw), m_length_solver(solver), m_context_solver(ctx_solver), m_parikh(alloc(seq_parikh, sg)),
        m_seq_regex(alloc(seq::seq_regex, sg)), m_split_rw(sg.get_manager()), m_deriv_rw(sg.get_manager()),
        m_monadic_rw(sg.get_manager()), m_monadic_leaf_rw(sg.get_manager()),
        m_partial_dfa_pin(sg.get_manager()) {
    }

    nielsen_graph::~nielsen_graph() {
        dealloc(m_parikh);
        dealloc(m_seq_regex);
        reset();
    }

    nielsen_node* nielsen_graph::mk_node() {
        const unsigned id = m_nodes.size();
        nielsen_node* n = alloc(nielsen_node, *this, id);
        m_nodes.push_back(n);
        SASSERT(n->id() == m_nodes.size() - 1);
        return n;
    }

    nielsen_node* nielsen_graph::mk_child(nielsen_node* parent) {
        nielsen_node *child = mk_node();
        child->clone_from(*parent);
        child->m_parent_ic_count = parent->constraints().size();
        return child;
    }

    nielsen_edge *nielsen_graph::mk_edge(nielsen_node* src, nielsen_node* tgt, const char* rule,
                                         const bool is_progress) {
        SASSERT(src != nullptr);
        SASSERT(tgt != nullptr);
        nielsen_edge* e = alloc(nielsen_edge, src, tgt, rule, is_progress);
        m_edges.push_back(e);
        src->add_outgoing(e);
        return e;
    }

    void nielsen_graph::add_str_eq(euf::snode const* lhs, euf::snode const* rhs, smt::enode *l, smt::enode *r) {
        const dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(l, r));
        str_eq eq(m, lhs, rhs, dep);
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_deq(euf::snode const* lhs, euf::snode const* rhs, sat::literal l) {
        const dep_tracker dep = m_dep_mgr.mk_leaf(l);
        str_deq deq(m, lhs, rhs, dep);
        m_root->add_str_deq(deq);
    }

    void nielsen_graph::add_str_mem(euf::snode const* str, euf::snode const* regex, sat::literal l) {
        const dep_tracker dep = m_dep_mgr.mk_leaf(l);
        m_root->add_str_mem(str_mem(m, str, regex, dep));
    }

    // test-friendly overloads (no external dependency tracking); create the
    // root lazily — production callers use the enode/literal overloads after
    // an explicit create_root()
    void nielsen_graph::add_str_eq(euf::snode const* lhs, euf::snode const* rhs) {
        if (!m_root)
            create_root();
        const dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(nullptr, nullptr));
        const str_eq eq(m, lhs, rhs, dep);
        m_root->add_str_eq(eq);
    }

    void nielsen_graph::add_str_deq(euf::snode const* lhs, euf::snode const* rhs) {
        if (!m_root)
            create_root();
        const dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(nullptr, nullptr));
        const str_deq deq(m, lhs, rhs, dep);
        m_root->add_str_deq(deq);
    }

    void nielsen_graph::add_str_mem(euf::snode const* str, euf::snode const* regex) {
        if (!m_root)
            create_root();
        // dummy leaf (like the eq/deq overloads): production invariants
        // (e.g. check_regex_widening) assume memberships carry a dep
        const dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(nullptr, nullptr));
        const str_mem mem(m, str, regex, dep);
        m_root->add_str_mem(mem);
    }

    void nielsen_graph::reset() {
        for (nielsen_node *n : m_nodes) {
            dealloc(n);
        }
        for (nielsen_edge *e : m_edges) {
            dealloc(e);
        }
        // suspended factorization iterators (release their pinned expressions
        // while m_split_rw / the ast_manager are still alive)
        for (rf_state* st : m_rf_states) {
            dealloc(st);
        }
        m_rf_states.reset();
        // suspended monadic branch enumerators: they hold iterators into m_monadic, so
        // they have to go before it does
        for (mon_state* st : m_mon_states) {
            dealloc(st);
        }
        m_mon_states.reset();
        // continuation-regex service: release its pinned derivative graph so a
        // fresh problem starts with a clean cache (its pins would grow forever).
        dealloc(m_monadic);
        m_monadic = nullptr;
        dealloc(m_monadic_leaf_engine);
        m_monadic_leaf_engine = nullptr;
        m_monadic_leaf_root_asked = false;
        m_nodes.reset();
        m_edges.reset();
        m_root = nullptr;
        m_sat_node = nullptr;
        m_sat_path.reset();
        m_depth_bound = 0;
        // m_fresh_cnt is deliberately NOT reset: it must stay monotone across
        // resets.  Names are hash-consed, so restarting the counter makes the
        // next problem's v!0 the very same expression as the previous one's --
        // and the previous one is still live in the main context, where
        // add_nielsen_assumptions internalized the sat leaf's constraints
        // (len(v!0) = ..., bounds) as literals that outlive our reset.  The new
        // variable would then inherit those stale bounds through
        // nielsen_node::lower_bound/upper_bound and literal_if_false.
        m_root_constraints_asserted = false;
        m_root_ic_asserted = 0;    // paired with the m_length_solver.reset() below
        m_partial_dfa_edges.reset();
        m_partial_dfa_out.clear();
        m_partial_dfa_edge_index.clear();
        m_partial_dfa_pin.reset();
        m_projection_extract_idx = 0;
        m_projection_snapshots.clear();
        m_projection_head_cache.clear();
        m_explored_automaton.reset();
        m_fully_explored.reset();
        m_unsat_node_cache.clear();
        m_siblings.clear();
        m_num_cache_hits = 0;
        m_eager_active = false;
        m_eager_leaf = nullptr;
        m_eager_substs.reset();
        m_dep_mgr.reset();
        m_length_solver.reset();
        SASSERT(m_nodes.empty());
        SASSERT(m_edges.empty());
        SASSERT(m_root == nullptr);
        SASSERT(m_sat_node == nullptr);
    }

    void nielsen_graph::add_le_dependency(const dep_tracker dep, nielsen_node *n, expr *lhs, expr *rhs) const {
        SASSERT(lhs);
        SASSERT(rhs);
        const expr_ref le(a.mk_le(lhs, rhs), m);
        // just assume it to be correct
        // Just add the constraint - we do not have to recompute it
        // [also it is on the set of side-conditions if we assert a satisfied node]
        n->add_constraint(constraint(le, dep, m));
    }

    euf::snode const* nielsen_graph::get_slice(euf::snode const* v, expr* left, expr* right) {
        SASSERT(v && v->get_expr() && left && right);
        SASSERT(v->is_var());

        expr_ref new_arg(v->get_expr(), m);
        expr_ref new_l(left, m), new_r(right, m);
        expr* arg, *l, *r;

        if (m_sk.is_slice(new_arg, arg, l, r)) {
            new_l = a.mk_add(left, l);
            new_r = a.mk_add(right, r);
            new_arg = arg;
        }
        // Normalize on BOTH paths.  The slice skolem is keyed on its index
        // expressions, so two callers passing arithmetically equal but
        // syntactically different indices would get different skolems, hence
        // different snodes, hence nodes that should be structurally identical
        // are not - and the sibling / unsat-cache lookups miss them.
        m_rw(new_l);
        m_rw(new_r);
        expr_ref slice = m_sk.mk_slice(new_arg, new_l, new_r);
        return m_sg.mk(slice);
    }


    euf::snode const* nielsen_graph::get_tail(euf::snode const* v, expr* cnt, const bool fwd) {
        if (fwd)
            return get_slice(v, cnt, a.mk_int(0));
        return get_slice(v, a.mk_int(0), cnt);
    }

    euf::snode const* nielsen_graph::get_tail(euf::snode const* v, const unsigned cnt, const bool fwd) {
        return get_tail(v, a.mk_int(cnt), fwd);
    }

    euf::snode const* nielsen_graph::mk_rewrite(expr* e) const {
        expr_ref er(e, m);
        m_rw(er);
        return m_sg.mk(er);
    }

    // -----------------------------------------------------------------------
    // nielsen_graph: mk_fresh_var
    // -----------------------------------------------------------------------

    euf::snode const* nielsen_graph::mk_fresh_var(sort* s) {
        ++m_stats.m_num_fresh_vars;
        const std::string name = "v!" + std::to_string(m_fresh_cnt++);
        return m_sg.mk_var(symbol(name.c_str()), s);
    }


    // -----------------------------------------------------------------------
    // nielsen_graph: length constraint generation
    // -----------------------------------------------------------------------

    expr_ref nielsen_graph::compute_length_expr(euf::snode const* n) {
        if (n->is_empty())
            return expr_ref(a.mk_int(0), m);

        if (n->is_char_or_unit())
            return expr_ref(a.mk_int(1), m);

        if (n->is_power()) {
            const expr_ref base = compute_length_expr(n->arg0());
            expr_ref res(m);
            m_a_rw.mk_mul(base.get(), n->arg(1)->get_expr(), res);
            return res;
        }

        if (n->is_concat()) {
            const expr_ref left = compute_length_expr(n->arg0());
            const expr_ref right = compute_length_expr(n->arg(1));
            expr_ref res(m);
            m_a_rw.mk_add(left, right, res);
            return res;
        }

        return expr_ref(m_seq.str.mk_length(n->get_expr()), m);
    }

    void nielsen_graph::generate_length_constraints(vector<length_constraint>& constraints) {
        if (!m_root)
            return;
        uint_set seen_vars;

        TRACE(seq, display(tout, m_root));

        const seq_util & seq = m_sg.get_seq_util();
        for (str_eq const& eq : m_root->str_eqs()) {
            if (eq.is_trivial())
                continue;

            expr_ref len_lhs = compute_length_expr(eq.m_lhs);
            expr_ref len_rhs = compute_length_expr(eq.m_rhs);
            TRACE(seq,
                tout << "Length constraint from LHS " << snode_label_html(eq.m_lhs, m, true) << " to " << len_lhs << ":\n";
                tout << "Length constraint from RHS " << snode_label_html(eq.m_rhs, m, true) << " to " << len_rhs << "\n");
            expr_ref len_eq(m.mk_eq(len_lhs, len_rhs), m);
            constraints.push_back(length_constraint(len_eq, eq.m_dep, length_kind::eq, m));

            // collect variables for non-negativity constraints
            euf::snode_vector tokens;
            eq.m_lhs->collect_tokens(tokens);
            eq.m_rhs->collect_tokens(tokens);
            for (euf::snode const* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var(seq.str.mk_length(tok->get_expr()), m);
                    expr_ref ge_zero(a.mk_ge(len_var, a.mk_int(0)), m);
                    TRACE(seq, tout << "non-negative length " << ge_zero << "\n");
                    // no dependency: len(x) >= 0 is an unconditional axiom, it
                    // is not entailed by the equation we happened to find x in.
                    // Attributing eq.m_dep would drag that input equality into
                    // every unsat core the bound participates in.
                    constraints.push_back(length_constraint(ge_zero, nullptr, length_kind::nonneg, m));
                }
            }
        }

        // Parikh interval reasoning for regex memberships
        for (str_mem const& mem : m_root->str_mems()) {
            SASSERT(seq.is_re(mem.m_regex->get_expr()));

            // Views never denote L(m_regex) — see generate_node_length_constraints.
            // (The root only ever carries plain memberships; kept for safety.)
            if (!mem.is_plain())
                continue;

            unsigned min_len = 0, max_len = UINT_MAX;
            compute_regex_length_interval(mem.m_regex, min_len, max_len);

            expr_ref len_str = compute_length_expr(mem.m_str);

            // generate len(str) >= min_len when min_len > 0
            if (min_len > 0) {
                expr_ref bound(a.mk_ge(len_str, a.mk_int(min_len)), m);
                TRACE(seq, tout << "Parikh " << mk_pp(mem.m_regex->get_expr(), m) << " bound: " << bound << "\n");
                constraints.push_back(length_constraint(bound, mem.m_dep, length_kind::bound, m));
            }

            // generate len(str) <= max_len when bounded
            if (max_len < UINT_MAX) {
                expr_ref bound(a.mk_le(len_str, a.mk_int(max_len)), m);
                TRACE(seq, tout << "Parikh " << mk_pp(mem.m_regex->get_expr(), m) << " bound: " << bound << "\n");
                constraints.push_back(length_constraint(bound, mem.m_dep, length_kind::bound, m));
            }

            // Exact semi-linear length set (visit-count Parikh) for classical
            // regexes; captures unions/strides precisely, unlike the coarse
            // interval above (which we keep alongside - we might want to delete it eventually)
            if (mem.is_plain() && mem.m_regex->is_classical()) {
                vector<constraint> exact;
                if (m_parikh->encode_length_set(mem.m_str->get_expr(), mem.m_regex->get_expr(), len_str, mem.m_dep, exact)) {
                    for (auto const& c : exact) {
                        TRACE(seq, tout << "semilinear " << mk_pp(mem.m_regex->get_expr(), m) << ": " << c.fml << "\n");
                        constraints.push_back(length_constraint(c.fml, c.dep, length_kind::bound, m));
                    }
                }
            }
        }
    }

    void nielsen_graph::compute_regex_length_interval(euf::snode const* regex, unsigned& min_len, unsigned& max_len) const {
        const seq_util & seq = m_sg.get_seq_util();
        expr* e = regex->get_expr();
        SASSERT(e && seq.is_re(e));
        min_len = seq.re.min_length(e);
        max_len = seq.re.max_length(e);
        // For an empty language min_length is UINT_MAX (vacuously true).  Test
        // that explicitly as well as min > max: a saturating add can leave BOTH
        // fields at UINT_MAX, which min > max does not catch and which would
        // emit len(s) >= 4294967295 into the arithmetic solver.
        if (min_len == UINT_MAX || min_len > max_len) {
            min_len = 0;
            max_len = 0;
        }
    }

    // -----------------------------------------------------------------------
    // int_constraint display
    // -----------------------------------------------------------------------

    std::ostream& constraint::display(std::ostream& out) const {
        return out << fml;
    }

    // -----------------------------------------------------------------------
    // Integer feasibility subsolver implementation
    // Uses the injected simple_solver (default: lp_simple_solver).
    // -----------------------------------------------------------------------

    // -----------------------------------------------------------------------
    // Modification counter: substitution length tracking
    // -----------------------------------------------------------------------

    expr_ref nielsen_graph::get_or_create_char_var(euf::snode const* var) {
        SASSERT(var && var->is_var());
        // the symbolic char is the first character of the (current) variable: x[0].
        // (The former index len(x) - compute_length_expr(x) was a mod-count
        // vestige and always denoted 0.)
        const auto e = seq().str.mk_nth_u(var->get_expr(), a.mk_int(0));
        return expr_ref(m_seq.str.mk_unit(expr_ref(e, m)), m);
    }

    expr_ref nielsen_graph::get_or_create_gpower_n_var(euf::snode const* var) {
        SASSERT(var && var->is_var());
        return m_sk.mk("gpn!", var->get_expr(), a.mk_int());
    }

    expr_ref nielsen_graph::get_or_create_gpower_m_var(euf::snode const* var) {
        SASSERT(var && var->is_var());
        return m_sk.mk("gpm!", var->get_expr(), a.mk_int());
    }

    void nielsen_graph::add_subst_length_constraints(nielsen_edge* e) {
        // |x| = |replacement| for every substitution of a sequence variable.
        // Substitutions are eliminating by construction, so the equation never
        // degenerates to |x| = ... + |x|.  The check must be DEEP: a variable
        // hidden inside a power base is invisible to the token-level check in
        // nielsen_subst's ctor, and would make this equation wrong.
        for (auto const& s : e->subst()) {
            if (!s.m_var->is_var() || !m_seq.is_seq(s.m_var->get_expr()))
                continue;
            SASSERT(s.is_eliminating());
            e->add_side_constraint(mk_constraint(
                a.mk_eq(compute_length_expr(s.m_var), compute_length_expr(s.m_replacement)),
                s.m_dep));
        }
    }

    void nielsen_graph::assert_to_subsolver(const constraint& c) const {
        m_length_solver.assert_expr(c.fml, c.dep);
    }

    void nielsen_graph::assert_to_subsolver(expr* e) const {
        m_length_solver.assert_expr(e);
    }

    void nielsen_graph::assert_node_side_constraints(nielsen_node* node, unsigned from_idx) {
        // Assert only the constraints that are new to this node (beyond those
        // inherited from its parent via clone_from).  The parent's constraints are
        // already present in the enclosing solver scope; asserting them again would
        // be redundant (though harmless).  This is called by search_dfs right after
        // simplify_and_init, which is where new constraints are produced.
        // Within one visit, `from_idx` skips the prefix already asserted by an
        // earlier call — each re-assert would otherwise burn a kernel clause and
        // an assumption/dep slot per constraint, on every visit.
        if (from_idx == UINT_MAX)
            from_idx = node->m_parent_ic_count;
        // The ROOT's constraints are asserted at the sub-solver's BASE level,
        // which is never popped between deepening iterations or across hot
        // restarts (until the solver itself is reset).  Skip the prefix that is
        // already in the solver: each redundant re-assertion would permanently
        // burn one assumption literal + kernel clause per constraint
        // (sub_solver::assert_expr) and grow every subsequent check().
        const bool is_root = node == m_root;
        if (is_root)
            from_idx = std::max(from_idx, m_root_ic_asserted);
        unsigned i = from_idx;
        for (; i < node->constraints().size(); ++i) {
            auto& c = node->constraints()[i];
            auto lit = m_context_solver.literal_if_false(c.fml);
            // std::cout << "Internalizing literal " << mk_pp(c.fml, m) << " [" << (lit == sat::null_literal) << "]" <<
            // std::endl;
            if (lit != sat::null_literal) {
                node->set_external_conflict(lit, c.dep);
                break;   // constraints [from_idx, i) were asserted, i was not
            }
            assert_to_subsolver(c);
        }
        if (is_root && i > m_root_ic_asserted)
            m_root_ic_asserted = i;
    }

    void nielsen_graph::generate_node_length_constraints(nielsen_node* node) {
        if (node->m_node_len_constraints_generated)
            return;
        node->m_node_len_constraints_generated = true;

        // Skip the root node — its length constraints are already asserted
        // at the base solver level by assert_root_constraints_to_solver().
        if (node == m_root)
            return;

        // TODO: Do we really need this?
        uint_set seen_vars;

        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;

            expr_ref len_lhs = compute_length_expr(eq.m_lhs);
            expr_ref len_rhs = compute_length_expr(eq.m_rhs);
            //node->add_constraint(mk_constraint(m.mk_eq(len_lhs, len_rhs), eq.m_dep));
            node->add_constraint(mk_constraint(a.mk_eq(len_lhs, len_rhs), eq.m_dep));

            // non-negativity for each variable (mod-count-aware)
            euf::snode_vector tokens;
            eq.m_lhs->collect_tokens(tokens);
            eq.m_rhs->collect_tokens(tokens);
            for (euf::snode const* tok : tokens) {
                if (tok->is_var() && !seen_vars.contains(tok->id())) {
                    seen_vars.insert(tok->id());
                    expr_ref len_var = compute_length_expr(tok);
                    // unconditional axiom - no dependency (see generate_length_constraints)
                    node->add_constraint(mk_constraint(a.mk_ge(len_var, a.mk_int(0)), nullptr));
                }
            }
        }

        // Parikh interval bounds for regex memberships at this node
        for (str_mem const& mem : node->str_mems()) {
            SASSERT(m_seq.is_re(mem.m_regex->get_expr()));

            // A land-state view  s ∈_{Q_ν,{root}} state  does NOT denote the
            // plain language of `state`: it collects the words that *walk*
            // from `state` to `root` inside Q_ν, which is neither a sub- nor a
            // superset of L(state).  Its plain min/max length interval is
            // therefore unsound in BOTH directions — e.g. the stabilizer view
            // (state == root) always admits ε even when L(state) has min
            // length > 0, which would kill exactly the landing branch that
            // absorbs a cycle lap (spurious UNSAT).  The correct length
            // abstraction for views is emitted on the pinning edge by
            // add_view_length_constraints (compute_view_length_info).
            if (!mem.is_plain())
                continue;

            unsigned min_len = 0, max_len = UINT_MAX;
            compute_regex_length_interval(mem.m_regex, min_len, max_len);

            expr_ref len_str = compute_length_expr(mem.m_str);

            if (min_len > 0)
                node->add_constraint(mk_constraint(a.mk_ge(len_str, a.mk_int(min_len)), mem.m_dep));
            if (max_len < UINT_MAX)
                node->add_constraint(mk_constraint(a.mk_le(len_str, a.mk_int(max_len)), mem.m_dep));
        }
    }

    bool nielsen_graph::check_int_feasibility() const {
        // In incremental mode the solver already holds all path constraints
        // (root length constraints at the base level, edge side_constraints and node
        // constraints pushed/popped as the DFS descends and backtracks).
        // A plain check() is therefore sufficient.
        return m_length_solver.check() != l_false;
    }

    dep_tracker nielsen_graph::get_subsolver_dependency(nielsen_node* /*n*/) const {
        // check_int_feasibility() already called m_solver.check() which computed
        // the UNSAT core in terms of tracked assumption literals and their deps.
        //
        // Re-anchor the core in the graph's own dep arena.  The tree returned by
        // core() has its join nodes in the sub-solver's PRIVATE region, which
        // theory_nseq frees on a hot restart (m_length_solver.reset()) while the
        // nodes that store the tracker — arithmetic general conflicts and
        // check_lp_le-derived constraints — are deliberately kept.  Rebuilding the
        // tree from its leaves here ties the tracker's lifetime to m_dep_mgr,
        // which is only reset together with the nodes (nielsen_graph::reset).
        vector<dep_source, false> vs;
        m_dep_mgr.linearize(m_length_solver.core(), vs);
        dep_tracker d = nullptr;
        for (dep_source const& v : vs)
            d = m_dep_mgr.mk_join(d, m_dep_mgr.mk_leaf(v));
        return d;
    }

    bool nielsen_graph::check_lp_le(expr* lhs, expr* rhs, nielsen_node* n, dep_tracker& dep) {
        dep = nullptr;

        rational lhs_lo, rhs_up;
        literal_vector lits;
        enode_pair_vector eqs;
        if (m_context_solver.lower_bound(lhs, lhs_lo, lits, eqs) &&
            m_context_solver.upper_bound(rhs, rhs_up, lits, eqs) && lhs_lo > rhs_up)
            return false;

        // lhs <= lhs_up <= rhs_lo <= rhs
        // => lhs <= rhs is entailed

        lits.reset();
        eqs.reset();
        rational rhs_lo, lhs_up;
        if (m_context_solver.upper_bound(lhs, lhs_up, lits, eqs) &&
            m_context_solver.lower_bound(rhs, rhs_lo, lits, eqs) &&
            lhs_up <= rhs_lo) {
            for (auto lit : lits) {
                dep = m_dep_mgr.mk_join(dep, m_dep_mgr.mk_leaf(lit));
            }
            for (enode_pair eq : eqs) {
                dep = m_dep_mgr.mk_join(dep, m_dep_mgr.mk_leaf(eq));
            }
            return true;
        }

        // fall through - ask the solver [expensive]

        // TODO: Maybe cache the result?

        // The solver already holds all path constraints incrementally.
        // Temporarily add NOT(lhs <= rhs), i.e. lhs >= rhs + 1.
        // If that is unsat, then lhs <= rhs is entailed.
        const expr_ref one(a.mk_int(1), m);
        const expr_ref rhs_plus_one(a.mk_add(rhs, one), m);

        m_length_solver.push();
        assert_to_subsolver(a.mk_ge(lhs, rhs_plus_one));
        const lbool result = m_length_solver.check();
        if (result == l_false)
            // re-anchored copy of the core (see get_subsolver_dependency): the
            // derived constraint is stored on the node and must outlive the
            // sub-solver's core region, which is freed on hot restart.
            dep = get_subsolver_dependency(n);
        m_length_solver.pop(1);
        if (result == l_false) {
            n->add_constraint(constraint(a.mk_le(lhs, rhs), dep, m));
            return true;
        }
        return false;
    }

    constraint nielsen_graph::mk_constraint(expr *fml, dep_tracker const &dep) const {
        // we need to rewrite e.g., division or <; otw. the integer solver will cry
        expr_ref c(fml, m);
        c = normalize_arith(m_rw, c);
        return constraint(c, dep, m);
    }

    expr* nielsen_graph::get_power_exponent(euf::snode const* power) {
        SASSERT(power);
        if (!power->is_power())
            return nullptr;
        SASSERT(power->num_args() == 2);
        euf::snode const* exp_snode = power->arg(1);
        return exp_snode ? exp_snode->get_expr() : nullptr;
    }

    // -----------------------------------------------------------------------
    // Statistics collection
    // -----------------------------------------------------------------------

    void nielsen_graph::collect_statistics(::statistics& st) const {
        st.update("nseq solve calls",     m_stats.m_num_solve_calls);
        st.update("nseq eager calls",     m_stats.m_num_eager_calls);
        st.update("nseq dfs nodes",       m_stats.m_num_dfs_nodes);
        st.update("nseq sat",             m_stats.m_num_sat);
        st.update("nseq unsat",           m_stats.m_num_unsat);
        st.update("nseq unknown",         m_stats.m_num_unknown);
        st.update("nseq simplify clash",  m_stats.m_num_simplify_conflict);
        st.update("nseq extensions",      m_stats.m_num_extensions);
        st.update("nseq fresh vars",      m_stats.m_num_fresh_vars);
        st.update("nseq arith prune",     m_stats.m_num_arith_infeasible);
        st.update("nseq positional clash", m_stats.m_num_positional_clash);
        st.update("nseq max depth",       m_stats.m_max_depth);

        // modifier breakdown
        st.update("nseq mod det",              m_stats.m_mod_det);
        st.update("nseq mod power epsilon",    m_stats.m_mod_power_epsilon);
        st.update("nseq mod num cmp",          m_stats.m_mod_num_cmp);
        st.update("nseq mod split power elim", m_stats.m_mod_split_power_elim);
        st.update("nseq mod fine wilf",        m_stats.m_mod_fine_wilf);
        st.update("nseq mod const num unwind", m_stats.m_mod_const_num_unwinding);
        st.update("nseq mod eq split",         m_stats.m_mod_eq_split);
        st.update("nseq mod landing",          m_stats.m_mod_landing);
        st.update("nseq mod cycle subsump",    m_stats.m_mod_cycle_subsumption);
        st.update("nseq mod view land",        m_stats.m_mod_view_land);
        st.update("nseq mod gpower intr",      m_stats.m_mod_gpower_intr);
        st.update("nseq mod regex fact",       m_stats.m_mod_regex_factorization);
        st.update("nseq mod monadic split",    m_stats.m_mod_monadic_split);
        st.update("nseq mod monadic landing",  m_stats.m_mod_monadic_landing);
        st.update("nseq mod monadic leaf",     m_stats.m_mod_monadic_leaf);
        st.update("nseq monadic leaf sat",     m_stats.m_monadic_leaf_sat);
        st.update("nseq monadic leaf unsat",   m_stats.m_monadic_leaf_unsat);
        st.update("nseq monadic leaf gaveup",  m_stats.m_monadic_leaf_gaveup);
        st.update("nseq monadic leaf refuted", m_stats.m_monadic_leaf_refuted);
        st.update("nseq monadic leaf root asks", m_stats.m_monadic_leaf_root_asks);
        st.update("nseq monadic leaf root refutes", m_stats.m_monadic_leaf_root_refutes);
        st.update("nseq monadic branches",     m_stats.m_monadic_branches);
        st.update("nseq monadic drained",      m_stats.m_monadic_drained);
        st.update("nseq monadic fresh",        m_stats.m_monadic_fresh);
        st.update("nseq monadic resumed",      m_stats.m_monadic_resumed);
        st.update("nseq monadic gaveup",       m_stats.m_monadic_gaveup);
        st.update("nseq mod const nielsen",    m_stats.m_mod_const_nielsen);
        st.update("nseq mod block compr",      m_stats.m_mod_block_compression);
        st.update("nseq block chars",          m_stats.m_block_chars_consumed);
        st.update("nseq block pruned",         m_stats.m_block_children_pruned);
        st.update("nseq mod signature split",  m_stats.m_mod_signature_split);
        st.update("nseq mod regex var",        m_stats.m_mod_regex_var_split);
        st.update("nseq mod regex if",         m_stats.m_mod_regex_if_split);
        st.update("nseq mod power split",      m_stats.m_mod_power_split);
        st.update("nseq mod var nielsen",      m_stats.m_mod_var_nielsen);
        st.update("nseq mod var num unwind (eq)",   m_stats.m_mod_var_num_unwinding_eq);
        st.update("nseq mod var num unwind (mem)",   m_stats.m_mod_var_num_unwinding_mem);
        st.update("nseq mod axiomatized disequalities",   m_stats.m_ax_diseq);
        st.update("nseq unsat-cache size",                (unsigned) m_unsat_node_cache.size());
        st.update("nseq unsat-cache hits",                m_num_cache_hits);
        st.update("nseq sibling cuts",                    m_stats.m_num_sibling_cut);
        st.update("nseq sibling closures",                m_stats.m_num_sibling_closure);

        // split-algebra (sigma) counters, from the shared seq_split engine.
        split_stats const& sp = m_split_rw.get_split_stats();
        st.update("nseq split make",             sp.m_make);
        st.update("nseq split sigma-expand",     sp.m_sigma_expand);
        st.update("nseq split materialize",      sp.m_materialize);
        st.update("nseq split splits",           sp.m_splits);
        st.update("nseq split pushes",           sp.m_pushes);
        st.update("nseq split oracle-prunes",    sp.m_oracle_prunes);
        st.update("nseq split intersect",        sp.m_intersect);
        st.update("nseq split intersect-pairs",  sp.m_intersect_pairs);
        st.update("nseq split complement",       sp.m_complement);
        st.update("nseq split giveups",          sp.m_giveups);
        st.update("nseq split threshold-overruns", sp.m_threshold_overruns);
        st.update("nseq split max-split-set",    sp.m_max_split_set);
        st.update("nseq split dedup-drops",      sp.m_dedup_drops);
        st.update("nseq split simplify",         sp.m_simplify);

        // monadic-decomposition counters (bail reasons, states, cofactor calls), from the
        // shared seq_monadic engine.  Without this the reasons the landing enumerator and
        // the split backstop give up are invisible.
        if (m_monadic)
            m_monadic->collect_statistics(st);
        // The monadic_leaf rule runs its own engine instance, so its counters are separate
        // and were invisible before: a run with only smt.nseq.monadic_leaf=true reported a
        // give-up with no way to see which bail caused it.  When both engines are enabled
        // the keys coincide and the counters read as the sum over the two.
        if (m_monadic_leaf_engine)
            m_monadic_leaf_engine->collect_statistics(st);
    }
}
