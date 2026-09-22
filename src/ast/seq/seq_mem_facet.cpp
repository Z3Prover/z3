/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.cpp

Abstract:

    See seq_mem_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026


NSB code review:

There is a serious flaw with the mem_split rule. 
The current implementation collects all membership constraints and creates a split iterator on m_mon.
All membership constraints are used for this.
The flaw is that dependencies are not tracked correctly. This leads to unsound behavior.
The iterator creates a set of branches based on all membership constraints. Infeasible leaves are pruned internally in seq_monadic.
It could settle on that there are no branches. Then the dependencies for the membership constraints used to show emptiness should be
added to a conflicting state. 
It could skip leaves that are infeasible because of intersection constraints. 
Dependencies for skipped leaves have to be reflected in the justification for closing the sub-tree.
It is probably better to use monadic decomposition one by one for membership constraint.
In this case, a single membership constraints (uv) in R with dependency dep is decomposed into new membership constraints u in R_i1, v in R_i2 with dependency d.
We have to then also check non-emptiness of intersections for x in R_i for variables that are either in the original constraints or end up being produced by the iterator.
seq-monadic has code internally for checking non-emptiness. It would have to be exposed in a suitable way to also minimize conflict dependencies.
Say, i add x in R_1 with dep_1, x in R_2 with dep_2, ..., sucn that a prefix is known to have non-empty intersection, then adding x in R_k with dep_k is unsat, we can try to
throw away other constraints x in R_1, .., x in R_{k-1}.


- nice to have: allow reverse live_states from a regex.
  - extend str_mem type to have a "reverse" Boolean flag where regexes are interpreted in a live_states graph that was obtained by reversing a regex.
  - have reversal be decided by the live_states layer to not have it controlled at this level.


--*/
#include "ast/seq/seq_mem_facet.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

    // True when `sm` is an active membership whose own flattened string
    // is already exactly one bare variable (`x in R` or a narrowed reach
    // view `x reaches s`): mem_facet registers these with its own
    // view_witness (m_vw) as soon as they are added, and
    // mem_monadic_split never decomposes them (see the class comments on
    // mem_facet::m_vw and mem_monadic_split). Deliberately not restricted
    // to `sm.is_plain()`: mem_monadic_split's own narrowed reach views for
    // a non-final atom are exactly as single-variable as a plain `x in R`
    // membership, and withholding them from m_vw would silently exempt
    // them from the joint per-variable feasibility check the comments
    // above promise - which is exactly what used to let a reach view
    // admitting several distinct lengths (e.g. a Kleene-plus loop-back
    // state) coexist unchecked with an incompatible length-derived
    // membership on the same variable.
    static bool is_single_var_plain(str_mem const& sm) {
        return sm.m_str.size() == 1 && is_uninterp(sm.m_str.get(0));
    }

    void mem_facet::advance_qhead(unsigned head) {
        m_trail.push(value_trail<unsigned>(m_qhead));
        m_qhead = head;
    }

    void mem_facet::add(str_mem const& sm) {
        m_mems.push_back(sm);
        m_trail.push(push_back_trail<str_mem>(m_mems));
        if (is_single_var_plain(sm))
            m_vw.add(sm.m_str.get(0), sm.m_view, sm.m_dep);
        if (m_witness_extracted)
            set_witness_extracted(false);
    }

    void mem_facet::narrow(unsigned idx, view const& new_view) {
        SASSERT(idx < m_mems.size());
        str_mem const& sm = m_mems[idx];
        if (!sm.active() || sm.m_view == new_view)
            return;
        // Append-only: an "update" to an existing membership never mutates
        // its entry in place - it deactivates the old entry and appends a
        // fresh one with the new view (mirrors str_mem::m_active's own
        // append-only discipline comment; also matches how
        // mem_monadic_split::iterator::next already narrows a variable's
        // membership this way). Copy the fields that survive the update
        // before remove()/add() touch m_mems, since add() may reallocate
        // the vector out from under a live reference into it.
        expr_ref_vector str(sm.m_str);
        eq_tree::dep_tracker dep = sm.m_dep;
        remove(idx);
        add(str_mem(m, str, new_view, dep));
    }

    void mem_facet::remove(unsigned idx) {
        SASSERT(idx < m_mems.size());
        m_trail.push(vector_field_trail<str_mem, bool>(m_mems, idx, &str_mem::m_active));
        m_mems[idx].m_active = false;
    }

    void mem_facet::replace(unsigned idx, expr_ref_vector const& new_str, eq_tree::dep_tracker dep) {
        SASSERT(idx < m_mems.size());
        str_mem const& sm = m_mems[idx];
        if (!sm.active())
            return;
        view v = sm.m_view;
        eq_tree::dep_tracker new_dep = m_dm.mk_join(sm.m_dep, dep);
        remove(idx);
        add(str_mem(m, new_str, v, new_dep));
    }

    void mem_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        // Snapshot the size: entries appended below (already substituted)
        // must not be revisited by this same pass.
        unsigned n = m_mems.size();
        for (unsigned i = 0; i < n; ++i) {
            str_mem const& sm = m_mems[i];
            if (!sm.active())
                continue;
            bool present = false;
            for (expr* t : sm.m_str)
                if (t == var) { present = true; break; }
            if (!present)
                continue;
            expr_ref_vector new_str(sm.m_str);
            subst_in(new_str, var, repl);
            view v = sm.m_view;
            eq_tree::dep_tracker dep = m_dm.mk_join(sm.m_dep, subst_dep);
            remove(i);
            add(str_mem(m, new_str, v, dep));
        }
    }

    stx::facet_i* mem_facet::clone(trail_stack& trail) const {
        mem_facet* f = alloc(mem_facet, trail, m, u, m_dm, m_rw);
        f->m_mems.append(m_mems);
        f->m_qhead = m_qhead;
        // Replay registration of every active single-variable plain
        // membership with the clone's own m_vw (which was built fresh
        // against `trail`, not `this->m_vw`'s private state) - mirrors
        // how the rest of this facet's state is deep-copied field by
        // field rather than shared.
        for (auto const& sm : f->m_mems)
            if (is_single_var_plain(sm))
                f->m_vw.add_untrailed(sm.m_str.get(0), sm.m_view, sm.m_dep);
        f->m_witness_extracted = m_witness_extracted;
        for (auto const& [var, w] : m_witness) {
            f->m_witness_pin.push_back(w);
            f->m_witness.insert(var, w);
        }
        return f;
    }

    bool mem_facet::is_satisfied() const {
        for (auto const& sm : m_mems)
            if (sm.active() && !is_single_var_plain(sm))
                return false;
        return true;
    }

    namespace {
        class mem_witness_trail : public trail {
            obj_map<expr, expr*>& m_map;
            expr*                 m_var;
            bool                  m_had_prior;
            expr*                 m_prior;
        public:
            mem_witness_trail(obj_map<expr, expr*>& map, expr* var, bool had_prior, expr* prior) :
                m_map(map), m_var(var), m_had_prior(had_prior), m_prior(prior) {}
            void undo() override {
                if (m_had_prior)
                    m_map.insert(m_var, m_prior);
                else
                    m_map.remove(m_var);
            }
        };
    }

    void mem_facet::set_witness_extracted(bool v) {
        m_trail.push(value_trail<bool>(m_witness_extracted));
        m_witness_extracted = v;
    }

    void mem_facet::set_witness(expr* var, expr* w) {
        expr* prior = nullptr;
        bool had_prior = m_witness.find(var, prior);
        m_witness_pin.push_back(w);
        m_trail.push(mem_witness_trail(m_witness, var, had_prior, prior));
        m_witness.insert(var, w);
    }

    bool mem_facet::get_witness(expr* var, expr_ref& w) const {
        if (!m_witness_extracted)
            return false;
        expr* e = nullptr;
        if (!m_witness.find(var, e))
            return false;
        w = e;
        return true;
    }

    void mem_facet::get_witness_model(obj_map<expr, expr*>& subst, expr_ref_vector& pin) const {
        subst.reset();
        pin.reset();
        expr_mark seen;
        for (auto const& sm : m_mems) {
            if (!sm.active() || sm.m_str.size() != 1)
                continue;                          // defensive: shouldn't happen when sat
            expr* v = sm.m_str.get(0);
            if (seen.is_marked(v))
                continue;
            seen.mark(v);
            expr_ref w(m);
            if (get_witness(v, w)) {
                subst.insert(v, w);
                pin.push_back(w);
            }
        }
    }

    std::ostream& mem_facet::display(std::ostream& out) const {
        unsigned num_active = 0;
        for (auto const& sm : m_mems)
            if (sm.active())
                ++num_active;
        out << "mem_facet: " << num_active << " membership(s) (" << m_mems.size() << " total incl. inactive)\n";
        for (auto const& sm : m_mems) {
            if (!sm.active())
                continue;
            out << "  ";
            for (expr* t : sm.m_str)
                out << mk_pp(t, m) << " ";
            out << "in state " << seq_util::rex::pp(u.re, sm.m_view.m_state, false);
            if (sm.m_view.is_reach())
                out << " -> " << seq_util::rex::pp(u.re, sm.m_view.m_target, false);
            out << "\n";
        }
        return out;
    }

    // NSB code review: also strip units from back for membership constraints.
    // you can do this by reversing regex, take derivative and reverse result. 
    // derivative itself can be an if-then-else tree with predicates on characters.
    // we have to handle it by separately splitting on if-then-else for membership constraints
    // membership regexes that are if-then-else should not be propagated on. So disable propagation for those.
    // hoist the ite patterns.
    // consider if co-factor code in ast/rewriter directory already does this.
    stx::simplify_result mem_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.mem_facet_ref();
        bool changed = false;
        m_stats.m_num_propagate++;
        // Every active single-variable plain membership (`x in R`) is
        // registered incrementally with f.vw() as it is added (see
        // mem_facet::add / is_single_var_plain) - including narrowed
        // views mem_monadic_split materializes from a compound
        // membership's decomposition. Check their joint feasibility per
        // variable here, before this round's structural checks below:
        // this is the ONLY place that decides those constraints now that
        // mem_monadic_split no longer runs a joint multi-membership
        // search of its own (see mem_monadic_split's class comment).
        // Gated by smt.seq.regex_precheck (default true, mirroring c3's
        // smt.nseq.regex_precheck): turning it off only forgoes this
        // early single-variable joint-feasibility check, it does not
        // affect soundness elsewhere - mem_leaf_split and the ordinary
        // per-membership splitting still see the same constraints.
        if (ac.fparams().m_seq_regex_precheck) {
            view_witness& vw = f.vw();
            f.reset_vw_budget();
            lbool r = vw.check();
            if (r == l_false) {
                eq_tree::dep_tracker dep = nullptr;
                for (void* d : vw.core())
                    dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
                n.set_conflict(stx::br_plugin_base, dep);
                return stx::simplify_result::conflict;
            }
        }
        // Incremental scan: [qhead, memberships().size()) only (see
        // mem_facet::m_qhead's comment). A membership left pending here
        // (still active, not yet removed/conflicted) never needs to be
        // revisited on a later round unless it is actually updated, and
        // any update always deactivates this index and appends a fresh
        // one past the current size - so advancing past every entry seen
        // this pass, whether resolved or merely pending, is sound.
        unsigned head = f.qhead();
        while (head < f.memberships().size()) {
            unsigned i = head++;
            auto const& sm = f.memberships()[i];
            if (!sm.active())
                continue;
            if (sm.is_view())
                continue;
            // c3 branch's generate_length_constraints/
            // generate_node_length_constraints (seq_nielsen.cpp): a plain
            // membership `str in re` bounds `len(str)` by re's own
            // min/max accepted length, independent of whatever
            // derivative/live-state reasoning this loop does below -
            // assert those bounds to the arithmetic sub-solver so length
            // reasoning (arith_propagation, power facets, ...) can prune
            // on them without waiting for this membership to be fully
            // resolved structurally. solver_facet::add_constraint itself
            // de-dupes identical terms via `m_own`; the qhead above also
            // means this fires at most once per membership entry, since
            // an entry is never revisited once passed.
            {
                auto& sf = ac.solver_facet_ref();
                arith_util& a = sf.get_arith_util();
                unsigned lo = u.re.min_length(sm.m_view.m_state);
                unsigned hi = u.re.max_length(sm.m_view.m_state);
                if (lo > 0 || hi < UINT_MAX) {
                    expr_ref len_str(a.mk_int(0), m_rw.m());
                    for (expr* t : sm.m_str) {
                        expr_ref tok_len(u.str.is_unit(t) ? (expr*)a.mk_int(1) : (expr*)u.str.mk_length(t), m_rw.m());
                        len_str = a.mk_add(len_str, tok_len);
                    }
                    if (lo > 0)
                        sf.add_constraint(a.mk_ge(len_str, a.mk_int(lo)), sm.m_dep);
                    if (hi < UINT_MAX)
                        sf.add_constraint(a.mk_le(len_str, a.mk_int(hi)), sm.m_dep);
                }
            }
            expr_ref cur(sm.m_view.m_state, m_rw.m());
            bool bad = false;
            expr* elem = nullptr;
            for (auto t : sm.m_str) {
                if (!u.str.is_unit(t)) { 
                    bad = true; 
                    break; 
                }
                VERIFY(u.str.is_unit(t, elem));
                cur = m_rw.mk_derivative(elem, cur);
                if (u.re.is_empty(cur)) {
                    n.set_conflict(stx::br_plugin_base, sm.m_dep);
                    return stx::simplify_result::conflict;
                }
            }
            #if 0 
            // NSB code review: todo
            if (bad) {
                SASSERT(!sm.m_str.empty());
                auto rcur = cur;
                rcur = u.rex.mk_reverse(rcur);
                for (unsigned i = sm.m_str.size(); i-- > 0; ) {
                    auto t = sm.m_str.get(i);
                    if (!u.str.is_unit(t, elem))
                        break;
                
                    rcur = m_rw.mk_derivative(elem, rcur);
                    if (u.re.is_empty(rcur)) {
                        n.set_conflict(stx::br_plugin_base, sm.m_dep);
                        return stx::simplify_result::conflict;
                    }
                }
                cur = u.rex.mk_reverse(rcur);
                // simplify it too?
            }
            #endif

            // string was all characters
            if (!bad) {
                expr_ref nb = m_rw.is_nullable(cur);
                if (m_rw.m().is_false(nb)) {
                    n.set_conflict(stx::br_plugin_base, sm.m_dep);
                    return stx::simplify_result::conflict;
                }
                if (m_rw.m().is_true(nb)) {
                    f.remove(i);
                    changed = true;
                    continue;
                }
            }
            auto live = f.live().reachable_live(sm.m_view);
            if (live.is_dead() || seq::is_dead(sm.m_view, m_rw)) {
                n.set_conflict(stx::br_plugin_base, sm.m_dep);
                return stx::simplify_result::conflict;
            }
            lbool a = bad ? l_undef : seq::accepts(sm.m_view, m_rw);
            if (a == l_false) {
                n.set_conflict(stx::br_plugin_base, sm.m_dep);
                return stx::simplify_result::conflict;
            }
            if (a == l_true) {
                f.remove(i);
                changed = true;
                continue;
            }
        }
        if (head != f.qhead()) {
            f.advance_qhead(head);
            changed = true;
        }
        if (f.is_satisfied()) {
            if (!f.witness_extracted() && !f.memberships().empty()) {
                view_witness& vw = f.vw();

                vector<std::pair<expr*, rational>> lens;
                {
                    expr_mark seen;
                    for (auto const& sm : f.memberships()) {
                        if (!sm.active() || sm.m_str.size() != 1)
                            continue;
                        expr* v = sm.m_str.get(0);
                        if (seen.is_marked(v))
                            continue;
                        seen.mark(v);
                        rational k;
                        if (!ac.current_value(u.str.mk_length(v), k) || !k.is_unsigned())
                            continue;
                        lens.push_back({v, k});
                    }
                }
                if (!lens.empty()) {
                    auto& sf = ac.solver_facet_ref();
                    arith_util& au = sf.get_arith_util();
                    assumption_facet& asf = ac.assumption_facet_ref();
                    for (auto const& [v, k] : lens) {
                        expr_ref len_eq(m.mk_eq(u.str.mk_length(v), au.mk_int(k)), m);
                        eq_tree::dep_tracker cond_dep = asf.add_assumption(len_eq, ac.context());
                        sort* re_sort = u.re.mk_re(v->get_sort());
                        app* full_char = u.re.mk_full_char(re_sort);
                        unsigned k_u = k.get_unsigned();
                        expr_ref exact(u.re.mk_loop_proper(full_char, k_u, k_u), m);
                        vw.add(v, view::membership(exact, m), static_cast<void*>(cond_dep));
                    }
                }

                vw.set_enable_witness(true);
                f.reset_vw_budget();
                lbool r = vw.check();
                if (r == l_false) {
                    eq_tree::dep_tracker dep = nullptr;
                    for (void* d : vw.core())
                        dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
                    vw.set_enable_witness(false);
                    n.set_conflict(stx::br_plugin_base, dep);
                    return stx::simplify_result::conflict;
                }
                if (r == l_true) {
                    expr_mark seen;
                    for (auto const& sm : f.memberships()) {
                        if (!sm.active() || sm.m_str.size() != 1)
                            continue;
                        expr* v = sm.m_str.get(0);
                        if (seen.is_marked(v))
                            continue;
                        seen.mark(v);
                        expr_ref w = vw.materialize_witness(v);
                        f.set_witness(v, w);
                    }
                    f.set_witness_extracted();
                }
                vw.set_enable_witness(false);
            }
            return stx::simplify_result::satisfied;
        }
        if (changed)
            return stx::simplify_result::proceed;
        m_stats.m_num_propagate--;
        return stx::simplify_result::noop;
    }


    // A power token with symbolic exponent at a directional end of a membership's string.
    static bool find_peel_mem_trigger(power_facet const& f, mem_facet const& mf, arith_util& a,
                                           unsigned& mem_idx, bool& fwd, unsigned& pow_idx,
                                           eq_tree::dep_tracker& dep) {
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            str_mem const& sm = mf.memberships()[i];
            if (!sm.active())
                continue;
            auto const& ts = sm.m_str;
            if (ts.empty())
                continue;
            for (bool f2 : {true, false}) {
                expr* tok = f2 ? ts.get(0) : ts.back();
                unsigned pidx;
                if (!f.find_power(tok, pidx))
                    continue;
                rational v;
                if (a.is_numeral(f.powers()[pidx].m_n, v))
                    continue; // resolved directly by power_propagation
                mem_idx = i;
                fwd = f2;
                pow_idx = pidx;
                dep = sm.m_dep;
                return true;
            }
        }
        return false;
    }

    bool power_peel_mem::iterator::next(eq_tree::edge& out) {
        if (m_done)
            return false;
        m_done = true;

        auto ac = get_ambient(m_n);
        auto& f = ac.power_facet_ref();
        auto& mf = ac.mem_facet_ref();
        if (m_pow_idx >= f.powers().size() || !f.powers()[m_pow_idx].active()
            || m_mem_idx >= mf.memberships().size() || !mf.memberships()[m_mem_idx].active())
            return false; // defensive; obligation/membership discharged by another route

        str_power p = f.powers()[m_pow_idx]; // copy: broadcast_subst may reallocate m_pows

        // Branch 2 (the remaining alternative once branch 1 - "n<=0",
        // materialized by split() itself - has been offered): n >= 1,
        // peel one copy: U^n -> U . U^(n-1) (nested power, same
        // directional end), broadcast to every occurrence of U^n.
        expr_ref n_minus_1(a.mk_sub(p.m_n, a.mk_int(1)), m);
        expr_ref nested_pow(u.str.mk_power(p.m_s, n_minus_1), m);
        expr_ref_vector base(m);
        u.str.get_concat_units(p.m_s, base);
        expr_ref_vector repl(m);
        if (m_fwd) { repl.append(base); repl.push_back(nested_pow.get()); }
        else       { repl.push_back(nested_pow.get()); repl.append(base); }

        broadcast_subst(m_n, p.m_e, repl, m_dep);
        ac.add_assumption(a.mk_ge(p.m_n, a.mk_int(1)), m_dep);

        out = eq_tree::edge("power-peel-mem:n>=1", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> power_peel_mem::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.power_facet_ref();
        auto& mf = ac.mem_facet_ref();

        unsigned mem_idx, pow_idx;
        bool fwd;
        eq_tree::dep_tracker dep;
        if (!find_peel_mem_trigger(f, mf, a, mem_idx, fwd, pow_idx, dep))
            return nullptr;
        has_more = true;

        str_power p = f.powers()[pow_idx]; // copy: broadcast_subst may reallocate m_pows

        // Branch 1 (first, immediately materialized): n <= 0, U^n := epsilon
        expr_ref_vector empty(m);
        broadcast_subst(n, p.m_e, empty, dep);
        ac.add_assumption(a.mk_le(p.m_n, a.mk_int(0)), dep);

        iterator* it = alloc(iterator, n, mem_idx, fwd, pow_idx, dep, m, u, a);
        out = eq_tree::edge("power-peel-mem:n=0", dep, true, 0);
        committed = true;
        m_stats.m_num_splits++;
        return it;
    }

    // ---- mem_split ------------------------------------------------------------------

    bool mem_split::out_of_budget() {
        if (m_budget == 0) {
            m_giveup = true;
            return true;
        }
        if (!m.inc()) {
            m_giveup = true;
            return true;
        }
        --m_budget;
        return false;
    }

    expr* mem_split::der_elem(expr* r, expr* elem) {
        expr* cached = nullptr;
        if (m_der_cache.find(r, elem, cached))
            return cached;
        expr_ref d = m_rw.mk_derivative(elem, r);
        expr_ref d2(m);
        m_thrw(d, d2);
        m_pin.push_back(r);
        m_pin.push_back(elem);
        m_pin.push_back(d2);
        m_der_cache.insert(r, elem, d2.get());
        return d2.get();
    }

    lbool mem_split::nullable(expr* r) {
        lbool i = re().get_info(r).nullable;
        if (i != l_undef)
            return i;
        expr_ref nb = m_rw.is_nullable(r);
        if (m.is_true(nb))
            return l_true;
        if (m.is_false(nb))
            return l_false;
        return l_undef;
    }

    lbool mem_split::final_accepts(expr* r) {
        if (m_target)
            return r == m_target ? l_true : l_false;
        return nullable(r);
    }

    bool mem_split::can_decide(expr_ref_vector const& str) {
        expr* v = nullptr;
        return any_of(str, [&](expr* e) { return u.str.is_unit(e, v) && !m.is_value(v); });
    }

    void mem_split::reset_search() {
        m_atoms.reset();
        m_stack.reset();
        m_branch.reset();
        m_giveup = false;
        m_any_undef = false;
        m_pos_i = 0;
        m_pos_R = nullptr;
        m_target = nullptr;
        ++m_gen;
    }

    lbool mem_split::advance_pos() {
        while (true) {
            if (m_pos_i == FINAL_POS)
                return l_true;
            if (out_of_budget())
                return l_undef;
            if (m_pos_i == m_atoms.size())
                return final_accepts(m_pos_R);
            expr* elem = nullptr;
            if (!u.str.is_unit(m_atoms.get(m_pos_i), elem))
                return l_true;                 // variable atom
            expr* d = der_elem(m_pos_R, elem);
            if (re().is_empty(d))
                return l_false;
            m_pos_R = d;
            ++m_pos_i;
        }
    }

    bool mem_split::push_frame() {
        if (m_pos_i == FINAL_POS || m_pos_i == m_atoms.size())
            return false;
        SASSERT(!u.str.is_unit(m_atoms.get(m_pos_i)));
        frame f;
        f.i = m_pos_i;
        f.R = m_pos_R;
        f.next = 0;
        f.last_atom = (m_pos_i + 1 == m_atoms.size());
        m_stack.push_back(f);
        return true;
    }

    bool mem_split::commit_next(frame& f) {
        if (re().is_empty(f.R))
            return false;
        expr_ref var(m_atoms.get(f.i), m);
        // The acceptance view for f.R: reaching m_target when the
        // membership being decomposed is itself a reach view, plain
        // membership (nullability) otherwise. Used both as the
        // final-atom branch's own view below, and to prune/filter
        // candidate intermediate states via reachable_live() by that
        // same condition - using a plain membership view unconditionally
        // there would prune by nullability even when the real target is
        // m_target, wrongly dropping a state that only leads to
        // m_target (never a nullable state) from the live frontier, and
        // silently losing a genuine satisfying branch.
        view goal = m_target ? view::reach(f.R, m_target, m) : view::membership(f.R, m);
        while (true) {
            expr* target = nullptr;
            view v(m);
            if (f.last_atom) {
                if (f.next++ > 0)
                    return false;
                v = goal;
            }
            else {
                auto live = m_live.reachable_live(goal);
                target = live.at(f.next++);
                if (!target) {
                    if (live.failed())
                        m_any_undef = true;
                    return false;
                }
                v = view::reach(f.R, target, m);
            }
            m_branch.push_back(elem(var, v));
            if (f.last_atom)
                m_pos_i = FINAL_POS;
            else {
                m_pos_i = f.i + 1;
                m_pos_R = target;
            }
            lbool adv = advance_pos();
            if (adv == l_true)
                return true;
            if (adv == l_undef)
                m_any_undef = true;
            m_branch.pop_back();
            if (m_giveup)
                return false;
            // else: retry the next candidate for this frame
        }
    }

    lbool mem_split::run_search(bool backtrack) {
        while (true) {
            if (m_giveup)
                return l_undef;
            if (backtrack) {
                if (m_stack.empty())
                    return m_any_undef ? l_undef : l_false;
                m_branch.pop_back();
                backtrack = false;             // commit_next re-seats the position
            }
            else if (!push_frame())
                return l_true;                 // leaf: m_branch holds the full branch
            if (!commit_next(m_stack.back())) {
                m_stack.pop_back();
                backtrack = true;
            }
        }
    }

    mem_split::iterator mem_split::iterate(expr_ref_vector const& str, view const& v) {
        reset_search();
        if (can_decide(str)) {
            m_giveup = true;
            return iterator(*this);
        }
        m_atoms.append(str);
        m_pin.push_back(v.m_state);
        m_pos_i = 0;
        m_pos_R = v.m_state;
        m_target = v.m_target;
        if (m_target)
            m_pin.push_back(m_target);
        m_budget = m_budget_limit;
        m_init_result = advance_pos();
        // advance_pos() can return l_undef straight from nullable() (a
        // string of concrete units whose final state's nullability the
        // rewriter could not decide), before any commit_next() call ever
        // runs - the only other caller of advance_pos(), which does set
        // m_any_undef on l_undef itself. Without this, iterator::next()
        // returning false here would look identical to a genuine
        // refutation to gave_up()'s callers (see mem_monadic_split::
        // split()), misreporting an undecided membership as UNSAT.
        if (m_init_result == l_undef)
            m_any_undef = true;
        return iterator(*this);
    }

    bool mem_split::iterator::next(branch& out) {
        if (m_gen != m_e->m_gen)
            return false;
        lbool r;
        if (!m_started) {
            m_started = true;
            r = m_e->m_init_result;
            if (r == l_true)
                r = m_e->run_search(false);
        }
        else
            r = m_e->run_search(true);
        if (r != l_true)
            return false;
        out = m_e->m_branch;
        return true;
    }

    // ---- mem_monadic_split ------------------------------------------------------------

    bool mem_monadic_split::find_split_target(mem_facet const& mf, unsigned& idx) {
        bool found = false;
        unsigned best_cost = UINT_MAX;
        for (unsigned i = 0; i < mf.memberships().size(); ++i) {
            str_mem const& sm = mf.memberships()[i];
            if (!sm.active())
                continue;
            if (is_single_var_plain(sm))
                continue;             // handled directly by mem_facet's own view_witness
            if (sm.m_str.size() == 1 && u.str.is_power(sm.m_str.get(0)))
                continue;             // power_peel_mem's: narrowing its view again makes no progress
            unsigned cost = 0;
            for (expr* e : sm.m_str)
                if (!u.str.is_unit(e))
                    ++cost;
            if (!found || cost < best_cost) {
                found = true;
                best_cost = cost;
                idx = i;
            }
        }
        return found;
    }

    bool mem_monadic_split::iterator::next(eq_tree::edge& out) {
        mem_split::branch br;
        if (!m_it.next(br))
            return false;
        auto ac = get_ambient(m_n);
        auto& mf = ac.mem_facet_ref();
        mf.remove(m_mem_idx);
        for (auto const& e : br) {
            expr_ref_vector ts(m);
            ts.push_back(e.var.get());
            mf.add(str_mem(m, ts, e.m_view, m_dep));
        }
        out = eq_tree::edge("mem-monadic", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_monadic_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto& mf = get_ambient(n).mem_facet_ref();
        unsigned idx;
        if (!find_split_target(mf, idx))
            return nullptr;
        has_more = true;
        str_mem const& sm = mf.memberships()[idx];
        eq_tree::dep_tracker dep0 = sm.m_dep;
        scoped_ptr<iterator> it(alloc(iterator, n, m_rw, m, u, mf.live(), idx, sm));
        if (!it->next(out)) {
            if (it->gave_up())
                return nullptr;   // resource bound hit before deciding; not a conflict
            // mem_split never consults any OTHER membership or variable's
            // constraints when decomposing one membership (see its class
            // comment): its own decomposition being exhausted with no
            // satisfying branch means THIS membership alone is UNSAT, so
            // its own dependency names the conflict precisely - no join
            // over anything else is needed or would even be more precise.
            m_stats.m_num_refuted++;
            n.set_conflict(stx::br_plugin_base, dep0);
            return nullptr;
        }
        committed = true;
        m_stats.m_num_splits++;
        has_more = true;
        return it.detach();
    }

    // ---- mem_leaf_split -----------------------------------------------------------

    lbool mem_leaf_split::ask(mem_facet const& mf, unsigned budget, eq_tree::dep_tracker& all_dep, expr_substitution* witnesses) {
        all_dep = nullptr;
        m_mon_trail.push_scope();
        bool any = false;
        for (str_mem const& sm : mf.memberships()) {
            if (!sm.active() || !sm.is_plain() || sm.m_str.empty())
                continue;
            expr* term = u.str.mk_concat(sm.m_str.size(), sm.m_str.data(), sm.m_str[0]->get_sort());
            if (!m_mon.can_decide_term(term))
                continue;
            m_mon.add(term, sm.m_view.m_state.get(), sm.m_dep);
            all_dep = mf.dm().mk_join(all_dep, sm.m_dep);
            any = true;
        }
        lbool result = l_undef;
        if (any) {
            m_mon.set_budget(budget);
            result = m_mon.check();
            m_stats.m_num_asked++;
            if (result == l_false) {
                eq_tree::dep_tracker core_dep = nullptr;
                for (void* d : m_mon.core())
                    core_dep = mf.dm().mk_join(core_dep, static_cast<eq_tree::dep_tracker>(d));
                all_dep = core_dep;
            }
            else if (result == l_true && witnesses) {
                if (m_mon.materialize_all(*witnesses) != l_true)
                    result = l_undef;
            }
        }
        m_mon_trail.pop_scope(1);
        return any ? result : l_undef;
    }

    bool mem_leaf_split::iterator::next(eq_tree::edge& out) {
        if (m_offered)
            return false;
        m_offered = true;
        auto ac = get_ambient(m_n);
        // See mem_leaf_split's class comment: this is the "unchanged"
        // branch, so the only mutation is the decline guard itself -
        // pushed on the SHARED node trail so it pops back to false
        // exactly when the search backtracks out of this branch.
        ac.trail().push(value_trail<bool>(m_owner.m_declined_here, true));
        out = eq_tree::edge("mem-leaf-decline", m_dep, true, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> mem_leaf_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        if (m_declined_here)
            return nullptr;
        auto ac = get_ambient(n);
        if (!ac.fparams().m_seq_monadic_leaf)
            return nullptr;
        // Ordinary asks only run once the node's own equations/
        // disequations are already settled - mirrors c3's
        // `m_monadic_leaf_refute` defaulting false: asking (and
        // discarding an l_true relaxation) on every equation-bearing
        // interior node visited by the DFS was measured to cost more
        // than it saves there.
        //
        // The ONE exception, mirroring c3's monadic_leaf_root_refute /
        // m_monadic_leaf_root (default true): a refutation-only ask,
        // regardless of eqs_done, exactly once for the whole lifetime of
        // this plugin instance. This port has no separate "before the
        // DFS proper starts" hook to call into (unlike c3's nielsen_graph,
        // whose root is a distinct, persistent object) - but since this
        // plugin is registered ahead of every other split plugin and at
        // min_cost 0 (see theory_nseq.cpp), the very first time split()
        // is ever invoked at all is necessarily on the search's root node,
        // before any split has committed a branch anywhere - so "first
        // call ever" is exactly the event c3's guard is asking for.
        // Deliberately NOT trailed: like m_monadic_leaf_root_asked, this
        // is a true one-time lifetime event, not a per-branch decision -
        // backtracking past the root never "undoes" having asked once.
        bool eqs_done = ac.eq_facet_ref().is_satisfied() && ac.deq_facet_ref().is_satisfied();
        bool root_ask = !m_root_asked && ac.fparams().m_seq_monadic_leaf_root;
        m_root_asked = true;
        if (!eqs_done && !root_ask)
            return nullptr;
        auto& mf = ac.mem_facet_ref();
        eq_tree::dep_tracker dep = nullptr;
        expr_substitution witnesses(m);
        unsigned budget = (!eqs_done && root_ask) ? ac.fparams().m_seq_monadic_leaf_budget_root : m_budget;
        lbool r = ask(mf, budget, dep, eqs_done ? &witnesses : nullptr);
        if (r == l_undef)
            return nullptr;   // nothing to feed, or gave up before deciding
        has_more = true;
        if (r == l_false) {
            m_stats.m_num_refuted++;
            n.set_conflict(stx::br_plugin_base, dep);
            return nullptr;
        }
        SASSERT(r == l_true);
        if (witnesses.empty())
            return nullptr;   // nothing to pin (all memberships already single-variable)
        // Child A: pin every variable to its witness word via a fresh
        // eq_facet equation (sound restriction; the rest of the search
        // checks it like any other equation).
        auto& ef = ac.eq_facet_ref();
        for (auto const& entry : witnesses.sub())
            ef.add_equation(&entry.get_key(), entry.get_value(), dep);
        out = eq_tree::edge("mem-leaf", dep, true, cost);
        committed = true;
        m_stats.m_num_committed++;
        // Child B: the unchanged alternative, offered by the iterator.
        return alloc(iterator, n, dep, *this);
    }

    // -- mem_bounds_propagation --

    // Trail-undo object for mem_bounds_propagation's own `m_last` cache;
    // see mem_bounds_propagation's class comment (seq_mem_facet.h). Kept
    // right next to its sole use site below rather than at file scope,
    // since nothing else in this file references it.
    //
    // m_prior is heap-allocated (via alloc()/dealloc()) rather than
    // embedded by value in this object: trail objects are placement-new'd
    // into trail_stack's own region allocator (see trail_stack::push()),
    // and popping/resetting that region only rewinds/frees raw memory -
    // it never runs the placed object's own destructor (region's
    // operator delete is a no-op by design). last_bound holds two
    // rational fields, whose own destructor frees a heap-allocated digit
    // buffer for any value too large for rational's inline
    // representation; embedding one by value here would silently leak
    // that buffer on every backtrack past this trail entry, since nothing
    // would ever call ~last_bound()/~rational() for it. Allocating it
    // separately on the ordinary heap and explicitly dealloc()-ing it in
    // undo() (which - unlike this object's own destructor - IS always
    // invoked on backtrack, see undo_trail_stack()) frees it correctly.
    class mem_bounds_last_trail : public trail {
        obj_map<expr, mem_bounds_propagation::last_bound>& m_map;
        expr*                                              m_var;        
        mem_bounds_propagation::last_bound*                 m_prior;
    public:
        mem_bounds_last_trail(obj_map<expr, mem_bounds_propagation::last_bound>& map, expr* var,
                               bool had_prior, mem_bounds_propagation::last_bound const& prior) :
            m_map(map), m_var(var),
            m_prior(had_prior ? alloc(mem_bounds_propagation::last_bound, prior) : nullptr) {}
        void undo() override {
            if (m_prior) {
                m_map.insert(m_var, *m_prior);
                dealloc(m_prior);
            }
            else
                m_map.remove(m_var);
        }
    };

    void mem_bounds_propagation::collect_vars(eq_tree::node& n, obj_hashtable<expr>& vars) const {
        auto ac = get_ambient(n);
        auto& ef = ac.eq_facet_ref();
        for (auto const& eq : ef.equations()) {
            if (!eq.active())
                continue;
            for (expr* t : eq.m_lhs)
                if (ac.is_var(t))
                    vars.insert(t);
            for (expr* t : eq.m_rhs)
                if (ac.is_var(t))
                    vars.insert(t);
        }
        auto& mf = ac.mem_facet_ref();
        for (auto const& sm : mf.memberships()) {
            if (!sm.active())
                continue;
            for (expr* t : sm.m_str)
                if (ac.is_var(t))
                    vars.insert(t);
        }
    }

    stx::simplify_result mem_bounds_propagation::propagate(eq_tree::node& n) {
        m_stats.m_num_propagate++;
        auto ac = get_ambient(n);
        auto& mf = ac.mem_facet_ref();
        obj_hashtable<expr> vars;
        collect_vars(n, vars);
        bool changed = false;
        for (expr* var : vars) {
            sort* elem_sort = nullptr;
            if (!u.is_seq(var->get_sort(), elem_sort))
                continue;
            expr_ref len(u.str.mk_length(var), m);
            rational lo, hi;
            eq_tree::dep_tracker lo_dep = nullptr, hi_dep = nullptr;
            bool has_lo = ac.lower_bound(len, lo, lo_dep);
            bool has_hi = ac.upper_bound(len, hi, hi_dep);
            if (!has_lo && !has_hi)
                continue;
            if (has_lo && lo.is_neg())
                has_lo = false;
            if (!has_lo && !has_hi)
                continue;

            last_bound prior;
            bool have_prior = m_last.find(var, prior);
            bool same_lo = have_prior && prior.has_lo == has_lo && (!has_lo || prior.lo == lo);
            bool same_hi = have_prior && prior.has_hi == has_hi && (!has_hi || prior.hi == hi);
            if (have_prior && same_lo && same_hi)
                continue;

            sort* re_sort = u.re.mk_re(var->get_sort());
            app* full_char = u.re.mk_full_char(re_sort);
            expr* state = nullptr;
            unsigned lo_u = has_lo ? (lo.is_unsigned() ? lo.get_unsigned() : 0) : 0;
            if (has_lo && has_hi) {
                // An infeasible range (hi < lo) is an arithmetic
                // conflict, not a regex-shape one; leave discharging it
                // to arith_propagation (which consults the same
                // ambient bounds directly) rather than duplicating that
                // conflict-detection responsibility here.
                if (hi.is_neg() || hi < lo)
                    continue;
                unsigned hi_u = hi.is_unsigned() ? hi.get_unsigned() : lo_u;
                state = u.re.mk_loop_proper(full_char, lo_u, hi_u);
            }
            else if (has_lo)
                state = u.re.mk_loop(full_char, lo_u);
            else /* has_hi only */
                state = u.re.mk_loop_proper(full_char, 0, hi.is_unsigned() ? hi.get_unsigned() : 0);

            eq_tree::dep_tracker dep = nullptr;
            if (has_lo)
                dep = mf.dm().mk_join(dep, lo_dep);
            if (has_hi)
                dep = mf.dm().mk_join(dep, hi_dep);

            mf.add(str_mem(m, var, view::membership(state, m), dep));

            last_bound updated;
            updated.has_lo = has_lo; updated.lo = has_lo ? lo : rational::zero();
            updated.has_hi = has_hi; updated.hi = has_hi ? hi : rational::zero();
            // `m_last` is a plugin-local cache used purely to skip
            // redundant re-adds (a performance/confluence aid, not part
            // of the tree's own state) - so its entries are undone via
            // the shared trail exactly like every other facet mutation,
            // restoring whatever was cached before this node was
            // visited (or removing the key entirely if it is new) once
            // the trail scope backtracking past this point unwinds.
            m_trail.push(mem_bounds_last_trail(m_last, var, have_prior, prior));
            m_last.insert(var, updated);
            changed = true;
            m_stats.m_num_added++;
        }
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    // -- mem_parikh_split --

    scoped_ptr<eq_tree::split_iterator_i> mem_parikh_split::split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        if (!ac.fparams().m_seq_mem_parikh)
            return nullptr;
        auto& mf = ac.mem_facet_ref();
        if (mf.is_satisfied())
            return nullptr;

        // Group plain membership views (`x in R_i`) by their single
        // variable token; reach views and multi-token strings carry no
        // per-variable length obligation this check can use, so they are
        // skipped (sound: skipping only loses precision, never
        // soundness).
        obj_map<expr, len_abs> lens;
        obj_map<expr, eq_tree::dep_tracker> deps;
        obj_map<expr, unsigned> counts;
        for (auto const& sm : mf.memberships()) {
            if (!sm.active())
                continue;
            if (!sm.is_plain() || sm.m_str.size() != 1)
                continue;
            expr* var = sm.m_str.get(0);
            if (!ac.is_var(var))
                continue;
            len_abs const cur = u.re.get_info(sm.m_view.m_state).len();
            len_abs combined;
            eq_tree::dep_tracker dep = sm.m_dep;
            unsigned cnt = 1;
            len_abs prior;
            if (lens.find(var, prior)) {
                combined = prior.meet(cur);
                eq_tree::dep_tracker prior_dep;
                deps.find(var, prior_dep);
                dep = mf.dm().mk_join(prior_dep, sm.m_dep);
                counts.find(var, cnt);
                cnt++;
            }
            else
                combined = cur;
            lens.insert(var, combined);
            deps.insert(var, dep);
            counts.insert(var, cnt);
        }

        for (auto const& [var, la] : lens) {
            m_stats.m_num_checks++;
            unsigned cnt = 0;
            counts.find(var, cnt);
            if (cnt < 2)
                continue; // a single membership's own length range cannot be self-contradictory
            if (!la.is_empty())
                continue;
            eq_tree::dep_tracker dep = nullptr;
            deps.find(var, dep);
            m_stats.m_num_refuted++;
            n.set_conflict(stx::br_plugin_base, dep);
            return nullptr;
        }
        return nullptr;
    }

}
