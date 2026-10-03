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

The old joint `mem_split` design can be unsound because it loses precise
dependencies. Branches pruned inside the monadic search, including
intersection-based pruning, must contribute to the justification for closing
the subtree. A safer design decomposes one membership at a time and checks
per-variable intersection non-emptiness separately so conflicts can name the
constraints actually used.


- nice to have: allow reverse live_states from a regex.
  - extend str_mem type to have a "reverse" Boolean flag where regexes are interpreted in a live_states graph that was obtained by reversing a regex.
  - have reversal be decided by the live_states layer to not have it controlled at this level.


--*/
#include "ast/seq/seq_mem_facet.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

    // Intentionally not restricted to plain memberships: single-variable
    // reach views must also participate in `m_vw`'s joint feasibility
    // check, or they can bypass incompatible constraints on the same
    // variable.

    void mem_facet::advance_qhead(unsigned head) {
        m_trail.push(value_trail<unsigned>(m_qhead));
        m_qhead = head;
    }

    void mem_facet::advance_bounds_qhead(unsigned head) {
        m_trail.push(value_trail<unsigned>(m_bounds_qhead));
        m_bounds_qhead = head;
    }

    void mem_facet::add(str_mem const& sm) {
        m_mems.push_back(sm);
        m_trail.push(push_back_trail<str_mem>(m_mems));
        if (is_single_var_plain(sm))
            m_vw.add(sm.m_str.get(0), sm.m_view, sm.m_dep);
        if (m_witness_extracted)
            set_witness_extracted(false);
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
        mem_facet* f = alloc(mem_facet, trail, m, u, m_dm, m_rw, m_ac);
        f->m_mems.append(m_mems);
        f->m_qhead = m_qhead;
        f->m_bounds_qhead = m_bounds_qhead;
        // Re-register active single-variable memberships in the clone's
        // fresh `m_vw`.
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

    uint64_t str_mem::hash() const {
        uint64_t h = stx::stx_hash_tag(0x6d656du); // tag: "mem"
        h = stx::stx_hash_ids(h, m_str);
        h = stx::stx_hash_mix(h, static_cast<uint64_t>(m_view.m_state->get_id()));
        h = stx::stx_hash_mix(h, m_view.m_target ? static_cast<uint64_t>(m_view.m_target->get_id()) : 0);
        return h;
    }

    bool str_mem::equals(stx::constraint_i const& other) const {
        auto const* o = dynamic_cast<str_mem const*>(&other);
        return o && m_str == o->m_str && m_view == o->m_view;
    }

    void mem_facet::append_constraints(vector<stx::constraint_i const*>& out) const {
        for (auto const& sm : m_mems)
            if (sm.active())
                out.push_back(&sm);
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

    // Ask `m_mon` to decide all active plain memberships jointly. Before
    // `check()`, add exact-length assumptions for variables whose length
    // already has a value in the arithmetic sub-solver. These are added as
    // assumptions, not hard facts, so a wrong guess only costs search.
    lbool mem_propagation::solve_monadic_endgame(ambient_ref<eq_tree::node, eq_tree::dep_tracker>& ac, mem_facet& f, eq_tree::dep_tracker& dep) {
        dep = nullptr;
        struct fed_item { expr* term; expr* regex; eq_tree::dep_tracker dep; };
        vector<fed_item> fed;
        // Pin freshly built concatenation terms for this call: `fed` stores
        // only raw expr*.
        expr_ref_vector pinned_terms(m);
        expr_mark vars_seen;
        ptr_vector<expr> vars;
        for (str_mem const& sm : f.memberships()) {
            if (!sm.active())
                continue;
            // `seq::monadic` only understands whole-language memberships,
            // not reach views. If any active membership is non-plain, fall
            // back to `view_witness` rather than producing only a partial
            // witness map.
            if (!sm.is_plain())
                return l_undef;
            if (sm.m_str.empty())
                continue;
            expr_ref term(u.str.mk_concat(sm.m_str.size(), sm.m_str.data(), sm.m_str[0]->get_sort()), m);
            pinned_terms.push_back(term);
            if (!m_mon.can_decide_term(term))
                return l_undef;
            fed.push_back({term, sm.m_view.m_state.get(), sm.m_dep});
            for (expr* t : sm.m_str) {
                if (u.str.is_unit(t) || vars_seen.is_marked(t))
                    continue;
                vars_seen.mark(t);
                vars.push_back(t);
            }
        }
        if (fed.empty())
            return l_undef;

        m_stats.m_num_monadic_asked++;
        auto& sf = ac.solver_facet_ref();
        arith_util& au = sf.get_arith_util();
        assumption_facet& asf = ac.assumption_facet_ref();
        m_mon_trail.push_scope();
        for (auto const& fi : fed)
            m_mon.add(fi.term, fi.regex, static_cast<void*>(fi.dep));
        for (expr* v : vars) {
            expr_ref len_expr(u.str.mk_length(v), m);
            rational k;
            if (!sf.value(len_expr, k) || !k.is_unsigned())
                continue;
            expr_ref len_eq(m.mk_eq(len_expr, au.mk_int(k)), m);
            eq_tree::dep_tracker cond_dep = asf.add_assumption(len_eq, ac.context());
            m_mon.add_len(v, k.get_unsigned(), static_cast<void*>(cond_dep));
        }
        lbool result = m_mon.check();
        if (result == l_false) {
            for (void* d : m_mon.core())
                dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
            m_stats.m_num_monadic_refuted++;
        }
        else if (result == l_true) {
            expr_substitution subst(m);
            if (m_mon.materialize_all(subst) != l_true)
                result = l_undef;
            else
                for (auto const& entry : subst.sub())
                    f.set_witness(&entry.get_key(), entry.get_value());
        }
        m_mon_trail.pop_scope(1);
        return result;
    }

    // NSB code review: also strip trailing units from membership
    // constraints by reversing the regex, taking derivatives, and
    // reversing back. This likely needs explicit handling of derivative
    // ITEs, or propagation must avoid such regexes.
    stx::simplify_result mem_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.mem_facet_ref();
        bool changed = false;
        m_stats.m_num_propagate++;
        // Every active single-variable membership is registered with
        // `f.vw()` as it is added. Check their joint feasibility here,
        // before the structural checks below. Disabling
        // `smt.seq.regex_precheck` only skips this early check.
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
        // Incremental scan over `[qhead, memberships().size())`. Pending
        // entries are only revisited if they are later replaced by a fresh
        // appended entry, so advancing `qhead` past everything seen here is
        // sound.
        unsigned head = f.qhead();
        while (head < f.memberships().size()) {
            unsigned i = head++;
            auto const& sm = f.memberships()[i];
            if (!sm.active())
                continue;
            if (sm.is_view())
                continue;
            // A plain membership `str in re` bounds `len(str)` by the
            // regex's min/max accepted length. Assert those bounds into the
            // arithmetic sub-solver so length reasoning can use them early.
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
            // Also strip trailing units by reversing the regex, taking
            // derivatives, then reversing back.
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
                ac.solver_facet_ref().add_constraint(nb, sm.m_dep);
                ac.assumption_facet_ref().add_assumption(nb, ac.context());
                f.remove(i);
                changed = true;
                continue;
            }
            auto live = f.live().reachable_live(sm.m_view);
            if (live.is_dead() || seq::is_dead(sm.m_view, m_rw)) {
                n.set_conflict(stx::br_plugin_base, sm.m_dep);
                return stx::simplify_result::conflict;
            }
        }
        if (head != f.qhead()) {
            f.advance_qhead(head);
            changed = true;
        }
        if (f.is_satisfied()) {
            if (!f.witness_extracted() && !f.memberships().empty()) {
                bool handled = false;
                if (ac.fparams().m_seq_mem_monadic_endgame) {
                    eq_tree::dep_tracker mdep = nullptr;
                    lbool mr = solve_monadic_endgame(ac, f, mdep);
                    if (mr == l_false) {
                        n.set_conflict(stx::br_plugin_base, mdep);
                        return stx::simplify_result::conflict;
                    }
                    if (mr == l_true) {
                        f.set_witness_extracted();
                        changed = true;
                        handled = true;
                    }
                    // `l_undef`: fall back to `view_witness`.
                }
                if (!handled) {
                view_witness& vw = f.vw();

                // Force witness search to respect exact known lengths from
                // the local arithmetic sub-solver.
                struct len_req { expr* v; unsigned len; };
                vector<len_req> lens;
                {
                    expr_mark seen;
                    auto& sf = ac.solver_facet_ref();
                    for (auto const& sm : f.memberships()) {
                        if (!sm.active() || sm.m_str.size() != 1)
                            continue;
                        expr* v = sm.m_str.get(0);
                        if (seen.is_marked(v))
                            continue;
                        seen.mark(v);
                        expr_ref len_expr(u.str.mk_length(v), m);
                        rational k;
                        if (sf.value(len_expr, k) && k.is_unsigned())
                            lens.push_back({v, k.get_unsigned()});
                    }
                }
                if (!lens.empty()) {
                    auto& sf = ac.solver_facet_ref();
                    arith_util& au = sf.get_arith_util();
                    assumption_facet& asf = ac.assumption_facet_ref();
                    for (auto const& req : lens) {
                        expr_ref len_eq(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
                        eq_tree::dep_tracker cond_dep = asf.add_assumption(len_eq, ac.context());
                        sort* re_sort = u.re.mk_re(req.v->get_sort());
                        app* full_char = u.re.mk_full_char(re_sort);
                        expr_ref exact(u.re.mk_loop_proper(full_char, req.len, req.len), m);
                        vw.add(req.v, view::membership(exact, m), static_cast<void*>(cond_dep));
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
                    changed = true;
                }
                vw.set_enable_witness(false);
            }
            }
        }
        if (!changed) {
            m_stats.m_num_propagate--;
            return stx::simplify_result::noop;
        }
        return f.is_satisfied() ? stx::simplify_result::satisfied : stx::simplify_result::proceed;
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
        ac.solver_facet_ref().add_constraint(a.mk_ge(p.m_n, a.mk_int(1)), m_dep);

        out = eq_tree::edge("power-peel-mem:n>=1", m_dep, false, 0);
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
        ac.solver_facet_ref().add_constraint(a.mk_le(p.m_n, a.mk_int(0)), dep);

        iterator* it = alloc(iterator, n, mem_idx, fwd, pow_idx, dep, m, u, a);
        out = eq_tree::edge("power-peel-mem:n<=0", dep, true, 0);
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
            if (mf.is_single_var_plain(sm))
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
        out = eq_tree::edge("mem-monadic", m_dep, false, 0);
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
            // `mem_split` reasons about this membership in isolation, so if
            // it exhausts every branch, this membership's own dependency is
            // the precise conflict.
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
        struct fed_item { expr* term; expr* regex; eq_tree::dep_tracker dep; };
        std::vector<fed_item> fed;
        for (str_mem const& sm : mf.memberships()) {
            if (!sm.active() || !sm.is_plain() || sm.m_str.empty())
                continue;
            expr* term = u.str.mk_concat(sm.m_str.size(), sm.m_str.data(), sm.m_str[0]->get_sort());
            if (!m_mon.can_decide_term(term))
                continue;
            fed.push_back({term, sm.m_view.m_state.get(), sm.m_dep});
        }
        if (fed.empty())
            return l_undef;

        for (auto const& fi : fed)
            all_dep = mf.dm().mk_join(all_dep, fi.dep);

        // Canonical cache key: sort so different iteration orders still hit.
        std::vector<std::pair<expr*, expr*>> key;
        key.reserve(fed.size());
        for (auto const& fi : fed)
            key.emplace_back(fi.term, fi.regex);
        std::sort(key.begin(), key.end());

        if (leaf_cache_entry* hit = find_cache(key)) {
            if (hit->result == l_false) {
                m_stats.m_num_cache_hits++;
                // `all_dep` already joins every fed dependency. That is
                // sound even though it is not core-minimized.
                return l_false;
            }
            if (hit->result == l_true && (!witnesses || hit->has_witnesses)) {
                m_stats.m_num_cache_hits++;
                if (witnesses)
                    for (unsigned i = 0; i < hit->wit_vars.size(); ++i)
                        witnesses->insert(hit->wit_vars.get(i), hit->wit_words.get(i));
                return l_true;
            }
            // Cached `l_true` without witnesses; recompute so the witness
            // map can be recorded too.
        }

        m_mon_trail.push_scope();
        for (auto const& fi : fed)
            m_mon.add(fi.term, fi.regex, fi.dep);
        m_mon.set_budget(budget);
        lbool result = m_mon.check();
        m_stats.m_num_asked++;
        if (result == l_false) {
            eq_tree::dep_tracker core_dep = nullptr;
            for (void* d : m_mon.core())
                core_dep = mf.dm().mk_join(core_dep, static_cast<eq_tree::dep_tracker>(d));
            all_dep = core_dep;
            cache_insert(key, l_false, nullptr);
        }
        else if (result == l_true) {
            if (witnesses) {
                if (m_mon.materialize_all(*witnesses) != l_true)
                    result = l_undef;
                else
                    cache_insert(key, l_true, witnesses);
            }
            else
                cache_insert(key, l_true, nullptr);
        }
        m_mon_trail.pop_scope(1);
        return result;
    }

    bool mem_leaf_split::iterator::next(eq_tree::edge& out) {
        if (m_offered)
            return false;
        m_offered = true;
        auto ac = get_ambient(m_n);
        // This is the unchanged branch, so the only mutation is the
        // trailed decline guard.
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
        // Ordinary asks run only after equations and disequations are
        // settled. The exception is a root-only, refutation-only ask,
        // retried every `seq.monadic_leaf_root_period` visits while
        // equations are still pending (see `m_pending_visits`'s comment);
        // not trailed, since it is meant to throttle across the whole
        // outer search rather than per-branch.
        bool eqs_done = ac.eq_facet_ref().is_satisfied() && ac.deq_facet_ref().is_satisfied();
        bool root_ask = false;
        if (!eqs_done && ac.fparams().m_seq_monadic_leaf_root) {
            unsigned period = ac.fparams().m_seq_monadic_leaf_root_period;
            root_ask = (period == 0) ? (m_pending_visits == 0) : (m_pending_visits % period == 0);
            ++m_pending_visits;
        }
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
        // equation.
        auto& ef = ac.eq_facet_ref();
        for (auto const& entry : witnesses.sub())
            ef.add_equation(&entry.get_key(), entry.get_value(), dep);
        out = eq_tree::edge("mem-leaf", dep, true, cost);
        committed = true;
        m_stats.m_num_committed++;
        // Child B: unchanged alternative, offered by the iterator.
        return alloc(iterator, n, dep, *this);
    }

    // -- mem_var_bounds_propagation --

    stx::simplify_result mem_var_bounds_propagation::propagate(eq_tree::node& n) {
        m_stats.m_num_propagate++;
        auto ac = get_ambient(n);
        auto& mf = ac.mem_facet_ref();
        bool changed = false;
        unsigned head = mf.bounds_qhead();
        unsigned end = mf.memberships().size();
        while (head < end) {
            str_mem const& sm = mf.memberships()[head++];
            if (!sm.active())
                continue;
            for (expr* var : sm.m_str) {
                if (!ac.is_var(var) || m_done.contains(var))
                    continue;
                sort* elem_sort = nullptr;
                if (!u.is_seq(var->get_sort(), elem_sort))
                    continue;
                expr_ref len(u.str.mk_length(var), m);
                rational lo, hi;
                eq_tree::dep_tracker lo_dep = nullptr, hi_dep = nullptr;
                bool has_lo = ac.lower_bound(len, lo, lo_dep);
                bool has_hi = ac.upper_bound(len, hi, hi_dep);
                if (has_lo && lo.is_neg())
                    has_lo = false;
                // No bound known yet: leave `var` unmarked so a later
                // membership mentioning it (e.g. from a split or
                // substitution) gets another chance.
                if (!has_lo && !has_hi)
                    continue;

                sort* re_sort = u.re.mk_re(var->get_sort());
                app* full_char = u.re.mk_full_char(re_sort);
                expr* state = nullptr;
                unsigned lo_u = has_lo ? (lo.is_unsigned() ? lo.get_unsigned() : 0) : 0;
                if (has_lo && has_hi) {
                    // An infeasible range is an arithmetic conflict; leave
                    // it to `arith_propagation`.
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
                // `m_done` is a plugin-local, whole-search cache (variable
                // identity is global), so it is unwound with the shared
                // trail.
                m_trail.push(insert_obj_trail<expr>(m_done, var));
                m_done.insert(var);
                changed = true;
                m_stats.m_num_added++;
            }
        }
        if (head != mf.bounds_qhead()) {
            mf.advance_bounds_qhead(head);
            changed = true;
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

        // Group plain single-variable memberships by variable. Reach views
        // and multi-token strings are skipped.
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
