/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_view_witness.cpp

Abstract:

    Incremental non-emptiness checking for products of sequence views.

--*/

#include "ast/seq/seq_view_witness.h"
#include <algorithm>
#include <functional>
#include <set>
#include <unordered_set>

namespace seq {

    view_witness::view_witness(trail_stack& t, seq_rewriter& rw, live_states& live,
                               transition_mode mode) :
        m(rw.m()),
        m_rw(rw),
        m_trail(t),
        m_live(live),
        m_mode(mode),
        m_pin(m),
        m_witness_pin(m),
        m_rp_cache(m),
        m_ivl_pin(m) {
    }

    view_witness::~view_witness() {
        reset_ivl_cache();
    }

    void view_witness::add(expr* x, view const& v, void* dependency) {
        m_assertions.push_back(assertion(x, v, dependency, m));
        m_trail.push(push_back_vector(m_assertions));
        m_last_result = l_undef;
        m_core.reset();
        m_witnesses.reset();
        m_witness_pin.reset();
    }

    void view_witness::dedup_views(view_vector const& in, view_vector& out) {
        std::set<view::sig> seen;
        for (auto const& v : in)
            if (seen.insert(v.key()).second)
                out.push_back(v);
    }

    view_witness::signature view_witness::mk_signature(view_vector const& views) {
        signature sig;
        for (auto const& v : views)
            sig.push_back(v.key());
        std::sort(sig.begin(), sig.end());
        sig.erase(std::unique(sig.begin(), sig.end()), sig.end());
        return sig;
    }

    bool view_witness::checkpoint() {
        if (!m_checkpoint)
            return false;
        m_failure = m_checkpoint();
        return m_failure != view_failure_reason::none;
    }

    lbool view_witness::nullable(expr* r) {
        lbool i = re().get_info(r).nullable;
        if (i != l_undef)
            return i;
        char v = 0;
        if (m_nullable_cache.find(r, v)) {
            if (v == 1)
                return l_true;
            if (v == 0)
                return l_false;
            return l_undef;
        }
        expr_ref nb = m_rw.is_nullable(r);
        lbool result = m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
        m_pin.push_back(r);
        m_nullable_cache.insert(r, result == l_true ? 1 : result == l_false ? 0 : 2);
        return result;
    }

    expr_ref_pair_vector const& view_witness::derivative_cofactors(expr* r) {
        ++m_cofactor_calls;
        return m_rw.get_derive().get_cached_cofactors(m_mode, r);
    }

    void view_witness::reset_ivl_cache() {
        for (auto& kv : m_ivl_cache)
            dealloc(kv.m_value);
        m_ivl_cache.reset();
        m_ivl_pin.reset();
    }

    view_witness::ivl_list const* view_witness::interval_cofactors(expr* r, expr* v0) {
        ivl_list* result = nullptr;
        if (m_ivl_cache.find(r, result))
            return result && result->ok ? result : nullptr;

        unsigned max_char = u().max_char();
        result = alloc(ivl_list);
        m_ivl_cache.insert(r, result);
        m_ivl_pin.push_back(r);

        struct transition {
            unsigned lo, hi;
            expr* target;
        };
        svector<transition> transitions;
        svector<unsigned> bounds;
        bounds.push_back(0);
        for (auto const& [guard, target] : derivative_cofactors(r)) {
            if (re().is_empty(target))
                continue;
            range_predicate* predicate = nullptr;
            if (!m_rp_cache.find(guard, predicate)) {
                predicate = m_rp_cache.fresh(max_char);
                if (!guard_to_range_predicate(u(), v0, guard, *predicate)) {
                    m_rp_cache.insert(guard, nullptr);
                    result->ok = false;
                    return nullptr;
                }
                m_rp_cache.insert(guard, predicate);
            }
            else if (!predicate) {
                result->ok = false;
                return nullptr;
            }
            m_ivl_pin.push_back(target);
            for (auto const& range : predicate->ranges()) {
                transitions.push_back({ range.first, range.second, target });
                bounds.push_back(range.first);
                if (range.second < max_char)
                    bounds.push_back(range.second + 1);
            }
        }
        if (transitions.empty())
            return result;

        std::sort(bounds.begin(), bounds.end());
        bounds.shrink(static_cast<unsigned>(std::unique(bounds.begin(), bounds.end()) - bounds.begin()));

        ptr_vector<expr> hits;
        for (unsigned i = 0; i < bounds.size(); ++i) {
            unsigned lo = bounds[i];
            unsigned hi = i + 1 < bounds.size() ? bounds[i + 1] - 1 : max_char;
            hits.reset();
            for (auto const& transition : transitions)
                if (transition.lo <= lo && lo <= transition.hi)
                    hits.push_back(transition.target);
            if (hits.empty())
                continue;
            if (!result->ranges.empty()) {
                ivl_range& previous = result->ranges.back();
                if (previous.hi + 1 == lo && previous.count == hits.size()) {
                    bool same = true;
                    for (unsigned j = 0; j < hits.size() && same; ++j)
                        same = result->targets[previous.first + j] == hits[j];
                    if (same) {
                        previous.hi = hi;
                        continue;
                    }
                }
            }
            result->ranges.push_back({ lo, hi, result->targets.size(), hits.size() });
            result->targets.append(hits.size(), hits.data());
        }
        return result;
    }

    lbool view_witness::product_nonempty(expr* var, view_vector const& input, expr_ref* witness_word) {
        m_failure = view_failure_reason::none;
        sort* elem_sort = nullptr;
        sort* seq_sort = var->get_sort();
        if (!u().is_seq(seq_sort, elem_sort)) {
            m_failure = view_failure_reason::unsupported;
            return l_undef;
        }

        view_vector views;
        dedup_views(input, views);
        unsigned n = views.size();
        if (n == 0) {
            if (witness_word)
                *witness_word = expr_ref(u().str.mk_empty(seq_sort), m);
            return l_true;
        }

        expr_ref var0(m.mk_var(0, elem_sort), m);
        ptr_vector<expr> work;
        std::unordered_set<key, key_hash> visited;
        key key_buffer(n);
        ptr_vector<expr> state;
        state.resize(n);
        ptr_vector<expr> current;
        current.resize(n);

        auto fill_key = [&](ptr_vector<expr> const& values) -> key const& {
            for (unsigned i = 0; i < n; ++i)
                key_buffer[i] = values[i]->get_id();
            return key_buffer;
        };

        bool undecided = false;
        auto is_accept = [&]() {
            for (unsigned i = 0; i < n; ++i) {
                if (views[i].m_target) {
                    if (state[i] != views[i].m_target)
                        return false;
                }
                else {
                    lbool nb = nullable(state[i]);
                    if (nb == l_true)
                        continue;
                    if (nb == l_false)
                        return false;
                    undecided = true;
                    return false;
                }
            }
            return true;
        };

        std::map<key, std::pair<key, expr*>> parent;
        key start_key(n);
        for (unsigned i = 0; i < n; ++i) {
            work.push_back(views[i].m_state);
            start_key[i] = views[i].m_state->get_id();
        }
        visited.insert(start_key);

        auto reconstruct = [&](key end_key) {
            ptr_vector<expr> elements;
            key k = end_key;
            while (k != start_key) {
                auto it = parent.find(k);
                if (it == parent.end())
                    break;
                elements.push_back(it->second.second);
                k = it->second.first;
            }
            expr_ref_vector units(m);
            for (unsigned i = elements.size(); i-- > 0; )
                units.push_back(u().str.mk_unit(elements[i]));
            return expr_ref(u().str.mk_concat(units.size(), units.data(), seq_sort), m);
        };

        svector<expr_ref_pair_vector const*> branches;
        branches.resize(n);
        key state_key;
        bool bail = false;
        uint64_t const inner_limit = 1u << 16;
        uint64_t inner_steps = 0;
        auto inner_step = [&]() {
            ++inner_steps;
            m_max_state_expansion = std::max(m_max_state_expansion, static_cast<unsigned>(inner_steps));
            if (inner_steps <= inner_limit)
                return false;
            m_failure = view_failure_reason::state_expansion;
            return true;
        };

        bool const sweep_ok = u().is_char(elem_sort);
        unsigned const max_char = sweep_ok ? u().max_char() : 0;
        svector<ivl_list const*> sweep_lists;
        svector<unsigned> sweep_cursors, sweep_odometer;
        sweep_lists.resize(n);
        sweep_cursors.resize(n);
        sweep_odometer.resize(n);

        auto sweep = [&]() {
            for (unsigned i = 0; i < n; ++i) {
                sweep_lists[i] = interval_cofactors(state[i], var0);
                if (!sweep_lists[i])
                    return false;
                if (sweep_lists[i]->ranges.empty())
                    return true;
                sweep_cursors[i] = 0;
            }
            uint64_t begin = 0;
            while (begin <= max_char) {
                if (inner_step()) {
                    bail = true;
                    return true;
                }
                uint64_t next = static_cast<uint64_t>(max_char) + 1;
                bool covered = true, done = false;
                for (unsigned i = 0; i < n; ++i) {
                    auto const& ranges = sweep_lists[i]->ranges;
                    unsigned& cursor = sweep_cursors[i];
                    while (cursor < ranges.size() && ranges[cursor].hi < begin)
                        ++cursor;
                    if (cursor == ranges.size()) {
                        done = true;
                        break;
                    }
                    if (ranges[cursor].lo > begin) {
                        covered = false;
                        next = std::min(next, static_cast<uint64_t>(ranges[cursor].lo));
                    }
                    else {
                        next = std::min(next, static_cast<uint64_t>(ranges[cursor].hi) + 1);
                    }
                }
                if (done)
                    break;
                if (covered) {
                    for (unsigned i = 0; i < n; ++i)
                        sweep_odometer[i] = 0;
                    while (true) {
                        if (inner_step()) {
                            bail = true;
                            return true;
                        }
                        for (unsigned i = 0; i < n; ++i) {
                            auto const& range = sweep_lists[i]->ranges[sweep_cursors[i]];
                            current[i] = sweep_lists[i]->targets[range.first + sweep_odometer[i]];
                        }
                        key const& child_key = fill_key(current);
                        if (!visited.contains(child_key)) {
                            visited.insert(child_key);
                            if (witness_word) {
                                expr* element = u().mk_char(static_cast<unsigned>(begin));
                                m_pin.push_back(element);
                                parent[child_key] = { state_key, element };
                            }
                            for (unsigned i = 0; i < n; ++i)
                                work.push_back(current[i]);
                        }
                        unsigned i = n;
                        while (i-- > 0) {
                            if (++sweep_odometer[i] <
                                sweep_lists[i]->ranges[sweep_cursors[i]].count)
                                break;
                            sweep_odometer[i] = 0;
                        }
                        if (i == UINT_MAX)
                            break;
                    }
                }
                begin = next;
            }
            return true;
        };

        std::function<void(unsigned, guard_set const&)> enumerate =
            [&](unsigned i, guard_set const& accumulated) {
                if (bail)
                    return;
                if (inner_step()) {
                    bail = true;
                    return;
                }
                if (i == n) {
                    key const& child_key = fill_key(current);
                    if (!visited.contains(child_key)) {
                        visited.insert(child_key);
                        if (witness_word) {
                            expr_ref element(m);
                            if (accumulated.eval(&element) == l_true) {
                                m_pin.push_back(element);
                                parent[child_key] = { state_key, element.get() };
                            }
                        }
                        for (unsigned j = 0; j < n; ++j)
                            work.push_back(current[j]);
                    }
                    return;
                }
                for (auto const& [guard, target] : *branches[i]) {
                    if (re().is_empty(target))
                        continue;
                    guard_set next = accumulated;
                    next.conjoin(guard);
                    lbool nonempty = next.eval(nullptr);
                    if (nonempty == l_undef) {
                        m_failure = view_failure_reason::guard;
                        bail = true;
                        return;
                    }
                    if (nonempty == l_false)
                        continue;
                    current[i] = target;
                    enumerate(i + 1, next);
                    if (bail)
                        return;
                }
            };

        while (!work.empty()) {
            if (checkpoint())
                return l_undef;
            ++m_states;
            inner_steps = 0;
            for (unsigned i = n; i-- > 0; ) {
                state[i] = work.back();
                work.pop_back();
            }
            if (is_accept()) {
                if (witness_word)
                    *witness_word = reconstruct(fill_key(state));
                return l_true;
            }
            if (undecided) {
                m_failure = view_failure_reason::nullability;
                return l_undef;
            }
            if (witness_word)
                state_key = fill_key(state);
            if (sweep_ok) {
                bool swept = sweep();
                if (bail)
                    return l_undef;
                if (swept)
                    continue;
            }
            for (unsigned i = 0; i < n; ++i)
                branches[i] = &derivative_cofactors(state[i]);
            guard_set top(m, u(), elem_sort, var0, &m_rp_cache);
            enumerate(0, top);
            if (bail)
                return l_undef;
        }
        return l_false;
    }

    void view_witness::minimize_core(expr* var, unsigned_vector const& indices) {
        unsigned_vector keep(indices);
        for (unsigned i = 0; i < keep.size(); ) {
            view_vector trial;
            for (unsigned j = 0; j < keep.size(); ++j)
                if (j != i)
                    trial.push_back(m_assertions[keep[j]].m_view);
            if (product_nonempty(var, trial) == l_false)
                keep.erase(keep.begin() + i);
            else
                ++i;
        }
        for (unsigned index : keep) {
            void* dependency = m_assertions[index].m_dependency;
            if (dependency && !m_core.contains(dependency))
                m_core.push_back(dependency);
        }
    }

    lbool view_witness::check() {
        m_core.reset();
        m_witnesses.reset();
        m_witness_pin.reset();
        m_failure = view_failure_reason::none;

        obj_map<expr, unsigned> group_ids;
        ptr_vector<expr> vars;
        vector<unsigned_vector> groups;
        for (unsigned i = 0; i < m_assertions.size(); ++i) {
            expr* var = m_assertions[i].m_var;
            unsigned group = 0;
            if (!group_ids.find(var, group)) {
                group = groups.size();
                group_ids.insert(var, group);
                vars.push_back(var);
                groups.push_back(unsigned_vector());
            }
            groups[group].push_back(i);
        }

        for (unsigned group = 0; group < groups.size(); ++group) {
            view_vector views;
            for (unsigned index : groups[group])
                views.push_back(m_assertions[index].m_view);
            signature sig = mk_signature(views);
            auto cached = m_product_cache.find(sig);
            lbool result = cached == m_product_cache.end() ? l_undef : cached->second;
            expr_ref witness(m);
            if (result != l_true || m_enable_witness)
                result = product_nonempty(vars[group], views, m_enable_witness ? &witness : nullptr);
            if (result == l_undef) {
                m_last_result = l_undef;
                return l_undef;
            }
            m_product_cache[sig] = result;
            if (result == l_false) {
                minimize_core(vars[group], groups[group]);
                m_last_result = l_false;
                return l_false;
            }
            if (m_enable_witness) {
                m_witness_pin.push_back(vars[group]);
                m_witness_pin.push_back(witness);
                m_witnesses.insert(vars[group], witness);
            }
        }
        m_last_result = l_true;
        return l_true;
    }

    expr_ref view_witness::materialize_witness(expr* x) {
        expr_ref result(m);
        if (!m_enable_witness || m_last_result != l_true)
            return result;
        expr* witness = nullptr;
        if (m_witnesses.find(x, witness))
            return expr_ref(witness, m);
        sort* elem_sort = nullptr;
        if (u().is_seq(x->get_sort(), elem_sort))
            result = u().str.mk_empty(x->get_sort());
        return result;
    }

    void view_witness::reset_cache() {
        reset_ivl_cache();
        m_nullable_cache.reset();
        m_product_cache.clear();
        m_pin.reset();
        m_rp_cache.maybe_reset(1u << 16);
    }
}
