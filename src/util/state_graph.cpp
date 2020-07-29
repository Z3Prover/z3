/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    state_graph.cpp

Abstract:

    Data structure for incrementally tracking "live" and "dead" states in an
    abstract transition system.

Author:

    Caleb Stanford (calebstanford-msr / cdstanford) 2020-7

--*/

#include "state_graph.h"

void state_graph::add_state_core(state s) {
    STRACE("seq_regex_brief", tout << "add(" << s << ") ";);
    SASSERT(!m_seen.contains(s));
    // Ensure corresponding var in union find structure
    while (s >= m_state_ufind.get_num_vars()) {
        m_state_ufind.mk_var();
    }
    // Initialize as unvisited
    m_seen.insert(s);
    m_unexplored.insert(s);
    m_targets.insert(s, state_set());
    m_sources.insert(s, state_set());
    m_sources_maybecycle.insert(s, state_set());
}
void state_graph::remove_state_core(state s) {
    // This is a partial deletion -- the state is still seen and can't be
    // added again later.
    // The state should be unknown, and all edges to or from the state
    // should already have been renamed.
    STRACE("seq_regex_brief", tout << "del(" << s << ") ";);
    SASSERT(m_seen.contains(s));
    SASSERT(!m_state_ufind.is_root(s));
    SASSERT(m_unknown.contains(s));
    m_targets.remove(s);
    m_sources.remove(s);
    m_sources_maybecycle.remove(s);
    m_unknown.remove(s);
}

void state_graph::mark_unknown_core(state s) {
    STRACE("seq_regex_brief", tout << "unk(" << s << ") ";);
    SASSERT(m_state_ufind.is_root(s));
    SASSERT(m_unexplored.contains(s));
    m_unexplored.remove(s);
    m_unknown.insert(s);
}
void state_graph::mark_live_core(state s) {
    STRACE("seq_regex_brief", tout << "live(" << s << ") ";);
    SASSERT(m_state_ufind.is_root(s));
    SASSERT(m_unknown.contains(s));
    m_unknown.remove(s);
    m_live.insert(s);
}
void state_graph::mark_dead_core(state s) {
    STRACE("seq_regex_brief", tout << "dead(" << s << ") ";);
    SASSERT(m_state_ufind.is_root(s));
    SASSERT(m_unknown.contains(s));
    m_unknown.remove(s);
    m_dead.insert(s);
}

/*
    Add edge to the graph.
    - If the annotation 'maybecycle' is false, then the user is sure
      that this edge will never be part of a cycle.
    - May already exist, in which case maybecycle = false overrides
      maybecycle = true.
*/
void state_graph::add_edge_core(state s1, state s2, bool maybecycle) {
    STRACE("seq_regex_brief", tout << "add(" << s1 << "," << s2 << ","
                                   << (maybecycle ? "y" : "n") << ") ";);
    SASSERT(m_state_ufind.is_root(s1));
    SASSERT(m_state_ufind.is_root(s2));
    if (s1 == s2) return;
    if (!m_targets[s1].contains(s2)) {
        // add new edge
        STRACE("seq_regex_debug", tout << std::endl << "  DEBUG: new edge! ";);
        m_targets[s1].insert(s2);
        m_sources[s2].insert(s1);
        if (maybecycle) m_sources_maybecycle[s2].insert(s1);
    }
    else if (!maybecycle && m_sources_maybecycle[s2].contains(s1)) {
        // update existing edge
        STRACE("seq_regex_debug", tout << std::endl << "  DEBUG: update edge! ";);
        m_sources_maybecycle[s2].remove(s1);
    }
}
void state_graph::remove_edge_core(state s1, state s2) {
    SASSERT(m_targets[s1].contains(s2));
    SASSERT(m_sources[s2].contains(s1));
    m_targets[s1].remove(s2);
    m_sources[s2].remove(s1);
    m_sources_maybecycle[s2].remove(s1);
}
void state_graph::rename_edge_core(state old1, state old2,
                                   state new1, state new2) {
    SASSERT(m_targets[old1].contains(old2));
    SASSERT(m_sources[old2].contains(old1));
    bool maybecycle = m_sources_maybecycle[old2].contains(old1);
    remove_edge_core(old1, old2);
    add_edge_core(new1, new2, maybecycle);
}

/*
    Merge two states or more generally a set of states into one,
    returning the new state. Also merges associated edges.

    Preconditions:
    - The set should be nonempty
    - Every state in the set should be unknown
    - Each state should currently exist
    - If passing a set of states by reference, it should not be a set
      from the edge relations, as merging states modifies edge relations.
*/
auto state_graph::merge_states(state s1, state s2) -> state {
    SASSERT(m_state_ufind.is_root(s1));
    SASSERT(m_state_ufind.is_root(s2));
    SASSERT(m_unknown.contains(s1));
    SASSERT(m_unknown.contains(s2));
    STRACE("seq_regex_brief", tout << "merge(" << s1 << "," << s2 << ") ";);
    m_state_ufind.merge(s1, s2);
    if (m_state_ufind.is_root(s2)) std::swap(s1, s2);
    // rename s2 to s1 in edges
    for (auto s_to: m_targets[s2]) {
        rename_edge_core(s2, s_to, s1, s_to);
    }
    for (auto s_from: m_sources[s2]) {
        rename_edge_core(s_from, s2, s_from, s1);
    }
    remove_state_core(s2);
    return s1;
}
auto state_graph::merge_states(state_set& s_set) -> state {
    SASSERT(s_set.num_elems() > 0);
    state prev_s = 0; // initialization here optional
    bool first_iter = true;
    for (auto s: s_set) {
        if (first_iter) {
            prev_s = s;
            first_iter = false;
            continue;
        }
        prev_s = merge_states(prev_s, s);
    }
    return prev_s;
}

/*
    If s is not live, mark it, and recurse on all states into s
    Precondition: s is live or unknown
*/
void state_graph::mark_live_recursive(state s) {
    SASSERT(m_live.contains(s) || m_unknown.contains(s));
    STRACE("seq_regex_debug", tout
        << std::endl << "  DEBUG: mark live recursive: " << s << " ";);
    if (m_live.contains(s)) return;
    mark_live_core(s);
    for (auto s_from: m_sources[s]) {
        mark_live_recursive(s_from);
    }
}

/*
    Check if s is now known to be dead. If so, mark and recurse
    on all states into s.
    Precondition: s is live, dead, or unknown
*/
void state_graph::mark_dead_recursive(state s) {
    SASSERT(m_live.contains(s) || m_dead.contains(s) ||
            m_unknown.contains(s));
    STRACE("seq_regex_debug", tout
        << std::endl << "  DEBUG: mark dead recursive: " << s << " ";);
    if (!m_unknown.contains(s)) return;
    for (auto s_to: m_targets[s]) {
        // unknown pointing to live should have been marked as live!
        SASSERT(!m_live.contains(s_to));
        if (m_unknown.contains(s_to) || m_unexplored.contains(s_to)) return;
    }
    // all states from s are dead
    mark_dead_core(s);
    for (auto s_from: m_sources[s]) {
        mark_dead_recursive(s_from);
    }
}

/*
    Merge all cycles of unknown states containing s into one state.
    Return the new state
    Precondition: s is unknown.
*/
auto state_graph::merge_all_cycles(state s) -> state {
    SASSERT(m_unknown.contains(s));
    // Visit states in a DFS backwards from s
    state_set visited;  // all backwards edges pushed
    state_set resolved; // known in SCC or not
    state_set scc;      // known in SCC
    resolved.insert(s);
    scc.insert(s);
    vector<state> to_search;
    to_search.push_back(s);
    while (to_search.size() > 0) {
        state x = to_search.back();
        if (!visited.contains(x)) {
            visited.insert(x);
            // recurse backwards only on maybecycle edges
            // and only on unknown states
            for (auto y: m_sources_maybecycle[x]) {
                if (m_unknown.contains(y))
                    to_search.push_back(y);
            }
        }
        else if (!resolved.contains(x)) {
            resolved.insert(x);
            to_search.pop_back();
            // determine in SCC or not
            for (auto y: m_sources_maybecycle[x]) {
                if (scc.contains(y)) {
                    scc.insert(x);
                    break;
                }
            }
        }
        else {
            to_search.pop_back();
        }
    }
    // scc is the union of all cycles containing s
    return merge_states(scc);
}

/*
    Exposed methods
*/

void state_graph::add_state(state s) {
    if (m_seen.contains(s)) return;
    add_state_core(s);
}
void state_graph::mark_live(state s) {
    SASSERT(m_unexplored.contains(s) || m_live.contains(s));
    SASSERT(m_state_ufind.is_root(s));
    if (m_unexplored.contains(s)) mark_unknown_core(s);
    mark_live_recursive(s);
}
void state_graph::add_edge(state s1, state s2, bool maybecycle) {
    SASSERT(m_unexplored.contains(s1) || m_live.contains(s1));
    SASSERT(m_state_ufind.is_root(s1));
    SASSERT(m_seen.contains(s2));
    s2 = m_state_ufind.find(s2);
    add_edge_core(s1, s2, maybecycle);
    if (m_live.contains(s2)) mark_live(s1);
}
void state_graph::mark_done(state s) {
    SASSERT(m_unexplored.contains(s) || m_live.contains(s));
    SASSERT(m_state_ufind.is_root(s));
    if (m_live.contains(s)) return;
    if (m_unexplored.contains(s)) mark_unknown_core(s);
    s = merge_all_cycles(s);
    // check if dead
    mark_dead_recursive(s);
    STRACE("seq_regex_brief", tout << "done(" << s << ") ";);
}

unsigned state_graph::get_size() const {
    return m_state_ufind.get_num_vars();
}

bool state_graph::is_seen(state s) const {
    return m_seen.contains(s);
}
bool state_graph::is_live(state s) const {
    return m_live.contains(m_state_ufind.find(s));
}
bool state_graph::is_dead(state s) const {
    return m_dead.contains(m_state_ufind.find(s));
}
bool state_graph::is_done(state s) const {
    return m_seen.contains(s) && !m_unexplored.contains(m_state_ufind.find(s));
}

/*
    Pretty printing
*/
std::ostream& state_graph::display(std::ostream& o) const {
    o << "---------- State Graph ----------" << std::endl
      << "Seen:";
    for (auto s: m_seen) {
        o << " " << s;
        state s_root = m_state_ufind.find(s);
        if (s_root != s)
            o << "(=" << s_root << ")";
    }
    o << std::endl
      << "Live:" << m_live << std::endl
      << "Dead:" << m_dead << std::endl
      << "Unknown:" << m_unknown << std::endl
      << "Unexplored:" << m_unexplored << std::endl
      << "Edges:" << std::endl;
    for (auto s1: m_seen) {
        if (m_state_ufind.is_root(s1)) {
            o << "  " << s1 << " -> " << m_targets[s1] << std::endl;
        }
    }
    o << "---------------------------------" << std::endl;

    return o;
}
