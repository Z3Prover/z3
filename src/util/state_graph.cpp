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
#include <sstream>

void state_graph::add_state_core(state s) {
    STRACE("state_graph", tout << "add(" << s << ") ";);
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
    STRACE("state_graph", tout << "del(" << s << ") ";);
    SASSERT(m_seen.contains(s));
    SASSERT(!m_state_ufind.is_root(s));
    SASSERT(m_unknown.contains(s));
    m_targets.remove(s);
    m_sources.remove(s);
    m_sources_maybecycle.remove(s);
    m_unknown.remove(s);
}

void state_graph::mark_unknown_core(state s) {
    STRACE("state_graph", tout << "unk(" << s << ") ";);
    SASSERT(m_state_ufind.is_root(s));
    SASSERT(m_unexplored.contains(s));
    m_unexplored.remove(s);
    m_unknown.insert(s);
}
void state_graph::mark_live_core(state s) {
    STRACE("state_graph", tout << "live(" << s << ") ";);
    SASSERT(m_state_ufind.is_root(s));
    SASSERT(m_unknown.contains(s));
    m_unknown.remove(s);
    m_live.insert(s);
}
void state_graph::mark_dead_core(state s) {
    STRACE("state_graph", tout << "dead(" << s << ") ";);
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
    STRACE("state_graph", tout << "add(" << s1 << "," << s2 << ","
                               << (maybecycle ? "y" : "n") << ") ";);
    SASSERT(m_state_ufind.is_root(s1));
    SASSERT(m_state_ufind.is_root(s2));
    if (s1 == s2) return;
    if (!m_targets[s1].contains(s2)) {
        // add new edge
        m_targets[s1].insert(s2);
        m_sources[s2].insert(s1);
        if (maybecycle) m_sources_maybecycle[s2].insert(s1);
    }
    else if (!maybecycle && m_sources_maybecycle[s2].contains(s1)) {
        // update existing edge
        m_sources_maybecycle[s2].remove(s1);
    }
}
void state_graph::remove_edge_core(state s1, state s2) {
    STRACE("state_graph", tout << "del(" << s1 << "," << s2 << ") ";);
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
    STRACE("state_graph", tout << "merge(" << s1 << "," << s2 << ") ";);
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
    vector<state> to_search;
    to_search.push_back(s);
    while (to_search.size() > 0) {
        state x = to_search.back();
        to_search.pop_back();
        SASSERT(m_live.contains(x) || m_unknown.contains(x));
        if (m_live.contains(x)) continue;
        mark_live_core(x);
        for (auto x_from: m_sources[x]) {
            to_search.push_back(x_from);
        }
    }
}

/*
    Check if all targets of a state are dead.
    Precondition: s is unknown
*/
bool state_graph::all_targets_dead(state s) {
    SASSERT(m_unknown.contains(s));
    for (auto s_to: m_targets[s]) {
        // unknown pointing to live should have been marked as live!
        SASSERT(!m_live.contains(s_to));
        if (m_unknown.contains(s_to) || m_unexplored.contains(s_to))
            return false;
    }
    return true;
}
/*
    Check if s is now known to be dead. If so, mark and recurse
    on all states into s.
    Precondition: s is live, dead, or unknown
*/
void state_graph::mark_dead_recursive(state s) {
    SASSERT(m_live.contains(s) || m_dead.contains(s) || m_unknown.contains(s));
    vector<state> to_search;
    to_search.push_back(s);
    while (to_search.size() > 0) {
        state x = to_search.back();
        to_search.pop_back();
        if (!m_unknown.contains(x)) continue;
        if (!all_targets_dead(x)) continue;
        // x is unknown and all targets from x are dead
        mark_dead_core(x);
        for (auto x_from: m_sources[x]) {
            to_search.push_back(x_from);
        }
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
    STRACE("state_graph", tout << "[state_graph] adding state " << s << ": ";);
    add_state_core(s);
    CASSERT("state_graph", write_dgml());
    CASSERT("state_graph", write_dot());
    CASSERT("state_graph", check_invariant());
    STRACE("state_graph", tout << std::endl;);
}
void state_graph::mark_live(state s) {
    STRACE("state_graph", tout << "[state_graph] marking live " << s << ": ";);
    SASSERT(m_unexplored.contains(s) || m_live.contains(s));
    SASSERT(m_state_ufind.is_root(s));
    if (m_unexplored.contains(s)) mark_unknown_core(s);
    mark_live_recursive(s);
    CASSERT("state_graph", write_dgml());
    CASSERT("state_graph", write_dot());
    CASSERT("state_graph", check_invariant());
    STRACE("state_graph", tout << std::endl;);
}
void state_graph::add_edge(state s1, state s2, bool maybecycle) {
    STRACE("state_graph", tout << "[state_graph] adding edge "
                               << s1 << "->" << s2 << ": ";);
    SASSERT(m_unexplored.contains(s1) || m_live.contains(s1));
    SASSERT(m_state_ufind.is_root(s1));
    SASSERT(m_seen.contains(s2));
    s2 = m_state_ufind.find(s2);
    add_edge_core(s1, s2, maybecycle);
    if (m_live.contains(s2)) mark_live(s1);
    CASSERT("state_graph", write_dgml());
    CASSERT("state_graph", write_dot());
    CASSERT("state_graph", check_invariant());
    STRACE("state_graph", tout << std::endl;);
}
void state_graph::mark_done(state s) {
    SASSERT(m_unexplored.contains(s) || m_live.contains(s));
    SASSERT(m_state_ufind.is_root(s));
    if (m_live.contains(s)) return;
    STRACE("state_graph", tout << "[state_graph] marking done " << s << ": ";);
    if (m_unexplored.contains(s)) mark_unknown_core(s);
    s = merge_all_cycles(s);
    mark_dead_recursive(s); // check if dead
    CASSERT("state_graph", write_dgml());
    CASSERT("state_graph", write_dot());
    CASSERT("state_graph", check_invariant());
    STRACE("state_graph", tout << std::endl;);
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
    for (auto s : m_seen) {
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
    for (auto s1 : m_seen) {
        if (m_state_ufind.is_root(s1)) {
            o << "  " << s1 << " -> " << m_targets[s1] << std::endl;
        }
    }
    o << "---------------------------------" << std::endl;

    return o;
}

#ifdef Z3DEBUG
/*
    Class invariants check (and associated auxiliary functions)

    check_invariant performs a sequence of SASSERT assertions,
    then always returns true.
*/
bool state_graph::is_subset(state_set set1, state_set set2) const {
    for (auto s1: set1) {
        if (!set2.contains(s1)) return false;
    }
    return true;
}
bool state_graph::is_disjoint(state_set set1, state_set set2) const {
    for (auto s1: set1) {
        if (set2.contains(s1)) return false;
    }
    return true;
}
#define ASSERT_FOR_ALL_STATES(STATESET, COND) { \
    for (auto s: STATESET) { SASSERT(COND); }} ((void) 0)
#define ASSERT_FOR_ALL_EDGES(EDGEREL, COND) { \
    for (auto e: (EDGEREL)) { \
        state s1 = e.m_key; for (auto s2: e.m_value) { SASSERT(COND); } \
    }} ((void) 0)
bool state_graph::check_invariant() const {
    // Check state invariants
    SASSERT(is_subset(m_live, m_seen));
    SASSERT(is_subset(m_dead, m_seen));
    SASSERT(is_subset(m_unknown, m_seen));
    SASSERT(is_subset(m_unexplored, m_seen));
    SASSERT(is_disjoint(m_live, m_dead));
    SASSERT(is_disjoint(m_live, m_unknown));
    SASSERT(is_disjoint(m_live, m_unexplored));
    SASSERT(is_disjoint(m_dead, m_unknown));
    SASSERT(is_disjoint(m_dead, m_unexplored));
    SASSERT(is_disjoint(m_unknown, m_unexplored));
    ASSERT_FOR_ALL_STATES(m_seen, s < m_state_ufind.get_num_vars());
    ASSERT_FOR_ALL_STATES(m_seen,
        (m_state_ufind.is_root(s) ==
         (m_live.contains(s) || m_dead.contains(s) ||
          m_unknown.contains(s) || m_unexplored.contains(s))));
    // Check edge invariants
    ASSERT_FOR_ALL_EDGES(m_sources_maybecycle, m_sources[s1].contains(s2));
    ASSERT_FOR_ALL_EDGES(m_sources, m_targets[s2].contains(s1));
    ASSERT_FOR_ALL_EDGES(m_targets, m_sources[s2].contains(s1));
    ASSERT_FOR_ALL_EDGES(m_targets,
        m_state_ufind.is_root(s1) && m_state_ufind.is_root(s2));
    ASSERT_FOR_ALL_EDGES(m_targets, s1 != s2);
    // Check relationship between states and edges
    ASSERT_FOR_ALL_EDGES(m_targets,
        !m_live.contains(s2) || m_live.contains(s1));
    ASSERT_FOR_ALL_STATES(m_dead, is_subset(m_targets[s], m_dead));
    ASSERT_FOR_ALL_STATES(m_unknown, !is_subset(m_targets[s], m_dead));
    // For the "no cycles" of unknown states on maybecycle edges,
    // we only do a partial check for cycles of size 2
    ASSERT_FOR_ALL_EDGES(m_sources_maybecycle,
        !(m_unknown.contains(s1) && m_unknown.contains(s2) &&
          m_sources_maybecycle[s2].contains(s1)));

    STRACE("state_graph", tout << "(invariant passed) ";);
    return true;
}

/*
    Output the whole state graph in dgml format into the file '.z3-state-graph.dgml'
 */
bool state_graph::write_dgml() {
    std::ofstream dgml(".z3-state-graph.dgml");
    dgml << "<?xml version=\"1.0\" encoding=\"utf-8\"?>" << std::endl
        << "<DirectedGraph xmlns=\"http://schemas.microsoft.com/vs/2009/dgml\" GraphDirection=\"TopToBottom\">" << std::endl
        << "<Nodes>" << std::endl;
    for (auto s : m_seen) {
        if (m_state_ufind.is_root(s)) {
            dgml << "<Node Id=\"" << s << "\" Label=\"";
            auto r = s;
            dgml << r;
            do {
                if (r != s)
                    dgml << "," << r;
                r = m_state_ufind.next(r);
            } while (r != s);
            r = s;
            dgml << "\" Value_of_" << r << "=\"";
            m_state_pp.pp_state_label(dgml, r) << "\"";
            do {
                if (r != s) {
                    dgml << " Value_of_" << r << "=\"";
                    m_state_pp.pp_state_label(dgml, r) << "\"";
                }
                r = m_state_ufind.next(r);
            } while (r != s);
            dgml << " Category=\"State\">" << std::endl;
            if (m_dead.contains(s))
                dgml << "<Category Ref=\"Dead\"/>" << std::endl;
            if (m_live.contains(s))
                dgml << "<Category Ref=\"Alive\"/>" << std::endl;
            if (m_unexplored.contains(s))
                dgml << "<Category Ref=\"Unexplored\"/>" << std::endl;
            dgml << "</Node>" << std::endl;
        }
    }
    dgml << "</Nodes>" << std::endl;
    dgml << "<Links>" << std::endl;
    for (auto s : m_seen) {
        if (m_state_ufind.is_root(s))
            for (auto t : m_targets[s]) {
                dgml << "<Link Source=\"" << s << "\" Target=\"" << t << "\" Category=\"Transition\">" << std::endl;
                if (!m_sources_maybecycle[t].contains(s))
                    dgml << "<Category Ref=\"Noncycle\"/>" << std::endl;
                dgml << "</Link>" << std::endl;
            }
    }
    dgml << "</Links>" << std::endl;
    dgml << "<Categories>" << std::endl
        << "<Category Id=\"Alive\" Label=\"Alive\" IsTag=\"True\"/>" << std::endl
        << "<Category Id=\"Dead\" Label=\"Dead\" IsTag=\"True\"/>" << std::endl
        << "<Category Id=\"Unexplored\" Label=\"Unexplored\" IsTag=\"True\"/>" << std::endl
        << "<Category Id=\"Transition\" Label=\"Transition\" IsTag=\"True\"/>" << std::endl
        << "<Category Id=\"State\" Label=\"State\" IsTag=\"True\"/>" << std::endl
        << "<Category Id=\"Noncycle\" Label=\"Noncycle Transition\" IsTag=\"True\"/>" << std::endl
        << "</Categories>" << std::endl
        << "<Styles>" << std::endl
        << "<Style TargetType=\"Node\" GroupLabel=\"Alive\" ValueLabel=\"True\">" << std::endl
        << "<Condition Expression=\"HasCategory('Alive')\"/>" << std::endl
        << "<Setter Property=\"Background\" Value=\"lightgreen\"/>" << std::endl
        << "</Style>" << std::endl
        << "<Style TargetType=\"Node\" GroupLabel=\"Dead\" ValueLabel=\"True\">" << std::endl
        << "<Condition Expression=\"HasCategory('Dead')\"/>" << std::endl
        << "<Setter Property=\"Background\" Value=\"tomato\"/>" << std::endl
        << "<Setter Property=\"Stroke\" Value=\"tomato\"/>" << std::endl
        << "</Style>" << std::endl
        << "<Style TargetType=\"Node\" GroupLabel=\"Unexplored\" ValueLabel=\"True\">" << std::endl
        << "<Condition Expression=\"HasCategory('Unexplored')\"/>" << std::endl
        << "<Setter Property=\"StrokeDashArray\" Value=\"8 8\"/>" << std::endl
        << "</Style>" << std::endl
        << "<Style TargetType=\"Node\" GroupLabel=\"State\" ValueLabel=\"True\">" << std::endl
        << "<Condition Expression=\"HasCategory('State')\"/>" << std::endl
        << "<Setter Property=\"Stroke\" Value=\"black\"/>" << std::endl
        << "<Setter Property=\"Background\" Value=\"white\"/>" << std::endl
        << "<Setter Property=\"MinWidth\" Value=\"0\"/>" << std::endl
        << "</Style>" << std::endl
        << "<Style TargetType=\"Link\" GroupLabel=\"Transition\" ValueLabel=\"True\">" << std::endl
        << "<Condition Expression=\"HasCategory('Transition')\"/>" << std::endl
        << "<Setter Property=\"Stroke\" Value=\"black\"/>" << std::endl
        << "</Style>" << std::endl
        << "<Style TargetType=\"Link\" GroupLabel=\"Noncycle\" ValueLabel=\"True\">" << std::endl
        << "<Condition Expression=\"HasCategory('Noncycle')\"/>" << std::endl
        << "<Setter Property=\"StrokeThickness\" Value=\"4\"/>" << std::endl
        << "</Style>" << std::endl
        << "</Styles>" << std::endl
        << "</DirectedGraph>" << std::endl;
    dgml.close();
    return true;
}

/*
    Output the whole state graph in dot format into the file '.z3-state-graph.dot'
 */
bool state_graph::write_dot() {
    std::ofstream dot(".z3-state-graph.dot");
    dot << "digraph \"state_graph\" {" << std::endl
        << "rankdir=TB" << std::endl
        << "node [peripheries=1,style=filled,fillcolor=white,fontsize=24]" << std::endl;
    for (auto s : m_seen) {
        if (m_state_ufind.is_root(s)) {
            dot << s << " [label=\"";
            auto r = s;
            dot << r;
            do {
                if (r != s)
                    dot << "," << r;
                r = m_state_ufind.next(r);
            } while (r != s);
            dot << "\"";
            if (m_unexplored.contains(s))
                dot << ",style=\"dashed,filled\"";
            if (m_dead.contains(s))
                dot << ",color=tomato,fillcolor=tomato";
            if (m_live.contains(s))
                dot << ",fillcolor=green";
            dot << "]" << std::endl;
        }
    }
    for (auto s : m_seen) {
        if (m_state_ufind.is_root(s))
            for (auto t : m_targets[s]) {
                dot << s << " -> " << t;
                if (!m_sources_maybecycle[t].contains(s))
                    dot << "[style=bold]";
                dot << std::endl;
            }
    }
    dot << "}" << std::endl;
    dot.close();
    return true;
}
#endif
