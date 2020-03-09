/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    diff_logic.h

Abstract:

    Basic support for difference logic

Author:

    Leonardo de Moura (leonardo) 2006-11-21.

Revision History:

--*/
#ifndef DIFF_LOGIC_H_
#define DIFF_LOGIC_H_

#include "util/vector.h"
#include "util/heap.h"
#include "util/statistics.h"
#include "util/trace.h"
#include "util/warning.h"
#include "util/uint_set.h"
#include<deque>

typedef int dl_var;

typedef enum {
    DL_UNMARKED = 0, // Node/Variable was not yet found in the forward/backward search.
    DL_FOUND,        // Node/Variable was found but not yet processed.
    DL_PROCESSED     // Node/Variable was found and processed in the forward/backward search/
} dl_search_mark;

typedef enum {
    DL_PROP_UNMARKED   = 0,
    DL_PROP_IRRELEVANT = 1,
    DL_PROP_RELEVANT   = 2,
    DL_PROP_PROCESSED_RELEVANT   = 3,
    DL_PROP_PROCESSED_IRRELEVANT = 4
} dl_prop_search_mark ;

template<typename Ext>
class dl_edge {
    typedef typename Ext::numeral     numeral;
    typedef typename Ext::explanation explanation;
    dl_var      m_source;
    dl_var      m_target;
    numeral     m_weight;
    unsigned    m_timestamp;  
    explanation m_explanation;
    bool        m_enabled;
public:

    dl_edge(dl_var s, dl_var t, const numeral & w, unsigned ts, const explanation & ex):
        m_source(s),
        m_target(t),
        m_weight(w),
        m_timestamp(ts), 
        m_explanation(ex),
        m_enabled(false) {
    }

    dl_var get_source() const {
        return m_source;
    }

    dl_var get_target() const {
        return m_target;
    }

    const numeral & get_weight() const {
        return m_weight;
    }

    const explanation & get_explanation() const {
        return m_explanation;
    }
    
    unsigned get_timestamp() const { 
        return m_timestamp;
    }

    bool is_enabled() const {
        return m_enabled;
    }

    void enable(unsigned timestamp) {
        SASSERT(!m_enabled);
        m_timestamp = timestamp;
        m_enabled = true;
    }

    void disable() {
        m_enabled = false;
    }

};

// Functor for comparing difference logic variables.
// This functor is used to implement Dijkstra algorithm (i.e., Heap).
template<typename Ext>
class dl_var_lt {
    typedef typename Ext::numeral numeral;
    vector<numeral> & m_values;
public:
    dl_var_lt(vector<numeral> & values):
        m_values(values) {
    }

    bool operator()(dl_var v1, dl_var v2) const {
        return m_values[v1] < m_values[v2];
    }
};

typedef int   edge_id;
const edge_id null_edge_id = -1;

template<typename Ext>
class dl_graph {
    struct stats {
        unsigned m_propagation_cost;
        unsigned m_implied_literal_cost;
        unsigned m_num_implied_literals;
        unsigned m_num_helpful_implied_literals;
        unsigned m_num_relax;
        void reset() {
            m_propagation_cost     = 0;
            m_implied_literal_cost = 0;
            m_num_implied_literals = 0;
            m_num_helpful_implied_literals = 0;
            m_num_relax = 0;
        }
        stats() { reset(); }
        void collect_statistics(::statistics& st) const {
            st.update("dl prop steps", m_propagation_cost);
            st.update("dl impl steps", m_implied_literal_cost);
            st.update("dl impl lits",  m_num_implied_literals);
            st.update("dl impl conf lits", m_num_helpful_implied_literals);
            st.update("dl bound relax", m_num_relax);
        }
    };
    stats m_stats;
    typedef typename Ext::numeral     numeral;
    typedef typename Ext::explanation explanation;
    typedef vector<numeral> assignment;
    typedef dl_edge<Ext>    edge;
    typedef vector<edge>    edges;
    
    class assignment_trail {
        dl_var  m_var;
        numeral m_old_value;
    public:
        assignment_trail(dl_var v, const numeral & val):
            m_var(v),
            m_old_value(val) {
        }
        
        dl_var get_var() const {
            return m_var;
        }

        const numeral & get_old_value() const {
            return m_old_value;
        }
    };

    typedef vector<assignment_trail> assignment_stack;

    assignment              m_assignment;       // per var
    assignment_stack        m_assignment_stack; // temporary stack for restoring the assignment
    edges                   m_edges;
    
    typedef int_vector      edge_id_vector;
    typedef int_vector      dl_var_vector;
    
    vector<edge_id_vector>  m_out_edges;  // per var
    vector<edge_id_vector>  m_in_edges;   // per var

    struct scope {
        unsigned m_edges_lim;
        unsigned m_enabled_edges_lim;
        unsigned m_old_timestamp;
        scope(unsigned e, unsigned enabled, unsigned t):
            m_edges_lim(e),
            m_enabled_edges_lim(enabled),
            m_old_timestamp(t) {
        }
    };

    svector<scope>          m_trail_stack;

    // forward reachability
    vector<numeral>         m_gamma;    // per var
    svector<char>           m_mark;     // per var
    edge_id_vector          m_parent;   // per var
    dl_var_vector           m_visited; 
    typedef heap<dl_var_lt<Ext> > var_heap;
    var_heap                m_heap;

    unsigned                m_timestamp;
    unsigned                m_last_enabled_edge;
    edge_id_vector          m_enabled_edges;

    // SCC for cheap equality propagation --
    svector<char>           m_unfinished_set; // per var
    int_vector              m_dfs_time;       // per var
    dl_var_vector           m_roots;     
    dl_var_vector           m_unfinished;
    int                     m_next_dfs_time;
    int                     m_next_scc_id;
    // -------------------------------------

    // activity vector for edges.
    svector<unsigned>       m_activity;


    bool check_invariant() const {
#ifdef Z3DEBUG
        SASSERT(m_assignment.size() == m_gamma.size());
        SASSERT(m_assignment.size() == m_mark.size());
        SASSERT(m_assignment.size() == m_parent.size());
        SASSERT(m_assignment.size() <= m_heap.get_bounds());
        SASSERT(m_in_edges.size() == m_out_edges.size());
        int n = m_out_edges.size();
        for (dl_var id = 0; id < n; id++) {
            const edge_id_vector & e_ids = m_out_edges[id];
            for (edge_id e_id : e_ids) {
                SASSERT(static_cast<unsigned>(e_id) <= m_edges.size());
                const edge & e = m_edges[e_id];
                SASSERT(e.get_source() == id);
            }
        }
        for (dl_var id = 0; id < n; id++) {
            const edge_id_vector & e_ids = m_in_edges[id];
            for (edge_id e_id : e_ids) {
                SASSERT(static_cast<unsigned>(e_id) <= m_edges.size());
                const edge & e = m_edges[e_id];
                SASSERT(e.get_target() == id);
            }
        }
        n = m_edges.size();
        for (int i = 0; i < n; i++) {
            const edge & e = m_edges[i];
            SASSERT(std::find(m_out_edges[e.get_source()].begin(), m_out_edges[e.get_source()].end(), i)
                    != m_out_edges[e.get_source()].end());
            SASSERT(std::find(m_in_edges[e.get_target()].begin(), m_in_edges[e.get_target()].end(), i)
                    != m_in_edges[e.get_target()].end());
        }
#endif
        return true;
    }

    
    bool is_feasible(const edge & e) const {
        return 
            !e.is_enabled() || 
            m_assignment[e.get_target()] - m_assignment[e.get_source()] <= e.get_weight();
    }

public:
    // An assignment is feasible if all edges are feasible.
    bool is_feasible() const {
#ifdef Z3DEBUG
        for (unsigned i = 0; i < m_edges.size(); ++i) {
            if (!is_feasible(m_edges[i])) {
                return false;
            }
        }
#endif
        return true;
    }

    unsigned get_num_edges() const { return m_edges.size(); }

    unsigned get_num_nodes() const { return m_out_edges.size(); }

    dl_var get_source(edge_id id) const {  return m_edges[id].get_source(); }

    dl_var get_target(edge_id id) const {  return m_edges[id].get_target(); }

    explanation const & get_explanation(edge_id id) const { return m_edges[id].get_explanation(); }

    bool is_enabled(edge_id id) const { return m_edges[id].is_enabled(); }

    bool is_feasible(edge_id id) const { return is_feasible(m_edges[id]); }

    numeral const& get_weight(edge_id id) const { return m_edges[id].get_weight(); }

    edge_id_vector const& get_out_edges(dl_var v) const { return m_out_edges[v]; }

    edge_id_vector const& get_in_edges(dl_var v) const { return m_in_edges[v]; }

private:
    // An assignment is almost feasible if all but edge with idt edge are feasible.
    bool is_almost_feasible(edge_id id) const {
#ifdef Z3DEBUG
        for (unsigned i = 0; i < m_edges.size(); ++i) {
            if (id != static_cast<edge_id>(i) && !is_feasible(m_edges[i])) {
                return false;
            }
        }
#endif
        return true;
    }


    // Restore the assignment using the information in m_assignment_stack.
    // This method is called when make_feasible fails.
    void undo_assignments() {
        typename assignment_stack::iterator it    = m_assignment_stack.end();
        typename assignment_stack::iterator begin = m_assignment_stack.begin();
        while (it != begin) {
            --it;
            TRACE("dl_bug", tout << "undo assignment: " << it->get_var() << " " << it->get_old_value() << "\n";);
            m_assignment[it->get_var()] = it->get_old_value();
        }
        m_assignment_stack.reset();
    }

    // Store in gamma the normalized weight. The normalized weight is given
    // by the formula  
    // m_assignment[e.get_source()] - m_assignment[e.get_target()] + e.get_weight()
    numeral& set_gamma(const edge & e, numeral & gamma) {
        gamma  = m_assignment[e.get_source()];
        gamma -= m_assignment[e.get_target()];
        gamma += e.get_weight();
        return gamma;
    }

    void reset_marks() {
        for (dl_var v : m_visited) {
            m_mark[v] = DL_UNMARKED;
        }
        m_visited.reset();
    }

    bool marks_are_clear() const {
        for (unsigned i = 0; i < m_mark.size(); ++i) {
            if (m_mark[i] != DL_UNMARKED) {
                return false;
            }
        }
        return true;
    }
    
    // Make the assignment feasible. An assignment is feasible if
    // Forall edge e. m_assignment[e.get_target()] - m_assignment[e.get_source()] <= e.get_weight()
    // 
    // This method assumes that if the assignment is not feasible, then the only infeasible edge
    // is the last added edge.
    bool make_feasible(edge_id id) {
        SASSERT(is_almost_feasible(id));
        SASSERT(!m_edges.empty());
        SASSERT(!is_feasible(m_edges[id]));
        SASSERT(m_assignment_stack.empty());
        SASSERT(m_heap.empty());
        const edge & last_e = m_edges[id];
        dl_var root      = last_e.get_source();
        m_gamma[root].reset();
        dl_var target    = last_e.get_target();
        numeral gamma;
        set_gamma(last_e, gamma);
        m_gamma[target]  = gamma;
        m_mark[target]   = DL_PROCESSED;
        m_parent[target] = id;
        m_visited.push_back(target);
        SASSERT(m_gamma[target].is_neg());
        acc_assignment(target, gamma);

        TRACE("arith", display(tout << id << "\n"););

        dl_var source = target;
        while (true) {
            ++m_stats.m_propagation_cost;
            if (m_mark[root] != DL_UNMARKED) {
                // negative cycle was found
                SASSERT(m_gamma[root].is_neg());
                m_heap.reset();
                reset_marks();
                undo_assignments();
                return false;
            }
            
            for (edge_id e_id : m_out_edges[source]) {
                edge & e     = m_edges[e_id];
                SASSERT(e.get_source() == source);
                if (!e.is_enabled()) {
                    continue;
                }
                set_gamma(e, gamma);
                
                if (gamma.is_neg()) {
                    target   = e.get_target();
                    switch (m_mark[target]) {
                    case DL_UNMARKED:
                        m_gamma[target]  = gamma;
                        m_mark[target]   = DL_FOUND;
                        m_parent[target] = e_id;
                        m_visited.push_back(target);
                        m_heap.insert(target);
                        break;
                    case DL_FOUND:
                        if (gamma < m_gamma[target]) {
                            m_gamma[target]  = gamma;
                            m_parent[target] = e_id;
                            m_heap.decreased(target);
                        }
                        break;
                    case DL_PROCESSED:
                    default:
                        UNREACHABLE();
                    }
                }
            }

            if (m_heap.empty()) {
                SASSERT(is_feasible());
                reset_marks();
                m_assignment_stack.reset();
                return true;
            }

            source = m_heap.erase_min();
            m_mark[source] = DL_PROCESSED;
            acc_assignment(source, m_gamma[source]);
        }
    }

    edge const* find_relaxed_edge(edge const* e, numeral & gamma) {
        SASSERT(gamma.is_neg());
        dl_var src = e->get_source();
        dl_var dst = e->get_target();
        numeral w = e->get_weight();
        for (edge_id e_id : m_out_edges[src]) {
            edge const& e2 = m_edges[e_id];
            if (e2.get_target() == dst && 
                e2.is_enabled() && // or at least not be inconsistent with current choices
                e2.get_weight() > w && (e2.get_weight() - w + gamma).is_neg()) {
                e = &e2;
                gamma += (e2.get_weight() - w);
                w = e2.get_weight();
                ++m_stats.m_num_relax;
            }
        }
        return e;
    }

public:
    
    dl_graph():
        m_heap(1024, dl_var_lt<Ext>(m_gamma)),
        m_timestamp(0),
        m_fw(m_mark),
        m_bw(m_mark) {
    }


    void collect_statistics(::statistics& st) const {
        m_stats.collect_statistics(st);
    }

    // Create/Initialize a variable with the given id.
    // The graph does not have control over the ids assigned by the theory.
    // That is init_var receives the id as an argument.
    void init_var(dl_var v) {
        TRACE("dl_bug", tout << "init_var " << v << "\n";);
        if (static_cast<unsigned>(v) < m_out_edges.size() && (!m_out_edges[v].empty() || !m_in_edges[v].empty())) {
            return;
        }
        SASSERT(check_invariant());
        while (static_cast<unsigned>(v) >= m_out_edges.size()) {
            m_assignment .push_back(numeral());
            m_out_edges  .push_back(edge_id_vector());
            m_in_edges   .push_back(edge_id_vector());
            m_gamma      .push_back(numeral());
            m_mark       .push_back(DL_UNMARKED);
            m_parent     .push_back(null_edge_id);
        }
        if (static_cast<unsigned>(v) >= m_heap.get_bounds()) {
            m_heap.set_bounds(v+1);
        }
        m_assignment[v].reset();
        SASSERT(static_cast<unsigned>(v) < m_heap.get_bounds());
        TRACE("dl_bug", tout << "init_var " << v << ", m_assignment[v]: " << m_assignment[v] << "\n";);
        SASSERT(m_assignment[v].is_zero());
        SASSERT(m_out_edges[v].empty());
        SASSERT(m_in_edges[v].empty());
        SASSERT(m_mark[v] == DL_UNMARKED);
        SASSERT(check_invariant());
    }

    // Add an new weighted edge "source --weight--> target" with explanation ex.
    edge_id add_edge(dl_var source, dl_var target, const numeral & weight, const explanation & ex) {
        // SASSERT(is_feasible());
        edge_id new_id = m_edges.size();
        m_edges.push_back(edge(source, target, weight, m_timestamp, ex));
        m_activity.push_back(0);
        TRACE("dl_bug", tout << "creating edge:\n"; display_edge(tout, m_edges.back()););
        m_out_edges[source].push_back(new_id);
        m_in_edges[target].push_back(new_id);
        return new_id;
    }

    // Return false if the resultant graph has a negative cycle. The negative
    // cycle can be extracted using traverse_neg_cycle.
    // The method assumes the graph is feasible before the invocation.
    bool enable_edge(edge_id id) {
        edge& e = m_edges[id];
        bool r = true;
        if (!is_feasible()) {
            return false;
        }
        if (!e.is_enabled()) {
            e.enable(m_timestamp);
            m_last_enabled_edge = id;
            m_timestamp++;
            if (!is_feasible(e)) {
                r = make_feasible(id);
            }
            SASSERT(check_invariant());
            SASSERT(!r || is_feasible()); 
            m_enabled_edges.push_back(id);
        }
        return r;
    }


    // This method should only be invoked when add_edge returns false.
    // That is, there is a negative cycle in the graph.
    // It will apply the functor f on every explanation attached to the edges
    // in the negative cycle.
    template<typename Functor>
    void traverse_neg_cycle(bool try_relax, Functor & f) {
        SASSERT(!is_feasible(m_edges[m_last_enabled_edge]));
        edge_id last_id = m_last_enabled_edge;
        edge const& last_e = m_edges[last_id];
        numeral gamma = m_gamma[last_e.get_source()];
        SASSERT(gamma.is_neg());
        edge_id e_id    = last_id;
        do {
            const edge * e = &m_edges[e_id];
            if (try_relax) {
                e = find_relaxed_edge(e, gamma);
            }
            inc_activity(e_id);
            f(e->get_explanation());
            e_id = m_parent[e->get_source()];
        }
        while (e_id != last_id);
    }


    //
    // Here is a version that tries to 
    // Find shortcuts on the cycle.
    // A shortcut is an edge that that is subsumed
    // by the current edges, but provides for a shorter
    // path to the conflict.
    // Example (<= (- a b) k1) (<= (- b c) k2) (<= (- c d) k3)
    // An edge (<= (- a d) k4) where k1 + k2 + k3 <= k4, but gamma + k4 - (k1+k2+k3) < 0
    // is still a conflict.
    // 
    template<typename Functor>
    void traverse_neg_cycle2(bool try_relax, Functor & f) {
        static unsigned num_conflicts = 0;
        ++num_conflicts;
        SASSERT(!is_feasible(m_edges[m_last_enabled_edge]));
        vector<numeral>  potentials;
        svector<edge_id> edges;
        svector<dl_var>  nodes;
        edge_id last_id = m_last_enabled_edge;
        edge const& last_e = m_edges[last_id];
        numeral potential(0);
        edge_id e_id    = last_id;
        numeral gamma = m_gamma[last_e.get_source()];
        SASSERT(check_gamma(last_id));

        do {
            SASSERT(gamma.is_neg());
            edges.push_back(e_id);
            const edge & e = m_edges[e_id];
            dl_var src = e.get_source();
            potential += e.get_weight();
                        
            //
            // search for edges that can reduce size of negative cycle.
            //
            for (edge_id e_id2 : m_out_edges[src]) {
                edge const& e2 = m_edges[e_id2];
                dl_var src2 = e2.get_target();                
                if (e_id2 == e_id || !e2.is_enabled()) {
                    continue;
                }
                for (unsigned j = 0; j < nodes.size(); ++j) {
                    if (nodes[j] != src2) {
                        continue;
                    }
                    numeral const& weight = e2.get_weight();
                    numeral delta = weight - potential + potentials[j];
                    if (delta.is_nonneg() && (gamma + delta).is_neg()) {
                        TRACE("diff_logic_traverse", tout << "Reducing path by ";
                              display_edge(tout, e2);
                              tout << "gamma: " << gamma << " weight: " << weight << "\n";
                              tout << "enabled: " << e2.is_enabled() << "\n";
                              tout << "delta: " << delta << "\n";
                              tout << "literals saved: " << (nodes.size() - j - 1) << "\n";
                              );
                        gamma += delta;
                        nodes.shrink(j + 1);
                        potentials.shrink(j + 1);
                        edges.shrink(j + 1);
                        edges.push_back(e_id2);           
                        potential = potentials[j] + weight;
                        break;
                    }
                    else {
                        TRACE("diff_logic_traverse", display_edge(tout << "skipping: ", e2););
                    }
                }
            }
            potentials.push_back(potential);
            nodes.push_back(src);
            e_id = m_parent[src];
                  
            SASSERT(check_path(potentials, nodes, edges));
        }
        while (e_id != last_id);
        
        TRACE("diff_logic_traverse", {   
                tout << "Num conflicts: " << num_conflicts << "\n";
                tout << "Resulting path:\n";
                for (unsigned i = 0; i < edges.size(); ++i) {
                    display_edge(tout << "potential: " << potentials[i] << " ", m_edges[edges[i]]);
                }
            }
            );

        if (!check_explanation(edges.size(), edges.c_ptr())) {
            throw default_exception("edges are not inconsistent");
        }
       
        // allow theory to introduce shortcut lemmas.
        prune_edges(edges, f);

        for (unsigned i = 0; i < edges.size(); ++i) {
            edge const& e = m_edges[edges[i]];
            f(e.get_explanation());
        }
    }

    bool can_reach(dl_var src, dl_var dst) {
        if (static_cast<unsigned>(src) >= m_out_edges.size() ||
            static_cast<unsigned>(dst) >= m_out_edges.size()) {
            return false;
        }            
        uint_set target, visited;
        target.insert(dst);
        return reachable(src, target, visited, dst);
    }

    bool reachable(dl_var start, uint_set const& target, uint_set& visited, dl_var& dst) {
        visited.reset();
        svector<dl_var> nodes;
        nodes.push_back(start);
        for (unsigned i = 0; i < nodes.size(); ++i) {
            dl_var n = nodes[i];
            if (visited.contains(n)) continue;
            visited.insert(n);
            edge_id_vector & edges = m_out_edges[n];
            for (edge_id e_id : edges) {
                edge & e = m_edges[e_id];
                if (!e.is_enabled()) continue;
                dst = e.get_target();
                if (target.contains(dst)) {
                    return true;
                }
                nodes.push_back(dst);
            }
        }
        return false;
    }

private:
    svector<int> m_freq_hybrid;
    int m_total_count = 0;
    int m_run_counter = -1;
    svector<int> m_hybrid_visited, m_hybrid_parent;

    bool is_connected(numeral const& gamma, bool zero_edge, edge const& e, unsigned timestamp) const {
        return (gamma.is_zero() || (!zero_edge && gamma.is_neg())) && e.get_timestamp() < timestamp;
    }

    int_vector bfs_todo;
    int_vector dfs_todo;

public:


    template<typename Functor>
    bool find_path(dl_var source, dl_var target, unsigned timestamp, Functor & f) {
        auto zero_edge = true;
        unsigned bfs_head = 0;
        bfs_todo.reset();
        dfs_todo.reset();
        m_hybrid_visited.resize(m_assignment.size(), m_run_counter++);
        m_hybrid_parent.resize(m_assignment.size(), -1);
        bfs_todo.push_back(source);
        m_hybrid_parent[source] = -1;
        m_hybrid_visited[source] = m_run_counter;
        numeral gamma;
        while (bfs_head < bfs_todo.size() || !dfs_todo.empty()) {
            m_total_count++;
            dl_var v;
            if (!dfs_todo.empty()) {
                v = dfs_todo.back();
                dfs_todo.pop_back();
            } 
            else {
                v = bfs_todo[bfs_head++];
            }

            edge_id_vector & edges = m_out_edges[v];
            for (edge_id e_id : edges) {
                edge & e     = m_edges[e_id];
                SASSERT(e.get_source() == v);
                if (!e.is_enabled()) {
                    continue;
                }
                set_gamma(e, gamma);
                if (is_connected(gamma, zero_edge, e, timestamp)) {
                    dl_var curr_target = e.get_target();
                    if (curr_target == target) {
                        f(e.get_explanation());
                        m_freq_hybrid[e_id]++;
                        while (true) {
                            int p = m_hybrid_parent[v];
                            if (p == -1)
                                return true;

                            edge_id eid;
                            bool ret = get_edge_id(p, v, eid);
                            if (eid == null_edge_id || !ret) {
                                return true;
                            }
                            else {
                                edge & e = m_edges[eid];
                                f(e.get_explanation());
                                m_freq_hybrid[eid]++;
                                v = p;
                            }
                        }
                    }
                    else if (m_hybrid_visited[curr_target] != m_run_counter) {
                        if (m_freq_hybrid[e_id] > 1) {                            
                            dfs_todo.push_back(curr_target);
                        } 
                        else {
                            bfs_todo.push_back(curr_target);                            
                        }
                        m_hybrid_visited[curr_target] = m_run_counter;                        
                        m_hybrid_parent[curr_target] = v;
                    }
                }
            }
        }
        return false;

    }

    // 
    // Create fresh literals obtained by resolving a pair (or more)
    // literals associated with the edges.
    // 

    template<typename Functor>
    void prune_edges(svector<edge_id>& edges, Functor & f) {
        unsigned max_activity = 0;
        edge_id e_id;
        for (unsigned i = 0; i < edges.size(); ++i) {
            e_id = edges[i];
            inc_activity(e_id);
            if (m_activity[e_id] > max_activity) {
                max_activity = m_activity[e_id];
            }
        }
        if (edges.size() > 5 && max_activity > 20) {
            prune_edges_min2(edges, f);
        }
    }

    template<typename Functor>
    void prune_edges_min1(svector<edge_id>& edges, Functor & f) {
        unsigned min_activity = ~0;
        unsigned idx = 0;
        for (unsigned i = 0; i + 1 < edges.size(); ++i) {
            edge_id e_id = edges[i];
            if (m_activity[e_id] < min_activity) {
                min_activity = m_activity[e_id];
                idx = i;
            }                
        }
        
        dl_var dst = get_source(edges[idx+1]);
        dl_var src = get_target(edges[idx]);
        
        f.new_edge(src, dst, 2, edges.begin()+idx);
    }

    template<typename Functor>
    void prune_edges_min2(svector<edge_id>& edges, Functor & f) {
        unsigned min1 = ~0, min2 = ~0, max = 0;
        unsigned idx1 = 0, idx2 = 0, max_idx = 0;
        dl_var src, dst;
        for (unsigned i = 0; i < edges.size(); ++i) {
            edge_id e_id = edges[i];
            if (m_activity[e_id] <= min1) {
                min2 = min1;
                min1 = m_activity[e_id];
                idx2 = idx1;
                idx1 = i;
            }
            else if (m_activity[e_id] < min2) {
                min2 = m_activity[e_id];
                idx2 = i;
            }
            // TBD: use also the edge with the maximal
            // traversals to create cut-edge.
            //
            if (m_activity[e_id] > max) {
                max = m_activity[e_id];
                max_idx = i;
            }
        }
        
        //
        // e1 e2 i1 e4 e5 e6 .. e8 i2 e9 e10
        // =>
        // e1 e2 e_new d9 e10
        // 
        // alternative:
        // e_new e4 ... e8 is the new edge.
        //
        // or both.
        //
        if (idx2 < idx1) {
            std::swap(idx1,idx2);
        }        
        (void) max_idx;
        SASSERT(idx1 < idx2 && idx2 < edges.size());
        SASSERT(max_idx < edges.size());
        dst = get_source(edges[idx2]);
        src = get_target(edges[idx1]);
        
        f.new_edge(src, dst, idx2-idx1+1, edges.begin()+idx1);
    }

    // Create a new scope.
    // That is, save the number of edges in the graph.
    void push() {
        // SASSERT(is_feasible()); <<< I relaxed this condition
        m_trail_stack.push_back(scope(m_edges.size(), m_enabled_edges.size(), m_timestamp));
    }
    
    // Backtrack num_scopes scopes.
    // Restore the previous number of edges.
    void pop(unsigned num_scopes) {
        unsigned lvl           = m_trail_stack.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl       = lvl - num_scopes;
        scope & s              = m_trail_stack[new_lvl];
        for (unsigned i = m_enabled_edges.size(); i > s.m_enabled_edges_lim; ) {
            --i;
            m_edges[m_enabled_edges[i]].disable();
        }
        m_enabled_edges.shrink(s.m_enabled_edges_lim);
        unsigned old_num_edges = s.m_edges_lim;
        m_timestamp            = s.m_old_timestamp;
        unsigned num_edges     = m_edges.size();
        SASSERT(old_num_edges <= num_edges);
        unsigned to_delete     = num_edges - old_num_edges;
        for (unsigned i = 0; i < to_delete; i++) {
            const edge & e = m_edges.back();
            TRACE("dl_bug", tout << "deleting edge:\n"; display_edge(tout, e););
            dl_var source  = e.get_source();
            dl_var target  = e.get_target();
            SASSERT(static_cast<int>(m_edges.size()) - 1 == m_out_edges[source].back());
            SASSERT(static_cast<int>(m_edges.size()) - 1 == m_in_edges[target].back());
            m_out_edges[source].pop_back();
            m_in_edges[target].pop_back();
            m_edges.pop_back();
        }
        m_trail_stack.shrink(new_lvl);
        SASSERT(check_invariant()); 
        // SASSERT(is_feasible()); <<< I relaxed the condition in push(), so this assertion is not valid anymore.
    }

    // Make m_assignment[v] == zero
    // The whole assignment is adjusted in a way feasibility is preserved.
    // This method should only be invoked if the current assignment if feasible.
    void set_to_zero(dl_var v) {
        SASSERT(is_feasible());
        if (!m_assignment[v].is_zero()) {
            numeral k = m_assignment[v];
            for (auto& a : m_assignment) {
                a -= k;
            }
            SASSERT(is_feasible());
        }
    }

    //
    // set assignments of v and w both to 0.
    // assumption: there are no prior dependencies between v and w.
    // so the graph is disconnected.
    // assumption: the current assignment is feasible.
    //
    void set_to_zero(unsigned n, dl_var const* vs) {
        for (unsigned i = 0; i < n; ++i) {
            dl_var v = vs[i];
            if (!m_assignment[v].is_zero()) {
                set_to_zero(v);
                for (unsigned j = 0; j < n; ++j) {
                    dl_var w = vs[j];
                    if (!m_assignment[w].is_zero()) {
                        enable_edge(add_edge(v, w, numeral(0), explanation()));
                        enable_edge(add_edge(w, v, numeral(0), explanation()));
                        SASSERT(is_feasible());                        
                    }
                }
                return;
            }
        }
    }

    void set_to_zero(dl_var v, dl_var w) {
        if (!m_assignment[v].is_zero()) {
            set_to_zero(v);
        }
        else {
            set_to_zero(w);
        }
        if (!m_assignment[v].is_zero() || !m_assignment[w].is_zero()) {
            enable_edge(add_edge(v, w, numeral(0), explanation()));
            enable_edge(add_edge(w, v, numeral(0), explanation()));
            SASSERT(is_feasible());
        }
    }

private:
    // Update the assignment of variable v, that is,
    // m_assignment[v] += inc
    // This method also stores the old value of v in the assignment stack.
    void acc_assignment(dl_var v, const numeral & inc) {
        TRACE("dl_bug", tout << "update v: " << v << " += " << inc << " m_assignment[v] " << m_assignment[v] << "\n";);
        m_assignment_stack.push_back(assignment_trail(v, m_assignment[v]));
        m_assignment[v] += inc;
    }

public:

    void inc_assignment(dl_var v, numeral const& inc) {
        m_assignment[v] += inc;
    }    


    struct every_var_proc {
        bool operator()(dl_var v) const {
            return true;
        }
    };

    void display(std::ostream & out) const {
        display_core(out, every_var_proc());
    }

    void display_agl(std::ostream & out) const {
        uint_set vars;
        for (edge const& e : m_edges) {
            if (e.is_enabled()) {
                vars.insert(e.get_source());
                vars.insert(e.get_target());
            }
        }
        out << "digraph "" {\n";
        
        unsigned n = m_assignment.size();
        for (unsigned v = 0; v < n; v++) {
            if (vars.contains(v)) {
                out << "\"" << v << "\" [label=\"" << v << ":" << m_assignment[v] << "\"]\n";
            }
        }
        for (edge const& e : m_edges) {
            if (e.is_enabled()) {
                out << "\"" << e.get_source() << "\"->\"" << e.get_target() << "\"[label=\"" << e.get_weight() << "\"]\n";
            }
        }

        out << "}\n";
    }

    template<typename FilterAssignmentProc>
    void display_core(std::ostream & out, FilterAssignmentProc p) const {
        display_edges(out);
        display_assignment(out, p);
    }

    void display_edges(std::ostream & out) const {
        for (edge const& e : m_edges) {
            if (e.is_enabled()) {
                display_edge(out, e);
            }
        }
    }

    std::ostream& display_edge(std::ostream & out, edge_id id) const {
        return display_edge(out, m_edges[id]);
    }

    std::ostream& display_edge(std::ostream & out, const edge & e) const {
        return out << e.get_explanation() << " (<= (- $" << e.get_target() << " $" << e.get_source() << ") " << e.get_weight() << ") " << e.get_timestamp() << "\n";
    }

    template<typename FilterAssignmentProc>
    void display_assignment(std::ostream & out, FilterAssignmentProc p) const {
        unsigned n = m_assignment.size();
        for (unsigned v = 0; v < n; v++) {
            if (p(v)) {
                out << "$" << v << " := " << m_assignment[v] << "\n";
            }
        }
    }

    // Return true if there is an edge source --> target.
    // If there is such edge, then the weight is stored in w and the explanation in ex.
    bool get_edge_weight(dl_var source, dl_var target, numeral & w, explanation & ex) {
        edge_id_vector & edges = m_out_edges[source];
        bool found = false;
        for (edge_id e_id : edges) {
            edge & e     = m_edges[e_id];
            if (e.is_enabled() && e.get_target() == target && (!found || e.get_weight() < w)) {
                w     = e.get_weight();
                ex    = e.get_explanation();
                found = true;
            }
        }
        return found;
    }

    // Return true if there is an edge source --> target (also counting disabled edges).
    // If there is such edge, return its edge_id in parameter id.
    bool get_edge_id(dl_var source, dl_var target, edge_id & id) const {
        edge_id_vector const & edges = m_out_edges[source];
        for (edge_id e_id : edges) {
            edge const & e = m_edges[e_id];
            if (e.get_target() == target) {
                id = e_id;
                return true;
            }
        }
        return false;
    }

    edges const & get_all_edges() const {
        return m_edges;
    }

    void get_neighbours_undirected(dl_var current, svector<dl_var> & neighbours) {
        neighbours.reset();
        edge_id_vector & out_edges = m_out_edges[current];
        for (edge_id e_id : out_edges) {
            edge & e     = m_edges[e_id];
            SASSERT(e.get_source() == current);
            dl_var neighbour = e.get_target();
            neighbours.push_back(neighbour);
        }
        edge_id_vector & in_edges = m_in_edges[current];
        for (edge_id e_id : in_edges) {
            edge & e     = m_edges[e_id];
            SASSERT(e.get_target() == current);
            dl_var neighbour = e.get_source();
            neighbours.push_back(neighbour);
        }
    }

    void dfs_undirected(dl_var start, svector<dl_var> & threads) {
        threads.reset();
        threads.resize(get_num_nodes());
        uint_set discovered, explored;
        svector<dl_var> nodes;
        discovered.insert(start);
        nodes.push_back(start);
        dl_var prev = start;
        while(!nodes.empty()) {
            dl_var current = nodes.back();
            SASSERT(discovered.contains(current) && !explored.contains(current));
            svector<dl_var> neighbours;
            get_neighbours_undirected(current, neighbours);
            SASSERT(!neighbours.empty());
            bool found = false;
            for (unsigned i = 0; i < neighbours.size(); ++i) {
                dl_var next = neighbours[i];
                DEBUG_CODE(
                edge_id id;
                SASSERT(get_edge_id(current, next, id) || get_edge_id(next, current, id)););                
                if (!discovered.contains(next) && !explored.contains(next)) {
                    TRACE("diff_logic", tout << "thread[" << prev << "] --> " << next << std::endl;);
                    threads[prev] = next;
                    prev = next;
                    discovered.insert(next);
                    nodes.push_back(next);
                    found = true;
                    break;
                }
            }            
            SASSERT(!nodes.empty());
            if (!found) {
                explored.insert(current);
                nodes.pop_back();
            }
        }
        threads[prev] = start;
    }

    void bfs_undirected(dl_var start, svector<dl_var> & parents, svector<dl_var> & depths) {
        parents.reset();
        parents.resize(get_num_nodes());
        parents[start] = -1;
        depths.reset();
        depths.resize(get_num_nodes());
        uint_set visited;
        std::deque<dl_var> nodes;
        visited.insert(start);
        nodes.push_front(start);
        while(!nodes.empty()) {
            dl_var current = nodes.back();
            nodes.pop_back();
            SASSERT(visited.contains(current));
            svector<dl_var> neighbours;
            get_neighbours_undirected(current, neighbours);
            SASSERT(!neighbours.empty());
            for (unsigned i = 0; i < neighbours.size(); ++i) {
                dl_var next = neighbours[i];
                DEBUG_CODE(
                edge_id id;
                SASSERT(get_edge_id(current, next, id) || get_edge_id(next, current, id)););
                if (!visited.contains(next)) {
                    TRACE("diff_logic", tout << "parents[" << next << "] --> " << current << std::endl;);
                    parents[next] = current;
                    depths[next] = depths[current] + 1;
                    visited.insert(next);
                    nodes.push_front(next);
                }
            }
        }
    }

    template<typename Functor>
    void enumerate_edges(dl_var source, dl_var target, Functor& f) {
        edge_id_vector & edges = m_out_edges[source];
        for (edge_id e_id : edges) {
            edge const& e = m_edges[e_id];
            if (e.get_target() == target) {
                f(e.get_weight(), e.get_explanation());
            }
        }
    }


    void reset() {
        m_assignment        .reset();
        m_assignment_stack  .reset();
        m_edges             .reset();
        m_in_edges          .reset();
        m_out_edges         .reset();
        m_trail_stack       .reset();
        m_gamma             .reset();
        m_mark              .reset();
        m_parent            .reset();
        m_visited           .reset();
        m_heap              .reset();
        m_enabled_edges     .reset();
        m_activity          .reset();
    }

    // Compute strongly connected components connected by (normalized) zero edges.
    void compute_zero_edge_scc(int_vector & scc_id) {
        m_unfinished_set.reset();
        m_dfs_time.reset();
        scc_id.reset();
        m_roots.reset();
        m_unfinished.reset();
        int n = m_assignment.size();
        m_unfinished_set.resize(n, false);
        m_dfs_time.resize(n, -1);
        scc_id.resize(n, -1);
        m_next_dfs_time = 0;
        m_next_scc_id = 0;
        for (dl_var v = 0; v < n; v++) {
            if (m_dfs_time[v] == -1) {
                dfs(v, scc_id);
            }        
        }
        TRACE("eq_scc",
              for (dl_var v = 0; v < n; v++) {
                  tout << "$" << v << " -> " << scc_id[v] << "\n";
              });
    }    

    void dfs(dl_var v, int_vector & scc_id) {
        m_dfs_time[v] = m_next_dfs_time;
        m_next_dfs_time++;
        m_unfinished_set[v] = true;
        m_unfinished.push_back(v);
        m_roots.push_back(v);
        numeral gamma;
        edge_id_vector & edges = m_out_edges[v];
        for (edge_id e_id : edges) {
            edge & e     = m_edges[e_id];
            if (!e.is_enabled()) {
                continue;
            }
            SASSERT(e.get_source() == v);
            set_gamma(e, gamma);
            if (gamma.is_zero()) {
                dl_var target = e.get_target();
                if (m_dfs_time[target] == -1) {
                    dfs(target, scc_id);
                }
                else if (m_unfinished_set[target]) {
                    SASSERT(!m_roots.empty());
                    while (m_dfs_time[m_roots.back()] > m_dfs_time[target]) {
                        m_roots.pop_back();
                        SASSERT(!m_roots.empty());
                    }
                }
            }
        }
        if (v == m_roots.back()) {
            dl_var scc_elem;
            unsigned size = 0;
            do {
                scc_elem = m_unfinished.back();
                m_unfinished.pop_back();
                SASSERT(m_unfinished_set[scc_elem]);
                m_unfinished_set[scc_elem] = false;
                scc_id[scc_elem] = m_next_scc_id;
                size++;
            } while (scc_elem != v);
            // Ignore SCC with size 1
            if (size == 1) {
                scc_id[scc_elem] = -1;
            }
            else {
                m_next_scc_id++;
            }
            m_roots.pop_back();
        }
    }

    void compute_zero_succ(dl_var v, int_vector& succ) {
        unsigned n = m_assignment.size();
        m_dfs_time.reset();
        m_dfs_time.resize(n, -1);
        m_dfs_time[v] = 0;
        succ.push_back(v);
        numeral gamma;
        for (dl_var w : succ) {
            for (edge_id e_id : m_out_edges[w]) {
                edge & e = m_edges[e_id];
                if (e.is_enabled() && set_gamma(e, gamma).is_zero()) {
                    SASSERT(e.get_source() == w);
                    dl_var target = e.get_target();
                    if (m_dfs_time[target] == -1) {
                        succ.push_back(target);
                        m_dfs_time[target] = 0;
                    }
                }
            }

        }
    }

    numeral get_assignment(dl_var v) const {
        return m_assignment[v]; 
    }

    void set_assignment(dl_var v, numeral const & n) {
        m_assignment[v] = n; 
    }

    unsigned get_timestamp() const {
        return m_timestamp;
    }

private:

    void inc_activity(edge_id e_id) {
        ++m_activity[e_id];
    }

    bool check_explanation(unsigned num_edges, edge_id const* edges) {
        numeral w;
        for (unsigned i = 0; i < num_edges; ++i) {
            edge const& e = m_edges[edges[i]];
            unsigned pred = (i>0)?(i-1):(num_edges-1);
            edge const& e1 = m_edges[edges[pred]];
            if (e.get_target() != e1.get_source()) {
                TRACE("check_explanation", display_edge(tout, e); display_edge(tout, e1); );
                return false;
            }
            w += e.get_weight();
        }
        if (w.is_nonneg()) {
            TRACE("check_explanation", tout << "weight: " << w << "\n";);
            return false;
        }
        return true;
    }

    bool check_path(vector<numeral>& potentials, svector<dl_var>& nodes, svector<edge_id>& edges) {
        // Debug:
        numeral potential0;
        for (unsigned i = 0; i < edges.size(); ++i) {
            
            potential0 += m_edges[edges[i]].get_weight();
            if (potential0 != potentials[i] || 
                nodes[i] != m_edges[edges[i]].get_source()) {
                TRACE("diff_logic_traverse", tout << "checking index " << i << " ";
                      tout << "potential: " << potentials[i] << " ";
                      display_edge(tout, m_edges[edges[i]]);
                      );
                return false;
            }                
        }
        return true;
    }

    bool check_gamma(edge_id last_id) {
        edge_id e_id    = last_id;
        numeral gamma2;
        do {
            gamma2 += m_edges[e_id].get_weight();
            e_id = m_parent[m_edges[e_id].get_source()];
        }
        while (e_id != last_id);
        
        return gamma2 == m_gamma[m_edges[last_id].get_source()];
    }


    // Auxliary structure used for breadth-first search.
    struct bfs_elem {
        dl_var       m_var;
        int          m_parent_idx;
        edge_id      m_edge_id;
        bfs_elem(dl_var v, int parent_idx, edge_id e):
            m_var(v),
            m_parent_idx(parent_idx),
            m_edge_id(e) {
        }
    };
    
public:
    // Find the shortest path from source to target using (normalized) zero edges with timestamp less than the given timestamp.
    // The functor f is applied on every explanation attached to the edges in the shortest path.
    // Return true if the path exists, false otherwise.
    
    
    // Return true if the path exists, false otherwise.
    template<typename Functor>
    bool find_shortest_zero_edge_path(dl_var source, dl_var target, unsigned timestamp, Functor & f) {
        return find_shortest_path_aux(source, target, timestamp, f, true);
    }

    template<typename Functor>
    bool find_shortest_reachable_path(dl_var source, dl_var target, unsigned timestamp, Functor & f) {
        return find_shortest_path_aux(source, target, timestamp, f, false);
    }

    template<typename Functor>
    bool find_shortest_path_aux(dl_var source, dl_var target, unsigned timestamp, Functor & f, bool zero_edge) {
        svector<bfs_elem> bfs_todo;
        svector<bool>     bfs_mark;
        bfs_mark.resize(m_assignment.size(), false);
        
        bfs_todo.push_back(bfs_elem(source, -1, null_edge_id));
        bfs_mark[source] = true;
        
        numeral gamma;
        for (unsigned head = 0; head < bfs_todo.size(); ++head) {
            bfs_elem & curr = bfs_todo[head];
            int parent_idx  = head;
            dl_var v = curr.m_var;
            TRACE("dl_bfs", tout << "processing: " << v << "\n";);
            edge_id_vector & edges = m_out_edges[v];
            for (edge_id e_id : edges) {
                edge & e     = m_edges[e_id];
                SASSERT(e.get_source() == v);
                if (!e.is_enabled()) {
                    continue;
                }
                set_gamma(e, gamma);
                TRACE("dl_bfs", display_edge(tout << "processing edge: ", e) << " gamma: " << gamma << "\n";);
                if (is_connected(gamma, zero_edge, e, timestamp)) {
                    dl_var curr_target = e.get_target();
                    TRACE("dl_bfs", tout << "curr_target: " << curr_target << ", mark: " << bfs_mark[curr_target] << "\n";);
                    if (curr_target == target) {
                        TRACE("dl_bfs", tout << "found path\n";);
                        TRACE("dl_eq_bug", tout << "path: " << source << " --> " << target << "\n";
                              display_edge(tout, e);
                              int tmp_parent_idx = parent_idx;
                              while (true) {
                                  bfs_elem & curr = bfs_todo[tmp_parent_idx];
                                  if (curr.m_edge_id == null_edge_id) {
                                      break;
                                  }
                                  else {
                                      edge & e = m_edges[curr.m_edge_id];
                                      display_edge(tout, e);
                                      tmp_parent_idx = curr.m_parent_idx;
                                  }
                              });
                        TRACE("dl_eq_bug", display_edge(tout, e););
                        f(e.get_explanation());
                        while (true) {
                            SASSERT(parent_idx >= 0);
                            bfs_elem & curr = bfs_todo[parent_idx];
                            if (curr.m_edge_id == null_edge_id) {
                                return true;
                            }
                            else {
                                edge & e = m_edges[curr.m_edge_id];
                                TRACE("dl_eq_bug", display_edge(tout, e););
                                f(e.get_explanation());
                                parent_idx = curr.m_parent_idx;
                            }
                        }
                    }
                    else if (!bfs_mark[curr_target]) {
                        bfs_todo.push_back(bfs_elem(curr_target, parent_idx, e_id));
                        bfs_mark[curr_target] = true;
                    }
                }
            }
        }
        return false;
    } 


    //
    // Theory propagation:
    // Given a (newly) added edge id, find the ids of un-asserted edges that
    // that are subsumed by the id.
    // Separately, reproduce explanations for those ids.
    // 
    // The algorithm works in the following way:
    // 1. Let e = source -- weight --> target be the edge at id.
    // 2. Compute successors (over the assigned edges) of source,
    //    those traversing source-target and those leaving source over different edges.
    //    compute forward potential of visited nodes.
    //    queue up nodes that are visited, and require the source->target edge.
    // 3. Compute pre-decessors (over the assigned edges) of target, 
    //    those traversing source-target, and those entering target
    //    without visiting source. Maintain only nodes that enter target
    //    compute backward potential of visited nodes.
    //    Queue up nodes that are visited, and require the source->target edge.
    // 4. traverse the smaller of the two lists.
    //    check if there is an edge between the two sets such that 
    //    the weight of the edge is >= than the sum of the two potentials - weight 
    //    (since 'weight' is added twice in the traversal.
    // 
private:
    struct dfs_state {
        class hp_lt {
            assignment& m_delta;
            char_vector& m_mark;
        public:
            hp_lt(assignment& asgn, char_vector& m) : m_delta(asgn),m_mark(m) {}
            bool operator()(dl_var v1, dl_var v2) const {
                numeral const& delta1 = m_delta[v1];
                numeral const& delta2 = m_delta[v2];
                return delta1 < delta2 ||
                    (delta1 == delta2 && 
                     m_mark[v1] == DL_PROP_IRRELEVANT && m_mark[v2] == DL_PROP_RELEVANT);
            }
        };
        assignment    m_delta;
        int_vector    m_visited;
        int_vector    m_parent;
        heap<hp_lt>   m_heap;
        unsigned      m_num_edges;
        dfs_state(char_vector& mark): m_heap(1024, hp_lt(m_delta, mark)), m_num_edges(0) {}

        void re_init(unsigned sz) {
            m_delta.resize(sz, numeral(0));
            m_parent.resize(sz, 0);
            m_visited.reset();
            m_num_edges = 0;
            m_heap.set_bounds(sz);
            SASSERT(m_heap.empty());
        }

        void add_size(unsigned n) { m_num_edges += n; }
        unsigned get_size() const { return m_num_edges; }

        bool contains(dl_var v) const { 
            // TBD can be done better using custom marking.
            for (unsigned i = 0; i < m_visited.size(); ++i) {
                if (v == m_visited[i]) {
                    return true;
                }
            }
            return false;
        }
    };

    dfs_state m_fw;
    dfs_state m_bw;

    void fix_sizes() {
        m_fw.re_init(m_assignment.size());
        m_bw.re_init(m_assignment.size());
    }

    numeral get_reduced_weight(dfs_state& state, dl_var n, edge const& e) {
        numeral gamma;
        return state.m_delta[n] + set_gamma(e, gamma);
    }

    template<bool is_fw>
    void find_relevant(dfs_state& state, edge_id id) {
        SASSERT(state.m_visited.empty());
        SASSERT(state.m_heap.empty());
        numeral delta;
        edge const& e_init = m_edges[id];
        vector<edge_id_vector> const& edges = is_fw?m_out_edges:m_in_edges;
        dl_var target = is_fw?e_init.get_target():e_init.get_source();
        dl_var source = is_fw?e_init.get_source():e_init.get_target();

        SASSERT(marks_are_clear());

        dl_prop_search_mark source_mark = DL_PROP_IRRELEVANT;
        dl_prop_search_mark target_mark =  DL_PROP_RELEVANT;
        m_mark[source] = source_mark;
        m_mark[target] = target_mark;
        state.m_delta[source] = numeral(0);
        state.m_delta[target] = get_reduced_weight(state, source, e_init);
        SASSERT(state.m_delta[source] <= state.m_delta[target]);

        state.m_heap.insert(source);
        state.m_heap.insert(target);
        unsigned num_relevant = 1;
        TRACE("diff_logic", display(tout); );
                
        while (!state.m_heap.empty() && num_relevant > 0) {
                      
            ++m_stats.m_implied_literal_cost;

            source = state.m_heap.erase_min();
            source_mark = static_cast<dl_prop_search_mark>(m_mark[source]);
            SASSERT(source_mark == DL_PROP_RELEVANT || source_mark == DL_PROP_IRRELEVANT);
            state.m_visited.push_back(source);
            if (source_mark == DL_PROP_RELEVANT) {
                --num_relevant;
                state.add_size(edges[source].size());
                m_mark[source] = DL_PROP_PROCESSED_RELEVANT;
            }
            else {
                m_mark[source] = DL_PROP_PROCESSED_IRRELEVANT;
            }
            TRACE("diff_logic", tout << "source: " << source << "\n";);
  
            for (edge_id e_id : edges[source]) {
                edge const& e = m_edges[e_id];

                if (&e == &e_init) {
                    continue;
                }
                SASSERT(!is_fw || e.get_source() == source);
                SASSERT(is_fw  || e.get_target() == source);
                if (!e.is_enabled()) {
                    continue;
                }
                TRACE("diff_logic", display_edge(tout, e););
                target = is_fw?e.get_target():e.get_source();
                delta  = get_reduced_weight(state, source, e);
                SASSERT(delta >= state.m_delta[source]);
                
                target_mark = static_cast<dl_prop_search_mark>(m_mark[target]);
                switch(target_mark) {
                case DL_PROP_UNMARKED: {
                    state.m_delta[target] = delta;
                    m_mark[target] = source_mark;
                    state.m_heap.insert(target);
                    if (source_mark == DL_PROP_RELEVANT) {
                        ++num_relevant;
                    }
                    state.m_parent[target] = e_id;
                    break;
                }
                case DL_PROP_RELEVANT:
                case DL_PROP_IRRELEVANT: {
                    numeral const& old_delta = state.m_delta[target];
                    if (delta < old_delta || 
                        (delta == old_delta && 
                         source_mark == DL_PROP_IRRELEVANT && target_mark == DL_PROP_RELEVANT)) {
                        state.m_delta[target] = delta;
                        m_mark[target]  = source_mark;
                        state.m_heap.decreased(target);
                        if (target_mark == DL_PROP_IRRELEVANT && source_mark == DL_PROP_RELEVANT) {
                            ++num_relevant;
                        }
                        if (target_mark == DL_PROP_RELEVANT && source_mark == DL_PROP_IRRELEVANT) {
                            --num_relevant;
                        }
                        state.m_parent[target] = e_id;
                    }
                    break;
                }
                case DL_PROP_PROCESSED_RELEVANT: 
                    TRACE("diff_logic", tout << delta << " ?> " << state.m_delta[target] << "\n";);
                    SASSERT(delta >= state.m_delta[target]);
                    SASSERT(!(delta == state.m_delta[target] && source_mark == DL_PROP_IRRELEVANT));
                    break;
                case DL_PROP_PROCESSED_IRRELEVANT: 
                    TRACE("diff_logic", tout << delta << " ?> " << state.m_delta[target] << "\n";);
                    SASSERT(delta >= state.m_delta[target]);
                    break;
                default:
                    UNREACHABLE();
                }
            }
        }        
        
        //
        // Clear marks using m_visited and m_heap.
        //
        unsigned sz = state.m_visited.size();
        for (unsigned i = 0; i < sz; ) {
            dl_var v = state.m_visited[i];
            source_mark = static_cast<dl_prop_search_mark>(m_mark[v]);
            m_mark[v] = DL_PROP_UNMARKED;
            SASSERT(source_mark == DL_PROP_PROCESSED_RELEVANT || source_mark == DL_PROP_PROCESSED_IRRELEVANT);
            if (source_mark == DL_PROP_PROCESSED_RELEVANT) {
                ++i;
            }
            else {
                state.m_visited[i] = state.m_visited[--sz];
                state.m_visited.resize(sz);
            }
        }

        TRACE("diff_logic", {
                tout << (is_fw?"is_fw":"is_bw") << ": ";
                for (unsigned i = 0; i < state.m_visited.size(); ++i) {
                    tout << state.m_visited[i] << " ";
                }
                tout << "\n";
            });

        for (auto & s : state.m_heap) {
            SASSERT(m_mark[s] != DL_PROP_UNMARKED);
            m_mark[s] = DL_PROP_UNMARKED;;
        }
        state.m_heap.reset();
        SASSERT(marks_are_clear());
    }

    void find_subsumed(edge_id bridge_edge, dfs_state& src, dfs_state& tgt, svector<edge_id>& subsumed) {
        edge const& e0 = m_edges[bridge_edge];
        dl_var a = e0.get_source();
        dl_var b = e0.get_target();
        numeral n0 = m_assignment[b] - m_assignment[a] - e0.get_weight();
        vector<edge_id_vector> const& edges = m_out_edges;
        TRACE("diff_logic", tout << "$" << a << " a:" << m_assignment[a] << " $" << b << " b: " << m_assignment[b] 
              << " e0: " << e0.get_weight() << " n0: " << n0 << "\n";
              display_edge(tout, e0);
              );

        for (unsigned i = 0; i < src.m_visited.size(); ++i) {
            dl_var c = src.m_visited[i];
            numeral n1 = n0 + src.m_delta[c] - m_assignment[c];
            for (edge_id e_id : edges[c]) {
                edge const& e1 = m_edges[e_id];
                SASSERT(c == e1.get_source());
                if (e1.is_enabled()) {
                    continue;
                }
                dl_var d = e1.get_target();
                numeral n2 = n1 + tgt.m_delta[d] + m_assignment[d];

                if (tgt.contains(d) && n2 <= e1.get_weight()) {
                    TRACE("diff_logic", 
                          tout << "$" << c << " delta_c: " << src.m_delta[c] << " c: " << m_assignment[c] << "\n";
                          tout << "$" << d << " delta_d: " << src.m_delta[d] << " d: " << m_assignment[d] 
                          << " n2: " << n2 << " e1: " << e1.get_weight() << "\n";
                          display_edge(tout << "found: ", e1););
                    ++m_stats.m_num_implied_literals;
                    subsumed.push_back(e_id);
                }
            }
        }
    }

public:
    void find_subsumed(edge_id id, svector<edge_id>& subsumed) {
        fix_sizes();
        find_relevant<true>(m_fw, id);        
        find_relevant<false>(m_bw, id);
        find_subsumed(id, m_bw, m_fw, subsumed);
        m_fw.m_visited.reset();
        m_bw.m_visited.reset();
        if (!subsumed.empty()) {
            TRACE("diff_logic", 
                  display(tout);
                  tout << "subsumed\n";
                  for (unsigned i = 0; i < subsumed.size(); ++i) {
                      display_edge(tout, m_edges[subsumed[i]]);
                  });
        }
    }

    // Find edges that are directly subsumed by id.
    void find_subsumed1(edge_id id, svector<edge_id>& subsumed) {
        edge const& e1 = m_edges[id];
        dl_var src = e1.get_source();
        dl_var dst = e1.get_target();
        edge_id_vector& out_edges = m_out_edges[src];
        edge_id_vector& in_edges  = m_in_edges[dst];
        numeral w = e1.get_weight();

        if (out_edges.size() < in_edges.size()) {
            for (edge_id e_id : out_edges) {
                ++m_stats.m_implied_literal_cost;
                edge const& e2 = m_edges[e_id];
                if (e_id != id && !e2.is_enabled() && e2.get_target() == dst && e2.get_weight() >= w) {
                    subsumed.push_back(e_id);
                    ++m_stats.m_num_implied_literals;
                }
            }
        }
        else {
            for (edge_id e_id : in_edges) {
                ++m_stats.m_implied_literal_cost;
                edge const& e2 = m_edges[e_id];
                if (e_id != id && !e2.is_enabled() && e2.get_source() == src && e2.get_weight() >= w) {
                    subsumed.push_back(e_id);
                    ++m_stats.m_num_implied_literals;
                }
            }
        }
    }

    //
    // Find edges that are subsumed by id, or is an edge between
    // a predecessor of id's source and id's destination, or
    // is an edge between a successor of id's dst, and id's source.
    // 
    //        src - id -> dst
    //     -                 - 
    //  src'                  dst'
    // 
    // so searching for:
    // . src - id' -> dst
    // . src' - id' -> dst
    // . src - id' -> dst'
    //
    void find_subsumed2(edge_id id, svector<edge_id>& subsumed) {
        edge const& e1 = m_edges[id];
        dl_var src = e1.get_source();
        dl_var dst = e1.get_target();
        numeral w = e1.get_weight();
        numeral w2;

        find_subsumed1(id, subsumed);

        for (edge_id e_id : m_in_edges[src]) {
            edge const& e2 = m_edges[e_id];
            if (!e2.is_enabled() || e2.get_source() == dst) {
                continue;
            }
            w2 = e2.get_weight() + w;
            for (edge_id e_id3 : m_out_edges[e2.get_source()]) {
                ++m_stats.m_implied_literal_cost;
                edge const& e3 = m_edges[e_id3];
                if (e3.is_enabled() || e3.get_target() != dst) {
                    continue;
                }
                if (e3.get_weight() >= w2) {
                    subsumed.push_back(e_id3);
                    ++m_stats.m_num_implied_literals;
                }
            }
        }
        for (edge_id e_id : m_out_edges[dst]) {
            edge const& e2 = m_edges[e_id];

            if (!e2.is_enabled() || e2.get_target() == src) {
                continue;
            }
            w2 = e2.get_weight() + w;
            for (edge_id e_id3 : m_in_edges[e2.get_target()]) {
                ++m_stats.m_implied_literal_cost;
                edge const& e3 = m_edges[e_id3];
                if (e3.is_enabled() || e3.get_source() != src) {
                    continue;
                }
                if (e3.get_weight() >= w2) {
                    subsumed.push_back(e_id3);
                    ++m_stats.m_num_implied_literals;
                }
            }
        }        
    }

    template<class Functor>
    void explain_subsumed_lazy(edge_id bridge_id, edge_id subsumed_id, Functor& f) {
        edge const& e1 = m_edges[bridge_id];
        edge const& e2 = m_edges[subsumed_id];        
        dl_var src2 = e2.get_source();
        dl_var dst2 = e2.get_target();
        unsigned timestamp = e1.get_timestamp();

        //
        // Find path from src2 to dst2 with edges having timestamps no greater than
        // timestamp, and of length no longer than weight of e2.
        //
        // use basic O(m*n) algorithm that traverses each edge once per node.
        // 

        ++m_stats.m_num_helpful_implied_literals;
        
        SASSERT(m_heap.empty());       
        SASSERT(e1.is_enabled());

        m_gamma[src2].reset();
        m_gamma[dst2] = e2.get_weight();
        m_heap.insert(src2);
        m_visited.push_back(src2);

        TRACE("diff_logic", 
              display_edge(tout << "bridge:   ", e1); 
              display_edge(tout << "subsumed: ", e2); 
              display(tout); );
        
        while (true) {
            SASSERT(!m_heap.empty());
            dl_var v = m_heap.erase_min();
            m_mark[v] = DL_PROCESSED;
            TRACE("diff_logic", tout << v << "\n";);

            for (edge_id e_id : m_out_edges[v]) {
                edge const& e = m_edges[e_id];
                if (!e.is_enabled() || e.get_timestamp() > timestamp) {
                    continue;
                }
                dl_var w = e.get_target();
                numeral gamma = m_gamma[v] + e.get_weight();
                if ((m_mark[w] != DL_UNMARKED) && m_gamma[w] <= gamma) {
                    continue;
                }
                m_gamma[w] = gamma;
                m_parent[w] = e_id;
                TRACE("diff_logic", tout << w << " : " << gamma << " " << e2.get_weight() << "\n";);
                if (w == dst2 && gamma <= e2.get_weight()) {
                    // found path.
                    reset_marks();
                    m_heap.reset();              
                    unsigned length = 0;
                    do {
                        inc_activity(m_parent[w]);
                        edge const& ee = m_edges[m_parent[w]];
                        f(ee.get_explanation());
                        w = ee.get_source();
                        ++length;
                    }
                    while (w != src2);
                    return;
                }
                switch(m_mark[w]) {
                case DL_UNMARKED:
                    m_visited.push_back(w);
                    // fall through
                case DL_PROCESSED:
                    m_mark[w] = DL_FOUND;
                    m_heap.insert(w);
                    break;
                case DL_FOUND:
                    m_heap.decreased(w);
                    break;
                }
            }
        }
        UNREACHABLE();
    }
};

#endif /* DIFF_LOGIC_H_ */

