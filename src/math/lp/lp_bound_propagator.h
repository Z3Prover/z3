/*
  Copyright (c) 2017 Microsoft Corporation
  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson   (levnach)
*/
#pragma once
#include "math/lp/lp_settings.h"
namespace lp {
template <typename T>
class lp_bound_propagator {

    // defining a graph on columns x, y such that there is a row x - y = c, where c is a constant    
    struct vertex {        
        unsigned           m_row; 
        unsigned           m_index; // in the row
        bool               m_sign; // true if the vertex plays the role of y
        vector<unsigned>   m_out_edges;  // the vertex is x in an x-y edge
        vector<unsigned>   m_in_edges;  // the vertex is y in an x-y edge
        vertex() {}
        vertex(unsigned row, unsigned index) : m_row(row), m_index(index) {}
        unsigned hash() const { return combine_hash(m_row, m_index); }
        bool operator==(const vertex& v) const { return m_row == v.m_row && m_index == v.m_index; }
        void add_out_edge(unsigned e) {
            SASSERT(m_out_edges.contains(e) == false);
            m_out_edges.push_back(e);
        }
        void add_in_edge(unsigned e) {
            SASSERT(m_in_edges.contains(e) == false);
            m_in_edges.push_back(e);
        }

    };

    struct vert_hash {  unsigned operator()(const vertex& u) const { return u.hash(); }};
    struct vert_eq { bool operator()(const vertex& u1, const vertex& u2) const { return u1 == u2; }};
    // an edge can be between columns in the same row or between two different rows in the same column
    // represents a - b = offset
    struct edge { 
        unsigned  m_a;
        unsigned  m_b;
        impq      m_offset;
        edge() {}
        edge(unsigned a, unsigned b, impq offset) : m_a(a), m_b(b), m_offset(offset) {}
        unsigned hash() const { return combine_hash(m_a, m_b); }
        bool operator==(const edge& e) const { return m_a == e.m_a && m_b == e.m_b; }
    };
    struct edge_hash {  unsigned operator()(const edge& u) const { return u.hash(); }};
    struct edge_eq { bool operator()(const edge& u1, const edge& u2) const { return u1 == u2; }}; 
    vector<vertex> m_vertices;
    vector<edge>   m_edges;
    
    std::unordered_map<unsigned, unsigned> m_improved_lower_bounds; // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned> m_improved_upper_bounds;
    T& m_imp;
public:
    vector<implied_bound> m_ibounds;
    lp_bound_propagator(T& imp): m_imp(imp) {}
    const lar_solver& lp() const { return m_imp.lp(); }
    column_type get_column_type(unsigned j) const {
        return m_imp.lp().get_column_type(j);
    }
    
    const impq & get_lower_bound(unsigned j) const {
        return m_imp.lp().get_lower_bound(j);
    }

    const impq & get_upper_bound(unsigned j) const {
        return m_imp.lp().get_upper_bound(j);
    }
    
    void try_add_bound(mpq const& v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict) {
        j = m_imp.lp().adjust_column_index_to_term_index(j);    

        lconstraint_kind kind = is_low? GE : LE;
        if (strict)
            kind = static_cast<lconstraint_kind>(kind / 2);
    
        if (!m_imp.bound_is_interesting(j, kind, v))
            return;
        unsigned k; // index to ibounds
        if (is_low) {
            if (try_get_value(m_improved_lower_bounds, j, k)) {
                auto & found_bound = m_ibounds[k];
                if (v > found_bound.m_bound || (v == found_bound.m_bound && found_bound.m_strict == false && strict)) {
                    found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                    TRACE("try_add_bound", m_imp.lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_lower_bounds[j] = m_ibounds.size();
                m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
                TRACE("try_add_bound", m_imp.lp().print_implied_bound(m_ibounds.back(), tout););
            }
        } else { // the upper bound case
            if (try_get_value(m_improved_upper_bounds, j, k)) {
                auto & found_bound = m_ibounds[k];
                if (v < found_bound.m_bound || (v == found_bound.m_bound && found_bound.m_strict == false && strict)) {
                    found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                    TRACE("try_add_bound", m_imp.lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_upper_bounds[j] = m_ibounds.size();
                m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
                TRACE("try_add_bound", m_imp.lp().print_implied_bound(m_ibounds.back(), tout););
            }
        }
    }

    void consume(const mpq& a, constraint_index ci) {
        m_imp.consume(a, ci);
    }

    bool no_duplicate_vertices() const {
        hashtable<vertex, vert_hash, vert_eq>  verts;
        for (auto & v : m_vertices) {
            verts.insert(v);
        }
        return verts.size() == m_vertices.size();
    }

    template <typename K>
    bool no_duplicate_in_vector(const K& vec) const {
        hashtable<unsigned, u_hash, u_eq> t;
        for (unsigned j : vec)
            t.insert(j);
        return t.size() == vec.size();
    }

    bool edge_exits_vertex(unsigned j, const vertex& v) const {
        const edge & e = m_edges[j];
        return m_vertices[e.m_b] == v;
    }

    bool edge_enters_vertex(unsigned j, const vertex& v) const {
        const edge & e = m_edges[j];
        return m_vertices[e.m_a] == v;
    }

    
    bool vertex_is_ok(unsigned i) const {
        const vertex& v = m_vertices[i];
        bool ret = no_duplicate_in_vector(v.m_out_edges)
            && no_duplicate_in_vector(v.m_in_edges);
        if (!ret)
            return false;
        for (unsigned j : v.m_out_edges) {
            if (edge_exits_vertex(j, v))
                return false;
        }
        for (unsigned j : v.m_in_edges) {
            if (edge_enters_vertex(j, v))
                return false;
        }
        return true;
    }
    
    bool vertices_are_ok() const {
        return no_duplicate_vertices();
        for (unsigned k = 0; k < m_vertices.size(); k++) {
            if (!vertex_is_ok(k))
                return false;
        }
        return true;
    }

    bool no_duplicate_edges() const {
        hashtable<edge, edge_hash, edge_eq> edges;
        for (auto & v : m_edges) {
            edges.insert(v);
        }
        return edges.size() == m_edges.size();
    
    }
    
    bool edges_are_ok() const {
        return no_duplicate_edges();
    }
    
    bool graph_is_ok() const {
        return vertices_are_ok() && edges_are_ok();
    }

    void create_initial_xy(unsigned x, unsigned y, unsigned row_index) {
        impq offset;
        const auto& row =  lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            if (k == x || k == y)
                continue;
            const auto& c = row[k];
            offset += c.coeff() * lp().get_lower_bound(c.var());
        }
        vertex xv(row_index, x);
        m_vertices.push_back(xv);
        vertex yv(row_index, y);
        m_vertices.push_back(yv);
        unsigned sz = m_vertices.size();
        m_edges.push_back(edge(sz - 2, sz - 1, offset));
        unsigned ei = m_edges.size() - 1;
        m_vertices[sz - 2].add_out_edge(ei);
        m_vertices[sz - 1].add_in_edge(ei);
        SASSERT(graph_is_ok());
        NOT_IMPLEMENTED_YET();
    }
    
    void try_create_eq(unsigned x, unsigned y, unsigned row_index) {
        m_vertices.clear();
        m_edges.clear();
        create_initial_xy(x, y, row_index);
        NOT_IMPLEMENTED_YET();
        
    }
};
}
