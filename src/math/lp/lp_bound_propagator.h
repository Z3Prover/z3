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
    struct impq_eq { bool operator()(const impq& a, const impq& b) const {return a == b;}};
    // Pairs (row,x), (row,y) such that there is the
    // row is x - y = c, where c is a constant form a tree.
    // The edges of the tree are of the form ((row,x), (row, y)) as from above,
    // or ((row, x), (other_row, x)) where the "other_row" is an offset row too.
    class vertex {        
        unsigned           m_row; 
        unsigned           m_index; // in the row
        bool               m_sign; // true if the vertex plays the role of y
        vector<unsigned>   m_children; // point to m_vertices
        impq               m_offset; // offset from parent (parent - child = offset)
        unsigned           m_id; // the index in m_vertices
        unsigned           m_parent;
    public:
        vertex() {}
        vertex(unsigned row,
               unsigned index,
               const impq & offset,
               unsigned id) :
            m_row(row),
            m_index(index),
            m_offset(offset),
            m_id(id),
            m_parent(-1)
        {}
        unsigned index() const { return m_index; }
        unsigned id() const { return m_id; }
        unsigned row() const { return m_row; }
        void add_child(vertex& child) {
            child.m_parent = m_id;
            m_children.push_back(child.m_id);
        }        
        std::ostream& print(std::ostream & out) const {
            out << "row = " << m_row << ", m_index = " << m_index << ", parent = " << (int)m_parent << " , offset = " << m_offset << "\n";;
            return out;
        }
    };
    hashtable<unsigned, u_hash, u_eq>         m_visited_rows;
    hashtable<unsigned, u_hash, u_eq>         m_visited_columns;
    vector<vertex>                            m_vertices;
    map<impq, lpvar, obj_hash<impq>, impq_eq> m_offsets_to_verts;

    // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned>    m_improved_lower_bounds;
    std::unordered_map<unsigned, unsigned>    m_improved_upper_bounds;
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

    void create_initial_xy(unsigned x, unsigned y, unsigned row_index) {
        impq offset;
        const auto& row =  lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            if (k == x || k == y)
                continue;
            const auto& c = row[k];
            offset += c.coeff() * lp().get_lower_bound(c.var());
        }
        vertex xv(row_index,
                  x, // index in row
                  impq(0), // offset
                  0 // id
                  );
        m_vertices.push_back(xv);
        vertex yv(row_index,
                  y, // index in row
                  offset,
                  1 // id
                  );
        m_vertices.push_back(yv);
        xv.add_child(yv);
    }
    bool is_offset_row(unsigned row_index,
                       unsigned & x_index,
                       lpvar & y_index,
                       impq& offset) const {
        x_index = y_index = UINT_MAX;

        const auto & row = lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            const auto& c = row[k];
            if (lp().column_is_fixed(c.var()))
                continue;
            if (x_index == UINT_MAX && c.coeff().is_one())
                x_index = k;
            else if (y_index == UINT_MAX && c.coeff().is_minus_one())
                y_index = k;
            else 
                return false;
        }
        if (x_index == UINT_MAX || y_index == UINT_MAX)
            return false;
        offset = impq(0);
        for (const auto& c : row) {
            if (!lp().column_is_fixed(c.var()))
                continue;
            offset += c.coeff() * lp().get_lower_bound(c.var());
        }
        return true;
    }

    void add_eq(lpvar j, lpvar k) {
        NOT_IMPLEMENTED_YET();
    }
    
    void check_for_eq_and_add_to_offset_table(lpvar j, const impq & offset) {
        lpvar k;
        if (m_offsets_to_verts.find(offset, k)) {
            SASSERT(j != k);
            add_eq(j, k);
        } else {
            m_offsets_to_verts.insert(offset, j);
        }
            
    }

    void clear_for_eq() {
        m_visited_rows.reset();
        m_visited_columns.reset();
        m_vertices.reset();
        m_offsets_to_verts.reset();
    }

    // we have v_i and v_j, indices of vertices at the same offsets
    void report_eq(unsigned v_i, unsigned v_j) {
        SASSERT(v_i != v_j);
        NOT_IMPLEMENTED_YET();
    }
        

    // offset is measured from the initial vertex in the search
    void search_for_collision(const vertex& v, const impq& offset) {
        TRACE("cheap_eq", tout << "v_i = " ; v.print(tout) << "\n";);
        unsigned registered_vert;
        
        if (m_offsets_to_verts.find(offset, registered_vert))
            report_eq(registered_vert, v.id());
        else 
            m_offsets_to_verts.insert(offset, v.id());
        lpvar j = get_column(v);
        if (m_visited_columns.contains(j))
            return;
        m_visited_columns.insert(j);
        for (const auto & c : lp().get_column(j)) {
            if (m_visited_rows.contains(c.var()))
                continue;
            m_visited_rows.insert(c.var());
            unsigned x_index, y_index;
            impq row_offset;
            if (!is_offset_row(c.var(), x_index, y_index, row_offset))
                return;
            add_column_edge(v.id(), c.var(), x_index);
            add_row_edge(offset, v.row(), x_index, y_index, row_offset);
        }
    }

        // row[x_index] gives x, and row[y_index] gives y
    // offset is accumulated during the recursion
    // edge_offset is the one in x - y = edge_offset
    // The parent is taken from m_vertices.back()
    void add_row_edge(const impq& offset,
                      unsigned row_index, unsigned x_index, unsigned y_index, const impq& row_offset) {
        const auto& row =  lp().get_row(row_index);
        unsigned parent_id = m_vertices.size() - 1; 
        vertex xv(row_index, x_index, row_offset, parent_id + 1);
        m_vertices.push_back(xv);
        if (parent_id != UINT_MAX) {
            m_vertices[parent_id].add_child(xv);
        }
        vertex yv(row_index, y_index, row_offset, parent_id + 2);
        m_vertices.push_back(yv);
        xv.add_child(yv);
        search_for_collision(xv, offset);
    }
    
    void add_column_edge(unsigned parent, lpvar j, unsigned index_in_row) {
        NOT_IMPLEMENTED_YET();
    }
    
    lpvar get_column(const vertex& v) const {
        return lp().get_row(v.row())[v.index()].var();
    }

    void try_create_eq(unsigned row_index) {
        TRACE("cheap_eq", tout << "row_index = " << row_index << "\n";);
        unsigned x_index, y_index;
        impq offset;
        if (!is_offset_row(row_index, x_index, y_index, offset))
            return;
        add_row_edge(impq(0), row_index, x_index, y_index, offset);
        TRACE("cheap_eq", tout << "done for row_index" << row_index << "\n";);
    }
};
}
