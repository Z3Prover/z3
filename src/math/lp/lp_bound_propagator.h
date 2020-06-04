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
        unsigned           m_index_in_row; // in the row
        bool               m_sign; // true if the vertex plays the role of y
        vector<unsigned>   m_children; // point to m_vertices
        impq               m_offset; // offset from parent (parent - child = offset)
        unsigned           m_id; // the index in m_vertices
        unsigned           m_parent;
        unsigned           m_level; // the number of hops from the root to reach the vertex,
                                    // it is handy to find the common ancestor
    public:
        vertex() {}
        vertex(unsigned row,
               unsigned index_in_row,
               const impq & offset,
               unsigned id) :
            m_row(row),
            m_index_in_row(index_in_row),
            m_offset(offset),
            m_id(id),
            m_parent(-1),
            m_level(0)
        {}
        unsigned index_in_row() const { return m_index_in_row; }
        unsigned id() const { return m_id; }
        unsigned row() const { return m_row; }
        unsigned parent() const { return m_parent; }
        unsigned level() const { return m_level; }
        void add_child(vertex& child) {
            child.m_parent = m_id;
            m_children.push_back(child.m_id);
            child.m_level = m_level + 1;
        }        
        std::ostream& print(std::ostream & out) const {
            out << "row = " << m_row << ", m_index_in_row = " << m_index_in_row << ", parent = " << (int)m_parent << " , offset = " << m_offset << ", id = " << m_id << ", level = " << m_level << "\n";;
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
        push_to_verts(xv);
        vertex yv(row_index,
                  y, // index in row
                  offset,
                  1 // id
                  );
        push_to_verts(yv);
        xv.add_child(yv);
        TRACE("cheap_eq", print_tree(tout););
        SASSERT(tree_is_correct());
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
        const vertex& u = m_vertices[v_i];
        const vertex& v = m_vertices[v_j];
        TRACE("cheap_eq", tout << "v_i = " << v_i << ", v_j = " << v_j << "\nu = "; u.print(tout) << "\nv = "; v.print(tout) <<"\n";);
        svector<unsigned> path;
        find_path_on_tree(path, v_i, v_j);
        TRACE("cheap_eq", tout << "path = \n";
              display_row_of_vertex(v_i, tout);
              for (unsigned k : path) {
                  display_row_of_vertex(k, tout);
              }
              display_row_of_vertex(v_j, tout);
              );
        NOT_IMPLEMENTED_YET();
    }

    std::ostream& display_row_of_vertex(unsigned k, std::ostream& out) const {
        return lp().get_int_solver()->display_row_info(out,m_vertices[k].row() );
    }
    // the path will not include the start and the end
    void find_path_on_tree(svector<unsigned> & path, unsigned u_i, unsigned v_i) const {
        const vertex* u = &m_vertices[u_i];
        const vertex* v = &m_vertices[v_i];
        // equalize the levels
        while (u->level() > v->level()) {
            u = &m_vertices[u->parent()];
            path.push_back(u->id());
        }
        while (u->level() < v->level()) {
            v = &m_vertices[v->parent()];
            path.push_back(v->id());
        }
        SASSERT(u->level() == v->level());
        TRACE("cheap_eq", tout << "u = " ;u->print(tout); tout << "\nv = ";v->print(tout);); 
        while (u != v) {
            u = &m_vertices[u->parent()];
            v = &m_vertices[v->parent()];
            TRACE("cheap_eq", tout << "u = "; u->print(tout); tout << "\nv = "; v->print(tout) << "\n";); 
            path.push_back(u->id());
            path.push_back(v->id());            
        }
        path.pop_back(); // the common ancestor will be pushed two times
    }
    
    bool tree_is_correct() const {
        unsigned id = 0;
        for (const auto & v : m_vertices) {
            if (id != v.id()) {
                TRACE("cheap_eq",
                      tout << "incorrect id at " << id << "\n";);
                return false;
            }
            if (id && v.parent() == UINT_MAX) {
                TRACE("cheap_eq", tout << "incorrect parent "; v.print(tout); );
                return false;
            }

            if (id) {
                const vertex& v_parent = m_vertices[v.parent()];
                if (v_parent.level() + 1 != v.level()) {
                    TRACE("cheap_eq", tout << "incorrect levels ";
                          tout << "parent = "; v_parent.print(tout);
                          tout << "v = "; v.print(tout););
                    return false;
                }
            }
            
            id++;
        }
        return true;
    }

    // offset is measured from the initial vertex in the search
    void search_for_collision(const vertex& v, const impq& offset) {
        TRACE("cheap_eq", tout << "v_i = " ; v.print(tout) << "\noffset = " << offset << "\n";);
        unsigned registered_vert;
        
        if (m_offsets_to_verts.find(offset, registered_vert)) {
            if (registered_vert != v.id())
                report_eq(registered_vert, v.id());
        } else {
            m_offsets_to_verts.insert(offset, v.id());
        }
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
                      unsigned row_index,
                      unsigned x_index,
                      unsigned y_index,
                      const impq& row_offset) {
        TRACE("cheap_eq", tout << "offset = " << offset <<
              " , row_index = " << row_index << ", x_index = " << x_index << ", y_index = " << y_index << ", row_offset = " << row_offset << "\n"; );
        unsigned parent_id = m_vertices.size() - 1; 
        vertex xv(row_index, x_index, offset, parent_id + 1);
        if (parent_id != UINT_MAX) {
            m_vertices[parent_id].add_child(xv);
        }
        push_to_verts(xv);
        vertex yv(row_index, y_index, offset + row_offset, parent_id + 2);
        xv.add_child(yv);
        push_to_verts(yv);
        TRACE("cheap_eq", print_tree(tout););
        m_visited_rows.insert(row_index);
        search_for_collision(xv, offset);        
        TRACE("cheap_eq", print_tree(tout););
        SASSERT(tree_is_correct());
        search_for_collision(yv, offset + row_offset);
        SASSERT(tree_is_correct());
    }

    void push_to_verts(const vertex& v) {
        TRACE("cheap_eq", tout << "v = "; v.print(tout););
        m_vertices.push_back(v);
    }
        
    
    void add_column_edge(unsigned parent, unsigned row_index, unsigned index_in_row) {
        TRACE("cheap_eq", tout << "parent=" << parent << ", row_index = " << row_index << "\n";);
        vertex v(row_index, index_in_row, impq(0), m_vertices.size());
        m_vertices[parent].add_child(v);
        push_to_verts(v);
        TRACE("cheap_eq", tout << "tree = "; print_tree(tout););
        SASSERT(tree_is_correct());
    }
    std::ostream& print_tree(std::ostream & out) const {
        for (auto & v : m_vertices) {
            v.print(out);
        }
        return out;
    }
    lpvar get_column(const vertex& v) const {
        return lp().get_row(v.row())[v.index_in_row()].var();
    }

    void try_create_eq(unsigned row_index) {
        clear_for_eq();
        TRACE("cheap_eq", tout << "row_index = " << row_index << "\n";);
        unsigned x_index, y_index;
        impq offset;
        if (!is_offset_row(row_index, x_index, y_index, offset))
            return;
        add_row_edge(impq(0), row_index, x_index, y_index, offset);
        TRACE("cheap_eq", tout << "done for row_index " << row_index << "\n";);
    }
};
}
