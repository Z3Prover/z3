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

    // vertex represents a pair (row,x) or (row,y) for an offset row.
    // The set of all pair are organised in a tree.
    // The edges of the tree are of the form ((row,x), (row, y)) for an offset row,
    // or ((row, u), (other_row, v)) where the "other_row" is an offset row too,
    // and u, v reference the same column
    class vertex {        
        unsigned           m_row; 
        unsigned           m_index_in_row; // in the row
        svector<unsigned>  m_children; // point to m_vertices
        impq               m_offset; // offset from parent (parent - child = offset)
        unsigned           m_id; // the index in m_vertices
        unsigned           m_parent;
        unsigned           m_level; // the distance in hops to the root;
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
            m_level(0) {}
        unsigned index_in_row() const { return m_index_in_row; }
        unsigned id() const { return m_id; }
        unsigned row() const { return m_row; }
        unsigned parent() const { return m_parent; }
        unsigned level() const { return m_level; }
        const impq& offset() const { return m_offset; }
        void add_child(vertex& child) {
            child.m_parent = m_id;
            m_children.push_back(child.m_id);
            child.m_level = m_level + 1;
        }
        const svector<unsigned> & children() const { return m_children; }
        std::ostream& print(std::ostream & out) const {
            out << "row = " << m_row << ", m_index_in_row = " << m_index_in_row << ", parent = " << (int)m_parent << " , offset = " << m_offset << ", id = " << m_id << ", level = " << m_level << "\n";;
            return out;
        }
#ifdef Z3DEBUG
        bool operator==(const vertex& o) const {
            return m_row == o.m_row && m_index_in_row == o.m_index_in_row;
        }
#endif
    };
    hashtable<unsigned, u_hash, u_eq>         m_visited_rows;
    hashtable<unsigned, u_hash, u_eq>         m_visited_columns;
    vector<vertex>                            m_vertices;
    map<impq, lpvar, obj_hash<impq>, impq_eq> m_offset_to_verts;
    // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned>    m_improved_lower_bounds;
    std::unordered_map<unsigned, unsigned>    m_improved_upper_bounds;
    T&                                        m_imp;
    impq                                      m_zero;
    typedef std::pair<unsigned, unsigned> upair;
    struct uphash {
        unsigned operator()(const upair& p) const { return combine_hash(p.first, p.second); }
    };
    struct upeq {
        unsigned operator()(const upair& p, const upair& q) const { return p == q; }
    };
    hashtable<upair, uphash, upeq>  m_reported_pairs; // contain the pairs of columns (first < second)
public:
    vector<implied_bound> m_ibounds;
    lp_bound_propagator(T& imp): m_imp(imp), m_zero(impq(0)) {}
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
        j = m_imp.lp().column_to_reported_index(j);    

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
                  m_zero, // offset
                  0 // id
                  );
        push_vertex(xv);
        vertex yv(row_index,
                  y, // index in row
                  offset,
                  1 // id
                  );
        push_vertex(yv);
        xv.add_child(yv);
        TRACE("cheap_eq", print_tree(tout););
        SASSERT(tree_is_correct());
    }

    bool is_offset_row(unsigned row_index,
                       unsigned & x_index,
                       lpvar & y_index,
                       impq& offset) {
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
        if (lp().column_is_int(row[x_index].var()) != lp().column_is_int(row[y_index].var()))
            return false; 

        offset = impq(0);
        for (const auto& c : row) {
            if (!lp().column_is_fixed(c.var()))
                continue;
            offset += c.coeff() * lp().get_lower_bound(c.var());
        }
        if (offset.is_zero() &&
            !pair_is_reported(row[x_index].var(), row[y_index].var())) {
            lp::explanation ex;
            explain_fixed_in_row(row_index, ex);
            add_eq_on_columns(ex, row[x_index].var(), row[y_index].var());
        }
        return true;
    }    

    bool pair_is_reported(lpvar j, lpvar k) const {        
        return j < k? m_reported_pairs.contains(std::make_pair(j, k)) :
            m_reported_pairs.contains(std::make_pair(k, j));
    }
    
    void check_for_eq_and_add_to_offset_table(const vertex& v) {
        unsigned k; // the other vertex index
        
        if (m_offset_to_verts.find(v.offset(), k)) {
            if (column(m_vertices[k]) != column(v) &&
                !pair_is_reported(column(m_vertices[k]),column(v)))
                report_eq(k, v.id());
        } else {
            TRACE("cheap_eq", tout << "registered offset " << v.offset() << " to " << v.id() << "\n";);
            m_offset_to_verts.insert(v.offset(), v.id());
        }
            
    }

    void clear_for_eq() {
        // m_reported_pairs.reset();
        // m_visited_rows.reset();
        // m_visited_columns.reset();
        m_vertices.reset();
        m_offset_to_verts.reset();
    }

    // we have v_i and v_j, indices of vertices at the same offsets
    void report_eq(unsigned v_i, unsigned v_j) {
        SASSERT(v_i != v_j);
        TRACE("cheap_eq", tout << "v_i = " << v_i << ", v_j = " << v_j << "\nu = ";
              m_vertices[v_i].print(tout) << "\nv = "; m_vertices[v_j].print(tout) <<"\n";);
        
        svector<unsigned> path;
        find_path_on_tree(path, v_i, v_j);
        TRACE("cheap_eq", tout << "path = \n";
              for (unsigned k : path) {
                  display_row_of_vertex(k, tout);
              });
        lp::explanation exp = get_explanation_from_path(path);
        add_eq_on_columns(exp, column(m_vertices[v_i]), column(m_vertices[v_j]));
    }

    void add_eq_on_columns(const explanation& exp, lpvar v_i_col, lpvar v_j_col) {
        SASSERT(v_i_col != v_j_col);
        upair p = v_i_col < v_j_col? upair(v_i_col, v_j_col) :upair(v_j_col, v_i_col);
        m_reported_pairs.insert(p);
        unsigned i_e = lp().column_to_reported_index(v_i_col);
        unsigned j_e = lp().column_to_reported_index(v_j_col);
        TRACE("cheap_eq", tout << "reporting eq " << i_e << ", " << j_e << "\n";);
        m_imp.add_eq(i_e, j_e, exp);        
    }
    
    explanation get_explanation_from_path(const svector<unsigned>& path) const {
        explanation ex;
        unsigned prev_row = UINT_MAX;
        for (unsigned k : path) {
            unsigned row = m_vertices[k].row();
            if (row == prev_row)
                continue;
            explain_fixed_in_row(prev_row = row, ex);
        }
        return ex;
    }

    void explain_fixed_in_row(unsigned row, explanation& ex) const {
        constraint_index lc, uc;
        for (const auto & c : lp().get_row(row)) {
            lpvar j = c.var();
            if (lp().is_fixed(j)) {               
                lp().get_bound_constraint_witnesses_for_column(j, lc, uc);
                ex.push_back(lc);
                ex.push_back(uc);
            }
        }
    }
    
    std::ostream& display_row_of_vertex(unsigned k, std::ostream& out) const {
        m_vertices[k].print(out);
        return lp().get_int_solver()->display_row_info(out,m_vertices[k].row() );
    }

    void find_path_on_tree(svector<unsigned> & path, unsigned u_i, unsigned v_i) const {
        const vertex* u = &m_vertices[u_i],* up, *vp;
        const vertex* v = &m_vertices[v_i];
        path.push_back(u->id());
        path.push_back(v->id());

         // equalize the levels
        while (u->level() > v->level()) {
            up = &m_vertices[u->parent()];
            if (u->row() == up->row())
                path.push_back(up->id());
            u = up;
        }
        
        while (u->level() < v->level()) {            
            vp = &m_vertices[v->parent()];
            if (u->row() == vp->row())
                path.push_back(vp->id());
            v = vp;
        }
        SASSERT(u->level() == v->level());
        TRACE("cheap_eq", tout << "u = " ;u->print(tout); tout << "\nv = ";v->print(tout);); 
        while (u != v) {
            if (u->row() == v->row() && u->offset() == v->offset()) // we have enough explanation now
                break;
            
            up = &m_vertices[u->parent()];
            vp = &m_vertices[v->parent()];
            if (up->row() == u->row())
                path.push_back(up->id());
            if (vp->row() == v->row())
                path.push_back(vp->id());
            u = up; v = vp;
        }
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

    void push_vertex(const vertex& v) {
        TRACE("cheap_eq", tout << "v = "; v.print(tout););
        SASSERT(!m_vertices.contains(v));
        m_vertices.push_back(v);
        
    }
        
    
    std::ostream& print_tree(std::ostream & out) const {
        for (auto & v : m_vertices) {
            v.print(out);
        }
        return out;
    }
    lpvar column(const vertex& v) const {
        return lp().get_row(v.row())[v.index_in_row()].var();
    }

    void try_create_eq(unsigned row_index) {        
        if (m_visited_rows.contains(row_index))
            return;
        TRACE("cheap_eq", tout << "row_index = " << row_index << "\n";);
        clear_for_eq();
        unsigned x_index, y_index;
        impq offset;
        if (!is_offset_row(row_index, x_index, y_index, offset))
            return;
        TRACE("cheap_eq", lp().get_int_solver()->display_row_info(tout, row_index););
        vertex root(row_index, x_index, impq(0), 0 /* id */);
        push_vertex(root);
        vertex v_y(row_index, y_index, offset, 1);
        root.add_child(v_y);
        push_vertex(v_y);
        SASSERT(tree_is_correct());
        m_visited_rows.insert(row_index);
        explore_under(root);
        TRACE("cheap_eq", tout << "done for row_index " << row_index << "\n";);
    }
        
    void go_over_vertex_column(vertex & v) {
        lpvar j = column(v);
        if (m_visited_columns.contains(j))
            return;
        m_visited_columns.insert(j);
        for (const auto & c : lp().get_column(j)) {
            unsigned row_index = c.var();
            if (m_visited_rows.contains(row_index))
                continue;
            m_visited_rows.insert(row_index);
            unsigned x_index, y_index;
            impq row_offset;
            if (!is_offset_row(row_index, x_index, y_index, row_offset))
                continue;
            TRACE("cheap_eq", lp().get_int_solver()->display_row_info(tout, row_index););
            // who is it the same column?
            if (lp().get_row(row_index)[x_index].var() == j) { // conected to x
                vertex x_v(row_index, x_index, v.offset(), m_vertices.size());
                v.add_child(x_v);
                vertex y_v(row_index, y_index, v.offset() + row_offset, m_vertices.size() + 1);
                x_v.add_child(y_v);
                push_vertex(x_v); // no need to explore from x_v
                push_vertex(y_v);
                SASSERT(tree_is_correct());
                explore_under(y_v);
            } else { // connected to y
                vertex y_v(row_index, y_index, v.offset(), m_vertices.size());
                v.add_child(y_v);
                vertex x_v(row_index, x_index, v.offset() - row_offset, m_vertices.size() + 1);
                y_v.add_child(x_v);
                push_vertex(y_v); // no need to explore from y_v
                push_vertex(x_v);
                SASSERT(tree_is_correct());
                explore_under(x_v);
            }
        }
    }
    
    void explore_under(vertex& v) {
        SASSERT(v.children().size() <= 1); // because we have not collected the vertices
        // from the column, so there might be only one child from the row
        check_for_eq_and_add_to_offset_table(v);
        unsigned v_id = v.id();
        go_over_vertex_column(v);
        // v might change in m_vertices expansion
        for (unsigned j : m_vertices[v_id].children()) {
            explore_under(m_vertices[j]);
        }
    }
};
}
