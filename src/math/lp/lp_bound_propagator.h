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
    typedef std::pair<int, mpq> var_offset;
    typedef pair_hash<int_hash, obj_hash<mpq> > var_offset_hash;
    typedef map<var_offset, unsigned, var_offset_hash, default_eq<var_offset> > var_offset2row_id;
    typedef std::pair<mpq, bool> value_sort_pair;
    var_offset2row_id       m_var_offset2row_id;

    struct mpq_eq { bool operator()(const mpq& a, const mpq& b) const {return a == b;}};

    // vertex represents a pair (row,x) or (row,y) for an offset row.
    // The set of all pair are organised in a tree.
    // The edges of the tree are of the form ((row,x), (row, y)) for an offset row,
    // or ((row, u), (other_row, v)) where the "other_row" is an offset row too,
    // and u, v reference the same column
    class vertex {        
        unsigned           m_row; 
        unsigned           m_index_in_row; // in the row
        ptr_vector<vertex> m_children;
        mpq               m_offset; // offset from parent (parent - child = offset)
        vertex*            m_parent;
        unsigned           m_level; // the distance in hops to the root;
                                    // it is handy to find the common ancestor
    public:
        vertex() {}
        vertex(unsigned row,
               unsigned index_in_row,
               const mpq & offset) :
            m_row(row),
            m_index_in_row(index_in_row),
            m_offset(offset),
            m_parent(nullptr),
            m_level(0) {}
        unsigned index_in_row() const { return m_index_in_row; }
        unsigned row() const { return m_row; }
        vertex* parent() const { return m_parent; }
        unsigned level() const { return m_level; }
        const mpq& offset() const { return m_offset; }
        void add_child(vertex* child) {
            child->m_parent = this;
            m_children.push_back(child);
            child->m_level = m_level + 1;
        }
        const ptr_vector<vertex> & children() const { return m_children; }
        std::ostream& print(std::ostream & out) const {
            out << "row = " << m_row << ", m_index_in_row = " << m_index_in_row << ", parent = " << m_parent << " , offset = " << m_offset << ", level = " << m_level << "\n";;
            return out;
        }
        bool operator==(const vertex& o) const {
            return m_row == o.m_row && m_index_in_row == o.m_index_in_row;
        }
    };
    hashtable<unsigned, u_hash, u_eq>         m_visited_rows;
    hashtable<unsigned, u_hash, u_eq>         m_visited_columns;
    vertex*                                   m_root;                                 
    map<mpq, vertex*, obj_hash<mpq>, mpq_eq> m_offset_to_verts;
    // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned>    m_improved_lower_bounds;
    std::unordered_map<unsigned, unsigned>    m_improved_upper_bounds;
    T&                                        m_imp;
    mpq                                      m_zero;
    vector<implied_bound> m_ibounds;
public:
    const vector<implied_bound>& ibounds() const { return m_ibounds; }
    void init() {
        m_improved_upper_bounds.clear();
        m_improved_lower_bounds.clear();
        m_ibounds.reset();
    }
    lp_bound_propagator(T& imp): m_imp(imp), m_zero(mpq(0)) {}
    const lar_solver& lp() const { return m_imp.lp(); }
    column_type get_column_type(unsigned j) const {
        return m_imp.lp().get_column_type(j);
    }
    
    const impq & get_lower_bound(unsigned j) const {
        return m_imp.lp().get_lower_bound(j);
    }

    const mpq & get_lower_bound_rational(unsigned j) const {
            return m_imp.lp().get_lower_bound(j).x;
    }

    
    const impq & get_upper_bound(unsigned j) const {
        return m_imp.lp().get_upper_bound(j);
    }

    const mpq & get_upper_bound_rational(unsigned j) const {
        return m_imp.lp().get_upper_bound(j).x;
    }

    // require also the zero infinitesemal part
    bool column_is_fixed(lpvar j) const {
        return lp().column_is_fixed(j) && get_lower_bound(j).y.is_zero();
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

    bool is_offset_row(unsigned r, lpvar & x, lpvar & y, mpq & k) const {
        if (r >= lp().row_count())
            return false;
        x = y = null_lpvar;
        for (auto& c : lp().get_row(r)) {
            lpvar v = c.var();
            if (column_is_fixed(v)) {
                // if (get_lower_bound_rational(c.var()).is_big())
                //     return false;
                continue;
            }
           
            if (c.coeff().is_one() && x == null_lpvar) {
                x = v;
                continue;
            }
            if (c.coeff().is_minus_one() && y == null_lpvar) {
                y = v;
                continue;
            }
            return false;
        }
    
        if (x == null_lpvar && y == null_lpvar) {
            return false;
        }
        
        k = mpq(0);
        for (const auto& c : lp().get_row(r)) {
            if (!column_is_fixed(c.var()))
                continue;
            k -= c.coeff() * get_lower_bound_rational(c.var());
            if (k.is_big())
                return false;
        }
        
        if (y == null_lpvar)
            return true;

        if (x == null_lpvar) {
            std::swap(x, y);
            k.neg();
            return true;
        }

        if (!lp().is_base(x) && x > y) {
            std::swap(x, y);
            k.neg();
        }
        return true;
    }

    bool is_offset_row_wrong(unsigned row_index,
                       unsigned & x_index,
                       lpvar & y_index,
                       mpq& offset) {
        if (row_index >= lp().row_count())
            return false;
        x_index = y_index = UINT_MAX;
        const auto & row = lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            const auto& c = row[k];
            if (column_is_fixed(c.var()))
                continue;
            if (x_index == UINT_MAX && c.coeff().is_one())
                x_index = k;
            else if (y_index == UINT_MAX && c.coeff().is_minus_one())
                y_index = k;
            else 
                return false;
        }
        if (x_index == UINT_MAX && y_index == UINT_MAX)
            return false;
        if (lp().column_is_int(row[x_index].var()) != lp().column_is_int(row[y_index].var()))
            return false; 

        offset = mpq(0);
        for (const auto& c : row) {
            if (!column_is_fixed(c.var()))
                continue;
            offset += c.coeff() * get_lower_bound_rational(c.var());
        }
        if (offset.is_zero() &&
            !is_equal(row[x_index].var(), row[y_index].var())) {
            lp::explanation ex;
            explain_fixed_in_row(row_index, ex);
            add_eq_on_columns(ex, row[x_index].var(), row[y_index].var());
        }
        return true;
    }    

    bool is_equal(lpvar j, lpvar k) const {        
        return m_imp.is_equal(col_to_imp(j), col_to_imp(k));
    }
    
    void check_for_eq_and_add_to_offset_table(vertex* v) {
        vertex *k; // the other vertex 
        
        if (m_offset_to_verts.find(v->offset(), k)) {
            if (column(k) != column(v) &&
                !is_equal(column(k),column(v)))
                report_eq(k, v);
        } else {
            TRACE("cheap_eq", tout << "registered offset " << v->offset() << " to " << v << "\n";);
            m_offset_to_verts.insert(v->offset(), v);
        }
            
    }
        
    void clear_for_eq() {
        m_visited_rows.reset();
        m_visited_columns.reset();
        m_offset_to_verts.reset();
    }

    // we have v_i and v_j, indices of vertices at the same offsets
    void report_eq(vertex* v_i, vertex* v_j) {
        SASSERT(v_i != v_j);
        TRACE("cheap_eq", tout << column(v_i) << " = " << column(v_j) << "\nu = ";
              v_i->print(tout) << "\nv = "; v_j->print(tout) <<"\n";
              display_row_of_vertex(v_i, tout);
              display_row_of_vertex(v_j, tout);              
              );
        
        ptr_vector<vertex> path;
        find_path_on_tree(path, v_i, v_j);
        TRACE("cheap_eq", tout << "path = \n";
              for (vertex* k : path) {
                  display_row_of_vertex(k, tout);
              });
        lp::explanation exp = get_explanation_from_path(path);
        add_eq_on_columns(exp, column(v_i), column(v_j));
    }

    void add_eq_on_columns(const explanation& exp, lpvar v_i_col, lpvar v_j_col) {
        SASSERT(v_i_col != v_j_col);
        unsigned i_e = lp().column_to_reported_index(v_i_col);
        unsigned j_e = lp().column_to_reported_index(v_j_col);
        TRACE("cheap_eq", tout << "reporting eq " << i_e << ", " << j_e << "\n";
              for (auto p : exp) {
                  lp().constraints().display(tout, [this](lpvar j) { return lp().get_variable_name(j);}, p.ci());
              });
        
        m_imp.add_eq(i_e, j_e, exp);        
    }

   /**
       Cheap propagation of equalities x_i = x_j, when
       x_i = y + k 
       x_j = y + k

       This equalities are detected by maintaining a map:
       (y, k) ->  row_id   when a row is of the form  x = y + k
       If x = k, then y is null_lpvar
       This methods checks whether the given row is an offset row (is_offset_row()) 
       and uses the map to find new equalities if that is the case.
       Some equalities, those spreading more than two rows, can be missed 
    */
    // column to theory_var
    unsigned col_to_imp(unsigned j) const {
        return lp().local_to_external(lp().column_to_reported_index(j));
    }

    // theory_var to column
    unsigned imp_to_col(unsigned j) const {
        return lp().external_to_column_index(j);
    }

    bool is_int(lpvar j) const {
        return lp().column_is_int(j);
    }
    
    void cheap_eq_table(unsigned rid) {
        TRACE("cheap_eqs", tout << "checking if row " << rid << " can propagate equality.\n";  display_row_info(rid, tout););
        unsigned x;
        unsigned y;
        mpq k;
        if (is_offset_row(rid, x, y, k)) {
            if (y == null_lpvar) {
                // x is an implied fixed var at k.
                value_sort_pair key(k, is_int(x));
                int x2;
                if (m_imp.m_fixed_var_table.find(key, x2) && 
                    x2 < static_cast<int>(m_imp.get_num_vars())                    
                    && 
                    lp().column_is_fixed(x2 = imp_to_col(x2)) && // change x2
                        get_lower_bound_rational(x2) == k &&
                    // We must check whether x2 is an integer. 
                    // The table m_fixed_var_table is not restored during backtrack. So, it may
                    // contain invalid (key -> value) pairs. 
                    // So, we must check whether x2 is really equal to k (previous test) 
                    // AND has the same sort of x.
                        is_int(x) == is_int(x2) &&
                    !is_equal(x, x2)) {
                    explanation ex;
                    constraint_index lc, uc;
                    lp().get_bound_constraint_witnesses_for_column(x2, lc, uc);
                    ex.push_back(lc);
                    ex.push_back(uc);
                    explain_fixed_in_row(rid, ex);
                    add_eq_on_columns(ex, x, x2);
                }
            }
            if (k.is_zero() && y != null_lpvar && !is_equal(x, y) &&
                is_int(x) == is_int(y)) {
                explanation ex;
                explain_fixed_in_row(rid, ex);
                add_eq_on_columns(ex, x, y);
            }

            unsigned row_id;
            var_offset key(y, k);
            if (m_var_offset2row_id.find(key, row_id)) {               
                if (row_id == rid) {
                    // it is the same row.
                    return;
                }
                unsigned x2;
                unsigned y2;
                mpq  k2;
                if (is_offset_row(row_id, x2, y2, k2)) {

                    bool new_eq  = false;
#ifdef _TRACE
                    bool swapped = false;
#endif
                    if (y == y2 && k == k2) {
                        new_eq = true;
                    }
                    else if (y2 != null_lpvar) {
#ifdef _TRACE
                        swapped = true;
#endif
                        std::swap(x2, y2);
                        k2.neg();
                        if (y == y2 && k == k2) {
                            new_eq = true;
                        }
                    }

                    if (new_eq) {
                        if (!is_equal(x, x2) && is_int(x) == is_int(x2)) {
                            SASSERT(y == y2 && k == k2);
                            explanation ex;
                            explain_fixed_in_row(rid, ex);
                            explain_fixed_in_row(row_id, ex);
                            TRACE("arith_eq", tout << "propagate eq two rows:\n"; 
                                  tout << "swapped: " << swapped << "\n";
                                  tout << "x  : v" << x << "\n";
                                  tout << "x2 : v" << x2 << "\n";
                                  display_row_info(rid, tout); 
                                  display_row_info(row_id, tout););
                            add_eq_on_columns(ex, x, x2);
                        }
                        return;
                        }
                        }
                // the original row was deleted or it is not offset row anymore ===> remove it from table 
                m_var_offset2row_id.erase(key);
            }
            // add new entry
            m_var_offset2row_id.insert(key, rid);
        }
   }
    
    explanation get_explanation_from_path(const ptr_vector<vertex>& path) const {
        explanation ex;
        unsigned prev_row = UINT_MAX;
        for (vertex* k : path) {
            unsigned row = k->row();
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
    
    std::ostream& display_row_of_vertex(vertex* k, std::ostream& out) const {
        return display_row_info(k->row(), out );
    }
    std::ostream& display_row_info(unsigned r, std::ostream& out) const {
        return lp().get_int_solver()->display_row_info(out, r);
    }

    void find_path_on_tree(ptr_vector<vertex> & path, vertex* u, vertex* v) const {
        vertex* up; // u parent
        vertex* vp; // v parent
        ptr_vector<vertex> v_branch;
        path.push_back(u);
        v_branch.push_back(v);
         // equalize the levels
        while (u->level() > v->level()) {
            up = u->parent();
            if (u->row() == up->row())
                path.push_back(up);
            u = up;
        }
        
        while (u->level() < v->level()) {            
            vp = v->parent();
            if (v->row() == vp->row())
                v_branch.push_back(vp);
            v = vp;
        }
        SASSERT(u->level() == v->level());
        TRACE("cheap_eq", tout << "u = " ;u->print(tout); tout << "\nv = ";v->print(tout);); 
        while (u != v) {
            if (u->row() == v->row() && u->offset() == v->offset()) // we have enough explanation now
                break;
            
            up = u->parent();
            vp = v->parent();
            if (up->row() == u->row())
                path.push_back(up);
            if (vp->row() == v->row())
                v_branch.push_back(vp);
            u = up; v = vp;
        }
        
        for (unsigned i = v_branch.size(); i--; ) {
            path.push_back(v_branch[i]);
        }
    }
    
    bool tree_is_correct() const {
        ptr_vector<vertex> vs;
        vs.push_back(m_root);
        return tree_is_correct(m_root, vs);
    }
    bool contains_vertex(vertex* v, const ptr_vector<vertex> & vs) const {
        for (auto* u : vs) {
            if (*u == *v)
                return true;
        }
        return false;
    }
    bool tree_is_correct(vertex* v, ptr_vector<vertex>& vs) const {
        for (vertex * u : v->children()) {
            if (contains_vertex(u, vs))
                return false;
        }
        for (vertex * u : v->children()) {
            vs.push_back(u);
        }

        for (vertex * u : v->children()) {
            if (!tree_is_correct(u, vs))
                return false;
        }

        return true;
    }
    std::ostream& print_tree(std::ostream & out, vertex* v) const {
        v->print(out);
        out << "children :\n";
        for (auto * v : v->children()) {
            print_tree(out, v);
        }
        return out;
    }
    lpvar column(const vertex* v) const {
        return lp().get_row(v->row())[v->index_in_row()].var();
    }

    void cheap_eq_tree(unsigned row_index) {        
        TRACE("cheap_eq", tout << "row_index = " << row_index << "\n";);
        clear_for_eq();
        unsigned x_index, y_index;
        mpq offset;
        if (!is_offset_row_wrong(row_index, x_index, y_index, offset))
            return;
        TRACE("cheap_eq", lp().get_int_solver()->display_row_info(tout, row_index););
        m_root = alloc(vertex, row_index, x_index, mpq(0));
        vertex* v_y = alloc(vertex, row_index, y_index, offset);
        m_root->add_child(v_y);
        SASSERT(tree_is_correct());
        m_visited_rows.insert(row_index);
        explore_under(m_root);
        TRACE("cheap_eq", tout << "done for row_index " << row_index << "\n";);
        TRACE("cheap_eq", tout << "tree size = " << verts_size(););
        delete_tree(m_root);
    }

    unsigned verts_size() const {
        return subtree_size(m_root);
    }

    unsigned subtree_size(vertex* v) const {
        unsigned r = 1; // 1 for v
        for (vertex * u : v->children())
            r += subtree_size(u);
        return r;
    }
            
    void delete_tree(vertex * v) {
        for (vertex* u : v->children())
            delete_tree(u);
        dealloc(v);
    }
    
    void go_over_vertex_column(vertex * v) {
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
            mpq row_offset;
            if (!is_offset_row_wrong(row_index, x_index, y_index, row_offset))
                continue;
            TRACE("cheap_eq", lp().get_int_solver()->display_row_info(tout, row_index););
            // who is it the same column?
            if (lp().get_row(row_index)[x_index].var() == j) { // conected to x
                vertex* x_v = alloc(vertex, row_index, x_index, v->offset());
                v->add_child(x_v);
                vertex* y_v = alloc(vertex, row_index, y_index, v->offset() + row_offset);
                x_v->add_child(y_v);
                SASSERT(tree_is_correct());
                explore_under(y_v);
            } else { // connected to y
                vertex* y_v = alloc(vertex, row_index, y_index, v->offset());
                v->add_child(y_v);
                vertex* x_v = alloc(vertex, row_index, x_index, v->offset() - row_offset);
                y_v->add_child(x_v);
                SASSERT(tree_is_correct());
                explore_under(x_v);
            }
        }
    }
    
    void explore_under(vertex * v) {
        check_for_eq_and_add_to_offset_table(v);
        go_over_vertex_column(v);
        // v might change in m_vertices expansion
        for (vertex* j : v->children()) {
            explore_under(j);
        }
    }
};
}
