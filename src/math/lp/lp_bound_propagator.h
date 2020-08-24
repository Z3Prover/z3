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
    // vertex represents a pair (row,x) or (row,y) for an offset row.
    // The set of all pair are organised in a tree.
    // The edges of the tree are of the form ((row,x), (row, y)) for an offset row,
    // or ((row, u), (other_row, v)) where the "other_row" is an offset row too,
    // and u, v reference the same column.
    // Vertices with m_neg set to false grow with the same rate as the root.
    // Vertices with m_neq set to true diminish with the same rate as the roow grows.
    // When two vertices with the same m_neg have the same value of columns
    // then we have an equality betweet the columns.
    class vertex {        
        unsigned           m_row; 
        unsigned           m_column;
        ptr_vector<vertex> m_children;
        vertex*            m_parent;
        unsigned           m_level; // the distance in hops to the root;
                                    // it is handy to find the common ancestor
    public:
        vertex() {}
        vertex(unsigned row,
               unsigned column) :
            m_row(row),
            m_column(column),
            m_parent(nullptr),
            m_level(0)
        {}
        unsigned column() const { return m_column; }
        unsigned row() const { return m_row; }
        vertex* parent() const { return m_parent; }
        unsigned level() const { return m_level; }
        void add_child(vertex* child) {
            SASSERT(!(*this == *child));
            child->m_parent = this;
            m_children.push_back(child);
            child->m_level = m_level + 1;
        }
        const ptr_vector<vertex> & children() const { return m_children; }
        bool operator==(const vertex& o) const {
            return m_row == o.m_row && m_column == o.m_column;
        }
    };

    std::ostream& print(std::ostream & out, const vertex* v) const {
        out << "r = " << v->row() << ", c = " << v->column() << ", P = {";
        if (v->parent()) { out << "(" << v->parent()->row() << ", " << v->parent()->column() << ")";}
        else { out << "null"; }
        out <<  "} , lvl = " << v->level();
        if (fixed_phase()) {
            out << " fixed phase";
        } if (m_pol.contains(v->column())) {
            out << (pol(v) == -1? " -":" +");
        } else {
            out << " not in m_pol";
        }
        return out;
    }

    hashtable<unsigned, u_hash, u_eq>         m_visited_rows;
    hashtable<unsigned, u_hash, u_eq>         m_visited_columns;
    vertex*                                   m_root;
    // At some point we can find a row with a single vertex non fixed vertex
    // then we can fix the whole tree,
    // by adjusting the vertices offsets, so they become absolute.
    // If the tree is fixed then in addition to checking with the m_vals_to_verts
    // we are going to check with the m_fixed_var_tables.
    const vertex*                             m_fixed_vertex;
    explanation                               m_fixed_vertex_explanation;
    // a pair (o, j) belongs to m_vals_to_verts iff x[j] = x[m_root->column()] + o
    map<mpq, const vertex*, obj_hash<mpq>, default_eq<mpq>>  m_vals_to_verts;
    // a pair (o, j) belongs to m_vals_to_verts_neg iff -x[j] = x[m_root->column()] + o
    map<mpq, const vertex*, obj_hash<mpq>, default_eq<mpq>>  m_vals_to_verts_neg;
    // x[m_root->column()] - m_pol[j].pol()*x[j] == const;
    // to bind polarity and the vertex in the table
    struct pol_vert {
        int m_polarity;
        const vertex* m_v;
        pol_vert() {}
        pol_vert(int p, const vertex* v): m_polarity(p), m_v(v) {}
        int pol() const { return m_polarity; }
        const vertex* v() const { return m_v; }
    };
    u_map<pol_vert>                                     m_pol; 
    // if m_pos.contains(j) then  x[j] = x[m_root->column()] + o
    uint_set                                  m_pos;
    
    // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned>    m_improved_lower_bounds;
    std::unordered_map<unsigned, unsigned>    m_improved_upper_bounds;
    
    T&                                        m_imp;
    vector<implied_bound>                     m_ibounds;
public:
    const vector<implied_bound>& ibounds() const { return m_ibounds; }
    void init() {
        m_improved_upper_bounds.clear();
        m_improved_lower_bounds.clear();
        m_ibounds.reset();
    }
    lp_bound_propagator(T& imp): m_root(nullptr),
                                 m_fixed_vertex(nullptr),
                                 m_imp(imp) {}
    
    const lar_solver& lp() const { return m_imp.lp(); }
    lar_solver& lp() { return m_imp.lp(); }
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
                if (v > found_bound.m_bound || (v == found_bound.m_bound && !found_bound.m_strict && strict)) {
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
                if (v < found_bound.m_bound || (v == found_bound.m_bound && !found_bound.m_strict && strict)) {
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

    const mpq& val(unsigned j) const { 
        return  lp().get_column_value(j).x;
    }
    
    const mpq& val(const vertex* v) const {
        return val(v->column());
    }
    
    void try_add_equation_with_lp_fixed_tables(const vertex *v) {
        SASSERT(m_fixed_vertex);
        unsigned v_j = v->column();
        unsigned j = null_lpvar;
        if (!lp().find_in_fixed_tables(val(v_j), is_int(v_j), j)) 
            return;
        TRACE("cheap_eq", tout << "found j=" << j << " for v=";
              print(tout, v) << "\n in lp.fixed tables\n";);
        ptr_vector<const vertex> path;
        find_path_on_tree(path, v, m_fixed_vertex);
        explanation ex = get_explanation_from_path(path);
        ex.add_expl(m_fixed_vertex_explanation);
        add_eq_on_columns(ex, j, v->column());
    }

    void try_add_equation_with_val_table(const vertex *v) {
        SASSERT(m_fixed_vertex);
        unsigned v_j = v->column();
        const vertex *u = nullptr;
        if (!m_vals_to_verts.find(val(v_j), u)) {
            m_vals_to_verts.insert(val(v_j), v);
            return;
        }
        unsigned j = u->column();
        if (j == v_j || is_int(j) != is_int(v_j))
            return;
    
        TRACE("cheap_eq", tout << "found j=" << j << " for v=";
              print(tout, v) << "\n in m_vals_to_verts\n";);
        ptr_vector<const vertex> path;
        find_path_on_tree(path, u, v);
        explanation ex = get_explanation_from_path(path);
        ex.add_expl(m_fixed_vertex_explanation);
        add_eq_on_columns(ex, j, v_j);
    }

    
    bool tree_contains_r(vertex* root, vertex *v) const {
        if (*root == *v)
            return true;
        for (vertex *c : root->children()) {
            if (tree_contains_r(c, v))
                return true;
        }
        return false;
    }

    // pol for polarity
    int pol(const vertex* v) const { return pol(v->column()); }
    int pol(unsigned j) const { return m_pol[j].pol(); }
    void set_polarity(const vertex* v, int p) {
        SASSERT(p == 1 || p == -1);
        unsigned j = v->column();
        SASSERT(!m_pol.contains(j));
        m_pol.insert(j, pol_vert(p, v));
    }

    void check_polarity(vertex* v, int polarity) {
        pol_vert prev_pol;
        if (!m_pol.find(v->column(), prev_pol)) {
            set_polarity(v, polarity);
            return;
        }
        if (prev_pol.pol() == polarity)
            return;
        const vertex *u = prev_pol.v();
        // we have a path L between u and v with p(L) = -1, that means we can
        // create an equality of the form x + x = a, where x = v->column() = u->column()
        ptr_vector<const vertex> path;
        find_path_on_tree(path, u, v);
        m_fixed_vertex_explanation = get_explanation_from_path(path);
        set_fixed_vertex(v);
        TRACE("cheap_eq", tout << "polarity switch between: v = "; print(tout , v) << "\nand u = "; print(tout, u) << "\n";);
        TRACE("cheap_eq", tout << "fixed vertex explanation\n";
              for (auto p : m_fixed_vertex_explanation) {
                  lp().constraints().display(tout, [this](lpvar j) { return lp().get_variable_name(j);}, p.ci());
              });

    }
    
    bool tree_contains(vertex *v) const {
        if (!m_root)
            return false;
        return tree_contains_r(m_root, v);
    }
    
    vertex * alloc_v(unsigned row_index, unsigned column) {
        vertex * v = alloc(vertex, row_index, column);
        SASSERT(!tree_contains(v));
        return v;
    }

    static bool not_set(unsigned j) { return j == UINT_MAX; }
    static bool is_set(unsigned j) { return j != UINT_MAX; }
    
    void create_root(unsigned row_index) {
        SASSERT(!m_root && !m_fixed_vertex);
        unsigned x, y;
        int polarity;
        TRACE("cheap_eq", print_row(tout, row_index););
        if (!is_tree_offset_row(row_index, x, y, polarity)) {
            TRACE("cheap_eq", tout << "not an offset row\n";);
            return;
        }
        const mpq& r = val(x);
        m_root = alloc_v(row_index, x);
        set_polarity(m_root, 1);
        if (not_set(y)) {
            set_fixed_vertex(m_root);
            explain_fixed_in_row(row_index, m_fixed_vertex_explanation);
        } else {
            vertex *v = alloc_v(row_index, y);
            m_root->add_child(v);            
            set_polarity(v, polarity);
        }
        // keep root in the positive table
        m_vals_to_verts.insert(r, m_root);
    }

    unsigned column(unsigned row, unsigned index) {
        return lp().get_row(row)[index].var();
    }

    bool fixed_phase() const { return m_fixed_vertex; }

    // Returns the vertex to start exploration from, or nullptr.
    // It is assumed that parent->column() is present in the row
    vertex* add_child_from_row(unsigned row_index, vertex* parent) {
        TRACE("cheap_eq", print_row(tout, row_index););
        unsigned x, y; int polarity;
        if (!is_tree_offset_row(row_index, x, y, polarity)) {
            TRACE("cheap_eq", tout << "not an offset row\n"; );
            return nullptr;
        }
        if (not_set(y)) {
            SASSERT(parent->column() == x);
            vertex *v = alloc_v(row_index, x);
            parent->add_child(v);
            if (!fixed_phase()) {
                set_fixed_vertex(v);
                explain_fixed_in_row(row_index, m_fixed_vertex_explanation);
            }
            return v;
        }
        
        SASSERT(is_set(x) && is_set(y));

        // v has the column of the parent, but the row is different
        vertex *v = alloc_v(row_index, parent->column());        
        parent->add_child(v);
        SASSERT(x == v->column() || y == v->column());
        unsigned col = v->column() == y? x : y;
        vertex *vy = alloc_v(v->row(), col);
        v->add_child(vy);
        if (!fixed_phase())
            check_polarity(vy, polarity * pol(v));
        return v;
    }

    bool is_equal(lpvar j, lpvar k) const {        
        return m_imp.is_equal(col_to_imp(j), col_to_imp(k));
    }

    void check_for_eq_and_add_to_val_table(vertex* v,  map<mpq, const vertex*, obj_hash<mpq>, default_eq<mpq>>& table) {
        TRACE("cheap_eq", tout << "v="; print(tout, v) << "\n";);
        const vertex *k; // the other vertex
        if (table.find(val(v), k)) {
            TRACE("cheap_eq", tout << "found k " ; print(tout, k) << "\n";);
            if (k->column() != v->column() &&
                is_int(k->column()) == is_int(v->column()) &&
                !is_equal(k->column(), v->column())) {
                report_eq(k, v);
            } else {
                TRACE("cheap_eq", tout << "no report\n";);
            }
        } else {
            TRACE("cheap_eq", tout << "registered: " << val(v) << " -> { "; print(tout, v) << "} \n";);
            table.insert(val(v), v);
        }
    }
    
    void check_for_eq_and_add_to_val_tables(vertex* v) {
        TRACE("cheap_eq_det", print(tout, v) << "\n";);
        if (!fixed_phase()) {
            if (pol(v->column()) == -1)
                check_for_eq_and_add_to_val_table(v, m_vals_to_verts_neg);
            else 
                check_for_eq_and_add_to_val_table(v, m_vals_to_verts);
        }
    }
        
    void clear_for_eq() {
        m_visited_rows.reset();
        m_visited_columns.reset();
        m_root = nullptr;
    }

    std::ostream& print_path(const ptr_vector<const vertex>& path, std::ostream& out) const {
        unsigned pr = UINT_MAX;
        out << "path = \n";
        for (const vertex* k : path) {
            print(out, k) << "\n";
            if (k->row() != pr) {
                print_row(out, pr = k->row());
            }
        }
        return out;
    }
    
    // we have v_i and v_j, indices of vertices at the same offsets
    void report_eq(const vertex* v_i, const vertex* v_j) {
        SASSERT(v_i != v_j);
        SASSERT(lp().get_column_value(v_i->column()) == lp().get_column_value(v_j->column()));
        TRACE("cheap_eq", tout << v_i->column() << " = " << v_j->column() << "\nu = ";
              print(tout, v_i) << "\nv = "; print(tout, v_j) <<"\n";
              display_row_of_vertex(v_i, tout);
              if (v_j->row() != v_i->row())
                  display_row_of_vertex(v_j, tout);              
              );
        
        ptr_vector<const vertex> path;
        find_path_on_tree(path, v_i, v_j);
        lp::explanation exp = get_explanation_from_path(path);
        add_eq_on_columns(exp, v_i->column(), v_j->column());
        
    }

    void add_eq_on_columns(const explanation& exp, lpvar j, lpvar k) {
        SASSERT(j != k);
        unsigned je = lp().column_to_reported_index(j);
        unsigned ke = lp().column_to_reported_index(k);
        TRACE("cheap_eq", tout << "reporting eq " << j << ", " << k << "\n";
              for (auto p : exp) {
                  lp().constraints().display(tout, [this](lpvar j) { return lp().get_variable_name(j);}, p.ci());
              }
              tout << "theory_vars  v" << lp().local_to_external(je) << " == v" << lp().local_to_external(ke) << "\n";
              );
        
        m_imp.add_eq(je, ke, exp);
        lp().settings().stats().m_cheap_eqs++;
    }

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
    
    explanation get_explanation_from_path(const ptr_vector<const vertex>& path) const {
        explanation ex;
        unsigned prev_row = UINT_MAX;
        for (const vertex* k : path) {
            unsigned row = k->row();
            if (row == prev_row)
                continue;
            explain_fixed_in_row(prev_row = row, ex);
        }
        return ex;
    }

    void explain_fixed_in_row(unsigned row, explanation& ex) const {
        for (const auto & c : lp().get_row(row)) {
            if (lp().is_fixed(c.var())) {
                explain_fixed_column(ex, c.var());
            }
        }
    }

    void explain_fixed_column(explanation & ex, unsigned j) const {
        SASSERT(column_is_fixed(j));
        constraint_index lc, uc;            
        lp().get_bound_constraint_witnesses_for_column(j, lc, uc);
        ex.push_back(lc);
        ex.push_back(uc);        
    }
    
    std::ostream& display_row_of_vertex(const vertex* k, std::ostream& out) const {
        return print_row(out, k->row());
    }

    void find_path_on_tree(ptr_vector<const vertex> & path, const vertex* u, const vertex* v) const {
        TRACE("cheap_eq_details", tout << "u = " ; print(tout, u); tout << "\nv = ";print(tout, v) << "\n";); 
        vertex* up; // u parent
        vertex* vp; // v parent
        vector<const vertex*> v_branch;
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
        TRACE("cheap_eq_details", tout << "u = " ; print(tout, u); tout << "\nv = "; print(tout, v) << "\n";); 
        while (u != v) {
            up = u->parent();
            vp = v->parent();
            if (up->row() == u->row())
                path.push_back(up);
            if (vp->row() == v->row())
                v_branch.push_back(vp);
            u = up; v = vp;
        }
        
        for (unsigned i = v_branch.size(); i--; ) {
            const vertex * bv = v_branch[i];
            if (path.back() != bv)                
                path.push_back(bv);
        }
        TRACE("cheap_eq", print_path(path, tout););
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
        if (fixed_phase())
            return true;
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
        print(out, v);
        out << "\nchildren :\n";
        for (auto * c : v->children()) {
            print_tree(out, c);
        }
        return out;
    }

    void try_add_equation_with_fixed_tables(const vertex* v) {
        try_add_equation_with_lp_fixed_tables(v);
        try_add_equation_with_val_table(v);
    }
    
    void create_fixed_eqs(const vertex* v) {
        try_add_equation_with_fixed_tables(v);
        for (vertex* c: v->children())
            try_add_equation_with_fixed_tables(c);
    }

    void handle_fixed_phase() {
        create_fixed_eqs(m_root);
    }
    
    void cheap_eq_tree(unsigned row_index) {        
        TRACE("cheap_eq", tout << "row_index = " << row_index << "\n";);        
        if (!check_insert(m_visited_rows, row_index))
            return; // already explored
        create_root(row_index);
        if (m_root == nullptr) {
            return;
        }
        TRACE("cheap_eq", tout << "tree = "; print_tree(tout, m_root) << "\n";);
        SASSERT(tree_is_correct());
        explore_under(m_root);
        if (fixed_phase())
            handle_fixed_phase();
        TRACE("cheap_eq", tout << "done for row_index " << row_index << "\n";);
        TRACE("cheap_eq", tout << "tree size = " << verts_size(););
        delete_tree(m_root);
        m_root = nullptr;
        set_fixed_vertex(nullptr);
        m_fixed_vertex_explanation.clear();
        m_vals_to_verts.reset();
        m_vals_to_verts_neg.reset();
        m_pol.reset();
    }

    std::ostream& print_row(std::ostream & out, unsigned row_index) const  {
        unsigned x, y; int polarity;
        if (true || !is_tree_offset_row(row_index, x, y, polarity))
            return lp().get_int_solver()->display_row_info(out, row_index);
        
        bool first = true;
        for (const auto &c: lp().A_r().m_rows[row_index]) {
            if (lp().column_is_fixed(c.var()))
                continue;
            if (c.coeff().is_one()) {
                    if (!first)
                        out << "+";
                }
                else if (c.coeff().is_minus_one())
                    out << "-";                             
            out << lp().get_variable_name(c.var()) << " ";
            first = false;        
        }
        out << "\n";
        return out;
    }
    
    void set_fixed_vertex(vertex *v) {        
        TRACE("cheap_eq", if (v) print(tout, v); else tout << "set m_fixed_vertex to nullptr"; tout << "\n";);
        SASSERT(!m_fixed_vertex || v == nullptr);
        m_fixed_vertex = v;
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

    template <typename C>
    bool check_insert(C& table, unsigned j) {
        if (table.contains(j))
            return false;
        table.insert(j);
        return true;
    }
    
    void go_over_vertex_column(vertex * v) {
        lpvar j = v->column();
        if (!check_insert(m_visited_columns, j))
            return;
        
        for (const auto & c : lp().get_column(j)) {
            unsigned row_index = c.var();
            if (!check_insert(m_visited_rows, row_index))
                continue;
            vertex *u = add_child_from_row(row_index, v);
            if (u) {
                explore_under(u);
            }
        }
    }
    
    void explore_under(vertex * v) {
        check_for_eq_and_add_to_val_tables(v);
        go_over_vertex_column(v);
        // v might change in m_vertices expansion
        for (vertex* c : v->children()) {
            explore_under(c);
        }
    }

    // In case of only one non fixed column, and the function returns true,
    // this column would be represened by x.
    bool is_tree_offset_row( unsigned row_index,
        unsigned & x, unsigned & y, int & polarity ) const {
        x = y =  UINT_MAX;
        const row_cell<mpq>* x_cell = nullptr;
        const row_cell<mpq>* y_cell = nullptr;
        const auto & row = lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            const auto& c = row[k];
            if (column_is_fixed(c.var()))
                continue;
            if (not_set(x)) {
                if (c.coeff().is_one() || c.coeff().is_minus_one()) {
                    x = c.var();
                    x_cell = & c;
                } else {
                    return false;
                }
            } else if (not_set(y)) {
                if (c.coeff().is_one() || c.coeff().is_minus_one()) {
                    y = c.var();
                    y_cell = & c;
                } else
                    return false;
            } else
                return false;
        }
        if (is_set(x)) {
            if (is_set(y))
                polarity = x_cell->coeff().is_pos() == y_cell->coeff().is_pos()? -1 : 1;
            else
                polarity = 1;
            return true;
        }
        return false;
    }
};
}
