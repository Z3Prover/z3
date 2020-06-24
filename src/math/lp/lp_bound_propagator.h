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
        bool               m_neg; // false if grows with the root, true if grows with -root
    public:
        vertex() {}
        vertex(unsigned row,
               unsigned column,
               bool neg) :
            m_row(row),
            m_column(column),
            m_parent(nullptr),
            m_level(0),
            m_neg(neg)
        {}
        unsigned column() const { return m_column; }
        unsigned row() const { return m_row; }
        vertex* parent() const { return m_parent; }
        unsigned level() const { return m_level; }
        bool neg() const { return m_neg; }
        bool& neg() { return m_neg; }
        void add_child(vertex* child) {
            SASSERT(!(*this == *child));
            child->m_parent = this;
            m_children.push_back(child);
            child->m_level = m_level + 1;
        }
        const ptr_vector<vertex> & children() const { return m_children; }
        std::ostream& print(std::ostream & out) const {
            out << "r = " << m_row << ", c = " << m_column << ", P = {";
            if (m_parent) { out << "(" << m_parent->row() << ", " << m_parent->column() << ")";}
            else { out << "null"; }
            out <<  "} , lvl = " << m_level << (neg()? " -":" +");
            return out;
        }
        bool operator==(const vertex& o) const {
            return m_row == o.m_row && m_column == o.m_column;
        }
    };
    hashtable<unsigned, u_hash, u_eq>         m_visited_rows;
    hashtable<unsigned, u_hash, u_eq>         m_visited_columns;
    vertex*                                   m_root;
    // At some point we can find a row with a single vertex non fixed vertex
    // then we can fix the whole tree,
    // by adjusting the vertices offsets, so they become absolute.
    // If the tree is fixed then in addition to checking with the m_vals_to_verts
    // we are going to check with the m_fixed_var_tables.
    vertex*                                   m_fixed_vertex;
    // a pair (o, j) belongs to m_vals_to_verts iff x[j] = x[m_root->column()] + o
    map<mpq, vertex*, obj_hash<mpq>, mpq_eq>  m_vals_to_verts;
    // a pair (o, j) belongs to m_vals_to_verts_neg iff -x[j] = x[m_root->column()] + o
    map<mpq, vertex*, obj_hash<mpq>, mpq_eq>  m_vals_to_verts_neg;
    // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned>    m_improved_lower_bounds;
    std::unordered_map<unsigned, unsigned>    m_improved_upper_bounds;
    class signed_column {
        bool       m_sign;
        unsigned   m_column;
    public:
        signed_column() : m_column(UINT_MAX) {}
        bool not_set() const { return m_column == UINT_MAX; }
        bool is_set() const { return m_column != UINT_MAX; }
        bool sign() const { return m_sign; }
        bool& sign() { return m_sign; }
        unsigned column() const { return m_column; }
        unsigned& column() { return m_column; }
    };
    
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

    
    bool set_sign_and_column(signed_column& i, const row_cell<mpq> & c) const {
        if (c.coeff().is_one()) {
            i.sign() = false;
            i.column() = c.var();
            return true;
        }
        else if (c.coeff().is_minus_one()){
            i.sign() = true;
            i.column()  = c.var();
            return true;
        }
        return false;
    }
    const mpq& val(unsigned j) const { 
        return  lp().get_column_value(j).x;
    }
    
    const mpq& val(const vertex* v) const {
        return val(v->column());
    }
    
    void try_add_equation_with_fixed_tables(vertex *v) {
        SASSERT(m_fixed_vertex);
        unsigned v_j = v->column();
        unsigned j;
        if (!lp().find_in_fixed_tables(val(v_j), is_int(v_j), j)) 
            return;
        TRACE("cheap_eq", tout << "found j=" << j << " for v=";
              v->print(tout) << "\n in lp.fixed tables\n";);
        ptr_vector<vertex> path;
        find_path_on_tree(path, v, m_fixed_vertex);
        explanation ex = get_explanation_from_path(path);
        explain_fixed_column(ex, j);
        add_eq_on_columns(ex, j, v->column());
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
    
    bool tree_contains(vertex *v) const {
        if (!m_root)
            return false;
        return tree_contains_r(m_root, v);
    }
    
    vertex * alloc_v(unsigned row_index, unsigned column, bool neg) {
        vertex * v = alloc(vertex, row_index, column, neg);
        SASSERT(!tree_contains(v));
        return v;
    }
    
    void create_root(unsigned row_index) {
        SASSERT(!m_root && !m_fixed_vertex);
        signed_column x, y;
        TRACE("cheap_eq", print_row(tout, row_index););
        if (!is_tree_offset_row(row_index, x, y)) {
            TRACE("cheap_eq", tout << "not an offset row\n";);
            return;
        }
        const mpq& r = val(x.column());
        m_root = alloc_v(row_index, x.column(), false);
        if (y.not_set()) {
            set_fixed_vertex(m_root);           
        } else {
            bool neg = x.sign() == y.sign();        
            vertex *v = alloc_v(row_index, y.column(),  neg);
            m_root->add_child(v);            
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
        signed_column x, y;
        if (!is_tree_offset_row(row_index, x, y)) {
            TRACE("cheap_eq", tout << "not an offset row\n"; );
            return nullptr;
        }
        if (y.not_set()) {
            SASSERT(parent->column() == x.column());
            vertex *v = alloc_v( row_index, x.column(), parent->neg());
            parent->add_child(v);
            set_fixed_vertex(v);
            return v;
        }
        
        SASSERT(x.is_set() && y.is_set());

        // v is exactly like parent, but the row is different
        vertex *v = alloc_v(row_index, parent->column(), parent->neg());        
        parent->add_child(v);
        SASSERT(x.column() == v->column() || y.column() == v->column());
        unsigned col = v->column() == y.column()? x.column(): y.column();
        bool neg = x.sign() == y.sign() ? !v->neg(): v->neg();
        vertex *vy = alloc_v(v->row(), col, neg);
        v->add_child(vy);
        return v;
    }

    bool is_equal(lpvar j, lpvar k) const {        
        return m_imp.is_equal(col_to_imp(j), col_to_imp(k));
    }

    void check_for_eq_and_add_to_offset_table(vertex* v,  map<mpq, vertex*, obj_hash<mpq>, mpq_eq>& table) {
        vertex *k; // the other vertex
        if (table.find(val(v), k)) {
            TRACE("cheap_eq", tout << "found k " ; k->print(tout) << "\n";);
            if (k->column() != v->column() &&
                is_int(k->column()) == is_int(v->column()) &&
                !is_equal(k->column(), v->column()))
                report_eq(k, v);
        } else {
            TRACE("cheap_eq", tout << "registered: " << val(v) << " -> { "; v->print(tout) << "} \n";);
            table.insert(val(v), v);
        }
    }
    
    void check_for_eq_and_add_to_offsets(vertex* v) {
        TRACE("cheap_eq_det", v->print(tout) << "\n";);
        if (v->neg())
            check_for_eq_and_add_to_offset_table(v, m_vals_to_verts_neg);
        else 
            check_for_eq_and_add_to_offset_table(v, m_vals_to_verts);                
    }
        
    void clear_for_eq() {
        m_visited_rows.reset();
        m_visited_columns.reset();
        m_root = nullptr;
    }

    std::ostream& print_path(const ptr_vector<vertex>& path, std::ostream& out) const {
        unsigned pr = UINT_MAX;
        out << "path = \n";
        for (vertex* k : path) {
            k->print(out) << "\n";
            if (k->row() != pr) {
                print_row(out, pr = k->row());
            }
        }
        return out;
    }
    
    // we have v_i and v_j, indices of vertices at the same offsets
    void report_eq(vertex* v_i, vertex* v_j) {
        SASSERT(v_i != v_j);
        SASSERT(lp().get_column_value(v_i->column()) == lp().get_column_value(v_j->column()));
        TRACE("cheap_eq", tout << v_i->column() << " = " << v_j->column() << "\nu = ";
              v_i->print(tout) << "\nv = "; v_j->print(tout) <<"\n";
              display_row_of_vertex(v_i, tout);
              if (v_j->row() != v_i->row())
                  display_row_of_vertex(v_j, tout);              
              );
        
        ptr_vector<vertex> path;
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

   /**
       The table functionality:
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
        TRACE("cheap_eqs", tout << "checking if row " << rid << " can propagate equality.\n";  print_row(tout, rid););
        unsigned x = 0, y = 0;
        mpq k;
        if (is_offset_row(rid, x, y, k)) {
            if (y == null_lpvar) {
                // x is an implied fixed var at k.
                unsigned x2 = null_lpvar;
                if (lp().find_in_fixed_tables(k, is_int(x), x2) &&
                    !is_equal(x, x2)) {
                    SASSERT(is_int(x) == is_int(x2) && lp().column_is_fixed(x2) &&
                            get_lower_bound_rational(x2) == k); 
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
                if (row_id == rid) { // it is the same row.
                    return;
                }
                unsigned x2, y2;
                mpq  k2;
                if (is_offset_row(row_id, x2, y2, k2)) {
                    bool new_eq  = false;
                    if (y == y2 && k == k2) {
                        new_eq = true;
                    }
                    else if (y2 != null_lpvar && x2 == y && k == - k2) {
                            std::swap(x2, y2);
                            new_eq = true;
                    }
                    
                    if (new_eq) {
                        if (!is_equal(x, x2) && is_int(x) == is_int(x2)) {
                            //    SASSERT(y == y2 && k == k2 );
                            explanation ex;
                            explain_fixed_in_row(rid, ex);
                            explain_fixed_in_row(row_id, ex);
                            TRACE("arith_eq", tout << "propagate eq two rows:\n"; 
                                  tout << "x  : v" << x << "\n";
                                  tout << "x2 : v" << x2 << "\n";
                                  print_row(tout, rid); 
                                  print_row(tout, row_id););
                            add_eq_on_columns(ex, x, x2);
                        }
                        return;
                    }
                }
                // the original row was deleted or it is not offset row anymore ===> remove it from table 
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
    
    std::ostream& display_row_of_vertex(vertex* k, std::ostream& out) const {
        return print_row(out, k->row());
    }

    void find_path_on_tree(ptr_vector<vertex> & path, vertex* u, vertex* v) const {
        TRACE("cheap_eq_details", tout << "u = " ;u->print(tout); tout << "\nv = ";v->print(tout) << "\n";); 
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
        TRACE("cheap_eq_details", tout << "u = " ;u->print(tout); tout << "\nv = ";v->print(tout) << "\n";); 
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
            vertex * bv = v_branch[i];
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
        if (fixed_phase() && v->neg())
            return false;
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
        out << "\nchildren :\n";
        for (auto * c : v->children()) {
            print_tree(out, c);
        }
        return out;
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
        if (fixed_phase()) {
            create_fixed_eqs(m_root);
        }
        TRACE("cheap_eq", tout << "done for row_index " << row_index << "\n";);
        TRACE("cheap_eq", tout << "tree size = " << verts_size(););
        delete_tree(m_root);
        m_root = nullptr;
        set_fixed_vertex(nullptr);
        m_vals_to_verts.reset();
        m_vals_to_verts_neg.reset();
    }

    void create_fixed_eqs(vertex* v) {
        try_add_equation_with_fixed_tables(v);
        for (vertex* c: v->children())
            try_add_equation_with_fixed_tables(c);
    }

    std::ostream& print_row(std::ostream & out, unsigned row_index) const  {
        signed_column x, y;
        if (true || !is_tree_offset_row(row_index, x, y))
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
        TRACE("cheap_eq", if (v) v->print(tout); else tout << "set m_fixed_vertex to nullptr"; tout << "\n";);
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
        check_for_eq_and_add_to_offsets(v);
        go_over_vertex_column(v);
        // v might change in m_vertices expansion
        for (vertex* c : v->children()) {
            explore_under(c);
        }
    }

    // In case of only one non fixed column, and the function returns true,
    // this column would be represened by x.
    bool is_tree_offset_row( unsigned row_index,
        signed_column & x,
        signed_column & y) const {
        const auto & row = lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            const auto& c = row[k];
            if (column_is_fixed(c.var()))
                continue;
            if (x.not_set()) {
                if (!set_sign_and_column(x, c))
                    return false;
            } else if (y.not_set()) {
                if (!set_sign_and_column(y, c))
                    return false;
            } else
                return false;
        }
        return x.is_set() || y.is_set();
    }    
};
}
