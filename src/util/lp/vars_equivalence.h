/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/

namespace nla {

typedef lp::constraint_index     lpci;
typedef lp::explanation          expl_set;
typedef lp::var_index            lpvar;
struct hash_svector {
    size_t operator()(const unsigned_vector & v) const {
        return svector_hash<unsigned_hash>()(v);
    }
};

struct index_with_sign {
    unsigned m_i; // the index
    rational m_sign; // the sign: -1 or 1
    index_with_sign(unsigned i, rational sign) : m_i(i), m_sign(sign) {}
    index_with_sign() {}
    bool operator==(const index_with_sign& b) {
        return m_i == b.m_i && m_sign == b.m_sign;
    }
    unsigned var() const { return m_i; }
    const rational& sign() const { return m_sign; }
};


struct vars_equivalence {
    
    struct equiv {
        lpvar                m_i;
        lpvar                m_j;
        rational             m_sign;
        lpci                 m_c0;
        lpci                 m_c1;

        equiv(lpvar i, lpvar j, rational const& sign, lpci c0, lpci c1) :
            m_i(i),
            m_j(j),
            m_sign(sign),
            m_c0(c0),
            m_c1(c1) {
            SASSERT(m_i != m_j);
        }
    };

   
    //fields
    
    // The map from the variables to m_equivs indices
    // m_tree is a spanning tree of the graph of equivs represented by m_equivs
    std::unordered_map<unsigned, unsigned>        m_tree;  
    // If m_tree[v] == -1 then the variable is a root.
    // if m_tree[v] is not equal to -1 then m_equivs[m_tree[v]] = (k, v) or (v, k), that k is the parent of v
    vector<equiv>                                 m_equivs;         // all equivalences extracted from constraints
    std::unordered_map<rational, unsigned_vector> m_vars_by_abs_values;
    std::function<rational(lpvar)>                m_vvr;
    

    // constructor
    vars_equivalence(std::function<rational(lpvar)> vvr) : m_vvr(vvr) {}
    
    void clear() {
        m_equivs.clear();
        m_tree.clear();
        m_vars_by_abs_values.clear(); 
    }

    const svector<lpvar>& get_vars_with_the_same_abs_val(const rational& v) const {
        auto it = m_vars_by_abs_values.find(abs(v));
        SASSERT (it != m_vars_by_abs_values.end());
        return it->second; 
    } 

    unsigned size() const { return static_cast<unsigned>(m_tree.size()); }

    // we create a spanning tree on all variables participating in an equivalence
    void create_tree() {
        for (unsigned k = 0; k < m_equivs.size(); k++)
            connect_equiv_to_tree(k);
    }

    void add_equiv(lpvar i, lpvar j, rational const& sign, lpci c0, lpci c1) {
        m_equivs.push_back(equiv(i, j, sign, c0, c1));
    }
    
    void connect_equiv_to_tree(unsigned k) {
        // m_tree is a spanning tree of the graph of m_equivs
        const equiv &e = m_equivs[k];
        TRACE("nla_vars_eq", tout << "m_i = " << e.m_i << ", " << "m_j = " << e.m_j ;);
        bool i_is_in = m_tree.find(e.m_i) != m_tree.end();
        bool j_is_in = m_tree.find(e.m_j) != m_tree.end();
        
        if (!(i_is_in || j_is_in)) {
            // none of the edge vertices is in the tree
            // let m_i be the parent, and m_j be the child
            TRACE("nla_vars_eq", tout << "create nodes for " << e.m_i << " and " << e.m_j; );
            m_tree.emplace(e.m_i, -1);
            m_tree.emplace(e.m_j, k);
        } else if (i_is_in && (!j_is_in)) {
            // create a node for m_j, with m_i is the parent
            TRACE("nla_vars_eq", tout << "create a node for " << e.m_j; );
            m_tree.emplace(e.m_j, k);
            // if m_i is a root here we can set its parent m_j
        } else if ((!i_is_in) && j_is_in) {
            TRACE("nla_vars_eq", tout << "create a node for " << e.m_i; );
            m_tree.emplace(e.m_i, k);
            // if m_j is a root here we can set its parent to m_i
        } else {
            TRACE("nla_vars_eq", tout << "both vertices are in the tree";);
        }
    }
    
    bool empty() const {
        return m_tree.empty();
    }

    bool is_root(unsigned j) const {
        auto it = m_tree.find(j);
        if (it == m_tree.end())
            return true;

        return it->second == static_cast<unsigned>(-1);
    }

    static unsigned get_parent_node(unsigned j, const equiv& e) {
        SASSERT(e.m_i == j || e.m_j == j);
        return e.m_i == j? e.m_j : e.m_i;
    }
    
    // Finds the root var which is equivalent to j.
    // The sign is flipped if needed
    lpvar map_to_root(lpvar j, rational& sign) const {
        TRACE("nla_vars_eq", tout << "j = " << j << "\n";);
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return j;
            if (it->second == static_cast<unsigned>(-1)) {
                TRACE("nla_vars_eq", tout << "mapped to " << j << "\n";);
                return j;
            }
            const equiv & e = m_equivs[it->second];
            sign *= e.m_sign;
            j = get_parent_node(j, e);
        }
    }

        // Finds the root var which is equivalent to j.
    // The sign is flipped if needed
    lpvar map_to_root(lpvar j) const {
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return j;
            if (it->second == static_cast<unsigned>(-1))
                return j;
            const equiv & e = m_equivs[it->second];
            j = get_parent_node(j, e);
        }
    }

    template <typename T>
    void explain(const T& collection, expl_set & exp) const {
        for (lpvar j : collection) {
            explain(j, exp);
        }
    } 
    void explain(lpvar j, expl_set& exp) const {
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return;
            if (it->second == static_cast<unsigned>(-1))
                return;
            const equiv & e = m_equivs[it->second];
            exp.add(e.m_c0);
            exp.add(e.m_c1);
            j = get_parent_node(j, e);
        }
    }
    
    template <typename T>
    void add_explanation_of_reducing_to_rooted_monomial(const T & m, expl_set & exp) const {
        for (lpvar j : m)
            explain(j, exp);
    }

    void register_var(unsigned j, const rational& val) {
        TRACE("nla_vars_eq", tout << "j = " << j;);
        rational v = abs(val);
        auto it = m_vars_by_abs_values.find(v);
        if (it == m_vars_by_abs_values.end()) {
            unsigned_vector uv;
            uv.push_back(j);
            m_vars_by_abs_values[v] = uv;
        } else {
            it->second.push_back(j);
        }
    }

    vector<rational> get_sorted_abs_vals_from_mon(const monomial& m, int & sign) {
        sign = 1;
        vector<rational> abs_vals;
        for (lpvar j : m) {
            const rational v = m_vvr(j);
            abs_vals.push_back(abs(v));
            if (v.is_neg()) {
                sign = -sign;
            }
        }
        std::sort(abs_vals.begin(), abs_vals.end());
        return abs_vals;
    }
}; // end of vars_equivalence
}
