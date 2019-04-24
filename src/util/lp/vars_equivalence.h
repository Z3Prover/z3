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

    struct node {
        unsigned            m_parent;   // points to m_equivs
        svector<unsigned>   m_children;  // point to m_equivs
        node() : m_parent(-1) {}
    };
   
    //fields
    
    // The map from the variables to m_nodes
    // m_tree is a spanning tree of the graph of equivs represented by m_equivs
    std::unordered_map<unsigned, node>            m_tree;  
    // If m_tree[v] == -1 then the variable is a root.
    // if m_tree[v] is not equal to -1 then m_equivs[m_tree[v]] = (k, v) or (v, k), where k is the parent of v
    vector<equiv>                                 m_equivs;         // all equivalences extracted from constraints
    std::function<rational(lpvar)>                m_val;
    

    // constructor
    vars_equivalence(std::function<rational(lpvar)> val) : m_val(val) {}
    
    void clear() {
        m_equivs.clear();
        m_tree.clear();
    }

    // j itself is also included
    svector<lpvar> eq_vars(lpvar j) const {
        svector<lpvar> r = path_to_root(j);
        r.append(children(j));
        r.push_back(j);
        return r;
    } 

    svector<lpvar> children(lpvar j) const {
        svector<lpvar> r;
        auto it = m_tree.find(j);
        if (it == m_tree.end())
            return r;

        const node& n = it->second;
        for (unsigned e_k: n.m_children) {
            const equiv & e = m_equivs[e_k];
            lpvar oj = e.m_i == j? e.m_j : e.m_i;
            r.push_back(oj);
            for (lpvar k :  children(oj)) {
                r.push_back(k);
            }
        }
        return r;
    } 

    
    
    svector<lpvar> path_to_root(lpvar j) const {
        svector<lpvar> r;
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end() || it->second.m_parent == static_cast<unsigned>(-1))
                return r;
              
            const equiv & e = m_equivs[it->second.m_parent];
            j = get_parent_node(j, e);
            r.push_back(j);
        }
        SASSERT(false);
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
        // m_tree is the tree with the edges formed by m_equivs
        const equiv &e = m_equivs[k];
        TRACE("nla_vars_eq", tout << "m_i = " << e.m_i << ", " << "m_j = " << e.m_j ;);
        auto it_i = m_tree.find(e.m_i);
        auto it_j = m_tree.find(e.m_j);
        bool i_is_in = it_i != m_tree.end();
        bool j_is_in = it_j != m_tree.end();
        
        if (!(i_is_in || j_is_in)) {
            // none of the edge vertices is in the tree
            // let m_i be the parent, and m_j be the child
            TRACE("nla_vars_eq", tout << "create nodes for " << e.m_i << " and " << e.m_j; );
            node parent;
            node child;
            child.m_parent = k;
            parent.m_children.push_back(k);
            m_tree.emplace(e.m_i, parent);
            m_tree.emplace(e.m_j, child);
        } else if (i_is_in && (!j_is_in)) {
            // create a node for m_j, with m_i is the parent
            node child;
            child.m_parent = k;
            TRACE("nla_vars_eq", tout << "create a node for " << e.m_j; );
            m_tree.emplace(e.m_j, child);
            it_i->second.m_children.push_back(k);
        } else if ((!i_is_in) && j_is_in) {
            TRACE("nla_vars_eq", tout << "create a node for " << e.m_i; );
            node child;
            child.m_parent = k;            
            m_tree.emplace(e.m_i, child);
            it_j->second.m_children.push_back(k);            
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

        return it->second.m_parent == static_cast<unsigned>(-1);
    }

    static unsigned get_parent_node(unsigned j, const equiv& e) {
        SASSERT(e.m_i == j || e.m_j == j);
        return e.m_i == j? e.m_j : e.m_i;
    }

    bool vars_are_equiv(lpvar a, lpvar b) const {
        return map_to_root(a) == map_to_root(b);
    }


    // Finds the root var which is equivalent to j.
    // The sign is flipped if needed
    lpvar map_to_root(lpvar j, rational& sign) const {
        TRACE("nla_vars_eq", tout << "j = " << j << "\n";);
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return j;
            if (it->second.m_parent == static_cast<unsigned>(-1)) {
                TRACE("nla_vars_eq", tout << "mapped to " << j << "\n";);
                return j;
            }
            const equiv & e = m_equivs[it->second.m_parent];
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
            if (it->second.m_parent == static_cast<unsigned>(-1))
                return j;
            const equiv & e = m_equivs[it->second.m_parent];
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
            if (it->second.m_parent == static_cast<unsigned>(-1))
                return;
            const equiv & e = m_equivs[it->second.m_parent];
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

}; // end of vars_equivalence
}
