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
typedef std::unordered_set<lpci> expl_set;
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

struct rat_hash {
    typedef rational data;
    unsigned operator()(const rational& x) const { return x.hash(); }
};


struct hash_vector {
    size_t operator()(const vector<rational> & v) const {
        return vector_hash<rat_hash>()(v);
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

   
    //fields
    
    // The map from the variables to m_equivs indices
    // m_tree is a spanning tree of the graph of equivs represented by m_equivs
    std::unordered_map<unsigned, unsigned>       m_tree;  
    // If m_tree[v] == -1 then the variable is a root.
    // if m_tree[v] is not equal to -1 then m_equivs[m_tree[v]] = (k, v) or (v, k), that k is the parent of v
    vector<equiv>                                m_equivs;         // all equivalences extracted from constraints
    std::unordered_map<rational,unsigned_vector> m_vars_by_abs_values;
    std::unordered_map<vector<rational>,
                       unsigned_vector,
                       hash_vector>              m_monomials_by_abs_vals;

    std::function<rational(lpvar)> m_vvr;


    // constructor
    vars_equivalence(std::function<rational(lpvar)> vvr) : m_vvr(vvr) {}
    
    const std::unordered_map<vector<rational>,
                             unsigned_vector,
                             hash_vector>& monomials_by_abs_values() const {
        return m_monomials_by_abs_vals;
    }

    
    void clear() {
        m_equivs.clear();
        m_tree.clear();
    }
    // it also returns (j, 1)
    vector<index_with_sign> get_equivalent_vars(lpvar j) const {
        vector<index_with_sign> ret;
        
        rational val = m_vvr(j);
        for (lpvar j : m_vars_by_abs_values.find(abs(val))->second) {
            if (val.is_pos())
                ret.push_back(index_with_sign(j, rational(1)));
            else
                ret.push_back(index_with_sign(j, rational(-1)));
        }
        return ret; 
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
        TRACE("nla_solver", tout << "m_i = " << e.m_i << ", " << "m_j = " << e.m_j ;);
        bool i_is_in = m_tree.find(e.m_i) != m_tree.end();
        bool j_is_in = m_tree.find(e.m_j) != m_tree.end();
        
        if (!(i_is_in || j_is_in)) {
            // none of the edge vertices is in the tree
            // let m_i be the parent, and m_j be the child
            TRACE("nla_solver", tout << "create nodes for " << e.m_i << " and " << e.m_j; );
            m_tree.emplace(e.m_i, -1);
            m_tree.emplace(e.m_j, k);
        } else if (i_is_in && (!j_is_in)) {
            // create a node for m_j, with m_i is the parent
            TRACE("nla_solver", tout << "create a node for " << e.m_j; );
            m_tree.emplace(e.m_j, k);
            // if m_i is a root here we can set its parent m_j
        } else if ((!i_is_in) && j_is_in) {
            TRACE("nla_solver", tout << "create a node for " << e.m_i; );
            m_tree.emplace(e.m_i, k);
            // if m_j is a root here we can set its parent to m_i
        } else {
            TRACE("nla_solver", tout << "both vertices are in the tree";);
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
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return j;
            if (it->second == static_cast<unsigned>(-1))
                return j;
            const equiv & e = m_equivs[it->second];
            sign *= e.m_sign;
            j = get_parent_node(j, e);
        }
    }

    void add_equiv_exp(unsigned j, expl_set& exp) const {
        while (true) {
            auto it = m_tree.find(j);
            if (it == m_tree.end())
                return;
            if (it->second == static_cast<unsigned>(-1))
                return;
            const equiv & e = m_equivs[it->second];
            exp.insert(e.m_c0);
            exp.insert(e.m_c1);
            j = get_parent_node(j, e);
        }
    }
    
    template <typename T>
    void add_explanation_of_reducing_to_rooted_monomial(const T & m, expl_set & exp) const {
        for (auto j : m)
            add_equiv_exp(j, exp);
    }

    void register_var(unsigned j, const rational& val) {
        rational v = abs(val);
        auto it = m_vars_by_abs_values.find(v);
        if (it == m_vars_by_abs_values.end()) {
            unsigned_vector uv;
            uv.push_back(j);
            m_vars_by_abs_values[val] = uv;
        } else {
            it->second.push_back(j);
        }
    }

    void deregister_monomial_from_abs_vals(const monomial & m, unsigned i){
        int sign;
        auto key = get_sorted_abs_vals_from_mon(m, sign);
        SASSERT(m_monomials_by_abs_vals.find(key)->second.back() == i);
        m_monomials_by_abs_vals.find(key)->second.pop_back();
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
    
    void register_monomial_in_abs_vals(unsigned i, const monomial & m ) {
        int sign;
        vector<rational> abs_vals = get_sorted_abs_vals_from_mon(m, sign);
        auto it = m_monomials_by_abs_vals.find(abs_vals);
        if (it == m_monomials_by_abs_vals.end()) {
            unsigned_vector v;
            v.push_back(i);
            // v is a vector containing a single index_with_sign
            m_monomials_by_abs_vals.emplace(abs_vals, v);
        } 
        else {
            it->second.push_back(i);
        }
        
    }

    void clear_monomials_by_abs_vals() {
        m_monomials_by_abs_vals.clear();
    }

}; // end of vars_equivalence
}
