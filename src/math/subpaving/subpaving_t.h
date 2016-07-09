/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_t.h

Abstract:

    Subpaving template for non-linear arithmetic.

Author:

    Leonardo de Moura (leonardo) 2012-07-31.

Revision History:

--*/
#ifndef SUBPAVING_T_H_
#define SUBPAVING_T_H_

#include<iostream>
#include"tptr.h"
#include"small_object_allocator.h"
#include"chashtable.h"
#include"parray.h"
#include"interval.h"
#include"scoped_numeral_vector.h"
#include"subpaving_types.h"
#include"params.h"
#include"statistics.h"
#include"lbool.h"
#include"id_gen.h"
#include"rlimit.h"
#ifdef _MSC_VER
#pragma warning(disable : 4200)
#pragma warning(disable : 4355)
#endif

namespace subpaving {

template<typename C>
class context_t {
public:
    typedef typename C::numeral_manager       numeral_manager;
    typedef typename numeral_manager::numeral numeral;

    /**
       \brief Inequalities used to encode a problem.
    */
    class ineq {
        friend class context_t;
        var         m_x;
        numeral     m_val;
        unsigned    m_ref_count:30;
        unsigned    m_lower:1;
        unsigned    m_open:1;
    public:
        var x() const { return m_x; }
        numeral const & value() const { return m_val; }
        bool is_lower() const { return m_lower; }
        bool is_open() const { return m_open; }
        void display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc = display_var_proc());
        struct lt_var_proc { bool operator()(ineq const * a, ineq const * b) const { return a->m_x < b->m_x; } };
    };

    class node;

    class constraint {
    public:
        enum kind {
            CLAUSE, MONOMIAL, POLYNOMIAL
            // TODO: add SIN, COS, TAN, ...
        };
    protected:
        kind   m_kind;
        uint64 m_timestamp;
    public:
        constraint(kind k):m_kind(k), m_timestamp(0) {}
        
        kind get_kind() const { return m_kind; }
        
        // Return the timestamp of the last propagation visit
        uint64 timestamp() const { return m_timestamp; }
        // Reset propagation visit time
        void set_visited(uint64 ts) { m_timestamp = ts; }
    };

    /**
       \brief Clauses in the problem description and lemmas learned during paving.
    */
    class clause : public constraint {
        friend class context_t;
        unsigned m_size;            //!< Number of atoms in the clause.
        unsigned m_lemma:1;         //!< True if it is a learned clause.
        unsigned m_watched:1;       //!< True if it we are watching this clause. All non-lemmas are watched.
        unsigned m_num_jst:30;      //!< Number of times it is used to justify some bound.
        ineq *   m_atoms[0];
        static unsigned get_obj_size(unsigned sz) { return sizeof(clause) + sz*sizeof(ineq*); }
    public:
        clause():constraint(constraint::CLAUSE) {}
        unsigned size() const { return m_size; }
        bool watched() const { return m_watched; }
        ineq * operator[](unsigned i) const { SASSERT(i < size()); return m_atoms[i]; }
        void display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc = display_var_proc());
    };

    class justification {
        void * m_data;
    public:
        enum kind {
            AXIOM = 0,
            ASSUMPTION,
            CLAUSE,
            VAR_DEF
        };
        
        justification(bool axiom = true) {
            m_data = axiom ? reinterpret_cast<void*>(static_cast<size_t>(AXIOM)) : reinterpret_cast<void*>(static_cast<size_t>(ASSUMPTION));
        }
        justification(justification const & source) { m_data = source.m_data; }
        explicit justification(clause * c) { m_data = TAG(void*, c, CLAUSE); }
        explicit justification(var x) { m_data = BOXTAGINT(void*, x, VAR_DEF);  }
        
        kind get_kind() const { return static_cast<kind>(GET_TAG(m_data)); }
        bool is_clause() const { return get_kind() == CLAUSE; }
        bool is_axiom() const { return get_kind() == AXIOM; }
        bool is_assumption() const { return get_kind() == ASSUMPTION; }
        bool is_var_def() const { return get_kind() == VAR_DEF; }

        clause * get_clause() const {
            SASSERT(is_clause());
            return UNTAG(clause*, m_data);
        }

        var get_var() const { 
            SASSERT(is_var_def());
            return UNBOXINT(m_data);
        }
        
        bool operator==(justification const & other) const { return m_data == other.m_data;  }
        bool operator!=(justification const & other) const { return !operator==(other); }
    };

    class bound {
        friend class context_t;
        numeral       m_val;
        unsigned      m_x:29;
        unsigned      m_lower:1;
        unsigned      m_open:1;
        unsigned      m_mark:1;
        uint64        m_timestamp;
        bound *       m_prev;
        justification m_jst;
        void set_timestamp(uint64 ts) { m_timestamp = ts; }
    public:
        var x() const { return static_cast<var>(m_x); }
        numeral const & value() const { return m_val; }
        numeral & value() { return m_val; }
        bool is_lower() const { return m_lower; }
        bool is_open() const { return m_open; }
        uint64 timestamp() const { return m_timestamp; }
        bound * prev() const { return m_prev; }
        justification jst() const { return m_jst; }
        void display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc = display_var_proc());
    };

    struct bound_array_config {
        typedef context_t                value_manager;
        typedef small_object_allocator   allocator;
        typedef bound *                  value;                    
        static const bool ref_count        = false;
        static const bool preserve_roots   = true;
        static const unsigned max_trail_sz = 16;
        static const unsigned factor       = 2;
    };
    
    // auxiliary declarations for parray_manager
    void dec_ref(bound *) {}
    void inc_ref(bound *) {}

    typedef parray_manager<bound_array_config> bound_array_manager;
    typedef typename bound_array_manager::ref  bound_array;

    /**
       \brief Node in the context_t.
    */
    class node {
        bound_array_manager & m_bm;
        bound_array           m_lowers;
        bound_array           m_uppers;
        var                   m_conflict;
        unsigned              m_id;
        unsigned              m_depth;
        bound *               m_trail;
        node *                m_parent; //!< parent node
        node *                m_first_child;
        node *                m_next_sibling;
        // Doubly linked list of leaves to be processed
        node *                m_prev;
        node *                m_next;
    public:
        node(context_t & s, unsigned id);
        node(node * parent, unsigned id);
        // return unique indentifier.
        unsigned id() const { return m_id; }
        bound_array_manager & bm() const { return m_bm; }
        bound_array & lowers() { return m_lowers; }
        bound_array & uppers() { return m_uppers; }
        bool inconsistent() const { return m_conflict != null_var; }
        void set_conflict(var x) { SASSERT(!inconsistent()); m_conflict = x; }
        bound * trail_stack() const { return m_trail; }
        bound * parent_trail_stack() const { return m_parent == 0 ? 0 : m_parent->m_trail; }
        bound * lower(var x) const { return bm().get(m_lowers, x); }
        bound * upper(var x) const { return bm().get(m_uppers, x); }
        node * parent() const { return m_parent; }
        node * first_child() const { return m_first_child; }
        node * next_sibling() const { return m_next_sibling; }
        node * prev() const { return m_prev; }
        node * next() const { return m_next; }
        /**
           \brief Return true if x is unbounded in this node
        */
        bool is_unbounded(var x) const { return lower(x) == 0 && upper(x) == 0; }
        void push(bound * b);
    
        void set_first_child(node * n) { m_first_child = n; }
        void set_next_sibling(node * n) { m_next_sibling = n; } 
        void set_next(node * n) { m_next = n; }
        void set_prev(node * n) { m_prev = n; }

        unsigned depth() const { return m_depth; }
    };
    
    /**
       \brief Intervals are just temporary place holders.
       The pavers maintain bounds. 
    */
    struct interval {
        bool   m_constant; // Flag: constant intervals are pairs <node*, var>
        // constant intervals
        node * m_node;
        var    m_x;
        // mutable intervals
        numeral      m_l_val;
        bool         m_l_inf;
        bool         m_l_open;
        numeral      m_u_val;
        bool         m_u_inf;
        bool         m_u_open;
        
        interval():m_constant(false) {}
        void set_constant(node * n, var x) { 
            m_constant = true; 
            m_node = n; 
            m_x = x; 
        }
        void set_mutable() { m_constant = false; }
    };
    
    class interval_config {
    public:
        typedef typename C::numeral_manager         numeral_manager;
        typedef typename numeral_manager::numeral   numeral;
        typedef typename context_t::interval        interval;
    private:
        numeral_manager & m_manager;
    public:
        interval_config(numeral_manager & m):m_manager(m) {}

        numeral_manager & m() const { return m_manager; }
        void round_to_minus_inf() { C::round_to_minus_inf(m()); }
        void round_to_plus_inf() {  C::round_to_plus_inf(m()); }
        void set_rounding(bool to_plus_inf) {  C::set_rounding(m(), to_plus_inf); }
        numeral const & lower(interval const & a) const {
            if (a.m_constant) {
                bound * b = a.m_node->lower(a.m_x);
                return b == 0 ? a.m_l_val /* don't care */ : b->value();
            }
            return a.m_l_val;
        }
        numeral const & upper(interval const & a) const {
            if (a.m_constant) {
                bound * b = a.m_node->upper(a.m_x);
                return b == 0 ? a.m_u_val /* don't care */ : b->value();
            }
            return a.m_u_val;
        }
        numeral & lower(interval & a) { SASSERT(!a.m_constant); return a.m_l_val; }
        numeral & upper(interval & a) { SASSERT(!a.m_constant); return a.m_u_val; }
        bool lower_is_inf(interval const & a) const { return a.m_constant ? a.m_node->lower(a.m_x) == 0 : a.m_l_inf; }
        bool upper_is_inf(interval const & a) const { return a.m_constant ? a.m_node->upper(a.m_x) == 0 : a.m_u_inf; }
        bool lower_is_open(interval const & a) const {
            if (a.m_constant) {
                bound * b = a.m_node->lower(a.m_x);
                return b == 0 || b->is_open();
            }
            return a.m_l_open;
        }
        bool upper_is_open(interval const & a) const {
            if (a.m_constant) {
                bound * b = a.m_node->upper(a.m_x);
                return b == 0 || b->is_open();
            }
            return a.m_u_open; 
        }
        // Setters
        void set_lower(interval & a, numeral const & n) { SASSERT(!a.m_constant); m().set(a.m_l_val, n); }
        void set_upper(interval & a, numeral const & n) { SASSERT(!a.m_constant); m().set(a.m_u_val, n); }
        void set_lower_is_open(interval & a, bool v) { SASSERT(!a.m_constant); a.m_l_open = v; }
        void set_upper_is_open(interval & a, bool v) { SASSERT(!a.m_constant); a.m_u_open = v; }
        void set_lower_is_inf(interval & a, bool v) { SASSERT(!a.m_constant); a.m_l_inf = v; }
        void set_upper_is_inf(interval & a, bool v) { SASSERT(!a.m_constant); a.m_u_inf = v; }
    };

    typedef ::interval_manager<interval_config> interval_manager;

    class definition : public constraint {
    public:
        definition(typename constraint::kind k):constraint(k) {}
    };

    class monomial : public definition {
        friend class context_t;
        unsigned m_size;
        power    m_powers[0];
        monomial(unsigned sz, power const * pws);
        static unsigned get_obj_size(unsigned sz) { return sizeof(monomial) + sz*sizeof(power); }
    public:
        unsigned size() const { return m_size; }
        power const & get_power(unsigned idx) const { SASSERT(idx < size()); return m_powers[idx]; }
        power const * get_powers() const { return m_powers; }
        var x(unsigned idx) const { return get_power(idx).x(); }
        unsigned degree(unsigned idx) const { return get_power(idx).degree(); }
        void display(std::ostream & out, display_var_proc const & proc = display_var_proc(), bool use_star = false) const;
    };

    class polynomial : public definition {
        friend class context_t;
        unsigned    m_size;
        numeral     m_c;
        numeral *   m_as;
        var *       m_xs;
        static unsigned get_obj_size(unsigned sz) { return sizeof(polynomial) + sz*sizeof(numeral) + sz*sizeof(var); }
    public:
        polynomial():definition(constraint::POLYNOMIAL) {}
        unsigned size() const { return m_size; }
        numeral const & a(unsigned i) const { return m_as[i]; }
        var x(unsigned i) const { return m_xs[i]; }
        var const * xs() const { return m_xs; }
        numeral const * as() const { return m_as; }
        numeral const & c() const { return m_c; }
        void display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc = display_var_proc(), bool use_star = false) const;
    };

    /**
       \brief Watched element (aka occurrence) can be:
       
       - A clause
       - A definition (i.e., a variable)

       Remark: we cannot use the two watched literal approach since we process multiple nodes.
    */
    class watched {
    public:
        enum kind { CLAUSE=0, DEFINITION };
    private:
        void * m_data;
    public:
        watched():m_data(0) {}
        explicit watched(var x) { m_data = BOXTAGINT(void*, x, DEFINITION); }
        explicit watched(clause * c) { m_data = TAG(void*, c, CLAUSE); }
        kind get_kind() const { return static_cast<kind>(GET_TAG(m_data)); }
        bool is_clause() const { return get_kind() != DEFINITION; }
        bool is_definition() const { return get_kind() == DEFINITION; }
        clause * get_clause() const { SASSERT(is_clause()); return UNTAG(clause*, m_data); }
        var get_var() const { SASSERT(is_definition()); return UNBOXINT(m_data); }
        bool operator==(watched const & other) const { return m_data == other.m_data;  }
        bool operator!=(watched const & other) const { return !operator==(other); }
    };

    /**
       \brief Abstract functor for selecting the next leaf node to be explored.
    */
    class node_selector {
        context_t * m_ctx;
    public:
        node_selector(context_t * ctx):m_ctx(ctx) {}
        virtual ~node_selector() {}

        context_t * ctx() const { return m_ctx; }

        // Return the next leaf node to be processed. 
        // Front and back are the first and last nodes in the doubly linked list of
        // leaf nodes. 
        // Remark: new nodes are always inserted in the front of the list.
        virtual node * operator()(node * front, node * back) = 0;
    };

    /**
       \brief Abstract functor for selecting the next variable to branch.
    */
    class var_selector {
        context_t * m_ctx;
    public:
        var_selector(context_t * ctx):m_ctx(ctx) {}
        virtual ~var_selector() {}

        context_t * ctx() const { return m_ctx; }

        // Return the next variable to branch.
        virtual var operator()(node * n) = 0;
        
        // -----------------------------------
        //
        // Event handlers
        //
        // -----------------------------------

        // Invoked when a new variable is created.
        virtual void new_var_eh(var x) {}
        // Invoked when node n is created
        virtual void new_node_eh(node * n) {}
        // Invoked before deleting node n.
        virtual void del_node_eh(node * n) {}
        // Invoked when variable x is used during conflict resolution.
        virtual void used_var_eh(node * n, var x) {}
    };

    class node_splitter;
    friend class node_splitter;

    /**
       \brief Abstract functor for creating children for node n by branching on a given variable.
    */
    class node_splitter {
        context_t * m_ctx;
    public:
        node_splitter(context_t * ctx):m_ctx(ctx) {}
        virtual ~node_splitter() {}
        
        context_t * ctx() const { return m_ctx; }
        node * mk_node(node * p) { return ctx()->mk_node(p); }
        bound * mk_decided_bound(var x, numeral const & val, bool lower, bool open, node * n) { 
            return ctx()->mk_bound(x, val, lower, open, n, justification());
        }
        
        /**                                     
          \brief Create children nodes for n by splitting on x.
        
          \pre n is a leaf. The interval for x in n has more than one element.
        */
        virtual void operator()(node * n, var x) = 0;
    };

    /**
       \brief Return most recent splitting var for node n.
    */
    var splitting_var(node * n) const;

    /**
       \brief Return true if x is a definition.
    */
    bool is_definition(var x) const { return m_defs[x] != 0; }
    
    typedef svector<watched> watch_list;
    typedef _scoped_numeral_vector<numeral_manager> scoped_numeral_vector;

private:
    reslimit&                 m_limit;
    C                         m_c;
    bool                      m_arith_failed; //!< True if the arithmetic module produced an exception.
    bool                      m_own_allocator;
    small_object_allocator *  m_allocator;
    bound_array_manager       m_bm;
    interval_manager          m_im;
    scoped_numeral_vector     m_num_buffer;

    svector<bool>             m_is_int;
    ptr_vector<definition>    m_defs;
    vector<watch_list>        m_wlist;

    ptr_vector<ineq>          m_unit_clauses;
    ptr_vector<clause>        m_clauses;
    ptr_vector<clause>        m_lemmas;
    
    id_gen                    m_node_id_gen;

    uint64                    m_timestamp;
    node *                    m_root;
    // m_leaf_head is the head of a doubly linked list of leaf nodes to be processed.
    node *                    m_leaf_head; 
    node *                    m_leaf_tail;

    var                       m_conflict;
    ptr_vector<bound>         m_queue;
    unsigned                  m_qhead;

    display_var_proc          m_default_display_proc;
    display_var_proc *        m_display_proc;

    scoped_ptr<node_selector> m_node_selector;
    scoped_ptr<var_selector>  m_var_selector;
    scoped_ptr<node_splitter> m_node_splitter;
    
    svector<power>            m_pws;

    // Configuration
    numeral                   m_epsilon;         //!< If upper - lower < epsilon, then new bound is not propagated.
    bool                      m_zero_epsilon;
    numeral                   m_max_bound;       //!< Bounds > m_max and < -m_max are not propagated
    numeral                   m_minus_max_bound; //!< -m_max_bound
    numeral                   m_nth_root_prec;   //!< precision for computing the nth root
    unsigned                  m_max_depth;       //!< Maximum depth
    unsigned                  m_max_nodes;       //!< Maximum number of nodes in the tree
    unsigned long long        m_max_memory;      // in bytes
    
    // Counters
    unsigned                  m_num_nodes;
    
    // Statistics
    unsigned                  m_num_conflicts;
    unsigned                  m_num_mk_bounds;
    unsigned                  m_num_splits;
    unsigned                  m_num_visited;
    
    // Temporary
    numeral                   m_tmp1, m_tmp2, m_tmp3;
    interval                  m_i_tmp1, m_i_tmp2, m_i_tmp3;


    friend class node;

    void set_arith_failed() { m_arith_failed = true; }

    void checkpoint();

    bound_array_manager & bm() { return m_bm; }
    interval_manager & im() { return m_im; }
    small_object_allocator & allocator() const { return *m_allocator; }

    bound * mk_bound(var x, numeral const & val, bool lower, bool open, node * n, justification jst);
    void del_bound(bound * b);
    // Create a new bound and add it to the propagation queue.
    void propagate_bound(var x, numeral const & val, bool lower, bool open, node * n, justification jst);

    bool is_int(monomial const * m) const;
    bool is_int(polynomial const * p) const;
    
    bool is_monomial(var x) const { return m_defs[x] != 0 && m_defs[x]->get_kind() == constraint::MONOMIAL; }
    monomial * get_monomial(var x) const { SASSERT(is_monomial(x)); return static_cast<monomial*>(m_defs[x]); }
    bool is_polynomial(var x) const { return m_defs[x] != 0 && m_defs[x]->get_kind() == constraint::POLYNOMIAL; }
    polynomial * get_polynomial(var x) const { SASSERT(is_polynomial(x)); return static_cast<polynomial*>(m_defs[x]); }
    static void display(std::ostream & out, numeral_manager & nm, display_var_proc const & proc, var x, numeral & k, bool lower, bool open);
    void display(std::ostream & out, var x) const;
    void display_definition(std::ostream & out, definition const * d, bool use_star = false) const;
    void display(std::ostream & out, constraint * a, bool use_star = false) const;
    void display(std::ostream & out, bound * b) const;
    void display(std::ostream & out, ineq * a) const;
    void display_params(std::ostream & out) const;
    void add_unit_clause(ineq * a, bool axiom);
    // Remark: Not all lemmas need to be watched. Some of them can be used to justify clauses only.
    void add_clause_core(unsigned sz, ineq * const * atoms, bool lemma, bool watched);
    void del_clause(clause * cls);

    node * mk_node(node * parent = 0);
    void del_node(node * n);
    void del_nodes();

    void del(interval & a);
    void del_clauses(ptr_vector<clause> & cs);
    void del_unit_clauses();
    void del_clauses();
    void del_monomial(monomial * m);
    void del_sum(polynomial * p);
    void del_definitions();

    /**
       \brief Insert n in the beginning of the doubly linked list of leaves.

       \pre n is a leaf, and it is not already in the list.
    */
    void push_front(node * n);
    
    /**
       \brief Insert n in the end of the doubly linked list of leaves.
       
       \pre n is a leaf, and it is not already in the list.
    */
    void push_back(node * n);
    
    /**
       \brief Remove n from the doubly linked list of leaves.

       \pre n is a leaf, and it is in the list.
    */
    void remove_from_leaf_dlist(node * n);
    
    /**
       \brief Remove all nodes from the leaf dlist.
    */
    void reset_leaf_dlist();
    
    /**
       \brief Add all leaves back to the leaf dlist.
    */
    void rebuild_leaf_dlist(node * n);

    // -----------------------------------
    //
    // Propagation
    //
    // -----------------------------------

    /**
       \brief Return true if the given node is in an inconsistent state. 
    */
    bool inconsistent(node * n) const { return n->inconsistent(); }

    /**
       \brief Set a conflict produced by the bounds of x at the given node.
    */
    void set_conflict(var x, node * n);

    /**
       \brief Return true if bound b may propagate a new bound using constraint c at node n.
    */
    bool may_propagate(bound * b, constraint * c, node * n);

    /**
       \brief Normalize bound if x is integer.
       
       Examples:
       x < 2     --> x <= 1
       x <= 2.3  --> x <= 2
    */
    void normalize_bound(var x, numeral & val, bool lower, bool & open);

    /**
       \brief Return true if (x, k, lower, open) is a relevant new bound at node n.
       That is, it improves the current bound, and satisfies m_epsilon and m_max_bound.
    */
    bool relevant_new_bound(var x, numeral const & k, bool lower, bool open, node * n);

    /**
       \brief Return true if the lower and upper bounds of x are 0 at node n.
    */
    bool is_zero(var x, node * n) const;

    /**
       \brief Return true if upper bound of x is 0 at node n.
    */
    bool is_upper_zero(var x, node * n) const;

    /**
       \brief Return true if lower and upper bounds of x are conflicting at node n. That is, upper(x) < lower(x)
    */
    bool conflicting_bounds(var x, node * n) const;

    /**
       \brief Return true if x is unbounded at node n.
    */
    bool is_unbounded(var x, node * n) const { return n->is_unbounded(x); }

    /**
       \brief Return true if b is the most recent lower/upper bound for variable b->x() at node n.
    */
    bool most_recent(bound * b, node * n) const;

    /**
       \brief Add most recent bounds of node n into the propagation queue.
       That is, all bounds b s.t. b is in the trail of n, but not in the tail of parent(n), and most_recent(b, n).
    */
    void add_recent_bounds(node * n);

    /**
       \brief Propagate new bounds at node n using get_monomial(x)
       \pre is_monomial(x)
    */
    void propagate_monomial(var x, node * n);
    void propagate_monomial_upward(var x, node * n);
    void propagate_monomial_downward(var x, node * n, unsigned i);

    /**
       \brief Propagate new bounds at node n using get_polynomial(x)
       \pre is_polynomial(x)
    */
    void propagate_polynomial(var x, node * n);
    // Propagate a new bound for y using the polynomial associated with x. x may be equal to y.
    void propagate_polynomial(var x, node * n, var y);

    /**
       \brief Propagate new bounds at node n using clause c.
    */
    void propagate_clause(clause * c, node * n);
    
    /**
       \brief Return the truth value of inequaliy t at node n.
    */
    lbool value(ineq * t, node * n);

    /**
       \brief Propagate new bounds at node n using the definition of variable x.
       \pre is_definition(x)
    */
    void propagate_def(var x, node * n);

    /**
       \brief Propagate constraints in b->x()'s watch list.
    */
    void propagate(node * n, bound * b);
        
    /**
       \brief Perform bound propagation at node n.
    */
    void propagate(node * n);
    
    /**
       \brief Try to propagate at node n using all definitions.
    */
    void propagate_all_definitions(node * n);

    // -----------------------------------
    //
    // Main
    //
    // -----------------------------------
    void init();

    /**
       \brief Assert unit clauses in the node n.
    */
    void assert_units(node * n);

    // -----------------------------------
    //
    // Debugging support
    //
    // -----------------------------------
    
    /**
       \brief Return true if b is a bound for node n.
    */
    bool is_bound_of(bound * b, node * n) const;

    /**
       \brief Check the consistency of the doubly linked list of leaves.
    */
    bool check_leaf_dlist() const;

    /**
       \brief Check paving tree structure.
    */
    bool check_tree() const;
    
    /**
       \brief Check main invariants.
    */
    bool check_invariant() const;

public:
    context_t(reslimit& lim, C const & c, params_ref const & p, small_object_allocator * a);
    ~context_t();

    /**
       \brief Return true if the arithmetic module failed.
    */
    bool arith_failed() const { return m_arith_failed; }
    
    numeral_manager & nm() const { return m_c.m(); }

    unsigned num_vars() const { return m_is_int.size(); }

    bool is_int(var x) const { SASSERT(x < num_vars()); return m_is_int[x]; }

    /**
       \brief Create a new variable.
    */
    var mk_var(bool is_int);
    
    /**
       \brief Create the monomial xs[0]^ks[0] * ... * xs[sz-1]^ks[sz-1].
       The result is a variable y s.t. y = xs[0]^ks[0] * ... * xs[sz-1]^ks[sz-1].
       
       \pre for all i \in [0, sz-1] : ks[i] > 0
       \pre sz > 0
    */
    var mk_monomial(unsigned sz, power const * pws);
    
    /**
       \brief Create the sum c + as[0]*xs[0] + ... + as[sz-1]*xs[sz-1].
       The result is a variable y s.t. y = c + as[0]*xs[0] + ... + as[sz-1]*xs[sz-1].
       
       \pre sz > 0
       \pre for all i \in [0, sz-1] : as[i] != 0
    */
    var mk_sum(numeral const & c, unsigned sz, numeral const * as, var const * xs);
    
    /**
       \brief Create an inequality.
    */
    ineq * mk_ineq(var x, numeral const & k, bool lower, bool open);
    void inc_ref(ineq * a);
    void dec_ref(ineq * a);
    
    /**
       \brief Assert the clause atoms[0] \/ ... \/ atoms[sz-1]
       \pre sz > 1
    */
    void add_clause(unsigned sz, ineq * const * atoms) { add_clause_core(sz, atoms, false, true); }
    
    /**
       \brief Assert a constraint of one of the forms: x < k, x > k, x <= k, x >= k.
       
       If axiom == true, then the constraint is not tracked in proofs.
    */
    void add_ineq(var x, numeral const & k, bool lower, bool open, bool axiom);

    /**
       \brief Store in the given vector all leaves of the paving tree.
    */
    void collect_leaves(ptr_vector<node> & leaves) const;
    
    /**
       \brief Display constraints asserted in the subpaving.
    */
    void display_constraints(std::ostream & out, bool use_star = false) const;

    /**
       \brief Display bounds for each leaf of the tree.
    */
    void display_bounds(std::ostream & out) const;
    
    void display_bounds(std::ostream & out, node * n) const;

    void set_display_proc(display_var_proc * p) { m_display_proc = p; }

    void updt_params(params_ref const & p);

    static void collect_param_descrs(param_descrs & d);

    void reset_statistics();

    void collect_statistics(statistics & st) const;

    void operator()();
};

};

#endif
