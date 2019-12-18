/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    dd_pdd

Abstract:

    Poly DD package

    Non-leaf nodes are of the form x*hi + lo
    where 
    - maxdegree(x, lo) = 0, 

    Leaf nodes are of the form (0*idx + 0), where idx is an index into m_values.

    - reduce(a, b) reduces a using the polynomial equality b = 0. That is, given b = lt(b) + tail(b), 
      the occurrences in a where lm(b) divides a monomial a_i,      replace a_i in a by -tail(b)*a_i/lt(b)

    - try_spoly(a, b, c) returns true if lt(a) and lt(b) have a non-trivial overlap. c is the resolvent (S polynomial).

Author:

    Nikolaj Bjorner (nbjorner) 2019-12-17

--*/
#ifndef DD_PDD_H_
#define DD_PDD_H_

#include "util/vector.h"
#include "util/map.h"
#include "util/small_object_allocator.h"
#include "util/rational.h"

namespace dd {

    class pdd;

    class pdd_manager {
        friend pdd;

        typedef unsigned PDD;
        typedef vector<std::pair<rational,unsigned_vector>> monomials_t;

        const PDD null_pdd = UINT_MAX;
        const PDD zero_pdd = 0;
        const PDD one_pdd = 1;

        enum pdd_op {
            pdd_add_op = 2,
            pdd_minus_op = 3,
            pdd_mul_op = 4,
            pdd_reduce_op = 5,
            pdd_no_op = 6
        };

        struct pdd_node {
            pdd_node(unsigned level, PDD lo, PDD hi):
                m_refcount(0),
                m_level(level),
                m_lo(lo),
                m_hi(hi),
                m_index(0)
            {}
            pdd_node(unsigned value):
                m_refcount(0),
                m_level(0),
                m_lo(value),
                m_hi(0),
                m_index(0)
            {}

            pdd_node(): m_refcount(0), m_level(0), m_lo(0), m_hi(0), m_index(0) {}
            unsigned m_refcount : 10;
            unsigned m_level : 22;
            PDD      m_lo;
            PDD      m_hi;
            unsigned m_index;
            unsigned hash() const { return mk_mix(m_level, m_lo, m_hi); } 
            bool is_internal() const { return m_lo == 0 && m_hi == 0; }
            void set_internal() { m_lo = 0; m_hi = 0; }
        };

        struct hash_node {
            unsigned operator()(pdd_node const& n) const { return n.hash(); }
        };

        struct eq_node {
            bool operator()(pdd_node const& a, pdd_node const& b) const {
                return a.m_lo == b.m_lo && a.m_hi == b.m_hi && a.m_level == b.m_level;
            }
        };
        
        typedef hashtable<pdd_node, hash_node, eq_node> node_table;

        struct const_info {
            unsigned m_value_index;
            unsigned m_node_index;
        };

        typedef map<rational, const_info, rational::hash_proc, rational::eq_proc> mpq_table;

        struct op_entry {
            op_entry(PDD l, PDD r, PDD op):
                m_pdd1(l),
                m_pdd2(r),
                m_op(op),
                m_result(0)
            {}

            PDD      m_pdd1;
            PDD      m_pdd2;
            PDD      m_op;
            PDD      m_result;
            unsigned hash() const { return mk_mix(m_pdd1, m_pdd2, m_op); }
        };

        struct hash_entry {
            unsigned operator()(op_entry* e) const { return e->hash(); }
        };

        struct eq_entry {
            bool operator()(op_entry * a, op_entry * b) const { 
                return a->m_pdd1 == b->m_pdd2 && a->m_pdd2 == b->m_pdd2 && a->m_op == b->m_op;
            }
        };

        typedef ptr_hashtable<op_entry, hash_entry, eq_entry> op_table;

        svector<pdd_node>          m_nodes;
        vector<rational>           m_values;
        op_table                   m_op_cache;
        node_table                 m_node_table;
        mpq_table                  m_mpq_table;
        svector<PDD>               m_pdd_stack;
        op_entry*                  m_spare_entry;
        svector<PDD>               m_var2pdd;
        unsigned_vector            m_var2level, m_level2var;
        unsigned_vector            m_free_nodes;
        small_object_allocator     m_alloc;
        mutable svector<unsigned>  m_mark;
        mutable unsigned           m_mark_level;
        mutable svector<double>    m_count;
        mutable svector<PDD>       m_todo;
        bool                       m_disable_gc;
        bool                       m_is_new_node;
        unsigned                   m_max_num_pdd_nodes;

        PDD make_node(unsigned level, PDD l, PDD r);
        PDD insert_node(pdd_node const& n);
        bool is_new_node() const { return m_is_new_node; }

        PDD apply(PDD arg1, PDD arg2, pdd_op op);
        PDD apply_rec(PDD arg1, PDD arg2, pdd_op op);
        PDD minus_rec(PDD p);

        PDD reduce_on_match(PDD a, PDD b);
        bool lm_divides(PDD p, PDD q) const;
        PDD lt_quotient(PDD p, PDD q);

        PDD imk_val(rational const& r);        

        void push(PDD b);
        void pop(unsigned num_scopes);
        PDD read(unsigned index);

        op_entry* pop_entry(PDD l, PDD r, PDD op);
        void push_entry(op_entry* e);
        bool check_result(op_entry*& e1, op_entry const* e2, PDD a, PDD b, PDD c);
        
        void alloc_free_nodes(unsigned n);
        void init_mark();
        void set_mark(unsigned i) { m_mark[i] = m_mark_level; }
        bool is_marked(unsigned i) { return m_mark[i] == m_mark_level; }

        static const unsigned max_rc = (1 << 10) - 1;

        inline bool is_zero(PDD b) const { return b == zero_pdd; } 
        inline bool is_one(PDD b) const { return b == one_pdd; } 
        inline bool is_val(PDD b) const { return hi(b) == 0; }
        inline unsigned level(PDD b) const { return m_nodes[b].m_level; }
        inline unsigned var(PDD b) const { return m_level2var[level(b)]; }
        inline PDD lo(PDD b) const { return m_nodes[b].m_lo; }
        inline PDD hi(PDD b) const { return m_nodes[b].m_hi; }
        inline rational const& val(PDD b) const { SASSERT(is_val(b)); return m_values[lo(b)]; }
        inline void inc_ref(PDD b) { if (m_nodes[b].m_refcount != max_rc) m_nodes[b].m_refcount++; SASSERT(!m_free_nodes.contains(b)); }
        inline void dec_ref(PDD b) { if (m_nodes[b].m_refcount != max_rc) m_nodes[b].m_refcount--; SASSERT(!m_free_nodes.contains(b)); }
        inline PDD level2pdd(unsigned l) const { return m_var2pdd[m_level2var[l]]; }

        unsigned pdd_size(pdd const& b);

        void try_gc();
        void reserve_var(unsigned v);
        bool well_formed();

        unsigned_vector m_p, m_q;
        rational m_pc, m_qc;
        pdd spoly(pdd const& a, pdd const& b, unsigned_vector const& p, unsigned_vector const& q, rational const& pc, rational const& qc);
        bool common_factors(pdd const& a, pdd const& b, unsigned_vector& p, unsigned_vector& q, rational& pc, rational& qc);

        monomials_t to_monomials(pdd const& p);

        struct scoped_push {
            pdd_manager& m;
            unsigned     m_size;
            scoped_push(pdd_manager& m) :m(m), m_size(m.m_pdd_stack.size()) {}
            ~scoped_push() { m.m_pdd_stack.shrink(m_size); }
        };

    public:

        struct mem_out {};

        pdd_manager(unsigned nodes);
        ~pdd_manager();

        void set_max_num_nodes(unsigned n) { m_max_num_pdd_nodes = n; }
        void set_var_order(unsigned_vector const& levels);  // TBD: set variable order (m_var2level, m_level2var) before doing anything else.

        pdd mk_var(unsigned i);
        pdd mk_val(rational const& r);
        pdd zero(); 
        pdd one(); 
        pdd minus(pdd const& a);
        pdd add(pdd const& a, pdd const& b);
        pdd add(rational const& a, pdd const& b);
        pdd sub(pdd const& a, pdd const& b);
        pdd mul(pdd const& a, pdd const& b);
        pdd mul(rational const& c, pdd const& b);
        pdd reduce(pdd const& a, pdd const& b);
        bool try_spoly(pdd const& a, pdd const& b, pdd& r);

        std::ostream& display(std::ostream& out);
        std::ostream& display(std::ostream& out, pdd const& b);

        void gc();
    };

    class pdd {
        friend class pdd_manager;
        unsigned     root;
        pdd_manager* m;
        pdd(unsigned root, pdd_manager* m): root(root), m(m) { m->inc_ref(root); }
    public:
        pdd(pdd & other): root(other.root), m(other.m) { m->inc_ref(root); }
        pdd(pdd && other): root(0), m(other.m) { std::swap(root, other.root); }
        pdd& operator=(pdd const& other);
        ~pdd() { m->dec_ref(root); }
        pdd lo() const { return pdd(m->lo(root), m); }
        pdd hi() const { return pdd(m->hi(root), m); }
        unsigned var() const { return m->var(root); }
        rational const& val() const { SASSERT(is_val()); return m->val(root); }
        bool is_val() const { return m->is_val(root); }

        pdd operator+(pdd const& other) const { return m->add(*this, other); }
        pdd operator-(pdd const& other) const { return m->sub(*this, other); }
        pdd operator*(pdd const& other) const { return m->mul(*this, other); }
        pdd operator*(rational const& other) const { return m->mul(other, *this); }
        pdd operator+(rational const& other) const { return m->add(other, *this); }
        pdd reduce(pdd const& other) const { return m->reduce(*this, other); }

        std::ostream& display(std::ostream& out) const { return m->display(out, *this); }
        bool operator==(pdd const& other) const { return root == other.root; }
        bool operator!=(pdd const& other) const { return root != other.root; }
        unsigned size() const { return m->pdd_size(*this); }
    };

    inline pdd operator*(rational const& r, pdd const& b) { return b * r; }
    inline pdd operator*(int x, pdd const& b) { return b * rational(x); }
    inline pdd operator*(pdd const& b, int x) { return b * rational(x); }

    inline pdd operator+(rational const& r, pdd& b) { return b + r; }
    inline pdd operator+(int x, pdd const& b) { return b + rational(x); }
    inline pdd operator+(pdd const& b, int x) { return b + rational(x); }

    inline pdd operator-(pdd const& b, int x) { return b + (-rational(x)); }

    std::ostream& operator<<(std::ostream& out, pdd const& b);

}


#endif
