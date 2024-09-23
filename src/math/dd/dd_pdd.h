/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    dd_pdd

Abstract:

    Poly DD package

    It is a mild variant of ZDDs. 
    In PDDs arithmetic is either standard or using mod 2^n.

    Non-leaf nodes are of the form x*hi + lo
    where 
    - maxdegree(x, lo) = 0, meaning x does not appear in lo

    Leaf nodes are of the form (0*idx + 0), where idx is an index into m_values.

    - reduce(a, b) reduces a using the polynomial equality b = 0. That is, given b = lt(b) + tail(b), 
      the occurrences in a where lm(b) divides a monomial a_i,      replace a_i in a by -tail(b)*a_i/lt(b)

    - try_spoly(a, b, c) returns true if lt(a) and lt(b) have a non-trivial overlap. c is the resolvent (S polynomial).

    - reduce(v, a, b) reduces 'a' using b = 0 with respect to eliminating v.
      Given b = v^l*b1 + b2, where l is the leading coefficient of v in b
      Given a = v^m*a1 + b2, where m >= l is the leading coefficient of v in b.
      reduce(a1, b1)*v^{m - l} + reduce(v, a2, b);

Author:

    Nikolaj Bjorner (nbjorner) 2019-12-17

--*/
#pragma once

#include "util/vector.h"
#include "util/map.h"
#include "util/small_object_allocator.h"
#include "util/rational.h"

namespace dd {
    class test;
    class pdd;
    class pdd_manager;
    class pdd_iterator;
    class pdd_linear_iterator;

    class pdd_manager {
    public:
        enum semantics { free_e, mod2_e, zero_one_vars_e, mod2N_e };
    private:
        friend test;
        friend pdd;
        friend pdd_iterator;
        friend pdd_linear_iterator;

        typedef unsigned PDD;
        typedef vector<std::pair<rational,unsigned_vector>> monomials_t;

        static constexpr PDD null_pdd = UINT_MAX;
        static constexpr PDD zero_pdd = 0;
        static constexpr PDD one_pdd = 1;

        enum pdd_op {
            pdd_add_op = 2,
            pdd_sub_op = 3,
            pdd_minus_op = 4,
            pdd_mul_op = 5,
            pdd_reduce_op = 6,
            pdd_subst_val_op = 7,
            pdd_subst_add_op = 8,
            pdd_div_const_op = 9,
            pdd_no_op = 10
        };

        struct node {
            node(unsigned level, PDD lo, PDD hi):
                m_refcount(0),
                m_level(level),
                m_lo(lo),
                m_hi(hi),
                m_index(0)
            {}
            node(unsigned value):
                m_refcount(0),
                m_level(0),
                m_lo(value),
                m_hi(0),
                m_index(0)
            {}

            node(): m_refcount(0), m_level(0), m_lo(0), m_hi(0), m_index(0) {}
            unsigned m_refcount : 10;
            unsigned m_level : 22;
            PDD      m_lo;
            PDD      m_hi;
            unsigned m_index;
            unsigned hash() const { return mk_mix(m_level, m_lo, m_hi); } 
            bool is_val() const { return m_hi == 0 && (m_lo != 0 || m_index == 0); }
            bool is_internal() const { return m_hi == 0 && m_lo == 0 && m_index != 0; }
            void set_internal() { m_lo = 0; m_hi = 0; }
        };

        struct hash_node {
            unsigned operator()(node const& n) const { return n.hash(); }
        };

        struct eq_node {
            bool operator()(node const& a, node const& b) const {
                return a.m_lo == b.m_lo && a.m_hi == b.m_hi && a.m_level == b.m_level;
            }
        };
        
        typedef hashtable<node, hash_node, eq_node> node_table;

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

        struct factor_entry {
            factor_entry(PDD p, unsigned v, unsigned degree):
                m_p(p),
                m_v(v),
                m_degree(degree),
                m_lc(UINT_MAX),
                m_rest(UINT_MAX)
            {}

            factor_entry(): m_p(0), m_v(0), m_degree(0), m_lc(UINT_MAX), m_rest(UINT_MAX) {}

            PDD m_p;            // input
            unsigned m_v;       // input
            unsigned m_degree;  // input
            PDD m_lc;           // output
            PDD m_rest;         // output

            bool is_valid() { return m_lc != UINT_MAX; }

            unsigned hash() const { return mk_mix(m_p, m_v, m_degree); }
        };

        struct hash_factor_entry {
            unsigned operator()(factor_entry const& e) const { return e.hash(); }
        };

        struct eq_factor_entry {
            bool operator()(factor_entry const& a, factor_entry const& b) const {
                return a.m_p == b.m_p && a.m_v == b.m_v && a.m_degree == b.m_degree;
            }
        };

        typedef hashtable<factor_entry, hash_factor_entry, eq_factor_entry> factor_table;

        svector<node>              m_nodes;
        vector<rational>           m_values;
        op_table                   m_op_cache;
        factor_table               m_factor_cache;
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
        mutable svector<PDD>       m_todo;
        mutable unsigned_vector    m_degree;
        mutable svector<double>    m_tree_size;
        bool                       m_disable_gc;
        bool                       m_is_new_node;
        unsigned                   m_max_num_nodes;
        semantics                  m_semantics;
        unsigned_vector            m_free_vars;
        unsigned_vector            m_free_values;
        rational                   m_freeze_value;
        rational                   m_mod2N;
        unsigned                   m_power_of_2 = 0;
        rational                   m_max_value;

        void reset_op_cache();
        void init_nodes(unsigned_vector const& l2v);
        void init_vars(unsigned_vector const& l2v);

        PDD make_node(unsigned level, PDD l, PDD r);
        PDD insert_node(node const& n);
        bool is_new_node() const { return m_is_new_node; }

        PDD apply(PDD arg1, PDD arg2, pdd_op op);
        PDD apply_rec(PDD arg1, PDD arg2, pdd_op op);
        PDD minus_rec(PDD p);
        PDD div_rec(PDD p, rational const& c, PDD c_pdd);
        PDD pow(PDD p, unsigned j);
        PDD pow_rec(PDD p, unsigned j);

        PDD reduce_on_match(PDD a, PDD b);
        bool lm_occurs(PDD p, PDD q) const;
        PDD lt_quotient(PDD p, PDD q);
        PDD lt_quotient_hi(PDD p, PDD q);

        PDD imk_val(rational const& r);       
        void init_value(const_info& info, rational const& r);
        void init_value(rational const& v, unsigned r);

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

        inline bool is_zero(PDD p) const { return p == zero_pdd; } 
        inline bool is_one(PDD p) const { return p == one_pdd; } 
        inline bool is_val(PDD p) const { return m_nodes[p].is_val(); }
        inline bool is_internal(PDD p) const { return m_nodes[p].is_internal(); }
        inline bool is_var(PDD p) const { return !is_val(p) && is_zero(lo(p)) && is_one(hi(p)); }
        inline bool is_max(PDD p) const { SASSERT(m_semantics == mod2_e || m_semantics == mod2N_e); return is_val(p) && val(p) == max_value(); }
        bool is_never_zero(PDD p);
        unsigned min_parity(PDD p);
        inline unsigned level(PDD p) const { return m_nodes[p].m_level; }
        inline unsigned var(PDD p) const { return m_level2var[level(p)]; }
        inline PDD lo(PDD p) const { return m_nodes[p].m_lo; }
        inline PDD hi(PDD p) const { return m_nodes[p].m_hi; }
        inline rational const& val(PDD p) const { SASSERT(is_val(p)); return m_values[lo(p)]; }
        inline rational get_signed_val(PDD p) const { SASSERT(m_semantics == mod2_e || m_semantics == mod2N_e); rational const& a = val(p); return a.get_bit(power_of_2() - 1) ? a - two_to_N() : a; }
        inline void inc_ref(PDD p) { if (m_nodes[p].m_refcount != max_rc) m_nodes[p].m_refcount++; SASSERT(!m_free_nodes.contains(p)); }
        inline void dec_ref(PDD p) { if (m_nodes[p].m_refcount != max_rc) m_nodes[p].m_refcount--; SASSERT(!m_free_nodes.contains(p)); }
        inline PDD level2pdd(unsigned l) const { return m_var2pdd[m_level2var[l]]; }

        unsigned dag_size(pdd const& p);

        mutable svector<unsigned>  m_dmark;
        mutable unsigned           m_dmark_level;
        void init_dmark();
        void set_dmark(unsigned i) const { m_dmark[i] = m_dmark_level; }
        bool is_dmarked(unsigned i) const { return m_dmark[i] == m_dmark_level; }
        unsigned degree(pdd const& p) const;
        unsigned degree(PDD p) const;
        unsigned degree(PDD p, unsigned v);
        unsigned max_pow2_divisor(PDD p);
        unsigned max_pow2_divisor(pdd const& p);
        template <class Fn> pdd map_coefficients(pdd const& p, Fn f);

        void factor(pdd const& p, unsigned v, unsigned degree, pdd& lc, pdd& rest);
        bool factor(pdd const& p, unsigned v, unsigned degree, pdd& lc);

        pdd reduce(unsigned v, pdd const& a, unsigned m, pdd const& b1, pdd const& b2);

        bool var_is_leaf(PDD p, unsigned v);

        bool is_reachable(PDD p);
        void compute_reachable(bool_vector& reachable);
        void try_gc();
        void reserve_var(unsigned v);
        bool well_formed();
        bool well_formed(node const& n);

        unsigned_vector m_p, m_q;
        rational m_pc, m_qc;
        pdd spoly(pdd const& a, pdd const& b, unsigned_vector const& p, unsigned_vector const& q, rational const& pc, rational const& qc);
        bool common_factors(pdd const& a, pdd const& b, unsigned_vector& p, unsigned_vector& q, rational& pc, rational& qc);
        PDD first_leading(PDD p) const;
        PDD next_leading(PDD p) const;

        monomials_t to_monomials(pdd const& p);

        struct scoped_push {
            pdd_manager& m;
            unsigned     m_size;
            scoped_push(pdd_manager& m) :m(m), m_size(m.m_pdd_stack.size()) {}
            ~scoped_push() { m.m_pdd_stack.shrink(m_size); }
        };

    public:

        struct mem_out {};

        pdd_manager(unsigned num_vars, semantics s = free_e, unsigned power_of_2 = 0);
        ~pdd_manager();

        pdd_manager(pdd_manager const&) = delete;
        pdd_manager(pdd_manager&&) = delete;
        pdd_manager& operator=(pdd_manager const&) = delete;
        pdd_manager& operator=(pdd_manager&&) = delete;

        semantics get_semantics() const { return m_semantics; }

        void reset(unsigned_vector const& level2var);
        void set_max_num_nodes(unsigned n);
        unsigned_vector const& get_level2var() const { return m_level2var; }
        unsigned num_nodes() const { return m_nodes.size() - m_free_nodes.size(); }

        pdd mk_var(unsigned i);
        pdd mk_val(rational const& r);
        pdd mk_val(unsigned r);
        pdd zero(); 
        pdd one(); 
        pdd minus(pdd const& a);
        pdd add(pdd const& a, pdd const& b);
        pdd add(rational const& a, pdd const& b);
        pdd sub(pdd const& a, pdd const& b);
        pdd mul(pdd const& a, pdd const& b);
        pdd mul(rational const& c, pdd const& b);
        pdd div(pdd const& a, rational const& c);
        bool try_div(pdd const& a, rational const& c, pdd& out_result);
        pdd mk_and(pdd const& p, pdd const& q);
        pdd mk_or(pdd const& p, pdd const& q);
        pdd mk_xor(pdd const& p, pdd const& q);
        pdd mk_xor(pdd const& p, unsigned x);
        pdd mk_not(pdd const& p);
        pdd reduce(pdd const& a, pdd const& b);
        pdd subst_val0(pdd const& a, vector<std::pair<unsigned, rational>> const& s);
        pdd subst_val(pdd const& a, unsigned v, rational const& val);
        pdd subst_val(pdd const& a, pdd const& s);
        pdd subst_add(pdd const& s, unsigned v, rational const& val);
        bool subst_get(pdd const& s, unsigned v, rational& out_val);
        bool resolve(unsigned v, pdd const& p, pdd const& q, pdd& r);
        pdd reduce(unsigned v, pdd const& a, pdd const& b);
        void quot_rem(pdd const& a, pdd const& b, pdd& q, pdd& r);
        pdd pow(pdd const& p, unsigned j);

        bool is_linear(PDD p) { return degree(p) == 1; }
        bool is_linear(pdd const& p);

        bool is_binary(PDD p);
        bool is_binary(pdd const& p);

        bool is_monomial(PDD p);

        bool is_univariate(PDD p);
        bool is_univariate_in(PDD p, unsigned v);
        void get_univariate_coefficients(PDD p, vector<rational>& coeff);

        rational const& offset(PDD p) const;

        // create an spoly r if leading monomials of a and b overlap
        bool try_spoly(pdd const& a, pdd const& b, pdd& r);

        // simple lexicographic comparison
        bool lex_lt(pdd const& a, pdd const& b); 

        // more elaborate comparison based on leading monomials
        bool lm_lt(pdd const& a, pdd const& b);

        bool different_leading_term(pdd const& a, pdd const& b);
        double tree_size(pdd const& p);
        unsigned num_vars() const { return m_var2pdd.size(); }

        unsigned power_of_2() const { return m_power_of_2; }
        rational const& max_value() const { return m_max_value; }
        rational const& two_to_N() const { return m_mod2N; }
        rational normalize(rational const& n) const { return mod(-n, m_mod2N) < n ? -mod(-n, m_mod2N) : n; }


        unsigned_vector const& free_vars(pdd const& p);

        std::ostream& display(std::ostream& out);
        std::ostream& display(std::ostream& out, pdd const& b);

        void gc();
    };

    class pdd {
        friend test;
        friend class pdd_manager;
        friend class pdd_iterator;
        friend class pdd_linear_iterator;
        unsigned     root;
        pdd_manager* m;
        pdd(unsigned root, pdd_manager& pm): root(root), m(&pm) { m->inc_ref(root); }
        pdd(unsigned root, pdd_manager* pm): root(root), m(pm) { m->inc_ref(root); }
    public:
        pdd(pdd_manager& m): pdd(0, m) { SASSERT(is_zero()); }
        pdd(pdd const& other): pdd(other.root, other.m) { m->inc_ref(root); }
        pdd(pdd && other) noexcept : pdd(0, other.m) { std::swap(root, other.root); }
        pdd& operator=(pdd const& other);
        pdd& operator=(unsigned k);
        pdd& operator=(rational const& k);
        // TODO: pdd& operator=(pdd&& other);  (just swap like move constructor?)
        ~pdd() { m->dec_ref(root); }
        void reset(pdd_manager& new_m);
        pdd lo() const { return pdd(m->lo(root), m); }
        pdd hi() const { return pdd(m->hi(root), m); }
        unsigned index() const { return root; }
        unsigned var() const { return m->var(root); }
        rational const& val() const { return m->val(root); }
        rational get_signed_val() const { return m->get_signed_val(root); }
        rational const& leading_coefficient() const;
        rational const& offset() const { return m->offset(root); }
        bool is_val() const { return m->is_val(root); }
        bool is_one() const { return m->is_one(root); }
        bool is_zero() const { return m->is_zero(root); }
        bool is_linear() const { return m->is_linear(root); }
        bool is_var() const { return m->is_var(root); }
        bool is_max() const { return m->is_max(root); }
        /** Polynomial is of the form a * x + b for some numerals a, b. */
        bool is_unilinear() const { return !is_val() && lo().is_val() && hi().is_val(); }
        /** Polynomial is of the form a * x for some numeral a. */
        bool is_unary() const { return !is_val() && lo().is_zero() && hi().is_val(); }
        bool is_offset() const { return !is_val() && lo().is_val() && hi().is_one(); }
        bool is_binary() const { return m->is_binary(root); }
        bool is_monomial() const { return m->is_monomial(root); }
        bool is_univariate() const { return m->is_univariate(root); }
        bool is_univariate_in(unsigned v) const { return m->is_univariate_in(root, v); }
        void get_univariate_coefficients(vector<rational>& coeff) const { m->get_univariate_coefficients(root, coeff); }
        vector<rational> get_univariate_coefficients() const { vector<rational> coeff; m->get_univariate_coefficients(root, coeff); return coeff; }
        bool is_never_zero() const { return m->is_never_zero(root); }
        unsigned min_parity() const { return m->min_parity(root); }
        bool var_is_leaf(unsigned v) const { return m->var_is_leaf(root, v); }

        pdd operator-() const { return m->minus(*this); }
        pdd operator+(pdd const& other) const { VERIFY_EQ(m, other.m); return m->add(*this, other); }
        pdd operator-(pdd const& other) const { VERIFY_EQ(m, other.m); return m->sub(*this, other); }
        pdd operator*(pdd const& other) const { VERIFY_EQ(m, other.m); return m->mul(*this, other); }
        pdd operator&(pdd const& other) const { VERIFY_EQ(m, other.m); return m->mk_and(*this, other); }
        pdd operator|(pdd const& other) const { VERIFY_EQ(m, other.m); return m->mk_or(*this, other); }
        pdd operator^(pdd const& other) const { VERIFY_EQ(m, other.m); return m->mk_xor(*this, other); }
        pdd operator^(unsigned other) const { return m->mk_xor(*this, m->mk_val(other)); }

        pdd operator*(rational const& other) const { return m->mul(other, *this); }
        pdd operator+(rational const& other) const { return m->add(other, *this); }
        pdd operator~() const { return m->mk_not(*this); }
        pdd shl(unsigned n) const; 
        pdd rev_sub(rational const& r) const { return m->sub(m->mk_val(r), *this); }
        pdd div(rational const& other) const { return m->div(*this, other); }
        bool try_div(rational const& other, pdd& out_result) const { VERIFY_EQ(m, out_result.m); return m->try_div(*this, other, out_result); }
        pdd pow(unsigned j) const { return m->pow(*this, j); }
        pdd reduce(pdd const& other) const { VERIFY_EQ(m, other.m); return m->reduce(*this, other); }
        bool different_leading_term(pdd const& other) const { VERIFY_EQ(m, other.m); return m->different_leading_term(*this, other); }
        void factor(unsigned v, unsigned degree, pdd& lc, pdd& rest) const { VERIFY_EQ(m, lc.m); VERIFY_EQ(m, rest.m); m->factor(*this, v, degree, lc, rest); }
        bool factor(unsigned v, unsigned degree, pdd& lc) const { VERIFY_EQ(m, lc.m); return m->factor(*this, v, degree, lc); }
        bool resolve(unsigned v, pdd const& other, pdd& result) { VERIFY_EQ(m, other.m); VERIFY_EQ(m, result.m); return m->resolve(v, *this, other, result); }
        pdd reduce(unsigned v, pdd const& other) const { VERIFY_EQ(m, other.m); return m->reduce(v, *this, other); }

        /**
         * \brief factor out variables
         */
        std::pair<unsigned_vector, pdd> var_factors() const;

        pdd subst_val0(vector<std::pair<unsigned, rational>> const& s) const { return m->subst_val0(*this, s); }
        pdd subst_val(pdd const& s) const { VERIFY_EQ(m, s.m); return m->subst_val(*this, s); }
        pdd subst_val(unsigned v, rational const& val) const { return m->subst_val(*this, v, val); }
        pdd subst_add(unsigned var, rational const& val) const { return m->subst_add(*this, var, val); }
        bool subst_get(unsigned var, rational& out_val) const { return m->subst_get(*this, var, out_val); }

        /**
         * \brief substitute variable v by r.
         */
        pdd subst_pdd(unsigned v, pdd const& r) const;

        std::ostream& display(std::ostream& out) const { return m->display(out, *this); }
        bool operator==(pdd const& other) const { return root == other.root && m == other.m; }
        bool operator!=(pdd const& other) const { return !operator==(other); }
        unsigned hash() const { return root; }

        unsigned power_of_2() const { return m->power_of_2(); }

        unsigned dag_size() const { return m->dag_size(*this); }
        double tree_size() const { return m->tree_size(*this); }
        unsigned degree() const { return m->degree(*this); }
        unsigned degree(unsigned v) const { return m->degree(root, v); }
        unsigned max_pow2_divisor() const { return m->max_pow2_divisor(root); }
        unsigned_vector const& free_vars() const { return m->free_vars(*this); }

        void swap(pdd& other) noexcept { VERIFY_EQ(m, other.m); std::swap(root, other.root); }

        pdd_iterator begin() const;
        pdd_iterator end() const;

        class pdd_linear_monomials {
            friend class pdd;
            pdd const& m_pdd;
            pdd_linear_monomials(pdd const& p): m_pdd(p) {}
        public:
            pdd_linear_iterator begin() const;
            pdd_linear_iterator end() const;
        };
        pdd_linear_monomials linear_monomials() const { return pdd_linear_monomials(*this); }

        pdd_manager& manager() const { return *m; }
    };

    inline pdd operator*(rational const& r, pdd const& b) { return b * r; }
    inline pdd operator*(int x, pdd const& b) { return b * rational(x); }
    inline pdd operator*(pdd const& b, int x) { return b * rational(x); }

    inline pdd operator+(rational const& r, pdd const& b) { return b + r; }
    inline pdd operator+(int x, pdd const& b) { return b + rational(x); }
    inline pdd operator+(pdd const& b, int x) { return b + rational(x); }

    inline pdd operator^(unsigned x, pdd const& b) { return b ^ x; }
    inline pdd operator^(bool x, pdd const& b) { return b ^ x; }

    inline pdd operator-(rational const& r, pdd const& b) { return b.rev_sub(r); }
    inline pdd operator-(int x, pdd const& b) { return rational(x) - b; }
    inline pdd operator-(pdd const& b, int x) { return b + (-rational(x)); }
    inline pdd operator-(pdd const& b, rational const& r) { return b + (-r); }

    inline pdd& operator&=(pdd & p, pdd const& q) { p = p & q; return p; }
    inline pdd& operator^=(pdd & p, pdd const& q) { p = p ^ q; return p; }
    inline pdd& operator|=(pdd & p, pdd const& q) { p = p | q; return p; }
    inline pdd& operator*=(pdd & p, pdd const& q) { p = p * q; return p; }
    inline pdd& operator-=(pdd & p, pdd const& q) { p = p - q; return p; }
    inline pdd& operator+=(pdd & p, pdd const& q) { p = p + q; return p; }
    inline pdd& operator*=(pdd & p, rational const& q) { p = p * q; return p; }
    inline pdd& operator-=(pdd & p, rational const& q) { p = p - q; return p; }
    inline pdd& operator+=(pdd & p, rational const& q) { p = p + q; return p; }

    inline void swap(pdd& p, pdd& q) noexcept { p.swap(q); }

    std::ostream& operator<<(std::ostream& out, pdd const& b);

    struct pdd_monomial {
        rational coeff;
        unsigned_vector vars;
    };

    std::ostream& operator<<(std::ostream& out, pdd_monomial const& m);

    class pdd_iterator {
        friend class pdd;
        pdd m_pdd;
        svector<std::pair<bool, unsigned>> m_nodes;
        pdd_monomial m_mono;
        pdd_iterator(pdd const& p, bool at_start): m_pdd(p) { if (at_start) first(); }
        void first();
        void next();
    public:
        pdd_monomial const& operator*() const { return m_mono; }
        pdd_monomial const* operator->() const { return &m_mono; }
        pdd_iterator& operator++() { next(); return *this; }
        pdd_iterator operator++(int) { auto tmp = *this; next(); return tmp; }
        bool operator!=(pdd_iterator const& other) const { return m_nodes != other.m_nodes; }
    };

    class pdd_linear_iterator {
        friend class pdd::pdd_linear_monomials;
        pdd m_pdd;
        std::pair<rational, unsigned> m_mono;
        pdd_manager::PDD m_next = pdd_manager::null_pdd;
        pdd_linear_iterator(pdd const& p, bool at_start): m_pdd(p) { if (at_start) first(); }
        void first();
        void next();
    public:
        using value_type = std::pair<rational, unsigned>;  // coefficient and variable
        using reference = value_type const&;
        using pointer = value_type const*;
        reference operator*() const { return m_mono; }
        pointer operator->() const { return &m_mono; }
        pdd_linear_iterator& operator++() { next(); return *this; }
        pdd_linear_iterator operator++(int) { auto tmp = *this; next(); return tmp; }
        bool operator!=(pdd_linear_iterator const& other) const { return m_next != other.m_next; }
    };

    class val_pp {
        pdd_manager const& m;
        rational const& val;
        bool require_parens;
        char const* lparen() const { return require_parens ? "(" : ""; }
        char const* rparen() const { return require_parens ? ")" : ""; }
    public:
        val_pp(pdd_manager const& m, rational const& val, bool require_parens = false): m(m), val(val), require_parens(require_parens) {}
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, val_pp const& v) { return v.display(out); }
}


