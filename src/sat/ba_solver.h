/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_solver.h

Abstract:

    Cardinality extensions.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/
#ifndef BA_SOLVER_H_
#define BA_SOLVER_H_

#include"sat_extension.h"
#include"sat_solver.h"
#include"sat_lookahead.h"
#include"scoped_ptr_vector.h"


namespace sat {
    
    class ba_solver : public extension {

        friend class local_search;

        struct stats {
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            unsigned m_num_resolves;
            unsigned m_num_bin_subsumes;
            unsigned m_num_clause_subsumes;
            unsigned m_num_card_subsumes;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

    public:        
        enum tag_t {
            card_t,
            pb_t,
            xor_t
        };

        class card;
        class pb;
        class xor;

        class constraint {
        protected:
            tag_t          m_tag;
            bool           m_removed;
            literal        m_lit;
            unsigned       m_glue;
            unsigned       m_size;
            size_t         m_obj_size;
        public:
            constraint(tag_t t, literal l, unsigned sz, size_t osz): m_tag(t), m_removed(false), m_lit(l), m_glue(0), m_size(sz), m_obj_size(osz) {}
            ext_constraint_idx index() const { return reinterpret_cast<ext_constraint_idx>(this); }
            tag_t tag() const { return m_tag; }
            literal lit() const { return m_lit; }
            unsigned size() const { return m_size; }
            void set_size(unsigned sz) { SASSERT(sz <= m_size); m_size = sz; }
            void update_literal(literal l) { m_lit = l; }
            bool was_removed() const { return m_removed; }
            void remove() { m_removed = true; }
            void nullify_literal() { m_lit = null_literal; }
            unsigned glue() const { return m_glue; }
            void set_glue(unsigned g) { m_glue = g; }            

            size_t obj_size() const { return m_obj_size; }
            card& to_card();
            pb&  to_pb();
            xor& to_xor();
            card const& to_card() const;
            pb const&  to_pb() const;
            xor const& to_xor() const;
            bool is_card() const { return m_tag == card_t; }
            bool is_pb() const { return m_tag == pb_t; }
            bool is_xor() const { return m_tag == xor_t; }
            
            virtual bool is_watching(literal l) const { UNREACHABLE(); return false; };
            virtual literal_vector literals() const { UNREACHABLE(); return literal_vector(); }
            virtual void swap(unsigned i, unsigned j) { UNREACHABLE(); }
            virtual literal get_lit(unsigned i) const { UNREACHABLE(); return null_literal; }
            virtual void set_lit(unsigned i, literal l) { UNREACHABLE(); }
            virtual bool well_formed() const { return true; }
        };

        friend std::ostream& operator<<(std::ostream& out, constraint const& c);

        // base class for pb and cardinality constraints
        class pb_base : public constraint {
        protected:
            unsigned       m_k;
        public:
            pb_base(tag_t t, literal l, unsigned sz, size_t osz, unsigned k): constraint(t, l, sz, osz), m_k(k) {}
            virtual void set_k(unsigned k) { m_k = k; }
            virtual unsigned get_coeff(unsigned i) const { UNREACHABLE(); return 0; }
            unsigned k() const { return m_k; }
            virtual bool well_formed() const;
        };

        class card : public pb_base {
            literal        m_lits[0];
        public:
            static size_t get_obj_size(unsigned num_lits) { return sizeof(card) + num_lits * sizeof(literal); }
            card(literal lit, literal_vector const& lits, unsigned k);
            literal operator[](unsigned i) const { return m_lits[i]; }
            literal& operator[](unsigned i) { return m_lits[i]; }
            literal const* begin() const { return m_lits; }
            literal const* end() const { return static_cast<literal const*>(m_lits) + m_size; }
            void negate();                     
            virtual void swap(unsigned i, unsigned j) { std::swap(m_lits[i], m_lits[j]); }
            virtual literal_vector literals() const { return literal_vector(m_size, m_lits); }            
            virtual bool is_watching(literal l) const;
            virtual literal get_lit(unsigned i) const { return m_lits[i]; }
            virtual void set_lit(unsigned i, literal l) { m_lits[i] = l; }
            virtual unsigned get_coeff(unsigned i) const { return 1; }
        };

        
        typedef std::pair<unsigned, literal> wliteral;

        class pb : public pb_base {
            unsigned       m_slack;
            unsigned       m_num_watch;
            unsigned       m_max_sum;
            wliteral       m_wlits[0];
            void update_max_sum();
        public:
            static size_t get_obj_size(unsigned num_lits) { return sizeof(pb) + num_lits * sizeof(wliteral); }
            pb(literal lit, svector<wliteral> const& wlits, unsigned k);
            literal lit() const { return m_lit; }
            wliteral operator[](unsigned i) const { return m_wlits[i]; }
            wliteral& operator[](unsigned i) { return m_wlits[i]; }
            wliteral const* begin() const { return m_wlits; }
            wliteral const* end() const { return begin() + m_size; }

            unsigned slack() const { return m_slack; }
            void set_slack(unsigned s) { m_slack = s; }
            unsigned num_watch() const { return m_num_watch; }
            unsigned max_sum() const { return m_max_sum; }
            void set_num_watch(unsigned s) { m_num_watch = s; }
            bool is_cardinality() const;
            void negate();                       
            virtual void set_k(unsigned k) { m_k = k; update_max_sum(); }
            virtual void swap(unsigned i, unsigned j) { std::swap(m_wlits[i], m_wlits[j]); }
            virtual literal_vector literals() const { literal_vector lits; for (auto wl : *this) lits.push_back(wl.second); return lits; }
            virtual bool is_watching(literal l) const;
            virtual literal get_lit(unsigned i) const { return m_wlits[i].second; }
            virtual void set_lit(unsigned i, literal l) { m_wlits[i].second = l; }
            virtual unsigned get_coeff(unsigned i) const { return m_wlits[i].first; }
        };

        class xor : public constraint {
            literal        m_lits[0];
        public:
            static size_t get_obj_size(unsigned num_lits) { return sizeof(xor) + num_lits * sizeof(literal); }
            xor(literal lit, literal_vector const& lits);
            literal operator[](unsigned i) const { return m_lits[i]; }
            literal const* begin() const { return m_lits; }
            literal const* end() const { return begin() + m_size; }
            void negate() { m_lits[0].neg(); }
            virtual void swap(unsigned i, unsigned j) { std::swap(m_lits[i], m_lits[j]); }
            virtual bool is_watching(literal l) const;
            virtual literal_vector literals() const { return literal_vector(size(), begin()); }
            virtual literal get_lit(unsigned i) const { return m_lits[i]; }
            virtual void set_lit(unsigned i, literal l) { m_lits[i] = l; }
            virtual bool well_formed() const;
        };


    protected:

        struct ineq {
            literal_vector  m_lits;
            unsigned_vector m_coeffs;
            unsigned        m_k;
            void reset(unsigned k) { m_lits.reset(); m_coeffs.reset(); m_k = k; }
            void push(literal l, unsigned c) { m_lits.push_back(l); m_coeffs.push_back(c); }
        };

        solver*                m_solver;
        lookahead*             m_lookahead;
        stats                  m_stats; 
        small_object_allocator m_allocator;
       

        ptr_vector<constraint> m_constraints;
        ptr_vector<constraint> m_learned;
        unsigned_vector        m_constraint_lim;       

        // conflict resolution
        unsigned          m_num_marks;
        unsigned          m_conflict_lvl;
        svector<int>      m_coeffs;
        svector<bool_var> m_active_vars;
        int               m_bound;
        tracked_uint_set  m_active_var_set;
        literal_vector    m_lemma;
        unsigned          m_num_propagations_since_pop;
        unsigned_vector   m_parity_marks;
        literal_vector    m_parity_trail;

        unsigned_vector   m_pb_undef;

        void     ensure_parity_size(bool_var v);
        unsigned get_parity(bool_var v);
        void     inc_parity(bool_var v);
        void     reset_parity(bool_var v);

        solver& s() const { return *m_solver; }


        // simplification routines

        svector<bool>             m_visited;
        vector<svector<constraint*>>    m_cnstr_use_list;
        use_list                  m_clause_use_list;
        bool                      m_simplify_change;
        bool                      m_clause_removed;
        bool                      m_constraint_removed;
        literal_vector            m_roots;
        unsigned_vector           m_weights;
        bool subsumes(card& c1, card& c2, literal_vector& comp);
        bool subsumes(card& c1, clause& c2, literal_vector& comp);
        bool subsumed(card& c1, literal l1, literal l2);
        void binary_subsumption(card& c1, literal lit);
        void clause_subsumption(card& c1, literal lit);
        void card_subsumption(card& c1, literal lit);
        void mark_visited(literal l) { m_visited[l.index()] = true; }
        void unmark_visited(literal l) { m_visited[l.index()] = false; }
        bool is_marked(literal l) const { return m_visited[l.index()] != 0; }
        unsigned get_num_non_learned_bin(literal l);
        literal get_min_occurrence_literal(card const& c);
        void init_use_lists();
        void remove_unused_defs();
        unsigned set_non_external();
        unsigned elim_pure();
        bool elim_pure(literal lit);
        void subsumption();
        void subsumption(card& c1);
        void gc_half(char const* _method);
        void mutex_reduction();
        unsigned use_count(literal lit) const { return m_cnstr_use_list[lit.index()].size() + m_clause_use_list.get(lit).size(); }

        void cleanup_clauses();
        void cleanup_constraints();
        void cleanup_constraints(ptr_vector<constraint>& cs);
        void remove_constraint(constraint& c);

        // constraints
        constraint& index2constraint(size_t idx) const { return *reinterpret_cast<constraint*>(idx); }        
        void pop_constraint();
        void unwatch_literal(literal w, constraint& c);
        void watch_literal(literal w, constraint& c);
        void watch_literal(wliteral w, pb& p);
        void add_constraint(constraint* c);
        void init_watch(constraint& c, bool is_true);
        void init_watch(bool_var v);
        void clear_watch(constraint& c);
        lbool add_assign(constraint& c, literal l);
        void simplify(constraint& c);
        void nullify_tracking_literal(constraint& c);
        void set_conflict(constraint& c, literal lit);
        void assign(constraint& c, literal lit);
        void get_antecedents(literal l, constraint const& c, literal_vector & r);
        bool validate_conflict(constraint const& c) const;
        bool validate_unit_propagation(constraint const& c, literal alit) const;
        void attach_constraint(constraint const& c);
        void detach_constraint(constraint const& c);
        lbool eval(constraint const& c) const;
        lbool eval(lbool a, lbool b) const;
        void assert_unconstrained(literal lit, literal_vector const& lits);
        void flush_roots(constraint& c);
        void recompile(constraint& c);


        // cardinality
        void init_watch(card& c, bool is_true);
        lbool add_assign(card& c, literal lit);
        void clear_watch(card& c);
        void reset_coeffs();
        void reset_marked_literals();
        void get_antecedents(literal l, card const& c, literal_vector & r);
        void flush_roots(card& c);
        void recompile(card& c);
        lbool eval(card const& c) const;

        // xor specific functionality
        void clear_watch(xor& x);
        void init_watch(xor& x, bool is_true);
        bool parity(xor const& x, unsigned offset) const;
        lbool add_assign(xor& x, literal alit);
        void get_xor_antecedents(literal l, unsigned index, justification js, literal_vector& r);
        void get_antecedents(literal l, xor const& x, literal_vector & r);
        void simplify(xor& x);
        void flush_roots(xor& x);
        lbool eval(xor const& x) const;
        
        // pb functionality
        unsigned m_a_max;
        void init_watch(pb& p, bool is_true);
        lbool add_assign(pb& p, literal alit);
        void add_index(pb& p, unsigned index, literal lit);
        void clear_watch(pb& p);
        void get_antecedents(literal l, pb const& p, literal_vector & r);
        void simplify(pb_base& p);
        void simplify2(pb& p);
        bool is_cardinality(pb const& p);
        void flush_roots(pb& p);
        void recompile(pb& p);
        lbool eval(pb const& p) const;

        // access solver
        inline lbool value(bool_var v) const { return value(literal(v, false)); }
        inline lbool value(literal lit) const { return m_lookahead ? m_lookahead->value(lit) : m_solver->value(lit); }
        inline unsigned lvl(literal lit) const { return m_solver->lvl(lit); }
        inline unsigned lvl(bool_var v) const { return m_solver->lvl(v); }
        inline bool inconsistent() const { return m_lookahead ? m_lookahead->inconsistent() : m_solver->inconsistent(); }
        inline watch_list& get_wlist(literal l) { return m_lookahead ? m_lookahead->get_wlist(l) : m_solver->get_wlist(l); }
        inline watch_list const& get_wlist(literal l) const { return m_lookahead ? m_lookahead->get_wlist(l) : m_solver->get_wlist(l); }
        inline void assign(literal l, justification j) { if (m_lookahead) m_lookahead->assign(l); else m_solver->assign(l, j); }
        inline void set_conflict(justification j, literal l) { if (m_lookahead) m_lookahead->set_conflict(); else m_solver->set_conflict(j, l); }
        inline config const& get_config() const { return m_solver->get_config(); }
        inline void drat_add(literal_vector const& c, svector<drat::premise> const& premises) { m_solver->m_drat.add(c, premises); }


        void normalize_active_coeffs();
        void inc_coeff(literal l, int offset);
        int get_coeff(bool_var v) const;
        int get_abs_coeff(bool_var v) const;       

        literal get_asserting_literal(literal conseq);
        void process_antecedent(literal l, int offset);
        void process_card(card& c, int offset);
        void cut();

        // validation utilities
        bool validate_conflict(card const& c) const;
        bool validate_conflict(xor const& x) const;
        bool validate_conflict(pb const& p) const;
        bool validate_assign(literal_vector const& lits, literal lit);
        bool validate_lemma();
        bool validate_unit_propagation(card const& c, literal alit) const;
        bool validate_unit_propagation(pb const& p, literal alit) const;
        bool validate_unit_propagation(xor const& x, literal alit) const;
        bool validate_conflict(literal_vector const& lits, ineq& p);
        bool validate_watch_literals() const;
        bool validate_watch_literal(literal lit) const;
        bool validate_watched_constraint(constraint const& c) const;
        bool is_watching(literal lit, constraint const& c) const;

        ineq m_A, m_B, m_C;
        void active2pb(ineq& p);
        void justification2pb(justification const& j, literal lit, unsigned offset, ineq& p);
        bool validate_resolvent();

        void display(std::ostream& out, ineq& p) const;
        void display(std::ostream& out, constraint const& c, bool values) const;
        void display(std::ostream& out, card const& c, bool values) const;
        void display(std::ostream& out, pb const& p, bool values) const;
        void display(std::ostream& out, xor const& c, bool values) const;

        void add_at_least(literal l, literal_vector const& lits, unsigned k);
        pb const& add_pb_ge(literal l, svector<wliteral> const& wlits, unsigned k);
        void add_xor(literal l, literal_vector const& lits);

    public:
        ba_solver();
        virtual ~ba_solver();
        virtual void set_solver(solver* s) { m_solver = s; }
        virtual void set_lookahead(lookahead* l) { m_lookahead = l; }
        void    add_at_least(bool_var v, literal_vector const& lits, unsigned k);
        void    add_pb_ge(bool_var v, svector<wliteral> const& wlits, unsigned k);
        void    add_xor(bool_var v, literal_vector const& lits);

        virtual void propagate(literal l, ext_constraint_idx idx, bool & keep);
        virtual bool resolve_conflict();
        virtual void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r);
        virtual void asserted(literal l);
        virtual check_result check();
        virtual void push();
        virtual void pop(unsigned n);
        virtual void simplify();
        virtual void clauses_modifed();
        virtual lbool get_phase(bool_var v);
        virtual bool set_root(literal l, literal r);
        virtual void flush_roots();
        virtual std::ostream& display(std::ostream& out) const;
        virtual std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const;
        virtual void collect_statistics(statistics& st) const;
        virtual extension* copy(solver* s);
        virtual void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes);
        virtual void gc(); 

        ptr_vector<constraint> const & constraints() const { return m_constraints; }

        virtual void validate();

    };

};

#endif
