/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_solver.h

Abstract:

    Cardinality extensions, 
    Pseudo Booleans, 
    Xors

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/
#ifndef BA_SOLVER_H_
#define BA_SOLVER_H_

#include "sat/sat_extension.h"
#include "sat/sat_solver.h"
#include "sat/sat_lookahead.h"
#include "sat/sat_unit_walk.h"
#include "sat/sat_big.h"
#include "util/small_object_allocator.h"
#include "util/scoped_ptr_vector.h"
#include "util/sorting_network.h"

namespace sat {
    
    class ba_solver : public extension {

        friend class local_search;

        struct stats {
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            unsigned m_num_resolves;
            unsigned m_num_bin_subsumes;
            unsigned m_num_clause_subsumes;
            unsigned m_num_pb_subsumes;
            unsigned m_num_big_strengthenings;
            unsigned m_num_cut;
            unsigned m_num_gc;
            unsigned m_num_overflow;
            unsigned m_num_lemmas;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

    public:        
        enum tag_t {
            card_t,
            pb_t,
            xr_t
        };

        class card;
        class pb;
        class xr;
        class pb_base;

        class constraint {
        protected:
            tag_t          m_tag;
            bool           m_removed;
            literal        m_lit;
            literal        m_watch;
            unsigned       m_glue;
            unsigned       m_psm;
            unsigned       m_size;
            size_t         m_obj_size;
            bool           m_learned;
            unsigned       m_id;
            bool           m_pure;        // is the constraint pure (only positive occurrences)
        public:
            constraint(tag_t t, unsigned id, literal l, unsigned sz, size_t osz): 
            m_tag(t), m_removed(false), m_lit(l), m_watch(null_literal), m_glue(0), m_psm(0), m_size(sz), m_obj_size(osz), m_learned(false), m_id(id), m_pure(false) {}
            ext_constraint_idx index() const { return reinterpret_cast<ext_constraint_idx>(this); }
            unsigned id() const { return m_id; }
            tag_t tag() const { return m_tag; }
            literal lit() const { return m_lit; }
            unsigned size() const { return m_size; }
            void set_size(unsigned sz) { SASSERT(sz <= m_size); m_size = sz; }
            void update_literal(literal l) { m_lit = l; }
            bool was_removed() const { return m_removed; }
            void set_removed() { m_removed = true; }
            void nullify_literal() { m_lit = null_literal; }
            unsigned glue() const { return m_glue; }
            void set_glue(unsigned g) { m_glue = g; }          
            unsigned psm() const { return m_psm; }
            void set_psm(unsigned p) { m_psm = p; }
            void set_learned(bool f) { m_learned = f; }
            bool learned() const { return m_learned; }            
            bool is_watched() const { return m_watch == m_lit && m_lit != null_literal; }
            void set_watch() { m_watch = m_lit; }
            void clear_watch() { m_watch = null_literal; }
            bool is_clear() const { return m_watch == null_literal && m_lit != null_literal; }
            bool is_pure() const { return m_pure; }
            void set_pure() { m_pure = true; }
            unsigned fold_max_var(unsigned w) const;

            size_t obj_size() const { return m_obj_size; }
            card& to_card();
            pb&  to_pb();
            xr& to_xr();
            card const& to_card() const;
            pb const&  to_pb() const;
            xr const& to_xr() const;
            pb_base const& to_pb_base() const; 
            bool is_card() const { return m_tag == card_t; }
            bool is_pb() const { return m_tag == pb_t; }
            bool is_xr() const { return m_tag == xr_t; }
            
            virtual bool is_watching(literal l) const { UNREACHABLE(); return false; };
            virtual literal_vector literals() const { UNREACHABLE(); return literal_vector(); }
            virtual void swap(unsigned i, unsigned j) { UNREACHABLE(); }
            virtual literal get_lit(unsigned i) const { UNREACHABLE(); return null_literal; }
            virtual void set_lit(unsigned i, literal l) { UNREACHABLE(); }
            virtual bool well_formed() const { return true; }
            virtual void negate() { UNREACHABLE(); }
        };

        friend std::ostream& operator<<(std::ostream& out, constraint const& c);
        
        // base class for pb and cardinality constraints
        class pb_base : public constraint {
        protected:
            unsigned       m_k;
        public:
            pb_base(tag_t t, unsigned id, literal l, unsigned sz, size_t osz, unsigned k): constraint(t, id, l, sz, osz), m_k(k) { VERIFY(k < 4000000000); }
            virtual void set_k(unsigned k) { VERIFY(k < 4000000000);  m_k = k; }
            virtual unsigned get_coeff(unsigned i) const { UNREACHABLE(); return 0; }
            unsigned k() const { return m_k; }
            bool well_formed() const override;
        };

        class card : public pb_base {
            literal        m_lits[0];
        public:
            static size_t get_obj_size(unsigned num_lits) { return sizeof(card) + num_lits * sizeof(literal); }
            card(unsigned id, literal lit, literal_vector const& lits, unsigned k);
            literal operator[](unsigned i) const { return m_lits[i]; }
            literal& operator[](unsigned i) { return m_lits[i]; }
            literal const* begin() const { return m_lits; }
            literal const* end() const { return static_cast<literal const*>(m_lits) + m_size; }
            void negate() override;
            void swap(unsigned i, unsigned j) override { std::swap(m_lits[i], m_lits[j]); }
            literal_vector literals() const override { return literal_vector(m_size, m_lits); }
            bool is_watching(literal l) const override;
            literal get_lit(unsigned i) const override { return m_lits[i]; }
            void set_lit(unsigned i, literal l) override { m_lits[i] = l; }
            unsigned get_coeff(unsigned i) const override { return 1; }
        };

        
        typedef std::pair<unsigned, literal> wliteral;

        class pb : public pb_base {
            unsigned       m_slack;
            unsigned       m_num_watch;
            unsigned       m_max_sum;
            wliteral       m_wlits[0];
        public:
            static size_t get_obj_size(unsigned num_lits) { return sizeof(pb) + num_lits * sizeof(wliteral); }
            pb(unsigned id, literal lit, svector<wliteral> const& wlits, unsigned k);
            literal lit() const { return m_lit; }
            wliteral operator[](unsigned i) const { return m_wlits[i]; }
            wliteral& operator[](unsigned i) { return m_wlits[i]; }
            wliteral const* begin() const { return m_wlits; }
            wliteral const* end() const { return begin() + m_size; }

            unsigned slack() const { return m_slack; }
            void set_slack(unsigned s) { m_slack = s; }
            unsigned num_watch() const { return m_num_watch; }
            unsigned max_sum() const { return m_max_sum; }
            void update_max_sum();
            void set_num_watch(unsigned s) { m_num_watch = s; }
            bool is_cardinality() const;
            void negate() override;
            void set_k(unsigned k) override { m_k = k; VERIFY(k < 4000000000); update_max_sum(); }
            void swap(unsigned i, unsigned j) override { std::swap(m_wlits[i], m_wlits[j]); }
            literal_vector literals() const override { literal_vector lits; for (auto wl : *this) lits.push_back(wl.second); return lits; }
            bool is_watching(literal l) const override;
            literal get_lit(unsigned i) const override { return m_wlits[i].second; }
            void set_lit(unsigned i, literal l) override { m_wlits[i].second = l; }
            unsigned get_coeff(unsigned i) const override { return m_wlits[i].first; }
        };

        class xr : public constraint {
            literal        m_lits[0];
        public:
            static size_t get_obj_size(unsigned num_lits) { return sizeof(xr) + num_lits * sizeof(literal); }
            xr(unsigned id, literal_vector const& lits);
            literal operator[](unsigned i) const { return m_lits[i]; }
            literal const* begin() const { return m_lits; }
            literal const* end() const { return begin() + m_size; }
            void negate() override { m_lits[0].neg(); }
            void swap(unsigned i, unsigned j) override { std::swap(m_lits[i], m_lits[j]); }
            bool is_watching(literal l) const override;
            literal_vector literals() const override { return literal_vector(size(), begin()); }
            literal get_lit(unsigned i) const override { return m_lits[i]; }
            void set_lit(unsigned i, literal l) override { m_lits[i] = l; }
            bool well_formed() const override;
        };


    protected:

        struct ineq {
            svector<wliteral> m_wlits;
            uint64_t          m_k;
            ineq(): m_k(0) {}
            unsigned size() const { return m_wlits.size(); }
            literal lit(unsigned i) const { return m_wlits[i].second; }
            unsigned coeff(unsigned i) const { return m_wlits[i].first; }
            void reset(uint64_t k) { m_wlits.reset(); m_k = k; }
            void push(literal l, unsigned c) { m_wlits.push_back(wliteral(c,l)); }
            unsigned bv_coeff(bool_var v) const;
            void divide(unsigned c);
            void weaken(unsigned i);
            bool contains(literal l) const { for (auto wl : m_wlits) if (wl.second == l) return true; return false; }
        };

        solver*                m_solver;
        lookahead*             m_lookahead;
        unit_walk*             m_unit_walk;
        stats                  m_stats; 
        small_object_allocator m_allocator;
       

        ptr_vector<constraint> m_constraints;
        ptr_vector<constraint> m_learned;
        ptr_vector<constraint> m_constraint_to_reinit;
        unsigned_vector        m_constraint_to_reinit_lim;
        unsigned               m_constraint_to_reinit_last_sz;
        unsigned               m_constraint_id;

        // conflict resolution
        unsigned          m_num_marks;
        unsigned          m_conflict_lvl;
        svector<int64_t>  m_coeffs;
        svector<bool_var> m_active_vars;
        unsigned          m_bound;
        tracked_uint_set  m_active_var_set;
        literal_vector    m_lemma;
        literal_vector    m_skipped;
        unsigned          m_num_propagations_since_pop;
        unsigned_vector   m_parity_marks;
        literal_vector    m_parity_trail;

        unsigned_vector   m_pb_undef;

        struct ba_sort {
            typedef sat::literal pliteral;
            typedef sat::literal_vector pliteral_vector;

            ba_solver& s;
            pliteral m_true;
            pliteral_vector m_lits;
            

            ba_sort(ba_solver& s): s(s), m_true(null_literal) {}
            pliteral mk_false();
            pliteral mk_true();
            pliteral mk_not(pliteral l);
            pliteral fresh(char const*);
            pliteral mk_min(unsigned, pliteral const* lits);
            pliteral mk_max(unsigned, pliteral const* lits);
            void    mk_clause(unsigned n, literal const* lits);
            std::ostream& pp(std::ostream& out, pliteral l) const;
        };
        ba_sort           m_ba;
        psort_nw<ba_sort> m_sort;

        void     ensure_parity_size(bool_var v);
        unsigned get_parity(bool_var v);
        void     inc_parity(bool_var v);
        void     reset_parity(bool_var v);

        solver& s() const { return *m_solver; }


        // simplification routines

        svector<unsigned>             m_visited;
        unsigned                      m_visited_ts;
        vector<svector<constraint*>>    m_cnstr_use_list;
        use_list                  m_clause_use_list;
        bool                      m_simplify_change;
        bool                      m_clause_removed;
        bool                      m_constraint_removed;
        literal_vector            m_roots;
        svector<bool>             m_root_vars;
        unsigned_vector           m_weights;
        svector<wliteral>         m_wlits;
        bool subsumes(card& c1, card& c2, literal_vector& comp);
        bool subsumes(card& c1, clause& c2, bool& self);
        bool subsumed(card& c1, literal l1, literal l2);
        bool subsumes(pb const& p1, pb_base const& p2);
        void subsumes(pb& p1, literal lit);
        void subsumption(pb& p1);
        void binary_subsumption(card& c1, literal lit);
        void clause_subsumption(card& c1, literal lit, clause_vector& removed_clauses);
        void card_subsumption(card& c1, literal lit);
        void init_visited();
        void mark_visited(literal l) { m_visited[l.index()] = m_visited_ts; }
        void mark_visited(bool_var v) { mark_visited(literal(v, false)); }
        bool is_visited(bool_var v) const { return is_visited(literal(v, false)); }
        bool is_visited(literal l) const { return m_visited[l.index()] == m_visited_ts; }
        unsigned get_num_unblocked_bin(literal l);
        literal get_min_occurrence_literal(card const& c);
        void init_use_lists();
        void remove_unused_defs();
        unsigned set_non_external();
        unsigned elim_pure();
        bool elim_pure(literal lit);
        void unit_strengthen();
        void unit_strengthen(big& big, constraint& cs);
        void unit_strengthen(big& big, pb_base& p);
        void subsumption(constraint& c1);
        void subsumption(card& c1);
        void gc_half(char const* _method);
        void update_psm(constraint& c) const;
        void mutex_reduction();
        void update_pure();

        unsigned use_count(literal lit) const { return m_cnstr_use_list[lit.index()].size() + m_clause_use_list.get(lit).size(); }

        void cleanup_clauses();
        void cleanup_clauses(clause_vector& clauses);
        void cleanup_constraints();
        void cleanup_constraints(ptr_vector<constraint>& cs, bool learned);
        void remove_constraint(constraint& c, char const* reason);

        // constraints
        constraint& index2constraint(size_t idx) const { return *reinterpret_cast<constraint*>(idx); }        
        void pop_constraint();
        void unwatch_literal(literal w, constraint& c);
        void watch_literal(literal w, constraint& c);
        void watch_literal(wliteral w, pb& p);
        bool is_watched(literal l, constraint const& c) const;
        void add_constraint(constraint* c);
        bool init_watch(constraint& c);
        void init_watch(bool_var v);
        void clear_watch(constraint& c);
        lbool add_assign(constraint& c, literal l);
        bool incremental_mode() const;
        void simplify(constraint& c);
        void pre_simplify(constraint& c);
        void nullify_tracking_literal(constraint& c);
        void set_conflict(constraint& c, literal lit);
        void assign(constraint& c, literal lit);
        bool assigned_above(literal above, literal below);
        void get_antecedents(literal l, constraint const& c, literal_vector & r);
        bool validate_conflict(constraint const& c) const;
        bool validate_unit_propagation(constraint const& c, literal alit) const;
        void validate_eliminated();
        void validate_eliminated(ptr_vector<constraint> const& cs);
        void attach_constraint(constraint const& c);
        void detach_constraint(constraint const& c);
        lbool eval(constraint const& c) const;
        lbool eval(model const& m, constraint const& c) const;
        lbool eval(lbool a, lbool b) const;
        void assert_unconstrained(literal lit, literal_vector const& lits);
        void flush_roots(constraint& c);
        void recompile(constraint& c);
        void split_root(constraint& c);
        unsigned next_id() { return m_constraint_id++; }
        void set_non_learned(constraint& c);


        // cardinality
        bool init_watch(card& c);
        lbool add_assign(card& c, literal lit);
        void clear_watch(card& c);
        void reset_coeffs();
        void reset_marked_literals();
        void get_antecedents(literal l, card const& c, literal_vector & r);
        void flush_roots(card& c);
        void recompile(card& c);
        bool clausify(card& c);
        bool clausify(literal lit, unsigned n, literal const* lits, unsigned k);
        lbool eval(card const& c) const;
        lbool eval(model const& m, card const& c) const;
        double get_reward(card const& c, literal_occs_fun& occs) const;


        // xr specific functionality
        void clear_watch(xr& x);
        bool init_watch(xr& x);
        bool parity(xr const& x, unsigned offset) const;
        lbool add_assign(xr& x, literal alit);
        void get_xr_antecedents(literal l, unsigned index, justification js, literal_vector& r);
        void get_antecedents(literal l, xr const& x, literal_vector & r);
        void simplify(xr& x);
        void extract_xor();
        void merge_xor();
        struct clause_filter {
            unsigned m_filter;
            clause*  m_clause;            
            clause_filter(unsigned f, clause* cp):
                m_filter(f), m_clause(cp) {}
        };
        typedef svector<bool> bool_vector;
        unsigned                m_max_xor_size;
        vector<svector<clause_filter>>   m_clause_filters;      // index of clauses.
        unsigned                m_barbet_combination;  // bit-mask of parities that have been found
        vector<bool_vector>     m_barbet_parity;       // lookup parity for clauses
        clause_vector           m_barbet_clauses_to_remove;    // remove clauses that become xors
        unsigned_vector         m_barbet_var_position; // position of var in main clause
        literal_vector          m_barbet_clause;       // reference clause with literals sorted according to main clause
        unsigned_vector         m_barbet_missing;      // set of indices not occurring in clause.
        void init_clause_filter();
        void init_clause_filter(clause_vector& clauses);
        inline void barbet_set_combination(unsigned mask) { m_barbet_combination |= (1 << mask); }
        inline bool barbet_get_combination(unsigned mask) const { return (m_barbet_combination & (1 << mask)) != 0; }
        void barbet_extract_xor();
        void barbet_init_parity();
        void barbet_extract_xor(clause& c);
        bool barbet_extract_xor(bool parity, clause& c, clause& c2);
        bool barbet_extract_xor(bool parity, clause& c, literal l1, literal l2);
        bool barbet_update_combinations(clause& c, bool parity, unsigned mask);
        void barbet_add_xor(bool parity, clause& c);
        unsigned get_clause_filter(clause& c);

        vector<ptr_vector<clause>> m_ternary;
        void extract_ternary(clause_vector const& clauses);
        bool extract_xor(clause& c, literal l);
        bool extract_xor(clause& c1, clause& c2);
        bool clausify(xr& x);
        void flush_roots(xr& x);
        lbool eval(xr const& x) const;
        lbool eval(model const& m, xr const& x) const;
        
        // pb functionality
        unsigned m_a_max;
        bool init_watch(pb& p);
        lbool add_assign(pb& p, literal alit);
        void add_index(pb& p, unsigned index, literal lit);
        void clear_watch(pb& p);
        void get_antecedents(literal l, pb const& p, literal_vector & r);
        void split_root(pb_base& p);
        void simplify(pb_base& p);
        void simplify2(pb& p);
        bool is_cardinality(pb const& p);
        void flush_roots(pb& p);
        void recompile(pb& p);
        bool clausify(pb& p);
        bool is_cardinality(pb const& p, literal_vector& lits);
        lbool eval(pb const& p) const;
        lbool eval(model const& m, pb const& p) const;
        double get_reward(pb const& p, literal_occs_fun& occs) const;

        // RoundingPb conflict resolution
        lbool resolve_conflict_rs();
        void round_to_one(ineq& ineq, bool_var v);
        void round_to_one(bool_var v);
        void divide(unsigned c);
        void resolve_on(literal lit);
        void resolve_with(ineq const& ineq);
        void reset_marks(unsigned idx);
        void mark_variables(ineq const& ineq);

        void bail_resolve_conflict(unsigned idx);        

        // access solver
        inline lbool value(bool_var v) const { return value(literal(v, false)); }
        inline lbool value(literal lit) const { return m_lookahead ? m_lookahead->value(lit) : m_solver->value(lit); }
        inline lbool value(model const& m, literal l) const { return l.sign() ? ~m[l.var()] : m[l.var()]; }
        inline bool is_false(literal lit) const { return l_false == value(lit); }

        inline unsigned lvl(literal lit) const { return m_lookahead || m_unit_walk ? 0 : m_solver->lvl(lit); }
        inline unsigned lvl(bool_var v) const { return m_lookahead || m_unit_walk ? 0 : m_solver->lvl(v); }
        inline bool inconsistent() const { 
            if (m_lookahead) return m_lookahead->inconsistent(); 
            if (m_unit_walk) return m_unit_walk->inconsistent();
            return m_solver->inconsistent(); 
        }
        inline watch_list& get_wlist(literal l) { return m_lookahead ? m_lookahead->get_wlist(l) : m_solver->get_wlist(l); }
        inline watch_list const& get_wlist(literal l) const { return m_lookahead ? m_lookahead->get_wlist(l) : m_solver->get_wlist(l); }
        inline void assign(literal l, justification j) { 
            if (m_lookahead) m_lookahead->assign(l); 
            else if (m_unit_walk) m_unit_walk->assign(l);
            else m_solver->assign(l, j);
        }
        inline void set_conflict(justification j, literal l) { 
            if (m_lookahead) m_lookahead->set_conflict(); 
            else if (m_unit_walk) m_unit_walk->set_conflict();
            else m_solver->set_conflict(j, l); 
        }
        inline config const& get_config() const { return m_lookahead ? m_lookahead->get_config() : m_solver->get_config(); }
        inline void drat_add(literal_vector const& c, svector<drat::premise> const& premises) { if (m_solver) m_solver->m_drat.add(c, premises); }


        mutable bool m_overflow;
        void reset_active_var_set();
        bool test_and_set_active(bool_var v);
        void inc_coeff(literal l, unsigned offset);
        int64_t get_coeff(bool_var v) const;
        uint64_t get_coeff(literal lit) const;
        wliteral get_wliteral(bool_var v);
        unsigned get_abs_coeff(bool_var v) const;       
        int   get_int_coeff(bool_var v) const;
        unsigned get_bound() const;
        void inc_bound(int64_t i);

        literal get_asserting_literal(literal conseq);
        void process_antecedent(literal l, unsigned offset);
        void process_antecedent(literal l) { process_antecedent(l, 1); }
        void process_card(card& c, unsigned offset);
        void cut();
        bool create_asserting_lemma();

        // validation utilities
        bool validate_conflict(card const& c) const;
        bool validate_conflict(xr const& x) const;
        bool validate_conflict(pb const& p) const;
        bool validate_assign(literal_vector const& lits, literal lit);
        bool validate_lemma();
        bool validate_ineq(ineq const& ineq) const;
        bool validate_unit_propagation(card const& c, literal alit) const;
        bool validate_unit_propagation(pb const& p, literal alit) const;
        bool validate_unit_propagation(pb const& p, literal_vector const& r, literal alit) const;
        bool validate_unit_propagation(xr const& x, literal alit) const;
        bool validate_conflict(literal_vector const& lits, ineq& p);
        bool validate_watch_literals() const;
        bool validate_watch_literal(literal lit) const;
        bool validate_watched_constraint(constraint const& c) const;
        bool validate_watch(pb const& p, literal alit) const;
        bool is_watching(literal lit, constraint const& c) const;
        literal translate_to_sat(solver& s, u_map<bool_var>& translation, ineq const& pb);
        literal translate_to_sat(solver& s, u_map<bool_var>& translation, ineq& a, ineq& b);
        literal translate_to_sat(solver& s, u_map<bool_var>& translation, literal lit);
        ineq negate(ineq const& a) const;
        void push_lit(literal_vector& lits, literal lit);

        ineq m_A, m_B, m_C;
        void active2pb(ineq& p);
        constraint* active2lemma();
        constraint* active2constraint();
        constraint* active2card();
        void active2wlits();
        void active2wlits(svector<wliteral>& wlits);
        void justification2pb(justification const& j, literal lit, unsigned offset, ineq& p);
        void constraint2pb(constraint& cnstr, literal lit, unsigned offset, ineq& p);
        bool validate_resolvent();
        unsigned get_coeff(ineq const& pb, literal lit);

        void display(std::ostream& out, ineq const& p, bool values = false) const;
        void display(std::ostream& out, card const& c, bool values) const;
        void display(std::ostream& out, pb const& p, bool values) const;
        void display(std::ostream& out, xr const& c, bool values) const;
        void display_lit(std::ostream& out, literal l, unsigned sz, bool values) const;

        constraint* add_at_least(literal l, literal_vector const& lits, unsigned k, bool learned);
        constraint* add_pb_ge(literal l, svector<wliteral> const& wlits, unsigned k, bool learned);
        constraint* add_xr(literal_vector const& lits, bool learned);
        literal     add_xor_def(literal_vector& lits, bool learned = false);
        bool        all_distinct(literal_vector const& lits);
        bool        all_distinct(xr const& x);
        bool        all_distinct(clause const& cl);

        void copy_core(ba_solver* result, bool learned);
        void copy_constraints(ba_solver* result, ptr_vector<constraint> const& constraints);

    public:
        ba_solver();
        ~ba_solver() override;
        void set_solver(solver* s) override { m_solver = s; }
        void set_lookahead(lookahead* l) override { m_lookahead = l; }
        void set_unit_walk(unit_walk* u) override { m_unit_walk = u; }
        void    add_at_least(bool_var v, literal_vector const& lits, unsigned k);
        void    add_pb_ge(bool_var v, svector<wliteral> const& wlits, unsigned k);
        void    add_xr(literal_vector const& lits);

        bool propagate(literal l, ext_constraint_idx idx) override;
        lbool resolve_conflict() override;
        void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) override;
        void asserted(literal l) override;
        check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        void pre_simplify() override;
        void simplify() override;
        void clauses_modifed() override;
        lbool get_phase(bool_var v) override;
        bool set_root(literal l, literal r) override;
        void flush_roots() override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        extension* copy(solver* s) override;
        extension* copy(lookahead* s, bool learned) override;
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override;
        void pop_reinit() override;
        void gc() override;
        unsigned max_var(unsigned w) const override;
        double get_reward(literal l, ext_justification_idx idx, literal_occs_fun& occs) const override;
        bool is_extended_binary(ext_justification_idx idx, literal_vector & r) override;
        void init_use_list(ext_use_list& ul) override;
        bool is_blocked(literal l, ext_constraint_idx idx) override;
        bool check_model(model const& m) const override;

        ptr_vector<constraint> const & constraints() const { return m_constraints; }
        void display(std::ostream& out, constraint const& c, bool values) const;

        bool validate() override;


    };

};

#endif
