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
#pragma once

#include "sat/sat_extension.h"
#include "sat/sat_solver.h"
#include "sat/sat_lookahead.h"
#include "sat/sat_big.h"
#include "sat/smt/sat_smt.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/ba_constraint.h"
#include "sat/smt/ba_card.h"
#include "sat/smt/ba_pb.h"
#include "sat/smt/ba_xor.h"
#include "util/small_object_allocator.h"
#include "util/scoped_ptr_vector.h"
#include "util/sorting_network.h"
#include "ast/pb_decl_plugin.h"

namespace sat {

    typedef ba::constraint constraint;
    typedef ba::wliteral wliteral;
    typedef ba::card card;
    typedef ba::xr xr;
    typedef ba::pb_base pb_base;
    typedef ba::pb pb;

    class xor_finder;
    
    class ba_solver : public euf::th_solver, public ba::solver_interface {

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

        sat_internalizer&      si;
        pb_util                m_pb;

        lookahead*             m_lookahead{ nullptr };
        stats                  m_stats; 
        small_object_allocator m_allocator;
       
        ptr_vector<ba::constraint> m_constraints;
        ptr_vector<ba::constraint> m_learned;
        ptr_vector<ba::constraint> m_constraint_to_reinit;
        unsigned_vector        m_constraint_to_reinit_lim;
        unsigned               m_constraint_to_reinit_last_sz{ 0 };
        unsigned               m_constraint_id{ 0 };

        // conflict resolution
        unsigned          m_num_marks{ 0 };
        unsigned          m_conflict_lvl{ 0 };
        svector<int64_t>  m_coeffs;
        svector<bool_var> m_active_vars;
        unsigned          m_bound{ 0 };
        tracked_uint_set  m_active_var_set;
        literal_vector    m_lemma;
        literal_vector    m_skipped;
        unsigned          m_num_propagations_since_pop{ 0 };
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

        // simplification routines

        vector<svector<constraint*>>    m_cnstr_use_list;
        use_list                  m_clause_use_list;
        bool                      m_simplify_change{ false };
        bool                      m_clause_removed{ false };
        bool                      m_constraint_removed{ false };
        literal_vector            m_roots;
        bool_vector               m_root_vars;
        unsigned_vector           m_weights;
        svector<wliteral>         m_wlits;

        euf::th_solver* clone_aux(ast_manager& m, sat::solver& s, sat::sat_internalizer& si, euf::theory_id id);

        bool subsumes(card& c1, card& c2, literal_vector& comp);
        bool subsumes(card& c1, clause& c2, bool& self);
        bool subsumed(card& c1, literal l1, literal l2);
        bool subsumes(pb const& p1, pb_base const& p2);
        void subsumes(pb& p1, literal lit);
        void subsumption(pb& p1);
        void binary_subsumption(card& c1, literal lit);
        void clause_subsumption(card& c1, literal lit, clause_vector& removed_clauses);
        void card_subsumption(card& c1, literal lit);
        unsigned get_num_unblocked_bin(literal l);
        literal get_min_occurrence_literal(card const& c);
        void init_use_lists();
        void remove_unused_defs();
        unsigned set_non_external();
        unsigned elim_pure();
        bool elim_pure(literal lit);
        void unit_strengthen();
        void unit_strengthen(big& big, ba::constraint& cs);
        void unit_strengthen(big& big, pb_base& p);
        void subsumption(ba::constraint& c1);
        void subsumption(card& c1);
        void gc_half(char const* _method);
        void update_psm(constraint& c) const;
        void mutex_reduction();
        void update_pure();
        void reserve_roots();

        unsigned use_count(literal lit) const { return m_cnstr_use_list[lit.index()].size() + m_clause_use_list.get(lit).size(); }

        void cleanup_clauses();
        void cleanup_clauses(clause_vector& clauses);
        void cleanup_constraints();
        void cleanup_constraints(ptr_vector<constraint>& cs, bool learned);
        void remove_constraint(constraint& c, char const* reason);

        // constraints
        constraint& index2constraint(size_t idx) const { return *reinterpret_cast<constraint*>(constraint_base::from_index(idx)->mem()); }
        void pop_constraint();
        // void watch_literal(wliteral w, pb& p);
        void add_constraint(constraint* c);
        bool init_watch(constraint& c);
        void init_watch(bool_var v);
        void clear_watch(constraint& c);
        lbool add_assign(constraint& c, literal l);
        bool incremental_mode() const;
        void simplify(constraint& c);
        void pre_simplify(xor_finder& xu, constraint& c);
        void set_conflict(constraint& c, literal lit) override;
        void assign(constraint& c, literal lit) override;
        bool assigned_above(literal above, literal below);
        void get_antecedents(literal l, constraint const& c, literal_vector & r, bool probing);
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
        double get_reward(literal l, ext_justification_idx idx, literal_occs_fun& occs) const override;

        // cardinality
        lbool add_assign(card& c, literal lit);
        void reset_coeffs();
        void reset_marked_literals();
        void get_antecedents(literal l, card const& c, literal_vector & r);
        void flush_roots(card& c);
        void recompile(card& c);
        bool clausify(card& c);
        bool clausify(literal lit, unsigned n, literal const* lits, unsigned k);
        lbool eval(card const& c) const;
        lbool eval(model const& m, card const& c) const;


        // xr specific functionality
        lbool add_assign(xr& x, literal alit);
        void get_xr_antecedents(literal l, unsigned index, justification js, literal_vector& r);
        void get_antecedents(literal l, xr const& x, literal_vector & r);
        void simplify(xr& x);
        void extract_xor();
        void merge_xor();
        bool clausify(xr& x);
        void flush_roots(xr& x);
        lbool eval(xr const& x) const;
        lbool eval(model const& m, xr const& x) const;
        
        // pb functionality
        unsigned m_a_max{ 0 };
        lbool add_assign(pb& p, literal alit);
        void add_index(pb& p, unsigned index, literal lit);
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

        void init_visited();
        void mark_visited(literal l);
        void mark_visited(bool_var v);
        bool is_visited(bool_var v) const;
        bool is_visited(literal l) const;


        // access solver
        inline lbool value(bool_var v) const override { return value(literal(v, false)); }
        inline lbool value(literal lit) const override { return m_lookahead ? m_lookahead->value(lit) : m_solver->value(lit); }
        inline bool is_false(literal lit) const override { return l_false == value(lit); }

        inline unsigned lvl(literal lit) const override { return m_lookahead ? 0 : m_solver->lvl(lit); }
        inline unsigned lvl(bool_var v) const override { return m_lookahead ? 0 : m_solver->lvl(v); }
        inline bool inconsistent() const override { 
            if (m_lookahead) return m_lookahead->inconsistent(); 
            return m_solver->inconsistent(); 
        }
        inline watch_list& get_wlist(literal l) override { return m_lookahead ? m_lookahead->get_wlist(l) : m_solver->get_wlist(l); }
        inline watch_list const& get_wlist(literal l) const override { return m_lookahead ? m_lookahead->get_wlist(l) : m_solver->get_wlist(l); }
        inline void assign(literal l, justification j) override { 
            if (m_lookahead) m_lookahead->assign(l); 
            else m_solver->assign(l, j);
        }
        inline void set_conflict(justification j, literal l) override { 
            if (m_lookahead) m_lookahead->set_conflict(); 
            else m_solver->set_conflict(j, l); 
        }
        inline config const& get_config() const override { 
            return m_lookahead ? m_lookahead->get_config() : m_solver->get_config(); 
        }


        mutable bool m_overflow{ false };
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
        bool validate_unit_propagation(pb const& p, literal_vector const& r, literal alit) const;
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
        void display_lit(std::ostream& out, literal l, unsigned sz, bool values) const;

        constraint* add_at_least(literal l, literal_vector const& lits, unsigned k, bool learned);
        constraint* add_pb_ge(literal l, svector<wliteral> const& wlits, unsigned k, bool learned);
        constraint* add_xr(literal_vector const& lits, bool learned);
        literal     add_xor_def(literal_vector& lits, bool learned = false);
        bool        all_distinct(literal_vector const& lits);
        bool        all_distinct(clause const& c);
        bool        all_distinct(xr const& x);

        void copy_core(ba_solver* result, bool learned);
        void copy_constraints(ba_solver* result, ptr_vector<constraint> const& constraints);

        // Internalize
        literal convert_eq_k(app* t, rational const& k, bool root, bool sign);
        literal convert_at_most_k(app* t, rational const& k, bool root, bool sign);
        literal convert_at_least_k(app* t, rational const& k, bool root, bool sign);
        literal convert_pb_eq(app* t, bool root, bool sign);
        literal convert_pb_le(app* t, bool root, bool sign);
        literal convert_pb_ge(app* t, bool root, bool sign);
        void check_unsigned(rational const& c);
        void convert_to_wlits(app* t, sat::literal_vector const& lits, svector<wliteral>& wlits);
        void convert_pb_args(app* t, svector<wliteral>& wlits);
        void convert_pb_args(app* t, literal_vector& lits);
        bool m_is_redundant{ false };
        literal internalize_pb(expr* e, bool sign, bool root);
        literal internalize_xor(expr* e, bool sign, bool root);

        // Decompile
        expr_ref get_card(std::function<expr_ref(sat::literal)>& l2e, card const& c);
        expr_ref get_pb(std::function<expr_ref(sat::literal)>& l2e, pb const& p);
        expr_ref get_xor(std::function<expr_ref(sat::literal)>& l2e, xr const& x);

    public:
        ba_solver(euf::solver& ctx, euf::theory_id id);
        ba_solver(ast_manager& m, sat::sat_internalizer& si, euf::theory_id id);
        ~ba_solver() override;
        void set_lookahead(lookahead* l) override { m_lookahead = l; }
        void add_at_least(bool_var v, literal_vector const& lits, unsigned k);
        void add_pb_ge(bool_var v, svector<wliteral> const& wlits, unsigned k);
        void add_xr(literal_vector const& lits);

        bool is_external(bool_var v) override;
        bool propagated(literal l, ext_constraint_idx idx) override;
        bool unit_propagate() override { return false; }
        lbool resolve_conflict() override;
        void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r, bool probing) override;
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
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override;
        void pop_reinit() override;
        void gc() override;
        unsigned max_var(unsigned w) const override;
        bool is_extended_binary(ext_justification_idx idx, literal_vector & r) override;
        void init_use_list(ext_use_list& ul) override;
        bool is_blocked(literal l, ext_constraint_idx idx) override;
        bool check_model(model const& m) const override;

        literal internalize(expr* e, bool sign, bool root, bool redundant) override;
        void internalize(expr* e, bool redundant) override;
        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;
        euf::th_solver* clone(euf::solver& ctx) override;

        ptr_vector<constraint> const & constraints() const { return m_constraints; }
        std::ostream& display(std::ostream& out, constraint const& c, bool values) const;

        bool validate() override;

        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& add_cardinlaity,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& add_pb) override;


    };

};

