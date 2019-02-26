/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_pb.h

Abstract:

    Cardinality theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:

    This custom theory handles cardinality constraints
    It performs unit propagation and switches to creating
    sorting circuits if it keeps having to propagate (create new clauses).
--*/

#include "smt/smt_theory.h"
#include "ast/pb_decl_plugin.h"
#include "smt/smt_clause.h"
#include "smt/smt_b_justification.h"
#include "smt/params/theory_pb_params.h"
#include "math/simplex/simplex.h"

namespace smt {
    class theory_pb : public theory {

        struct psort_expr;
        class  pb_justification;
        class  pb_model_value_proc;
        class  unwatch_ge;
        class  rewatch_vars;
        class  negate_ineq;
        class  remove_var;
        class  undo_bound;

        class  card_justification;

        typedef rational numeral;
        typedef unsynch_mpq_inf_manager eps_manager;
        typedef _scoped_numeral<eps_manager> scoped_eps_numeral;

        struct arg_t : public vector<std::pair<literal, numeral> > {
            numeral         m_k;        // invariants: m_k > 0, coeffs[i] > 0

            unsigned get_hash() const;
            bool operator==(arg_t const& other) const;

            numeral const& k() const { return m_k; }

            struct hash {
                unsigned operator()(arg_t const& i) const { return i.get_hash(); }
            };
            struct eq {
                bool operator()(arg_t const& a, arg_t const& b) const { 
                    return a == b;
                }
            };
            struct child_hash {
                unsigned operator()(arg_t const& args, unsigned idx) const {
                    return args[idx].first.hash() ^ args[idx].second.hash();
                }
            };
            struct kind_hash {
                unsigned operator()(arg_t const& args) const {
                    return args.size();
                }
            };   

            void remove_negations();         

            void negate();

            lbool normalize(bool is_eq);

            void  prune(bool is_eq);
            
            literal lit(unsigned i) const { 
                return (*this)[i].first; 
            }

            numeral const & coeff(unsigned i) const { return (*this)[i].second; }

            std::ostream& display(context& ctx, std::ostream& out, bool values = false) const;

            app_ref to_expr(bool is_eq, context& ctx, ast_manager& m);

            bool well_formed() const;
        };

        struct stats {
            unsigned m_num_conflicts;
            unsigned m_num_propagations;
            unsigned m_num_predicates;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };


        struct ineq {
            unsynch_mpz_manager& m_mpz;    // mpz manager.
            literal         m_lit;      // literal representing predicate
            bool            m_is_eq;    // is this an = or >=.
            arg_t           m_args[2];  // encode args[0]*coeffs[0]+...+args[n-1]*coeffs[n-1] >= k();
            // Watch the first few positions until the sum satisfies:
            // sum coeffs[i] >= m_lower + max_watch            
            scoped_mpz      m_max_watch;    // maximal coefficient.
            unsigned        m_watch_sz;     // number of literals being watched.
            scoped_mpz      m_watch_sum;    // maximal sum of watch literals.
            // Watch infrastructure for = and unassigned >=:
            unsigned        m_nfixed;       // number of variables that are fixed.
            scoped_mpz      m_max_sum;      // maximal possible sum.
            scoped_mpz      m_min_sum;      // minimal possible sum.
            unsigned        m_num_propagations;
            
            ineq(unsynch_mpz_manager& m, literal l, bool is_eq) : 
                m_mpz(m), m_lit(l), m_is_eq(is_eq), 
                m_max_watch(m), m_watch_sum(m), 
                m_max_sum(m), m_min_sum(m) {
                reset();
            }

            arg_t const& args() const { return m_args[m_lit.sign()]; }
            arg_t& args() { return m_args[m_lit.sign()]; }

            literal lit() const { return m_lit; }
            numeral const & k() const { return args().m_k; }
            mpz const & mpz_k() const { return k().to_mpq().numerator(); }

            literal lit(unsigned i) const { return args()[i].first; }
            numeral const & coeff(unsigned i) const { return args()[i].second; }
            class mpz const& ncoeff(unsigned i) const { return coeff(i).to_mpq().numerator(); }

            unsigned size() const { return args().size(); }

            scoped_mpz const& watch_sum() const { return m_watch_sum; }
            scoped_mpz const& max_watch() const { return m_max_watch; }
            void set_max_watch(mpz const& n) { m_max_watch = n; }
            unsigned watch_size() const { return m_watch_sz; }

            // variable watch infrastructure
            scoped_mpz const& min_sum() const { return m_min_sum; }
            scoped_mpz const& max_sum() const { return m_max_sum; }
            unsigned nfixed() const { return m_nfixed; }
            bool vwatch_initialized() const { return !m_mpz.is_zero(max_sum()); }
            void vwatch_reset() { m_min_sum.reset(); m_max_sum.reset(); m_nfixed = 0; }

            unsigned find_lit(bool_var v, unsigned begin, unsigned end) {
                while (lit(begin).var() != v) {
                    ++begin;
                    SASSERT(begin < end);
                }
                return begin;
            }

            void reset();

            void negate();

            lbool normalize();

            void unique();

            void prune();

            void post_prune();

            app_ref to_expr(context& ctx, ast_manager& m);

            bool is_eq() const { return m_is_eq; }
            bool is_ge() const { return !m_is_eq; }

        };

        // cardinality constraint args >= bound
        // unit propagation on cardinality constraints is valid if the literals
        // from k() up to size are false.
        // In this case the literals 0..k()-1 need to be true. 
        // The literals in position 0..k() are watched.
        // whenever they are assigned to false, then find a literal among
        // k() + 1.. sz() to swap with.
        // If none are available, then perform unit propagation.
        // 
        class card {
            literal         m_lit;      // literal representing predicate
            literal_vector  m_args;
            unsigned        m_bound;
            unsigned        m_num_propagations;
            unsigned        m_all_propagations;
            bool            m_aux;
            
        public:
            card(literal l, unsigned bound, bool is_aux):
                m_lit(l),
                m_bound(bound),
                m_num_propagations(0),
                m_all_propagations(0),
                m_aux(is_aux)
            {
                SASSERT(bound > 0);
            }            
            
            literal lit() const { return m_lit; }
            literal lit(unsigned i) const { return m_args[i]; }
            unsigned k() const { return m_bound; }
            unsigned size() const { return m_args.size(); }
            unsigned all_propagations() const { return m_all_propagations; }
            unsigned num_propagations() const { return m_num_propagations; }
            void add_arg(literal l);
        
            void init_watch(theory_pb& th, bool is_true);

            lbool assign(theory_pb& th, literal lit);
        
            void negate();

            app_ref to_expr(theory_pb& th);

            void inc_propagations(theory_pb& th);

            void reset_propagations() { m_all_propagations += m_num_propagations; m_num_propagations = 0; }

            bool is_aux() const { return m_aux; }

        private:

            bool validate_conflict(theory_pb& th);
            
            bool validate_assign(theory_pb& th, literal_vector const& lits, literal l);

            void set_conflict(theory_pb& th, literal l);
        };

        typedef ptr_vector<card> card_watch;
        typedef ptr_vector<ineq> ineq_watch;
        typedef map<arg_t, bool_var, arg_t::hash, arg_t::eq> arg_map;


        struct var_info {
            ineq_watch*  m_lit_watch[2];
            ineq*        m_ineq;

            card_watch*  m_lit_cwatch[2];
            card*        m_card;
            
            var_info(): m_ineq(nullptr), m_card(nullptr)
            {
                m_lit_watch[0] = nullptr;
                m_lit_watch[1] = nullptr;
                m_lit_cwatch[0] = nullptr;
                m_lit_cwatch[1] = nullptr;
            }

            void reset() {
                dealloc(m_lit_watch[0]);
                dealloc(m_lit_watch[1]);
                dealloc(m_ineq);
                dealloc(m_lit_cwatch[0]);
                dealloc(m_lit_cwatch[1]);
                dealloc(m_card);
            }
        };

        theory_pb_params         m_params;        

        svector<var_info>        m_var_infos; 
        mutable unsynch_mpz_manager      m_mpz_mgr;        // Simplex: manager mpz numerals
        unsigned_vector          m_ineqs_trail;
        unsigned_vector          m_ineqs_lim;
        literal_vector           m_literals;    // temporary vector
        pb_util                  pb;
        stats                    m_stats;
        unsigned                 m_conflict_frequency;
        bool                     m_learn_complements;

        unsigned                 m_restart_lim;
        unsigned                 m_restart_inc;
        uint_set                 m_occs;

        // internalize_atom:
        literal compile_arg(expr* arg);
        void init_watch(bool_var v);
        
        // general purpose pb constraints
        void add_watch(ineq& c, unsigned index);
        void del_watch(ineq_watch& watch, unsigned index, ineq& c, unsigned ineq_index);
        void init_watch_literal(ineq& c);
        void init_watch_ineq(ineq& c);
        void clear_watch(ineq& c);
        void watch_literal(literal lit, ineq* c);
        void unwatch_literal(literal w, ineq* c);
        void remove(ptr_vector<ineq>& ineqs, ineq* c);

        bool assign_watch_ge(bool_var v, bool is_true, ineq_watch& watch, unsigned index);
        void assign_ineq(ineq& c, bool is_true);
        void assign_eq(ineq& c, bool is_true);

        // cardinality constraints
        // these are cheaper to handle than general purpose PB constraints
        // and in the common case PB constraints with small coefficients can
        // be handled using cardinality constraints.

        unsigned_vector          m_card_trail;
        unsigned_vector          m_card_lim;       
        bool is_cardinality_constraint(app * atom);
        bool internalize_card(app * atom, bool gate_ctx);
        void card2conjunction(card const& c);
        void card2disjunction(card const& c);

        void watch_literal(literal lit, card* c);
        void unwatch_literal(literal w, card* c);
        void add_clause(card& c, literal_vector const& lits);
        void add_assign(card& c, literal l);
        void remove(ptr_vector<card>& cards, card* c);
        void clear_watch(card& c); 
        bool gc();
        std::ostream& display(std::ostream& out, card const& c, bool values = false) const;


        // simplex:
        bool check_feasible();

        std::ostream& display(std::ostream& out, ineq const& c, bool values = false) const;
        std::ostream& display(std::ostream& out, arg_t const& c, bool values = false) const;
        void display(std::ostream& out) const override;
        void display_watch(std::ostream& out, bool_var v, bool sign) const;
        void display_resolved_lemma(std::ostream& out) const;

        void add_clause(ineq& c, literal_vector const& lits);
        void add_assign(ineq& c, literal_vector const& lits, literal l);
        literal_vector& get_lits();

        literal_vector& get_all_literals(ineq& c, bool negate);
        literal_vector& get_helpful_literals(ineq& c, bool negate);
        literal_vector& get_unhelpful_literals(ineq& c, bool negate);

        void inc_propagations(ineq& c);

        //
        // Conflict resolution, cutting plane derivation.
        // 
        unsigned          m_num_marks;
        literal_vector    m_resolved;
        unsigned          m_conflict_lvl;

        // Conflict PB constraints
        svector<int>      m_coeffs;
        svector<bool_var> m_active_vars;
        int               m_bound;
        literal_vector    m_antecedents;
        tracked_uint_set  m_active_var_set;
        expr_ref_vector   m_antecedent_exprs;
        svector<bool>     m_antecedent_signs;
        expr_ref_vector   m_cardinality_exprs;
        svector<bool>     m_cardinality_signs;

        void normalize_active_coeffs();
        void inc_coeff(literal l, int offset);
        int get_coeff(bool_var v) const;
        int get_abs_coeff(bool_var v) const;       
        int arg_max(int& coeff); 

        literal_vector& get_literals() { m_literals.reset(); return m_literals; }

        vector<svector<bool_var> > m_coeff2args;
        unsigned_vector m_active_coeffs;
        bool init_arg_max();
        void reset_arg_max();

        void reset_coeffs();
        literal get_asserting_literal(literal conseq);

        bool resolve_conflict(card& c, literal_vector const& conflict_clause);
        void process_antecedent(literal l, int offset);
        void process_card(card& c, int offset);
        void cut();
        bool is_proof_justification(justification const& j) const;


        void hoist_maximal_values();

        bool validate_lemma();
        void validate_final_check();
        void validate_final_check(ineq& c);
        void validate_final_check(card& c);
        void validate_assign(ineq const& c, literal_vector const& lits, literal l) const;
        void validate_watch(ineq const& c) const;
        bool validate_unit_propagation(card const& c);
        bool validate_antecedents(literal_vector const& lits);
        bool validate_implies(app_ref& A, app_ref& B);
        app_ref active2expr();
        app_ref literal2expr(literal lit);
        app_ref card2expr(card& c) { return c.to_expr(*this); }
        app_ref justification2expr(b_justification& js, literal conseq);

        bool proofs_enabled() const { return get_manager().proofs_enabled(); }
        justification* justify(literal l1, literal l2);
        justification* justify(literal_vector const& lits);

    public:
        theory_pb(ast_manager& m, theory_pb_params& p);
        
        ~theory_pb() override;

        theory * mk_fresh(context * new_ctx) override;
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override { UNREACHABLE(); return false; }
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override { }
        bool use_diseqs() const override { return false; }
        bool build_models() const override { return false; }
        final_check_status final_check_eh() override;
        void reset_eh() override;
        void assign_eh(bool_var v, bool is_true) override;
        void init_search_eh() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        void collect_statistics(::statistics & st) const override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
        void init_model(model_generator & m) override;
        bool include_func_interp(func_decl* f) override { return false; }
        bool can_propagate() override;
        void propagate() override; 
        static literal assert_ge(context& ctx, unsigned k, unsigned n, literal const* xs);
    };
};
