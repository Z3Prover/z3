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

#include "smt_theory.h"
#include "pb_decl_plugin.h"
#include "smt_clause.h"

namespace smt {
    class theory_pb : public theory {

        struct sort_expr;
        class  pb_justification;
        class pb_model_value_proc;
        typedef rational numeral;
        typedef vector<std::pair<literal, numeral> > arg_t;

        struct stats {
            unsigned m_num_conflicts;
            unsigned m_num_propagations;
            unsigned m_num_predicates;
            unsigned m_num_compiles;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };


        struct ineq {
            literal         m_lit;      // literal repesenting predicate
            arg_t           m_args;     // encode args[0]*coeffs[0]+...+args[n-1]*coeffs[n-1] >= m_k;
            numeral         m_k;        // invariants: m_k > 0, coeffs[i] > 0
            
            // Watch the first few positions until the sum satisfies:
            // sum coeffs[i] >= m_lower + max_watch
            
            numeral         m_max_watch;    // maximal coefficient.
            unsigned        m_watch_sz;     // number of literals being watched.
            numeral         m_watch_sum;      // maximal sum of watch literals.
            unsigned        m_num_propagations;
            unsigned        m_compilation_threshold;
            lbool           m_compiled;
            
            ineq(literal l) : m_lit(l) {
                reset();
            }

            literal lit() const { return m_lit; }
            numeral const & k() const { return m_k; }

            literal lit(unsigned i) const { return m_args[i].first; }
            numeral const & coeff(unsigned i) const { return m_args[i].second; }

            unsigned size() const { return m_args.size(); }

            numeral const& watch_sum() const { return m_watch_sum; }
            numeral const& max_watch() const { return m_max_watch; }
            void set_max_watch(numeral const& n) { m_max_watch = n; }
            
            unsigned watch_size() const { return m_watch_sz; }

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

            bool well_formed() const;

            app_ref to_expr(context& ctx, ast_manager& m);
        };

        typedef ptr_vector<ineq> watch_list;
        
        u_map<watch_list*>       m_watch;       // per literal.
        u_map<ineq*>             m_ineqs;       // per inequality.
        unsigned_vector          m_ineqs_trail;
        unsigned_vector          m_ineqs_lim;
        ptr_vector<ineq>         m_assign_ineqs_trail;
        unsigned_vector          m_assign_ineqs_lim;
        literal_vector           m_literals;    // temporary vector
        pb_util                  m_util;
        stats                    m_stats;
        ptr_vector<ineq>         m_to_compile;  // inequalities to compile.
        unsigned                 m_conflict_frequency;
        bool                     m_learn_complements;

        // internalize_atom:
        literal compile_arg(expr* arg);
        void add_watch(ineq& c, unsigned index);
        void del_watch(watch_list& watch, unsigned index, ineq& c, unsigned ineq_index);
        bool assign_watch(bool_var v, bool is_true, watch_list& watch, unsigned index);
        void assign_ineq(ineq& c, bool is_true);

        std::ostream& display(std::ostream& out, ineq const& c, bool values = false) const;
        virtual void display(std::ostream& out) const;
        void display_resolved_lemma(std::ostream& out) const;

        void add_clause(ineq& c, literal_vector const& lits);
        void add_assign(ineq& c, literal_vector const& lits, literal l);
        literal_vector& get_lits();

        literal_vector& get_helpful_literals(ineq& c, bool negate);
        literal_vector& get_unhelpful_literals(ineq& c, bool negate);

        //
        // Utilities to compile cardinality 
        // constraints into a sorting network.
        //
        void compile_ineq(ineq& c);
        void inc_propagations(ineq& c);
        unsigned get_compilation_threshold(ineq& c);

        //
        // Conflict resolution, cutting plane derivation.
        // 
        unsigned          m_num_marks;
        unsigned          m_conflict_lvl;
        ineq              m_lemma;
        literal_vector    m_ineq_literals;
        svector<bool_var> m_marked;

        // bool_var |-> index into m_lemma
        unsigned_vector   m_conseq_index;
        static const unsigned null_index = UINT_MAX;
        bool is_marked(bool_var v) const;
        void set_mark(bool_var v, unsigned idx);
        void unset_mark(bool_var v);
        void unset_marks();

        bool resolve_conflict(ineq& c);
        void process_antecedent(literal l, numeral coeff);
        void process_ineq(ineq& c, literal conseq, numeral coeff);
        void remove_from_lemma(ineq& c, unsigned idx);
        bool is_proof_justification(justification const& j) const;

        void hoist_maximal_values();

        void validate_final_check();
        void validate_final_check(ineq& c);
        void validate_assign(ineq const& c, literal_vector const& lits, literal l) const;
        void validate_watch(ineq const& c) const;
    public:
        theory_pb(ast_manager& m);
        
        virtual ~theory_pb();

        virtual theory * mk_fresh(context * new_ctx);
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term) { UNREACHABLE(); return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { }
        virtual bool use_diseqs() const { return false; }
        virtual bool build_models() const { return false; }
        virtual final_check_status final_check_eh();
        virtual void reset_eh();
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void init_search_eh();
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void restart_eh();
        virtual void collect_statistics(::statistics & st) const;
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        virtual void init_model(model_generator & m);        

        void set_conflict_frequency(unsigned f) { m_conflict_frequency = f; }
        void set_learn_complements(bool l) { m_learn_complements = l; }
    };
};
