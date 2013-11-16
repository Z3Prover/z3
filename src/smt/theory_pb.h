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
#include "card_decl_plugin.h"
#include "smt_clause.h"

namespace smt {
    class theory_pb : public theory {

        struct sort_expr;
        typedef svector<std::pair<literal, int> > arg_t;

        struct stats {
            unsigned m_num_axioms;
            unsigned m_num_propagations;
            unsigned m_num_predicates;
            unsigned m_num_compiles;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };


        struct ineq {
            app*            m_app;
            literal         m_lit;      // literal repesenting predicate
            arg_t           m_args;     // encode args[0]*coeffs[0]+...+args[n-1]*coeffs[n-1] >= m_k;
            int             m_k;        // invariants: m_k > 0, coeffs[i] > 0
            
            // Watch the first few positions until the sum satisfies:
            // sum coeffs[i] >= m_lower + max_coeff
            
            int             m_max_coeff;    // maximal coefficient.
            unsigned        m_watch_sz;     // number of literals being watched.
            unsigned        m_num_propagations;
            unsigned        m_compilation_threshold;
            bool            m_compiled;
            
            ineq(app* a, literal l):
                m_app(a),
                m_lit(l),                
                m_num_propagations(0),
                m_compilation_threshold(UINT_MAX),
                m_compiled(false)
            {}
        };

        typedef ptr_vector<ineq> watch_list;
        
        u_map<watch_list*>       m_watch;       // per literal.
        u_map<ineq*>             m_ineqs;       // per inequality.
        unsigned_vector          m_ineqs_trail;
        unsigned_vector          m_ineqs_lim;
        literal_vector           m_literals;    // temporary vector
        card_util                m_util;
        stats                    m_stats;

        // internalize_atom:
        lbool normalize_ineq(arg_t& args, int& k);
        literal compile_arg(expr* arg);
        void add_watch(literal l, ineq* c);
        void assign_watch(bool_var v, bool is_true, watch_list& watch, unsigned index);

        std::ostream& display(std::ostream& out, ineq& c) const;

        void add_clause(ineq& c, literal_vector const& lits);
        void add_assign(ineq& c, literal_vector const& lits, literal l);
        literal_vector& get_lits();

        //
        // Utilities to compile cardinality 
        // constraints into a sorting network.
        //
        void compile_ineq(ineq& c);
        bool should_compile(ineq& c);
        unsigned get_compilation_threshold(ineq& c);
    public:
        theory_pb(ast_manager& m);
        
        virtual ~theory_pb();

        virtual theory * mk_fresh(context * new_ctx);
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term) { UNREACHABLE(); return false; }
        virtual void new_eq_eh(theory_var v1, theory_var v2) { }
        virtual void new_diseq_eh(theory_var v1, theory_var v2) { }
        virtual bool use_diseqs() const { return false; }
        virtual bool build_models() const { return false; }
        virtual final_check_status final_check_eh() { return FC_DONE; }

        virtual void reset_eh();
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void init_search_eh();
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void collect_statistics(::statistics & st) const;

    };
};
