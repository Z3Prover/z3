/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_card.h

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
    class theory_card : public theory {

        struct sort_expr;
        typedef svector<std::pair<bool_var, int> > arg_t;

        struct stats {
            unsigned m_num_axioms;
            unsigned m_num_predicates;
            unsigned m_num_compiles;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };


        struct card {
            app*     m_app;
            int      m_k;
            bool_var m_bv;
            int      m_current_min;
            int      m_current_max;
            int      m_abs_min;
            int      m_abs_max;
            arg_t    m_args;
            unsigned m_num_propagations;
            unsigned m_compilation_threshold;
            bool     m_compiled;
            obj_map<expr, expr*> m_replay;
            expr_ref_vector m_trail;
            card(ast_manager& m, app* a, bool_var bv, int k, unsigned threshold):
                m_app(a), m_k(k), m_bv(bv), 
                m_num_propagations(0), m_compilation_threshold(threshold), m_compiled(false),
                m_trail(m)
            {
            }
        };

        u_map<ptr_vector<card>*> m_watch;  // use-list of literals.
        u_map<card*>             m_cards;  // bool_var |-> card
        unsigned_vector          m_cards_trail;
        unsigned_vector          m_cards_lim;
        unsigned_vector          m_watch_trail;
        unsigned_vector          m_watch_lim;
        literal_vector           m_literals;
        card_util                m_util;
        stats                    m_stats;

        void add_watch(bool_var bv, card* c);
        void add_card(card* c);

        void add_clause(card& c, literal_vector const& lits);
        literal_vector& get_lits();

        int   find_inc(bool_var bv, svector<std::pair<bool_var, int> >const& vars);
        void  propagate_assignment(card& c);
        int   accumulate_max(literal_vector& lits, card& c);
        int   accumulate_min(literal_vector& lits, card& c);
        lbool dec_max(int inc, lbool val);
        lbool inc_min(int inc, lbool val);
        void  assign_use(bool_var v, bool is_true, card& c);
        void  update_min_max(bool_var v, bool is_true, card& c);

        void compile_at_most(card& c);
        expr_ref nnf(expr* e);
        bool     should_compile(card& c);
        unsigned get_compilation_threshold(app* atom);
    public:
        theory_card(ast_manager& m);
        
        virtual ~theory_card();

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
