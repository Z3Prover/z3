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

namespace smt {
    class theory_card : public theory {

        typedef svector<std::pair<bool_var, int> > arg_t;

        struct stats {
            unsigned m_num_axioms;
            unsigned m_num_predicates;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        struct card {
            int      m_k;
            bool_var m_bv;
            int      m_current_min;
            int      m_current_max;
            int      m_abs_min;
            int      m_abs_max;
            arg_t    m_args;
            card(bool_var bv, unsigned k):
                m_k(k), m_bv(bv)
            {}
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

        void add_clause(literal_vector const& lits);
        literal_vector& get_lits();

        int find_inc(bool_var bv, svector<std::pair<bool_var, int> >const& vars);
        void theory_card::propagate_assignment(card* c);
        int theory_card::accumulate_max(literal_vector& lits, card* c);
        int theory_card::accumulate_min(literal_vector& lits, card* c);
        lbool theory_card::dec_max(int inc, lbool val);
        lbool theory_card::inc_min(int inc, lbool val);
        void theory_card::assign_use(bool_var v, bool is_true, card* c);
        void theory_card::update_min_max(bool_var v, bool is_true, card* c);
        
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
