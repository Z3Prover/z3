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
        struct card {
            unsigned m_k;
            bool_var m_bv;
            unsigned m_t;
            unsigned m_f;
            svector<bool_var> m_args;
            card(bool_var bv, unsigned k):
                m_k(k), m_bv(bv), m_t(0), m_f(0) 
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

        void add_watch(bool_var bv, card* c);

        void add_card(card* c) {
            m_cards.insert(c->m_bv, c);
            m_cards_trail.push_back(c->m_bv);
        }
        void add_clause(literal_vector const& lits);
        literal_vector& get_lits();
        
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

    };
};
