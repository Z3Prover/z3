/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_card.cpp

Abstract:

    Cardinality theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:

   - count number of clauses per cardinality constraint.
   - when number of conflicts exceeds n^2 or n*log(n), then create a sorting circuit.
     where n is the arity of the cardinality constraint.
   - extra: do clauses get re-created? keep track of gc status of created clauses.

--*/

#include "theory_card.h"
#include "smt_context.h"

namespace smt {
    
    theory_card::theory_card(ast_manager& m):
        theory(m.mk_family_id("card")),
        m_util(m)
    {}

    theory_card::~theory_card() {
        reset_eh();
    }

    theory * theory_card::mk_fresh(context * new_ctx) { 
        return alloc(theory_card, new_ctx->get_manager()); 
    }

    bool theory_card::internalize_atom(app * atom, bool gate_ctx) {
        context& ctx   = get_context();
        ast_manager& m = get_manager();
        unsigned num_args = atom->get_num_args();
        SASSERT(m_util.is_at_most_k(atom));
        unsigned k = m_util.get_k(atom);
        bool_var bv;
        if (ctx.b_internalized(atom)) {
            return false;
        }
        SASSERT(!ctx.b_internalized(atom));
        bv = ctx.mk_bool_var(atom);
        card* c = alloc(card, atom, bv, k);
        add_card(c);
        //
        // TBD take repeated bv into account.
        // base case: throw exception.
        // refinement: adjust argument list and k for non-repeated values.
        //
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            if (!ctx.b_internalized(arg)) {
                bv = ctx.mk_bool_var(arg);
            }
            else {
                bv = ctx.get_bool_var(arg);
            }
            ctx.set_var_theory(bv, get_id());
            add_watch(bv, c);
        }
        return true;
    }

    void theory_card::add_watch(bool_var bv, card* c) {
        ptr_vector<card>* cards;
        if (!m_watch.find(bv, cards)) {
            cards = alloc(ptr_vector<card>);
            m_watch.insert(bv, cards);
        }
        cards->push_back(c);
        m_watch_trail.push_back(bv);
    }
    
    
    void theory_card::reset_eh() {
        
        // m_watch;
        u_map<ptr_vector<card>*>::iterator it = m_watch.begin(), end = m_watch.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        u_map<card*>::iterator itc = m_cards.begin(), endc = m_cards.end();
        for (; itc != endc; ++itc) {
            dealloc(itc->m_value);
        }
        m_watch.reset();
        m_cards.reset();
        m_cards_trail.reset();
        m_cards_lim.reset();
        m_watch_trail.reset();
        m_watch_lim.reset();
    }

    void theory_card::assign_eh(bool_var v, bool is_true) {
        context& ctx = get_context();
        ptr_vector<card>* cards = 0;
        card* c = 0;
        if (m_watch.find(v, cards)) {
            for (unsigned i = 0; i < cards->size(); ++i) {
                c = (*cards)[i];
                app* atm = c->m_atom;
                //
                // is_true  && m_t + 1 > k          -> force false
                // !is_true && m_f + 1 >= arity - k -> force true
                //
                if (is_true && c->m_t >= c->m_k) {
                    unsigned k = c->m_k;
                    // force false
                    switch (ctx.get_assignment(c->m_bv)) {
                    case l_true:
                    case l_undef: {
                        literal_vector& lits = get_lits();
                        lits.push_back(literal(v));
                        for (unsigned i = 0; i < atm->get_num_args() && lits.size() <= k + 1; ++i) {
                            expr* arg = atm->get_arg(i);
                            if (ctx.get_assignment(arg) == l_true) {
                                lits.push_back(literal(ctx.get_bool_var(arg)));
                            }
                        }
                        SASSERT(lits.size() == k + 1);
                        add_clause(lits);
                        break;
                    }
                    default:
                        break;
                    }
                }
                else if (!is_true && c->m_k >= atm->get_num_args() - c->m_f) {
                    // forced true
                    switch (ctx.get_assignment(c->m_bv)) {
                    case l_false:
                    case l_undef: {
                        literal_vector& lits = get_lits();
                        lits.push_back(~literal(v));
                        for (unsigned i = 0; i < atm->get_num_args(); ++i) {
                            expr* arg = atm->get_arg(i);
                            if (ctx.get_assignment(arg) == l_false) {
                                lits.push_back(~literal(ctx.get_bool_var(arg)));
                            }
                        }
                        add_clause(lits);
                        break;
                    }
                    default:
                        break;
                    }
                }
                else if (is_true) {
                    ctx.push_trail(value_trail<context, unsigned>(c->m_t));
                    c->m_t++;
                }
                else {
                    ctx.push_trail(value_trail<context, unsigned>(c->m_f));
                    c->m_f++;
                }
            }
        }
        if (m_cards.find(v, c)) {
            app* atm = to_app(ctx.bool_var2expr(v));
            SASSERT(atm->get_num_args() >= c->m_f + c->m_t);
            bool_var bv;

            // at most k
            // propagate false to children that are not yet assigned.
            // v & t1 & ... & tk => ~l_j
            if (is_true && c->m_k <= c->m_t) {

                literal_vector& lits = get_lits();
                lits.push_back(literal(v));
                bool done = false;
                for (unsigned i = 0; !done && i < atm->get_num_args(); ++i) {                        
                    bv = ctx.get_bool_var(atm->get_arg(i));
                    if (ctx.get_assignment(bv) == l_true) {
                        lits.push_back(literal(bv));
                    }
                    if (lits.size() > c->m_k + 1) {
                        add_clause(lits);
                        done = true;
                    }
                }
                SASSERT(done || lits.size() == c->m_k + 1);
                for (unsigned i = 0; !done && i < atm->get_num_args(); ++i) {                        
                    bv = ctx.get_bool_var(atm->get_arg(i));
                    if (ctx.get_assignment(bv) == l_undef) {
                        lits.push_back(literal(bv));
                        add_clause(lits);
                        lits.pop_back();
                    }
                }
            }
            // at least k+1:
            // !v & !f1 & .. & !f_m => l_j
            // for m + k + 1 = arity()
            if (!is_true && atm->get_num_args() == 1 + c->m_f + c->m_k) {
                literal_vector& lits = get_lits();
                lits.push_back(~literal(v));
                bool done = false;
                for (unsigned i = 0; !done && i < atm->get_num_args(); ++i) {                        
                    bv = ctx.get_bool_var(atm->get_arg(i));
                    if (ctx.get_assignment(bv) == l_false) {
                        lits.push_back(~literal(bv));
                    }
                    if (lits.size() > c->m_k + 1) {
                        add_clause(lits);
                        done = true;
                    }
                }
                SASSERT(done || lits.size() == c->m_k + 1);
                for (unsigned i = 0; !done && i < atm->get_num_args(); ++i) {                        
                    bv = ctx.get_bool_var(atm->get_arg(i));
                    if (ctx.get_assignment(bv) != l_false) {
                        lits.push_back(~literal(bv));
                        add_clause(lits);
                        lits.pop_back();
                    }
                }
            }
        }
    }

    void theory_card::init_search_eh() {
        
    }

    void theory_card::push_scope_eh() {
        m_watch_lim.push_back(m_watch_trail.size());
        m_cards_lim.push_back(m_cards_trail.size());
    }

    void theory_card::pop_scope_eh(unsigned num_scopes) {
        unsigned sz = m_watch_lim[m_watch_lim.size()-num_scopes];
        for (unsigned i = m_watch_trail.size(); i > sz; ) {
            --i;
            ptr_vector<card>* cards = 0;
            VERIFY(m_watch.find(m_watch_trail[i], cards));
            SASSERT(cards && !cards->empty());
            cards->pop_back();
        }
        m_watch_lim.resize(m_watch_lim.size()-num_scopes);
        sz = m_cards_lim[m_cards_lim.size()-num_scopes];
        for (unsigned i = m_cards_trail.size(); i > sz; ) {
            --i;
            SASSERT(m_cards.contains(m_cards_trail[i]));
            m_cards.remove(m_cards_trail[i]);
        }
        m_cards_lim.resize(m_cards_lim.size()-num_scopes);
    }


    literal_vector& theory_card::get_lits() {
        m_literals.reset();
        return m_literals;
    }

    void theory_card::add_clause(literal_vector const& lits) {
        context& ctx = get_context();
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    }

}
