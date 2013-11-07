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
#include "ast_pp.h"

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

        if (ctx.b_internalized(atom)) {
            return false;
        }

        TRACE("card", tout << "internalize: " << mk_pp(atom, m) << "\n";);

        SASSERT(!ctx.b_internalized(atom));
        bool_var abv = ctx.mk_bool_var(atom);

        if (k >= atom->get_num_args()) {
            literal lit(abv);
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return true;
        }

        card* c = alloc(card, abv, k);
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            if (!ctx.b_internalized(arg)) {
                ctx.internalize(arg, false);
            }
            bool_var bv;
            bool has_bv = false;
            if (!m.is_not(arg) && ctx.b_internalized(arg)) {
                bv = ctx.get_bool_var(arg);
                
                if (null_theory_var == ctx.get_var_theory(bv)) {
                    ctx.set_var_theory(bv, get_id());
                    has_bv = true;
                }
                else if (get_id() == ctx.get_var_theory(bv)) {
                    has_bv = true;
                }
            }
            // pre-processing should better remove negations under cardinality.
            // assumes relevancy level = 2 or 0.
            if (!has_bv) {
                expr_ref tmp(m), fml(m);
                tmp = m.mk_fresh_const("card_proxy",m.mk_bool_sort());
                fml = m.mk_iff(tmp, arg);
                ctx.internalize(fml, false);
                SASSERT(ctx.b_internalized(tmp));
                bv = ctx.get_bool_var(tmp);
                SASSERT(null_theory_var == ctx.get_var_theory(bv));
                ctx.set_var_theory(bv, get_id());
                literal lit(ctx.get_bool_var(fml));
                ctx.mk_th_axiom(get_id(), 1, &lit);
                ctx.mark_as_relevant(tmp);
            }
            c->m_args.push_back(std::make_pair(bv,1));
        }
        add_card(c);
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

    void theory_card::add_card(card* c) {
        bool_var abv = c->m_bv;
        arg_t& args = c->m_args;

        // sort and coalesce arguments:
        std::sort(args.begin(), args.end());
        for (unsigned i = 0; i + 1 < args.size(); ++i) {
            if (args[i].first == args[i+1].first) {
                args[i].second += args[i+1].second;
                for (unsigned j = i+1; j + 1 < args.size(); ++j) {
                    args[j] = args[j+1];
                }
                args.resize(args.size()-1);
            }
            if (args[i].second == 0) {
                for (unsigned j = i; j + 1 < args.size(); ++j) {
                    args[j] = args[j+1];
                }
                args.resize(args.size()-1);                
            }
        }
        // apply cutting plane reduction:
        if (!args.empty()) {
            unsigned g = abs(args[0].second);
            for (unsigned i = 1; g > 1 && i < args.size(); ++i) {
                g = gcd(g, args[i].second);
            }
            if (g > 1) {
                unsigned k = c->m_k;
                if (k >= 0) {
                    c->m_k /= g;
                }
                else {
                    // watch out for truncation semantcs for k < 0!
                    k = abs(k);
                    k += (k % g);
                    k /= g;
                    k = -k;
                }
                for (unsigned i = 0; i < args.size(); ++i) {
                    args[i].second /= g;
                }                
            }
        }        
        
        int min = 0, max = 0;
        for (unsigned i = 0; i < args.size(); ++i) {            
            // update min and max:
            int inc = args[i].second;
            if (inc > 0) {
                max += inc;
            }
            else {
                SASSERT(inc < 0);
                min += inc;
            }
            // add watch literals:
            add_watch(args[i].first, c);
        }
        c->m_current_min = c->m_abs_min = min;
        c->m_current_max = c->m_abs_max = max;
        m_cards.insert(abv, c);
        m_cards_trail.push_back(abv);
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

    void theory_card::update_min_max(bool_var v, bool is_true, card* c) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        arg_t const& args = c->m_args;
        int inc = find_inc(v, args);
        int& min = c->m_current_min;
        int& max = c->m_current_max;
        int  k = c->m_k;
        // inc > 0 &  is_true -> min += inc
        // inc < 0 &  is_true -> max += inc
        // inc > 0 & !is_true -> max -= inc
        // inc < 0 & !is_true -> min -= inc
        
        if (inc > 0 && is_true) {
            ctx.push_trail(value_trail<context, int>(min));
            min += inc;
        }
        else if (inc < 0 && is_true) {
            ctx.push_trail(value_trail<context, int>(max));
            max += inc;
        }
        else if (inc > 0 && !is_true) {
            ctx.push_trail(value_trail<context, int>(max));
            max -= inc;
        }
        else {
            ctx.push_trail(value_trail<context, int>(min));
            min -= inc;
        }
        // invariant min <= max
        SASSERT(min <= max);
    }

    void theory_card::assign_use(bool_var v, bool is_true, card* c) {
        update_min_max(v, is_true, c);        
        propagate_assignment(c);
    }

    lbool theory_card::inc_min(int inc, lbool val) {
        if (inc > 0) {
            return val;
        }
        else if (inc < 0) {
            return ~val;
        }
        else {
            return l_undef;
        }
    }

    lbool theory_card::dec_max(int inc, lbool val) {
        if (inc > 0) {
            return ~val;
        }
        else if (inc < 0) {
            return val;
        }
        else {
            return l_undef;
        }
    }

    int theory_card::accumulate_min(literal_vector& lits, card* c) {
        context& ctx = get_context();
        int k = c->m_k;
        arg_t const& args = c->m_args;
        int curr_min = c->m_abs_min;
        for (unsigned i = 0; i < args.size() && curr_min <= k; ++i) {
            bool_var bv = args[i].first;
            int inc = args[i].second;
            lbool val = ctx.get_assignment(bv);
            if (inc_min(inc, val) == l_true) {
                curr_min += abs(inc);
                lits.push_back(literal(bv, val != l_true));
            }
        }
        return curr_min;
    }    

    int theory_card::accumulate_max(literal_vector& lits, card* c) {
        context& ctx = get_context();
        arg_t const& args = c->m_args;
        int k = c->m_k;
        int curr_max = c->m_abs_max;
        for (unsigned i = 0; i < args.size() && k < curr_max; ++i) {
            bool_var bv = args[i].first;
            int inc = args[i].second;
            lbool val = ctx.get_assignment(bv);
            if (dec_max(inc, val) == l_true) {
                curr_max -= abs(inc);
                lits.push_back(literal(bv, val == l_true));
            }
        }
        return curr_max;
    }

    void theory_card::propagate_assignment(card* c) {
        context& ctx = get_context();
        arg_t const& args = c->m_args;
        bool_var abv = c->m_bv;
        int min = c->m_current_min;
        int max = c->m_current_max;
        int k = c->m_k;

        //
        // if min >  k && abv != l_false -> force abv false
        // if max <= k && abv != l_true  -> force abv true
        // if min == k && abv == l_true  -> force positive unassigned literals false
        // if max == k + 1 && abv == l_false -> force negative unassigned literals false
        //
        lbool aval = ctx.get_assignment(abv);
        if (min > k && aval != l_false) {
            literal_vector& lits = get_lits();
            lits.push_back(~literal(abv));
            int curr_min = accumulate_min(lits, c);
            SASSERT(curr_min > k);
            add_clause(lits);                    
        }
        else if (max <= k && aval != l_true) {
            literal_vector& lits = get_lits();
            lits.push_back(literal(abv));
            int curr_max = accumulate_max(lits, c);
            SASSERT(curr_max <= k);
            add_clause(lits);                    
        }                
        else if (min == k && aval == l_true) {
            literal_vector& lits = get_lits();
            lits.push_back(~literal(abv));
            int curr_min = accumulate_min(lits, c);
            if (curr_min > k) {
                add_clause(lits);
            }
            else {
                SASSERT(curr_min == k);
                for (unsigned i = 0; i < args.size(); ++i) {
                    bool_var bv = args[i].first;
                    int inc = args[i].second;
                    if (inc_min(inc, ctx.get_assignment(bv)) == l_undef) {
                        lits.push_back(literal(bv, inc > 0)); // avoid incrementing min.
                        add_clause(lits);
                        lits.pop_back();                        
                    }
                }
            }
        }
        else if (max == k + 1 && aval == l_false) {
            literal_vector& lits = get_lits();
            lits.push_back(literal(abv));
            int curr_max = accumulate_max(lits, c);
            if (curr_max <= k) {
                add_clause(lits);
            }
            else if (curr_max == k + 1) {
                for (unsigned i = 0; i < args.size(); ++i) {
                    bool_var bv = args[i].first;
                    int inc = args[i].second;
                    if (dec_max(inc, ctx.get_assignment(bv)) == l_undef) {
                        lits.push_back(literal(bv, inc < 0)); // avoid decrementing max.
                        add_clause(lits);
                        lits.pop_back();                        
                    }
                }
            }
        }
    }

    void theory_card::assign_eh(bool_var v, bool is_true) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        ptr_vector<card>* cards = 0;
        card* c = 0;
        TRACE("card", tout << "assign: " << mk_pp(ctx.bool_var2expr(v), m) << " <- " << is_true << "\n";);

        if (m_watch.find(v, cards)) {
            for (unsigned i = 0; i < cards->size(); ++i) {
                assign_use(v, is_true, (*cards)[i]);
            }
        }
        if (m_cards.find(v, c)) {
            propagate_assignment(c);
        }
    }

    int theory_card::find_inc(bool_var bv, svector<std::pair<bool_var, int> >const& vars) {
        unsigned mid = vars.size()/2;
        unsigned lo = 0;
        unsigned hi = vars.size()-1;
        while (lo < hi) {            
            if (vars[mid].first == bv) {
                return vars[mid].second;
            }
            else if (vars[mid].first < bv) {
                lo = mid;
                mid += (hi-mid)/2;
            }
            else {
                hi = mid;
                mid = (mid-lo)/2 + lo;
            }
        }
        SASSERT(vars[mid].first == bv);
        return vars[mid].second;
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
        TRACE("card", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    }
}
