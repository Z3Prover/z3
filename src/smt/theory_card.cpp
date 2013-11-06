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
        bool_var bv = ctx.mk_bool_var(atom);

        if (k >= atom->get_num_args()) {
            literal lit(bv);
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return true;
        }

        card* c = alloc(card, bv, k);
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            if (!ctx.b_internalized(arg)) {
                ctx.internalize(arg, false);
            }
            
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
            c->m_args.push_back(bv);
            if (0 < k) {
                add_watch(bv, c);
            }
        }
        if (0 < k) {
            add_card(c);
        }
        else {
            // bv <=> (and (not bv1) ... (not bv_n))
            literal_vector& lits = get_lits();
            lits.push_back(literal(bv));
            for (unsigned i = 0; i < c->m_args.size(); ++i) {
                ctx.mk_th_axiom(get_id(), ~literal(bv), ~literal(c->m_args[i]));
                lits.push_back(literal(c->m_args[i]));
            }
            ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
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
        ast_manager& m = get_manager();
        ptr_vector<card>* cards = 0;
        card* c = 0;
        TRACE("card", tout << "assign: " << mk_pp(ctx.bool_var2expr(v), m) << " <- " << is_true << "\n";);

        if (m_watch.find(v, cards)) {
            for (unsigned i = 0; i < cards->size(); ++i) {
                c = (*cards)[i];
                svector<bool_var> const& args = c->m_args;
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
                        lits.push_back(~literal(c->m_bv));
                        for (unsigned i = 0; i < args.size() && lits.size() < k + 1; ++i) {
                            if (ctx.get_assignment(args[i]) == l_true) {
                                lits.push_back(~literal(args[i]));
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
                else if (!is_true && c->m_k >= args.size() - c->m_f - 1) {
                    // forced true
                    switch (ctx.get_assignment(c->m_bv)) {
                    case l_false:
                    case l_undef: {
                        unsigned deficit = args.size() - c->m_k;
                        literal_vector& lits = get_lits();
                        lits.push_back(literal(c->m_bv));
                        for (unsigned i = 0; i < args.size() && lits.size() <= deficit; ++i) {
                            if (ctx.get_assignment(args[i]) == l_false) {
                                lits.push_back(literal(args[i]));
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
            svector<bool_var> const& args = c->m_args;
            SASSERT(args.size() >= c->m_f + c->m_t);
            bool_var bv;

            TRACE("card", tout << " t:" << is_true << " k:" << c->m_k << " t:" << c->m_t << " f:" << c->m_f << "\n";);

            // at most k
            // propagate false to children that are not yet assigned.
            // v & t1 & ... & tk => ~l_j
            if (is_true && c->m_k <= c->m_t) {

                literal_vector& lits = get_lits();
                lits.push_back(literal(v));
                bool done = false;
                for (unsigned i = 0; !done && i < args.size(); ++i) {                        
                    bv = args[i];
                    if (ctx.get_assignment(bv) == l_true) {
                        lits.push_back(literal(bv));
                    }
                    if (lits.size() > c->m_k + 1) {
                        add_clause(lits);
                        done = true;
                    }
                }
                SASSERT(done || lits.size() == c->m_k + 1);
                for (unsigned i = 0; !done && i < args.size(); ++i) {                        
                    bv = args[i];
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
            if (!is_true && args.size() <= 1 + c->m_f + c->m_k) {
                literal_vector& lits = get_lits();
                lits.push_back(literal(v));
                bool done = false;
                for (unsigned i = 0; !done && i < args.size(); ++i) {                        
                    bv = args[i];
                    if (ctx.get_assignment(bv) == l_false) {
                        lits.push_back(literal(bv));
                    }
                    if (lits.size() > c->m_k + 1) {
                        add_clause(lits);
                        done = true;
                    }
                }
                for (unsigned i = 0; !done && i < args.size(); ++i) {                        
                    bv = args[i];
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
        TRACE("card", ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    }

}

#if 0

class sorting_network {
    ast_manager&     m;
    expr_ref_vector  m_es;
    expr_ref_vector* m_current;
    expr_ref_vector* m_next;

    void exchange(unsigned i, unsigned j, expr_ref_vector& es) {
        SASSERT(i <= j);
        if (i == j) {
            return;
        }
        expr* ei = es[i].get();
        expr* ej = es[j].get();
        es[i] = m.mk_ite(mk_le(ei,ej), ei, ej);
        es[j] = m.mk_ite(mk_le(ej,ei), ei, ej);
    }

    void sort(unsigned k) {
        if (k == 2) {
            for (unsigned i = 0; i < m_es.size()/2; ++i) {
                exchange(current(2*i), current(2*i+1), m_es);
                next(2*i) = current(2*i);
                next(2*i+1) = current(2*i+1);
            }
            std::swap(m_current, m_next);
        }
        else {
            
            for (unsigned i = 0; i < m_es.size()/k; ++i) {
                for (unsigned j = 0; j < k / 2; ++j) {
                    next((k * i) + j) = current((k * i) + (2 * j));
                    next((k * i) + (k / 2) + j) = current((k * i) + (2 * j) + 1);
                }
            }
            
            std::swap(m_current, m_next);
            sort(k / 2);
            for (unsigned i = 0; i < m_es.size() / k; ++i) {
                for (unsigned j = 0; j < k / 2; ++j) {
                    next((k * i) + (2 * j)) = current((k * i) + j);
                    next((k * i) + (2 * j) + 1) = current((k * i) + (k / 2) + j);
                }
                
                for (unsigned j = 0; j < (k / 2) - 1; ++j) {
                    exchange(next((k * i) + (2 * j) + 1), next((k * i) + (2 * (j + 1))));
                }
            }
            std::swap(m_current, m_next);
        }
    }

    expr_ref_vector merge(expr_ref_vector const& l1, expr_ref_vector& l2) {
        if (l1.empty()) {
            return l2;
        }
        if (l2.empty()) {
            return l1;
        }
        expr_ref_vector result(m);
        if (l1.size() == 1 && l2.size() == 1) {
            result.push_back(l1[0]);
            result.push_back(l2[0]);
            exchange(0, 1, result);
            return result;
        }
        unsigned l1o = l1.size()/2;
        unsigned l2o = l2.size()/2;
        unsigned l1e = (l1.size() % 2 == 1) ? l1o + 1 : l1o;
        unsigned l2e = (l2.size() % 2 == 1) ? l2o + 1 : l2o;
        expr_ref_vector evenl1(m, l1e);
        expr_ref_vector oddl1(m, l1o);
        expr_ref_vector evenl2(m, l2e);
        expr_ref_vector oddl2(m, l2o);
        for (unsigned i = 0; i < l1.size(); ++i) {
            if (i % 2 == 0) {
                evenl1[i/2] = l1[i];
            }
            else {
                oddl1[i/2] = l1[i];
            }
        }
        for (unsigned i = 0; i < l2.size(); ++i) {
            if (i % 2 == 0) {
                evenl2[i/2] = l2[i];
            }
            else {
                oddl2[i/2] = l2[i];
            }
        }
        expr_ref_vector even = merge(evenl1, evenl2);
        expr_ref_vector odd = merge(oddl1, oddl2);

        result.resize(l1.size() + l2.size());
        for (unsigned i = 0; i < result.size(); ++i) {
            if (i % 2 == 0) {
                result[i] = even[i/2].get();
                if (i > 0) {
                    exchange(i - 1, i, result);
                }
            }
            else {
                if (i /2 < odd.size()) {
                    result[i] = odd[i/2].get();
                }
                else {
                    result[i] = even[(i/2)+1].get();
                }
            }
        }
        return result;
    }

public:
    sorting_network(ast_manager& m):
        m(m),
        m_es(m),
        m_current(0),
        m_next(0)
    {}

    expr_ref_vector operator()(expr_ref_vector const& inputs) {
        if (inputs.size() <= 1) {
            return inputs;
        }
        m_es.reset();
        m_es.append(inputs);
        while (!is_power_of2(m_es.size())) {
            m_es.push_back(m.mk_false());
        }
        m_es.reverse();
        for (unsigned i = 0; i < m_es.size(); ++i) {
            current(i) = i;
        }
        unsigned k = 2;
        while (k <= m_es.size()) {
            sort(k);
            // TBD
            k *= 2;
        }
    }
};

Sorting networks used in Formula:

        public SortingNetwork(SymbolicState owner, Term[] inputs, Sort sortingDomain)
        {
            Contract.Requires(owner != null && inputs != null && sortingDomain != null);
            Contract.Requires(inputs.Length > 0);

            Owner = owner;
            Size = (int)Math.Pow(2, (int)Math.Ceiling(Math.Log(inputs.Length, 2)));

            if (Size == 1)
            {
                elements = new Term[1];
                elements[0] = inputs[0];
            }
            else if (Size > 1)
            {
                var defaultElement = owner.Context.MkNumeral(0, sortingDomain);

                current = new int[Size];
                next = new int[Size];
                elements = new Term[Size];
                for (int i = 0; i < Size; ++i)
                {
                    current[i] = i;
                    elements[i] = (i < Size - inputs.Length) ? defaultElement : inputs[i - (Size - inputs.Length)];
                }

                int k = 2;
                Term xi;
                while (k <= Size)
                {
                    Sort(k);

                    for (int i = 0; i < Size; ++i)
                    {
                        xi = owner.Context.MkFreshConst("x", sortingDomain);
                        owner.Context.AssertCnstr(owner.Context.MkEq(xi, elements[i]));
                        elements[i] = xi;
                    }

                    for (int i = 0; i < elements.Length / k; ++i)
                    {
                        for (int j = 0; j < k - 1; ++j)
                        {
                            owner.Context.AssertCnstr(owner.Context.MkBvUle(elements[(k * i) + j], elements[(k * i) + j + 1]));
                        }
                    }

                    k *= 2;
                }
            }
        }


}


#endif 
