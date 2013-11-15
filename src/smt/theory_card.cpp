/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_card.cpp

Abstract:

    Cardinality theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:

   - Uses cutting plane simplification on 'k' for repeated literals.
     In other words, if the gcd of the multiplicity of literals in c3
     is g, then divide through by g and truncate k.
   
     Example:
        ((_ at-most 3) x1 x1 x2 x2) == ((_ at-most 1) x1 x2)

   - When number of conflicts exceeds n*log(n), 
     then create a sorting circuit.
     where n is the arity of the cardinality constraint.

   - TBD: add conflict resolution
     The idea is that if cardinality constraints c1, c2
     are repeatedly asserted together, then 
     resolve them into combined cardinality constraint c3
     
     c1 /\ c2 -> c3
    
     That is, during a propagation, assignment or conflict resolution
     step track cutting-planes.

  - TBD: profile overhead of (re)creating sorting circuits.
    Possibly delay creating them until restart.

--*/

#include "theory_card.h"
#include "smt_context.h"
#include "ast_pp.h"
#include "sorting_network.h"

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
        SASSERT(m_util.is_at_most_k(atom) || m_util.is_le(atom));
        int k = m_util.get_k(atom);


        if (ctx.b_internalized(atom)) {
            return false;
        }

        m_stats.m_num_predicates++;

        TRACE("card", tout << "internalize: " << mk_pp(atom, m) << "\n";);

        SASSERT(!ctx.b_internalized(atom));
        bool_var abv = ctx.mk_bool_var(atom);

        card* c = alloc(card, m, atom, abv, k, get_compilation_threshold(atom));
        
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
            int coeff = m_util.get_le_coeff(atom, i);
            c->m_args.push_back(std::make_pair(bv, coeff));
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

    static unsigned gcd(unsigned a, unsigned b) {
        if (a == 0) return b;
        if (b == 0) return a;
        while (a != b) {
            if (a == 0) {
                return b;
            }
            if (b == 0) {
                return a;
            }
            if (a < b) {
                b %= a;
            }
            else {
                a %= b;
            }
        }
        return a;
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
                g = gcd(g, abs(args[i].second));
            }
            if (g > 1) {
                int k = c->m_k;
                if (k >= 0) {
                    c->m_k /= g;
                }
                else {
                    // watch out for truncation semantcs for k < 0!
                    k = abs(k);
                    k += (k % g);
                    k /= g;
                    c->m_k = -k;
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

    void theory_card::collect_statistics(::statistics& st) const {
        st.update("pb axioms", m_stats.m_num_axioms);
        st.update("pb propagations", m_stats.m_num_propagations);
        st.update("pb predicates", m_stats.m_num_predicates);        
        st.update("pb compilations", m_stats.m_num_compiles);
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
        m_stats.reset();
    }

    void theory_card::update_min_max(bool_var v, bool is_true, card& c) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        arg_t const& args = c.m_args;
        int inc = find_inc(v, args);
        int& min = c.m_current_min;
        int& max = c.m_current_max;
        int  k = c.m_k;
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

    void theory_card::assign_use(bool_var v, bool is_true, card& c) {
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

    int theory_card::accumulate_min(literal_vector& lits, card& c) {
        context& ctx = get_context();
        int k = c.m_k;
        arg_t const& args = c.m_args;
        int curr_min = c.m_abs_min;
        for (unsigned i = 0; i < args.size() && curr_min <= k; ++i) {
            bool_var bv = args[i].first;
            int inc = args[i].second;
            lbool val = ctx.get_assignment(bv);
            if (inc_min(inc, val) == l_true) {
                curr_min += abs(inc);
                lits.push_back(literal(bv, val == l_true));
            }
        }
        return curr_min;
    }    

    int theory_card::get_max_delta(card& c) {
        if (m_util.is_at_most_k(c.m_app)) {
            return 1;
        }
        int max = 0;
        context& ctx = get_context();
        for (unsigned i = 0; i < c.m_args.size(); ++i) {
            if (c.m_args[i].second > max && ctx.get_assignment(c.m_args[i].first) == l_undef) {
                max = c.m_args[i].second;
            }
        }
        return max;
    }


    int theory_card::accumulate_max(literal_vector& lits, card& c) {
        context& ctx = get_context();
        arg_t const& args = c.m_args;
        int k = c.m_k;
        int curr_max = c.m_abs_max;
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

    void theory_card::propagate_assignment(card& c) {
        if (c.m_compiled) {
            return;
        }
        if (should_compile(c)) {
            compile_at_most(c);
            return;
        }
        context& ctx = get_context();
        ast_manager& m = get_manager();
        arg_t const& args = c.m_args; 
        bool_var abv = c.m_bv;
        int min = c.m_current_min;
        int max = c.m_current_max;
        int k = c.m_k;

        TRACE("card", 
              tout << mk_pp(c.m_app, m) << " min: " 
              << min << " max: " << max << "\n";);

        //
        // if min >  k && abv != l_false -> force abv false
        // if max <= k && abv != l_true  -> force abv true
        // if min == k && abv == l_true  -> force positive 
        //                                  unassigned literals false
        // if max == k + 1 && abv == l_false -> force negative 
        //                                  unassigned literals false
        //
        lbool aval = ctx.get_assignment(abv);
        if (min > k && aval != l_false) {
            literal_vector& lits = get_lits();
            int curr_min = accumulate_min(lits, c);
            SASSERT(curr_min > k);
            add_assign(c, lits, ~literal(abv));                    
        }
        else if (max <= k && aval != l_true) {
            literal_vector& lits = get_lits();
            int curr_max = accumulate_max(lits, c);
            SASSERT(curr_max <= k);
            add_assign(c, lits, literal(abv));
        }                
        else if (min <= k && k < min + get_max_delta(c) && aval == l_true) {
            literal_vector& lits = get_lits();
            lits.push_back(~literal(abv));
            int curr_min = accumulate_min(lits, c);
            if (curr_min > k) {
                add_clause(c, lits);
            }
            else {
                for (unsigned i = 0; i < args.size(); ++i) {
                    bool_var bv = args[i].first;
                    int inc = args[i].second;
                    if (curr_min + inc > k && inc_min(inc, ctx.get_assignment(bv)) == l_undef) {
                        add_assign(c, lits, literal(bv, inc > 0));
                    }
                }
            }
        }
        else if (max - get_max_delta(c) <= k && k < max && aval == l_false) {
            literal_vector& lits = get_lits();
            lits.push_back(literal(abv));
            int curr_max = accumulate_max(lits, c);
            if (curr_max <= k) {
                add_clause(c, lits);
            }
            else {
                for (unsigned i = 0; i < args.size(); ++i) {
                    bool_var bv = args[i].first;
                    int inc = args[i].second;
                    if (curr_max - abs(inc) <= k && dec_max(inc, ctx.get_assignment(bv)) == l_undef) {
                        add_assign(c, lits, literal(bv, inc < 0));
                    }
                }
            }
        }
#if 0
        else if (aval == l_true) {
            SASSERT(min < k);
            literal_vector& lits = get_lits();
            int curr_min = accumulate_min(lits, c);
            bool all_inc = curr_min == k;
            unsigned num_incs = 0;
            for (unsigned i = 0; all_inc && i < args.size(); ++i) {
                bool_var bv = args[i].first;
                int inc = args[i].second;
                if (inc_min(inc, ctx.get_assignment(bv)) == l_undef) {
                    all_inc = inc + min > k;
                    num_incs++;
                }
            }
            if (num_incs > 0) {
                std::cout << "missed T propgations " << num_incs << "\n";
            }
        }
        else if (aval == l_false) {
            literal_vector& lits = get_lits();
            lits.push_back(literal(abv));
            int curr_max = accumulate_max(lits, c);
            bool all_dec = curr_max > k;
            unsigned num_decs = 0;
            for (unsigned i = 0; all_dec && i < args.size(); ++i) {
                bool_var bv = args[i].first;
                int inc = args[i].second;
                if (dec_max(inc, ctx.get_assignment(bv)) == l_undef) {
                    all_dec = inc + max <= k;
                    num_decs++;
                }
            }
            if (num_decs > 0) {
                std::cout << "missed F propgations " << num_decs << "\n";
            }
        }
#endif
    }

    void theory_card::assign_eh(bool_var v, bool is_true) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        ptr_vector<card>* cards = 0;
        card* c = 0;
        TRACE("card", tout << "assign: " << mk_pp(ctx.bool_var2expr(v), m) << " <- " << is_true << "\n";);

        if (m_watch.find(v, cards)) {
            for (unsigned i = 0; i < cards->size(); ++i) {
                assign_use(v, is_true, *(*cards)[i]);
            }
        }
        if (m_cards.find(v, c)) {
            propagate_assignment(*c);
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
                mid += (hi-mid)/2 + 1;
            }
            else {
                hi = mid;
                mid = (mid-lo)/2 + lo;
            }
        }
        SASSERT(vars[mid].first == bv);
        return vars[mid].second;
    }

    struct theory_card::sort_expr {
        theory_card& th;
        context&     ctx;
        ast_manager& m;
        expr_ref_vector m_trail;
        sort_expr(theory_card& th):
            th(th), 
            ctx(th.get_context()), 
            m(th.get_manager()), 
            m_trail(m) {}
        typedef expr* T;
        typedef expr_ref_vector vector;

        T mk_ite(T a, T b, T c) { 
            if (m.is_true(a)) {
                return b;
            }
            if (m.is_false(a)) {
                return c;
            }
            if (b == c) {
                return b;
            }
            m_trail.push_back(m.mk_ite(a, b, c));
            return m_trail.back();
        }

        T mk_le(T a, T b) {
            return mk_ite(b, a, m.mk_true());
        }

        T mk_default() {
            return m.mk_false();
        }       

        literal internalize(card& ca, expr* e) {
            obj_map<expr, literal> cache;
            for (unsigned i = 0; i < ca.m_args.size(); ++i) {
                cache.insert(ca.m_app->get_arg(i), literal(ca.m_args[i].first));
            }
            cache.insert(m.mk_false(), false_literal);
            cache.insert(m.mk_true(),  true_literal);
            ptr_vector<expr> todo;
            todo.push_back(e);
            expr *a, *b, *c;
            literal la, lb, lc;
            while (!todo.empty()) {
                expr* t = todo.back();
                if (cache.contains(t)) {
                    todo.pop_back();
                    continue;
                }
                VERIFY(m.is_ite(t, a, b, c));
                unsigned sz = todo.size();
                if (!cache.find(a, la)) {
                    todo.push_back(a);
                }
                if (!cache.find(b, lb)) {
                    todo.push_back(b);
                }
                if (!cache.find(c, lc)) {
                    todo.push_back(c);
                }
                if (sz != todo.size()) {
                    continue;
                }
                todo.pop_back();
                cache.insert(t, mk_ite(ca, t, la, lb, lc));                
            }
            return cache.find(e);
        }

        literal mk_ite(card& ca, expr* t, literal a, literal b, literal c) {
            if (a == true_literal) {
                return b;
            }
            else if (a == false_literal) {
                return c;
            }
            else if (b == true_literal && c == false_literal) {
                return a;
            }
            else if (b == false_literal && c == true_literal) {
                return ~a;
            }
            else if (b == c) {
                return b;
            }
            else {                
                expr_ref p(m);
                expr* r;
                if (ca.m_replay.find(t, r)) {
                    p = r;
                }
                else {
                    p = m.mk_fresh_const("s", m.mk_bool_sort());
                    ca.m_replay.insert(t, p);
                    ca.m_trail.push_back(p);
                }
                literal l;
                if (ctx.b_internalized(p)) {
                    l = literal(ctx.get_bool_var(p));
                }
                else {
                    l = literal(ctx.mk_bool_var(p));
                }
                add_clause(~l, ~a,  b);
                add_clause(~l,  a,  c);
                add_clause(l,  ~a, ~b);
                add_clause(l,   a, ~c);
                TRACE("card", tout << p << " ::= (if ";
                      ctx.display_detailed_literal(tout, a);
                      ctx.display_detailed_literal(tout << " ", b);
                      ctx.display_detailed_literal(tout << " ", c);
                      tout << ")\n";);
                return l;
            }
        }


        // auxiliary clauses don't get garbage collected.
        void add_clause(literal a, literal b, literal c) {
            literal_vector& lits = th.get_lits();
            if (a != null_literal) lits.push_back(a); 
            if (b != null_literal) lits.push_back(b); 
            if (c != null_literal) lits.push_back(c);         
            justification* js = 0;
            TRACE("card",
                  ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
            ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX, 0);
        }            

        void add_clause(literal l1, literal l2) {
            add_clause(l1, l2, null_literal);
        }

    };

    unsigned theory_card::get_compilation_threshold(app* a) {
        if (!m_util.is_at_most_k(a)) { 
            return UINT_MAX;
        }
        unsigned num_args = a->get_num_args();
        unsigned log = 1, n = 1;
        while (n <= num_args) {
            ++log;
            n *= 2;
        }
        TRACE("card", tout << "threshold:" << (num_args*log) << "\n";);
        return num_args*log;
    }

    bool theory_card::should_compile(card& c) {
#if 1
        return false;
#else
        if (!m_util.is_at_most_k(c.m_app)) {
            return false;
        }
        return c.m_num_propagations >= c.m_compilation_threshold;
#endif
    }

    void theory_card::compile_at_most(card& c) {
        ++m_stats.m_num_compiles;
        ast_manager& m = get_manager();
        context& ctx = get_context();
        app* a = c.m_app;
        SASSERT(m_util.is_at_most_k(a)); 
        literal atmostk;
        int k = m_util.get_k(a);
        unsigned num_args = a->get_num_args();

        sort_expr se(*this);
        if (k >= static_cast<int>(num_args)) {
            atmostk = true_literal;
        }
        else if (k < 0) {
            atmostk = false_literal;
        }
        else {
            sorting_network<sort_expr> sn(se);
            expr_ref_vector in(m), out(m);
            for (unsigned i = 0; i < num_args; ++i) {
                in.push_back(c.m_app->get_arg(i));
            }
            sn(in, out);
            atmostk = ~se.internalize(c, out[k].get()); // k'th output is 0.
            TRACE("card", tout << "~atmost: " << mk_pp(out[k].get(), m) << "\n";);
        }
        literal thl = literal(c.m_bv);
        se.add_clause(~thl, atmostk);
        se.add_clause(thl, ~atmostk);
        TRACE("card", tout << mk_pp(a, m) << "\n";);
        // auxiliary clauses get removed when popping scopes.
        // we have to recompile the circuit after back-tracking.
        ctx.push_trail(value_trail<context, bool>(c.m_compiled));
        c.m_compiled = true;
    }


    void theory_card::init_search_eh() {
        
    }

    void theory_card::push_scope_eh() {
        m_watch_lim.push_back(m_watch_trail.size());
        m_cards_lim.push_back(m_cards_trail.size());
    }

    void theory_card::pop_scope_eh(unsigned num_scopes) {
        unsigned sz = m_watch_lim[m_watch_lim.size()-num_scopes];
        while (m_watch_trail.size() > sz) {
            ptr_vector<card>* cards = 0;
            VERIFY(m_watch.find(m_watch_trail.back(), cards));
            SASSERT(cards && !cards->empty());
            cards->pop_back();
            m_watch_trail.pop_back();
        }
        m_watch_lim.resize(m_watch_lim.size()-num_scopes);
        sz = m_cards_lim[m_cards_lim.size()-num_scopes];
        while (m_cards_trail.size() > sz) {
            SASSERT(m_cards.contains(m_cards_trail.back()));
            m_cards.remove(m_cards_trail.back());
            m_cards_trail.pop_back();
        }
        m_cards_lim.resize(m_cards_lim.size()-num_scopes);
    }


    literal_vector& theory_card::get_lits() {
        m_literals.reset();
        return m_literals;
    }

    void theory_card::add_assign(card& c, literal_vector const& lits, literal l) {
        literal_vector ls;
        ++c.m_num_propagations;
        m_stats.m_num_propagations++;
        context& ctx = get_context();
        for (unsigned i = 0; i < lits.size(); ++i) {
            ls.push_back(~lits[i]);
        }
        ctx.assign(l, ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), ls.size(), ls.c_ptr(), l)));
    }
    
                   

    void theory_card::add_clause(card& c, literal_vector const& lits) {
        ++c.m_num_propagations;
        m_stats.m_num_axioms++;
        context& ctx = get_context();
        TRACE("card", tout << "#prop:" << c.m_num_propagations << " - "; ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
        justification* js = 0;
        ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, 0);
        IF_VERBOSE(2, ctx.display_literals_verbose(verbose_stream(), 
                                                   lits.size(), lits.c_ptr());
                   verbose_stream() << "\n";);
        // ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    }
}
