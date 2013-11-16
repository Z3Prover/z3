/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_pb.cpp

Abstract:

    Pseudo-Boolean theory plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-05

Notes:


--*/

#include "theory_pb.h"
#include "smt_context.h"
#include "ast_pp.h"
#include "sorting_network.h"

namespace smt {
    
    theory_pb::theory_pb(ast_manager& m):
        theory(m.mk_family_id("card")),
        m_util(m)
    {}

    theory_pb::~theory_pb() {
        reset_eh();
    }

    theory * theory_pb::mk_fresh(context * new_ctx) { 
        return alloc(theory_pb, new_ctx->get_manager()); 
    }

    bool theory_pb::internalize_atom(app * atom, bool gate_ctx) {
        context& ctx   = get_context();
        ast_manager& m = get_manager();
        unsigned num_args = atom->get_num_args();
        SASSERT(m_util.is_at_most_k(atom) || m_util.is_le(atom));

        if (ctx.b_internalized(atom)) {
            return false;
        }

        m_stats.m_num_predicates++;

        SASSERT(!ctx.b_internalized(atom));
        bool_var abv = ctx.mk_bool_var(atom);

        ineq* c = alloc(ineq, atom, literal(abv));
        c->m_k = m_util.get_k(atom);
        int& k = c->m_k;
        arg_t& args = c->m_args;

        // extract literals and coefficients.
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            literal l = compile_arg(arg);
            int     c = m_util.get_le_coeff(atom, i);
            args.push_back(std::make_pair(l, c));
        }
        // turn W <= k into -W >= -k
        for (unsigned i = 0; i < args.size(); ++i) {
            args[i].second = -args[i].second;
        }
        k = -k;
        lbool is_true = normalize_ineq(args, k);

        literal lit(abv);
        switch(is_true) {
        case l_false: 
            lit = ~lit;
            // fall-through
        case l_true: 
            ctx.mk_th_axiom(get_id(), 1, &lit);
            TRACE("card", tout << mk_pp(atom, m) << " := " << lit << "\n";);
            dealloc(c);
            return true;
        case l_undef: 
            break;
        }

        // TBD: special cases: args.size() == 1
        
        // maximal coefficient:
        int& max_coeff = c->m_max_coeff;
        max_coeff = 0;
        for (unsigned i = 0; i < args.size(); ++i) {
            max_coeff = std::max(max_coeff, args[i].second);
        }

        // compute watch literals:
        int sum = 0;
        unsigned& wsz = c->m_watch_sz; 
        wsz = 0;
        while (sum < k + max_coeff && wsz < args.size()) {
            sum += args[wsz].second;
            wsz++;
        }        

        for (unsigned i = 0; i < wsz; ++i) {
            add_watch(args[i].first, c);
        }        

        // pre-compile threshold for cardinality
        bool is_cardinality = true;
        for (unsigned i = 0; is_cardinality && i < args.size(); ++i) {
            is_cardinality = (args[i].second == 1);
        }
        if (is_cardinality) {
            unsigned log = 1, n = 1;
            while (n <= args.size()) {
                ++log;
                n *= 2;
            }
            c->m_compilation_threshold = args.size()*log;
            TRACE("card", tout << "threshold:" << (args.size()*log) << "\n";);
        }
        else {
            c->m_compilation_threshold = UINT_MAX;
        }
        m_ineqs.insert(abv, c);
        m_ineqs_trail.push_back(abv);

        TRACE("card", display(tout, *c););

        return true;
    }

    literal theory_pb::compile_arg(expr* arg) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        if (!ctx.b_internalized(arg)) {
            ctx.internalize(arg, false);
        }
        bool_var bv;
        bool has_bv = false;
        bool negate = m.is_not(arg, arg);
        if (ctx.b_internalized(arg)) {
            bv = ctx.get_bool_var(arg);
            if (null_theory_var == ctx.get_var_theory(bv)) {
                ctx.set_var_theory(bv, get_id());
            }
            has_bv = (ctx.get_var_theory(bv) == get_id());
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
        return negate?~literal(bv):literal(bv);
    }

    void theory_pb::add_watch(literal l, ineq* c) {
        unsigned idx = l.index();
        ptr_vector<ineq>* ineqs;
        if (!m_watch.find(idx, ineqs)) {
            ineqs = alloc(ptr_vector<ineq>);
            m_watch.insert(idx, ineqs);
        }
        ineqs->push_back(c);
    }

    static unsigned gcd(unsigned a, unsigned b) {
        while (a != b) {
            if (a == 0) return b;
            if (b == 0) return a;
            SASSERT(a != 0 && b != 0);
            if (a < b) {
                b %= a;
            }
            else {
                a %= b;
            }
        }
        return a;
    }

    lbool theory_pb::normalize_ineq(arg_t& args, int& k) {

        // normalize first all literals to be positive:
        // then we can compare them more easily.
        for (unsigned i = 0; i < args.size(); ++i) {
            if (args[i].first.sign()) {
                args[i].first.neg();
                k -= args[i].second;
                args[i].second = -args[i].second;
            }
        }
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
        // 
        // Ensure all coefficients are positive:
        //    c*l + y >= k 
        // <=> 
        //    c*(1-~l) + y >= k
        // <=>
        //    c - c*~l + y >= k
        // <=> 
        //    -c*~l + y >= k - c
        // 
        unsigned sum = 0;
        for (unsigned i = 0; i < args.size(); ++i) {
            int c = args[i].second;
            if (c < 0) {
                args[i].second = -c;
                args[i].first = ~args[i].first;
                k -= c;
            }
            sum += args[i].second;
        }
        // detect tautologies:
        if (k <= 0) {
            args.reset();
            return l_true;
        }
        // detect infeasible constraints:
        if (static_cast<int>(sum) < k) {
            args.reset();
            return l_false;
        }
        // Ensure the largest coefficient is not larger than k:
        for (unsigned i = 0; i < args.size(); ++i) {
            int c = args[i].second;
            if (c > k) {
                args[i].second = k;
            }
        }
        SASSERT(!args.empty());

        // apply cutting plane reduction:
        unsigned g = 0;
        for (unsigned i = 0; g != 1 && i < args.size(); ++i) {
            int c = args[i].second;
            if (c != k) {
                g = gcd(g, c);
            }
        }
        if (g == 0) {
            // all coefficients are equal to k.
            for (unsigned i = 0; i < args.size(); ++i) {
                SASSERT(args[i].second == k);
                args[i].second = 1;
            }
            k = 1;
        }
        else if (g > 1) {
            //
            // Example 5x + 5y + 2z + 2u >= 5
            // becomes 3x + 3y + z + u >= 3
            // 
            int k_new = k / g;    // k_new is the ceiling of k / g.
            if (gcd(k, g) != g) {
                k_new++;
            }
            for (unsigned i = 0; i < args.size(); ++i) {
                int c = args[i].second;
                if (c == k) {
                    c = k_new;
                }
                else {
                    c = c / g;
                }
                args[i].second = c;
            }
            k = k_new;            
        }

        return l_undef;
    }

    void theory_pb::collect_statistics(::statistics& st) const {
        st.update("pb axioms", m_stats.m_num_axioms);
        st.update("pb propagations", m_stats.m_num_propagations);
        st.update("pb predicates", m_stats.m_num_predicates);        
        st.update("pb compilations", m_stats.m_num_compiles);
    }
    
    void theory_pb::reset_eh() {
        
        // m_watch;
        u_map<ptr_vector<ineq>*>::iterator it = m_watch.begin(), end = m_watch.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        u_map<ineq*>::iterator itc = m_ineqs.begin(), endc = m_ineqs.end();
        for (; itc != endc; ++itc) {
            dealloc(itc->m_value);
        }
        m_watch.reset();
        m_ineqs.reset();
        m_ineqs_trail.reset();
        m_ineqs_lim.reset();
        m_stats.reset();
    }


#if 0
    void theory_pb::propagate_assignment(ineq& c) {
        if (c.m_compiled) {
            return;
        }
        if (should_compile(c)) {
            compile_ineq(c);
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
    }
#endif

    void theory_pb::assign_eh(bool_var v, bool is_true) {
        context& ctx = get_context();
        ast_manager& m = get_manager();
        ptr_vector<ineq>* ineqs = 0;
        ineq* c = 0;
        TRACE("card", tout << "assign: " << mk_pp(ctx.bool_var2expr(v), m) << " <- " << is_true << "\n";);

        if (m_watch.find(v, ineqs)) {
            for (unsigned i = 0; i < ineqs->size(); ++i) {
                assign_watch(v, is_true, *ineqs, i);
            }
        }
        if (m_ineqs.find(v, c)) {
            // TBD: propagate_assignment(*c);
        }
    }

    void theory_pb::assign_watch(bool_var v, bool is_true, watch_list& watch, unsigned index) {
#if 0
        TBD
        ineq& c = *watch[i];
        c.m_sum;
        unsigned w;
        for (w = 0; w < c.m_watch_sz; ++i) {
            if (c.m_args[w].first.var() == v) {
                break;
            }
        }
        SASSERT(w < c.m_watch_sz);
        literal l = c.m_args[w].first;
        int coeff = c.m_args[w].second;
        if (is_true == !l.sign()) {
            ctx.push_trail(value_trail<context, int>(c.m_sum));
            c.m_sum += coeff;
            // optional propagate
        }
        else {
            unsigned deficit = c.m_max_sum - coeff;
            for (unsigned i = c.m_watch_sz; i < c.m_args.size(); ++i) {
                if 
            }
            // find a different literal to watch.
            ctx.push_trail(value_trail<context, unsigned>(c.m_watch_sz));
        }
#endif
    }

    struct theory_pb::sort_expr {
        theory_pb& th;
        context&     ctx;
        ast_manager& m;
        expr_ref_vector m_trail;
        sort_expr(theory_pb& th):
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

        literal internalize(ineq& ca, expr* e) {
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

        literal mk_ite(ineq& ca, expr* t, literal a, literal b, literal c) {
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
                literal l;
                if (ctx.b_internalized(t)) {
                    l = literal(ctx.get_bool_var(t));
                }
                else {
                    l = literal(ctx.mk_bool_var(t));
                }
                add_clause(~l, ~a,  b);
                add_clause(~l,  a,  c);
                add_clause(l,  ~a, ~b);
                add_clause(l,   a, ~c);
                TRACE("card", tout << mk_pp(t, m) << " ::= (if ";
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


    bool theory_pb::should_compile(ineq& c) {
#if 1
        return false;
#else        
        return c.m_num_propagations > c.m_compilation_threshold;
#endif
    }

    void theory_pb::compile_ineq(ineq& c) {
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
        literal thl = c.m_lit;
        se.add_clause(~thl, atmostk);
        se.add_clause(thl, ~atmostk);
        TRACE("card", tout << mk_pp(a, m) << "\n";);
        // auxiliary clauses get removed when popping scopes.
        // we have to recompile the circuit after back-tracking.
        ctx.push_trail(value_trail<context, bool>(c.m_compiled));
        c.m_compiled = true;
    }


    void theory_pb::init_search_eh() {
        
    }

    void theory_pb::push_scope_eh() {
        m_ineqs_lim.push_back(m_ineqs_trail.size());
    }

    void theory_pb::pop_scope_eh(unsigned num_scopes) {
        unsigned sz = m_ineqs_lim[m_ineqs_lim.size()-num_scopes];
        while (m_ineqs_trail.size() > sz) {
            SASSERT(m_ineqs.contains(m_ineqs_trail.back()));
            m_ineqs.remove(m_ineqs_trail.back());
            m_ineqs_trail.pop_back();
        }
        m_ineqs_lim.resize(m_ineqs_lim.size()-num_scopes);
    }

    std::ostream& theory_pb::display(std::ostream& out, ineq& c) const {
        ast_manager& m = get_manager();
        out << mk_pp(c.m_app, m) << "\n";
        for (unsigned i = 0; i < c.m_args.size(); ++i) {
            out << c.m_args[i].second << "*" << c.m_args[i].first;
            if (i + 1 < c.m_args.size()) {
                out << " + ";
            }
        }
        out << " >= " << c.m_k  << "\n"
            << "propagations: " << c.m_num_propagations 
            << " max_coeff: "   << c.m_max_coeff 
            << " watch size: "  << c.m_watch_sz
            << "\n";
        return out;
    }


    literal_vector& theory_pb::get_lits() {
        m_literals.reset();
        return m_literals;
    }

    void theory_pb::add_assign(ineq& c, literal_vector const& lits, literal l) {
        literal_vector ls;
        ++c.m_num_propagations;
        m_stats.m_num_propagations++;
        context& ctx = get_context();
        for (unsigned i = 0; i < lits.size(); ++i) {
            ls.push_back(~lits[i]);
        }
        ctx.assign(l, ctx.mk_justification(theory_propagation_justification(get_id(), ctx.get_region(), ls.size(), ls.c_ptr(), l)));
    }
    
                   

    void theory_pb::add_clause(ineq& c, literal_vector const& lits) {
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
