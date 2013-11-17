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
        numeral& k = c->m_k;
        arg_t& args = c->m_args;

        // extract literals and coefficients.
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            literal l = compile_arg(arg);
            numeral c = m_util.get_le_coeff(atom, i);
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
        numeral& max_coeff = c->m_max_coeff;
        max_coeff = 0;
        for (unsigned i = 0; i < args.size(); ++i) {
            max_coeff = std::max(max_coeff, args[i].second);
        }

        // compute watch literals:
        numeral sum = 0;
        unsigned wsz = 0;
        while (sum < k + max_coeff && wsz < args.size()) {
            sum += args[wsz].second;
            wsz++;
        }        

        for (unsigned i = 0; i < wsz; ++i) {
            add_watch(*c, i);
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

    void theory_pb::del_watch(watch_list& watch, unsigned index, ineq& c, unsigned ineq_index) {
        if (index < watch.size()) {
            std::swap(watch[index], watch[watch.size()-1]);
        }
        watch.pop_back();
        
        SASSERT(ineq_index < c.watch_size());
        numeral coeff = c.coeff(ineq_index);
        if (ineq_index + 1 < c.watch_size()) {
            std::swap(c.m_args[ineq_index], c.m_args[c.watch_size()-1]);
        }
        --c.m_watch_sz;
        c.m_max_sum  -= coeff;

        // current index of unwatched literal is c.watch_size().
    }

    void theory_pb::add_watch(ineq& c, unsigned i) {
        bool_var v = c.lit(i).var();
        c.m_max_sum += c.coeff(i);
        SASSERT(i >= c.watch_size());
        if (i > c.watch_size()) {
            std::swap(c.m_args[i], c.m_args[c.watch_size()]);
        }
        ++c.m_watch_sz;
        ptr_vector<ineq>* ineqs;
        if (!m_watch.find(v, ineqs)) {
            ineqs = alloc(ptr_vector<ineq>);
            m_watch.insert(v, ineqs);
        }
        ineqs->push_back(&c);
    }

    theory_pb::numeral theory_pb::gcd(numeral a, numeral b) {
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


    lbool theory_pb::normalize_ineq(arg_t& args, numeral& k) {

        // normalize first all literals to be positive:
        // then we can compare them more easily.
        for (unsigned i = 0; i < args.size(); ++i) {
            if (args[i].first.sign()) {
                args[i].first.neg();
                k -= args[i].second;
                args[i].second = -args[i].second;
            }
        }
        // remove constants
        for (unsigned i = 0; i < args.size(); ++i) {
            if (args[i].first == true_literal) {
                k += args[i].second;
                std::swap(args[i], args[args.size()-1]);
                args.pop_back();
            }
            else if (args[i].first == false_literal) {
                std::swap(args[i], args[args.size()-1]);
                args.pop_back();                
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
        numeral sum = 0;
        for (unsigned i = 0; i < args.size(); ++i) {
            numeral c = args[i].second;
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
        if (sum < k) {
            args.reset();
            return l_false;
        }
        // Ensure the largest coefficient is not larger than k:
        for (unsigned i = 0; i < args.size(); ++i) {
            numeral c = args[i].second;
            if (c > k) {
                args[i].second = k;
            }
        }
        SASSERT(!args.empty());

        // apply cutting plane reduction:
        numeral g = 0;
        for (unsigned i = 0; g != 1 && i < args.size(); ++i) {
            numeral c = args[i].second;
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
            numeral k_new = k / g;    
            if ((k % g) != 0) {     // k_new is the ceiling of k / g.
                k_new++;
            }
            for (unsigned i = 0; i < args.size(); ++i) {
                numeral c = args[i].second;
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
        m_to_compile.reset();
    }

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
            assign_ineq(*c);
        }
    }

    literal_vector& theory_pb::get_helpful_literals(ineq& c, bool negate) {
        numeral sum = 0;
        context& ctx = get_context();
        literal_vector& lits = get_lits();
        for (unsigned i = 0; sum < c.k() && i < c.size(); ++i) {
            literal l = c.lit(i);
            if (ctx.get_assignment(l) == l_true) {
                sum += c.coeff(i);
                if (negate) l = ~l;
                lits.push_back(l);
            }
        }
        SASSERT(sum >= c.k());        
        return lits;
    }

    literal_vector& theory_pb::get_unhelpful_literals(ineq& c, bool negate) {
        context& ctx = get_context();
        literal_vector& lits = get_lits();
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.lit(i);
            if (ctx.get_assignment(l) == l_false) {
                if (negate) l = ~l;
                lits.push_back(l);
            }
        }
        return lits;
    }

    /**
       \brief propagate assignment to inequality.
       This is a basic, non-optimized implementation based
       on the assumption that inequalities are mostly units
       and/or relatively few compared to number of argumets.
     */
    void theory_pb::assign_ineq(ineq& c) {
        context& ctx = get_context();
        numeral sum = 0, maxsum = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            switch (ctx.get_assignment(c.lit(i))) {
            case l_true:
                sum += c.coeff(i);
                // falll through
            case l_undef:
                maxsum += c.coeff(i);
                break;
            default:
                break;
            }
        }
        lbool lit_assignment = ctx.get_assignment(c.lit());
        SASSERT(lit_assignment != l_undef);
        if (sum >= c.k() && lit_assignment == l_false) {
            literal_vector& lits = get_helpful_literals(c, true);
            lits.push_back(c.lit());
            add_clause(c, lits);
        }
        else if (maxsum < c.k() && lit_assignment == l_true) {
            literal_vector& lits = get_unhelpful_literals(c, true);
            lits.push_back(~c.lit());
            add_clause(c, lits);
        }
    }

    /**
       \brief v is assigned in inequality c. Update current bounds and watch list.
       Optimize for case where the c.lit() is True. This covers the case where 
       inequalities are unit literals and formulas in negation normal form 
       (inequalities are closed under negation).
       
     */
    void theory_pb::assign_watch(bool_var v, bool is_true, watch_list& watch, unsigned watch_index) {
        context& ctx = get_context();
        ineq& c = *watch[watch_index];
        numeral k = c.m_k;
        unsigned w = c.find_lit(v, 0, c.watch_size());
        numeral coeff = c.coeff(w);
        if (is_true == c.lit(w).sign()) {
            //
            // sum is not increased. 
            // Adjust set of watched literals.
            //
            del_watch(watch, watch_index, c, w);

            numeral tmp_sum = c.sum();
            for (unsigned i = c.watch_size(); c.max_sum() - coeff < k + c.max_coeff() && i < c.size(); ++i) {
                lbool lit_assignment = ctx.get_assignment(c.lit(i));
                switch(lit_assignment) {
                case l_true:
                    tmp_sum += c.coeff(i);  
                    // fall-through
                case l_undef:
                    add_watch(c, i);
                    break;
                case l_false:
                    break;
                }
            }
            SASSERT(tmp_sum <= c.max_sum());
            if (c.max_sum() < k) {
                //
                // c.lit() <- false
                // we have to add the previously watched literal back.
                // such that the sum of watched literals has maximal sum >= k
                // 

                SASSERT(coeff == c.coeff(w));
                SASSERT(c.max_sum() + coeff >= k);
                add_watch(c, c.find_lit(v, c.watch_size(), c.size()));
                SASSERT(c.max_sum() >= k);
                
                switch(ctx.get_assignment(c.lit())) {
                case l_false:
                    break;
                case l_true: {
                    literal_vector& lits = get_unhelpful_literals(c, true);
                    lits.push_back(~c.lit());
                    add_clause(c, lits);
                    break;
                }
                case l_undef: {
                    add_assign(c, get_unhelpful_literals(c, false), ~c.lit());
                    break;
                }
                }
            }
            else if (tmp_sum >= k) {
                // ineq should be true.
                // this is handled below
            }
            else if (c.max_sum() - c.max_coeff() < k) {
                // tmp_sum < k <= c.max_sum()
                // opportunities for unit propagation for unassigned 
                // literals whose coefficients satisfy
                // c.max_sum() - coeff < k
                if (l_true == ctx.get_assignment(c.lit())) {
                    literal_vector& lits = get_unhelpful_literals(c, false);
                    for (unsigned i = 0; i < c.size(); ++i) {
                        if (c.max_sum() - c.coeff(i) < k && ctx.get_assignment(c.lit(i)) == l_undef) {
                            add_assign(c, lits, c.lit(i));                            
                        }
                    }
                }
            }
            else {
                // tmp_sum < k <= c.max_sum() - c.max_coeff()
                // we might miss opportunities for unit propagation if 
                // max_coeff is not the maximal coefficient
                // of the current unassigned literal, but we can
                // rely on eventually learning this from propagations.
            }

        }
        else {
            // sum is increased the current set of watch 
            // literals represent a potentially feasible assignment.
            //
            ctx.push_trail(value_trail<context, numeral>(c.m_sum));
            c.m_sum += coeff;
        }

        if (c.sum() >= k) {
            lbool ineq_assignment = ctx.get_assignment(c.lit());
            switch(ineq_assignment) {
            case l_true:
                break;
            case l_undef: {
                add_assign(c, get_helpful_literals(c, false), c.lit());
                break;
            }
            case l_false: {
                literal_vector& lits = get_helpful_literals(c, true);
                lits.push_back(c.lit());
                add_clause(c, lits);
                break;
            }
            }
        }

        // else if c.sum() < k and lit(w) was assigned to true:
        //   Progress was made.
        //   The watch list contains at least enough
        //   literals to force the assignment.
        
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
            expr_ref_vector trail(m);
            for (unsigned i = 0; i < ca.size(); ++i) {
                expr_ref tmp(m);
                ctx.literal2expr(ca.lit(i), tmp);
                cache.insert(tmp, ca.lit(i));
                trail.push_back(tmp);
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


    void theory_pb::inc_propagations(ineq& c) {
        ++c.m_num_propagations;
        if (c.m_compiled == l_false && c.m_num_propagations > c.m_compilation_threshold) {
            c.m_compiled = l_undef;
            m_to_compile.push_back(&c);
        }
    }

    void theory_pb::restart_eh() {
        for (unsigned i = 0; i < m_to_compile.size(); ++i) {
            compile_ineq(*m_to_compile[i]);
        }
        m_to_compile.reset();
    }

    void theory_pb::compile_ineq(ineq& c) {
        ++m_stats.m_num_compiles;
        ast_manager& m = get_manager();
        context& ctx = get_context();
        // only cardinality constraints are compiled.
        SASSERT(c.m_compilation_threshold < UINT_MAX);
        DEBUG_CODE(for (unsigned i = 0; i < c.size(); ++i) SASSERT(c.coeff(i) == 1); );
        unsigned k = static_cast<unsigned>(c.k());        
        unsigned num_args = c.size();
        SASSERT(0 <= k && k <= num_args);

        sort_expr se(*this);
        sorting_network<sort_expr> sn(se);
        expr_ref_vector in(m), out(m);
        expr_ref tmp(m);
        for (unsigned i = 0; i < num_args; ++i) {
            ctx.literal2expr(c.lit(i), tmp);
            in.push_back(tmp);
        }
        sn(in, out);
        literal at_least_k = se.internalize(c, out[k-1].get()); // first k outputs are 1.
        TRACE("card", tout << "at_least: " << mk_pp(out[k-1].get(), m) << "\n";);
        
        literal thl = c.lit();
        se.add_clause(~thl, at_least_k);
        se.add_clause(thl, ~at_least_k);
        TRACE("card", tout << mk_pp(c.m_app, m) << "\n";);
        // auxiliary clauses get removed when popping scopes.
        // we have to recompile the circuit after back-tracking.
        c.m_compiled = l_false;
        ctx.push_trail(value_trail<context, lbool>(c.m_compiled));
        c.m_compiled = l_true;
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
        for (unsigned i = 0; i < c.size(); ++i) {
            out << c.coeff(i) << "*" << c.lit(i);
            if (i + 1 < c.size()) {
                out << " + ";
            }
        }
        out << " >= " << c.m_k  << "\n"
            << "propagations: " << c.m_num_propagations 
            << " max_coeff: "   << c.max_coeff() 
            << " watch size: "  << c.watch_size()
            << "\n";
        return out;
    }


    literal_vector& theory_pb::get_lits() {
        m_literals.reset();
        return m_literals;
    }

    void theory_pb::add_assign(ineq& c, literal_vector const& lits, literal l) {
        inc_propagations(c);
        m_stats.m_num_propagations++;
        context& ctx = get_context();
        ctx.assign(l, ctx.mk_justification(
                       theory_propagation_justification(
                           get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), l)));
    }
    
                   

    void theory_pb::add_clause(ineq& c, literal_vector const& lits) {
        inc_propagations(c);
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
