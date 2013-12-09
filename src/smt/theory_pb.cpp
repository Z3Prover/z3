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
#include "uint_set.h"

namespace smt {

    void theory_pb::ineq::negate() {
        m_lit.neg();
        numeral sum(0);
        for (unsigned i = 0; i < size(); ++i) {
            m_args[i].first.neg();
            sum += coeff(i);
        }
        m_k = sum - m_k + numeral::one();
        SASSERT(well_formed());
    }

    void theory_pb::ineq::reset() {
        m_max_coeff.reset();
        m_watch_sz = 0;
        m_max_sum.reset();
        m_num_propagations = 0;
        m_compilation_threshold = UINT_MAX;
        m_compiled = l_false;
        m_args.reset();
        m_k.reset();
    }


    void theory_pb::ineq::unique() {
        numeral& k = m_k;
        arg_t& args = m_args;
        // normalize first all literals to be positive:
        // then we can compare them more easily.
        for (unsigned i = 0; i < size(); ++i) {
            if (lit(i).sign()) {
                args[i].first.neg();
                k -= coeff(i);
                args[i].second = -coeff(i);
            }
        }
        // remove constants
        for (unsigned i = 0; i < size(); ++i) {
            if (lit(i) == true_literal) {
                k += coeff(i);
                std::swap(args[i], args[size()-1]);
                args.pop_back();
            }
            else if (lit(i) == false_literal) {
                std::swap(args[i], args[size()-1]);
                args.pop_back();                
            }
        }
        // sort and coalesce arguments:
        std::sort(args.begin(), args.end());
        for (unsigned i = 0; i + 1 < size(); ++i) {
            if (lit(i) == args[i+1].first) {
                args[i].second += coeff(i+1);
                for (unsigned j = i+1; j + 1 < size(); ++j) {
                    args[j] = args[j+1];
                }
                args.pop_back();
            }
            if (coeff(i).is_zero()) {
                for (unsigned j = i; j + 1 < size(); ++j) {
                    args[j] = args[j+1];
                }
                args.pop_back();
            }
        }            
    }

    lbool theory_pb::ineq::normalize() {

        numeral& k = m_k;
        arg_t& args = m_args;

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
        numeral sum(0);
        for (unsigned i = 0; i < size(); ++i) {
            numeral c = coeff(i);
            if (c.is_neg()) {
                args[i].second = -c;
                args[i].first = ~lit(i);
                k -= c;
            }
            sum += coeff(i);
        }
        // detect tautologies:
        if (k <= numeral::zero()) {
            args.reset();
            return l_true;
        }
        // detect infeasible constraints:
        if (sum < k) {
            args.reset();
            return l_false;
        }

        // normalize to integers.
        numeral d(denominator(k));
        for (unsigned i = 0; i < size(); ++i) {
            d = lcm(d, denominator(coeff(i)));
        }
        if (!d.is_one()) {
            k *= d;
            for (unsigned i = 0; i < size(); ++i) {
                args[i].second *= d;
            }            
        }

        // Ensure the largest coefficient is not larger than k:
        sum = numeral::zero();
        for (unsigned i = 0; i < size(); ++i) {
            numeral c = coeff(i);
            if (c > k) {
                args[i].second = k;
            }
            sum += coeff(i);
        }
        SASSERT(!args.empty());

        // normalize tight inequalities to unit coefficients.
        if (sum == k) {
            for (unsigned i = 0; i < size(); ++i) {
                args[i].second = numeral::one();
            }
            k = numeral(size());
        }

        // apply cutting plane reduction:
        numeral g(0);
        for (unsigned i = 0; !g.is_one() && i < size(); ++i) {
            numeral c = coeff(i);
            if (c != k) {
                if (g.is_zero()) {
                    g = c;
                }
                else {
                    g = gcd(g, c);
                }
            }
        }
        if (g.is_zero()) {
            // all coefficients are equal to k.
            for (unsigned i = 0; i < size(); ++i) {
                SASSERT(coeff(i) == k);
                args[i].second = numeral::one();
            }
            k = numeral::one();
        }
        else if (g > numeral::one()) {
            //
            // Example 5x + 5y + 2z + 2u >= 5
            // becomes 3x + 3y + z + u >= 3
            // 
            numeral k_new = div(k, g);    
            if (!(k % g).is_zero()) {     // k_new is the ceiling of k / g.
                k_new++;
            }
            for (unsigned i = 0; i < size(); ++i) {
                SASSERT(coeff(i).is_pos());
                numeral c = coeff(i);
                if (c == k) {
                    c = k_new;
                }
                else {
                    c = div(c, g);
                }
                args[i].second = c;
                SASSERT(coeff(i).is_pos());
            }
            k = k_new;            
        }
        //
        // normalize coefficients that fall within a range
        // k/n <= ... < k/(n-1) for some n = 1,2,...
        //
        // e.g, k/n <= min <= max < k/(n-1)
        //      k/min <= n, n-1 < k/max
        // .    floor(k/max) = ceil(k/min) - 1  
        // .    floor(k/max) < k/max
        //
        // example: k = 5, min = 3, max = 4: 5/3 -> 2   5/4 -> 1, n = 2
        // replace all coefficients by 1, and k by 2.
        //
        if (!k.is_one()) {
            numeral min = coeff(0), max = coeff(0);
            for (unsigned i = 1; i < size(); ++i) {
                if (coeff(i) < min) min = coeff(i);
                if (coeff(i) > max) max = coeff(i);
            }            
            numeral n0 = k/max;
            numeral n1 = floor(n0);
            numeral n2 = ceil(k/min) - numeral::one();
            if (n1 == n2 && !n0.is_int()) {
                for (unsigned i = 0; i < size(); ++i) {
                    args[i].second = numeral::one();
                }
                k = n1 + numeral::one();
            }
        }
        
        SASSERT(well_formed());
        return l_undef;
    }

    app_ref theory_pb::ineq::to_expr(context& ctx, ast_manager& m) {
        expr_ref tmp(m);
        app_ref result(m);
        svector<rational> coeffs;
        expr_ref_vector args(m);
        for (unsigned i = 0; i < size(); ++i) {
            ctx.literal2expr(lit(i), tmp);
            args.push_back(tmp);
            coeffs.push_back(coeff(i));
        }
        pb_util pb(m);
        result = pb.mk_ge(coeffs.size(), coeffs.c_ptr(), args.c_ptr(), k());
        return result;
    }

    bool theory_pb::ineq::well_formed() const {
        SASSERT(k().is_pos());
        uint_set vars;
        numeral sum = numeral::zero();
        for (unsigned i = 0; i < size(); ++i) {
            SASSERT(coeff(i) <= k());
            SASSERT(numeral::one() <= coeff(i));
            SASSERT(lit(i) != true_literal);
            SASSERT(lit(i) != false_literal);
            SASSERT(lit(i) != null_literal);
            SASSERT(!vars.contains(lit(i).var()));
            vars.insert(lit(i).var());
            sum += coeff(i);
        }
        SASSERT(sum >= k());
        return true;
    }
    
    theory_pb::theory_pb(ast_manager& m):
        theory(m.mk_family_id("pb")),
        m_util(m),
        m_lemma(null_literal)
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
        SASSERT(m_util.is_at_most_k(atom) || m_util.is_le(atom) || m_util.is_ge(atom));

        if (ctx.b_internalized(atom)) {
            return false;
        }

        m_stats.m_num_predicates++;

        SASSERT(!ctx.b_internalized(atom));
        bool_var abv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(abv, get_id());

        ineq* c = alloc(ineq, literal(abv));
        c->m_k = m_util.get_k(atom);
        numeral& k = c->m_k;
        arg_t& args = c->m_args;

        // extract literals and coefficients.
        for (unsigned i = 0; i < num_args; ++i) {
            expr* arg = atom->get_arg(i);
            literal l = compile_arg(arg);
            numeral c = m_util.get_coeff(atom, i);
            args.push_back(std::make_pair(l, c));
        }
        if (m_util.is_at_most_k(atom) || m_util.is_le(atom)) {
            // turn W <= k into -W >= -k
            for (unsigned i = 0; i < args.size(); ++i) {
                args[i].second = -args[i].second;
            }
            k = -k;
        }
        else {
            SASSERT(m_util.is_at_least_k(atom) || m_util.is_ge(atom));
        }
        c->unique();
        lbool is_true = c->normalize();

        literal lit(abv);
        switch(is_true) {
        case l_false: 
            lit = ~lit;
            // fall-through
        case l_true: 
            ctx.mk_th_axiom(get_id(), 1, &lit);
            TRACE("pb", tout << mk_pp(atom, m) << " := " << lit << "\n";);
            dealloc(c);
            return true;
        case l_undef: 
            break;
        }

        // TBD: special cases: args.size() == 1
        
        // maximal coefficient:
        numeral& max_coeff = c->m_max_coeff;
        max_coeff = numeral::zero();
        for (unsigned i = 0; i < args.size(); ++i) {
            max_coeff = std::max(max_coeff, args[i].second);
        }


        // pre-compile threshold for cardinality
        bool is_cardinality = true;
        for (unsigned i = 0; is_cardinality && i < args.size(); ++i) {
            is_cardinality = (args[i].second.is_one());
        }
        if (is_cardinality) {
            unsigned log = 1, n = 1;
            while (n <= args.size()) {
                ++log;
                n *= 2;
            }
            unsigned th = 10*args.size()*log;
            c->m_compilation_threshold = th;
            TRACE("pb", tout << "compilation threshold: " << th << "\n";);
        }
        else {
            c->m_compilation_threshold = UINT_MAX;
        }
        m_ineqs.insert(abv, c);
        m_ineqs_trail.push_back(abv);

        TRACE("pb", display(tout, *c););

        return true;
    }

    literal theory_pb::compile_arg(expr* arg) {
        context& ctx = get_context();
        ast_manager& m = get_manager();

        bool_var bv;
        bool has_bv = false;
        bool negate = m.is_not(arg, arg);
        SASSERT(!m.is_not(arg));
        if (!ctx.b_internalized(arg)) {
            ctx.internalize(arg, false);
        }
        if (ctx.b_internalized(arg)) {
            bv = ctx.get_bool_var(arg);
            if (is_uninterp(arg) && null_theory_var == ctx.get_var_theory(bv)) {
                ctx.set_var_theory(bv, get_id());
            }
            has_bv = (ctx.get_var_theory(bv) == get_id());
#if 0
        TBD:
            if (!has_bv) {
                if (!ctx.e_internalized(arg)) {
                    ctx.internalize(arg, false);
                    SASSERT(ctx.e_internalized(arg));
                }
                enode* n = ctx.get_enode(arg);
                theory_var v = mk_var(n);
                ctx.attach_th_var(n, this, v);
            }
#endif
        }
        else if (m.is_true(arg)) {
            bv = true_bool_var;
            has_bv = true;
        }
        else if (m.is_false(arg)) {
            bv = true_bool_var;
            has_bv = true;
            negate = !negate;
        }


        // assumes relevancy level = 2 or 0.
        // TBD: should should have been like an uninterpreted
        // function intenalize, where enodes for each argument
        // is available. 
        if (!has_bv) {
            expr_ref tmp(m), fml(m);
            tmp = m.mk_fresh_const("pb_proxy",m.mk_bool_sort());
            fml = m.mk_iff(tmp, arg);
            TRACE("pb", tout << "create proxy " << fml << "\n";);
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
        if (c.max_coeff() == coeff) {
            coeff = c.coeff(0);
            for (unsigned i = 1; coeff != c.max_coeff() && i < c.m_watch_sz; ++i) {
                if (coeff < c.coeff(i)) coeff = c.coeff(i);
            }
            c.set_max_coeff(coeff);
        }

        // current index of unwatched literal is c.watch_size().
    }

    void theory_pb::add_watch(ineq& c, unsigned i) {
        literal lit = c.lit(i);
        bool_var v = lit.var();
        c.m_max_sum += c.coeff(i);
        SASSERT(i >= c.watch_size());
        if (i > c.watch_size()) {
            std::swap(c.m_args[i], c.m_args[c.watch_size()]);
        }
        ++c.m_watch_sz;
        ptr_vector<ineq>* ineqs;
        if (!m_watch.find(lit.index(), ineqs)) {
            ineqs = alloc(ptr_vector<ineq>);
            m_watch.insert(lit.index(), ineqs);
        }
        ineqs->push_back(&c);
    }

    void theory_pb::collect_statistics(::statistics& st) const {
        st.update("pb conflicts", m_stats.m_num_conflicts);
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
        m_assign_ineqs_trail.reset();
        m_assign_ineqs_lim.reset();
        m_stats.reset();
        m_to_compile.reset();
    }

    void theory_pb::new_eq_eh(theory_var v1, theory_var v2) {
        IF_VERBOSE(0, verbose_stream() << v1 << " = " << v2 << "\n";);
    }
    
    final_check_status theory_pb::final_check_eh() {
        TRACE("pb", display(tout););
        DEBUG_CODE(validate_final_check(););
        return FC_DONE;
    }

    void theory_pb::validate_final_check() {
        u_map<ineq*>::iterator itc = m_ineqs.begin(), endc = m_ineqs.end();
        for (; itc != endc; ++itc) {
            validate_final_check(*itc->m_value);                
        }
    }

    void theory_pb::validate_final_check(ineq& c) {
        context& ctx = get_context();

        if (ctx.get_assignment(c.lit()) == l_undef) {
            return;
        }
        if (!ctx.is_relevant(c.lit())) {
            return;
        }
        numeral sum = numeral::zero(), maxsum = numeral::zero();
        for (unsigned i = 0; i < c.size(); ++i) {
            switch(ctx.get_assignment(c.lit(i))) {
            case l_true:
                sum += c.coeff(i);
            case l_undef:
                maxsum += c.coeff(i);
                break;
            }
        }
        TRACE("pb", display(tout << "validate: ", c, true);
              tout << "sum: " << sum << " " << maxsum << " ";
              tout << ctx.get_assignment(c.lit()) << "\n";
              );

        SASSERT(sum <= maxsum);
        SASSERT((sum >= c.k()) == (ctx.get_assignment(c.lit()) == l_true));
        SASSERT((maxsum < c.k()) == (ctx.get_assignment(c.lit()) == l_false));
    }


    void theory_pb::assign_eh(bool_var v, bool is_true) {
        context& ctx = get_context();
        ptr_vector<ineq>* ineqs = 0;
        literal nlit(v, is_true);
        TRACE("pb", tout << "assign: " << ~nlit << "\n";);
        if (m_watch.find(nlit.index(), ineqs)) {
            for (unsigned i = 0; i < ineqs->size(); ++i) {
                if (assign_watch(v, is_true, *ineqs, i)) {
                    // i was removed from watch list.
                    --i;
                }
            }
        }
        ineq* c = 0;
        if (m_ineqs.find(v, c)) {
            assign_ineq(*c, is_true);
        }
    }

    literal_vector& theory_pb::get_helpful_literals(ineq& c, bool negate) {
        numeral sum = numeral::zero();
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
    void theory_pb::assign_ineq(ineq& c, bool is_true) {

        if (c.lit().sign() == is_true) {
            c.negate();
        }
        SASSERT(c.well_formed());

        context& ctx = get_context();
        numeral maxsum = numeral::zero();
        numeral mininc = numeral::zero();
        for (unsigned i = 0; i < c.size(); ++i) {
            lbool asgn = ctx.get_assignment(c.lit(i));
            if (asgn != l_false) {
                maxsum += c.coeff(i);
            }
            if (asgn == l_undef && (mininc.is_zero() || mininc > c.coeff(i))) {
                mininc = c.coeff(i);
            }
        }

        TRACE("pb", 
              tout << "assign: " << c.lit() << "\n";
              display(tout, c); );

        if (maxsum < c.k()) {
            literal_vector& lits = get_unhelpful_literals(c, false);
            lits.push_back(~c.lit());
            add_clause(c, lits);
        }
        else {
            c.m_max_sum = numeral::zero();
            c.m_watch_sz = 0;
            for (unsigned i = 0; c.max_sum() < c.k() + c.max_coeff() && i < c.size(); ++i) {
                if (ctx.get_assignment(c.lit(i)) != l_false) {
                    add_watch(c, i);
                }       
            }
            SASSERT(c.max_sum() >= c.k());
            m_assign_ineqs_trail.push_back(&c);
        }

        // perform unit propagation
        if (maxsum >= c.k() && maxsum - mininc < c.k()) { 
            literal_vector& lits = get_unhelpful_literals(c, true);
            lits.push_back(c.lit());
            for (unsigned i = 0; i < c.size(); ++i) {
                if (ctx.get_assignment(c.lit(i)) == l_undef) {
                    add_assign(c, lits, c.lit(i));
                }                
            }
        }
    }

    /**
       \brief v is assigned in inequality c. Update current bounds and watch list.
       Optimize for case where the c.lit() is True. This covers the case where 
       inequalities are unit literals and formulas in negation normal form 
       (inequalities are closed under negation).
       
     */
    bool theory_pb::assign_watch(bool_var v, bool is_true, watch_list& watch, unsigned watch_index) {
        bool removed = false;
        context& ctx = get_context();
        ineq& c = *watch[watch_index];
        unsigned w = c.find_lit(v, 0, c.watch_size());

        SASSERT(ctx.get_assignment(c.lit()) == l_true);
        SASSERT(is_true == c.lit(w).sign());

        //
        // max_sum is decreased.
        // Adjust set of watched literals.
        //
        
        numeral k = c.k();
        numeral coeff = c.coeff(w);
        
        for (unsigned i = c.watch_size(); c.max_sum() - coeff < k + c.max_coeff() && i < c.size(); ++i) {
            if (ctx.get_assignment(c.lit(i)) != l_false) {
                add_watch(c, i);
            }
        }        
        
        if (c.max_sum() - coeff < k) {
            //
            // L: 3*x1 + 2*x2 + x4 >= 3, but x1 <- 0, x2 <- 0
            // create clause x1 or x2 or ~L
            // 
            literal_vector& lits = get_unhelpful_literals(c, false);
            lits.push_back(~c.lit());
            add_clause(c, lits);
        }
        else {
            del_watch(watch, watch_index, c, w);
            removed = true;
            if (c.max_sum() - coeff < k + c.max_coeff()) {
                
                //
                // opportunities for unit propagation for unassigned 
                // literals whose coefficients satisfy
                // c.max_sum() - coeff < k
                //
                // L: 3*x1 + 2*x2 + x4 >= 3, but x1 <- 0
                // Create clauses x1 or ~L or x2 
                //                x1 or ~L or x4
                //
                
                literal_vector& lits = get_unhelpful_literals(c, true);
                lits.push_back(c.lit());
                for (unsigned i = 0; i < c.size(); ++i) {
                    if (c.max_sum() - c.coeff(i) < k && ctx.get_assignment(c.lit(i)) == l_undef) {
                        add_assign(c, lits, c.lit(i));                            
                    }
                }
            }
            //
            // else: c.max_sum() >= k + c.max_coeff()
            // we might miss opportunities for unit propagation if 
            // max_coeff is not the maximal coefficient
            // of the current unassigned literal, but we can
            // rely on eventually learning this from propagations.
            //
        }

        TRACE("pb", 
              tout << "assign: " << literal(v,!is_true) << "\n";
              display(tout, c); );


        return removed;
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
                TRACE("pb", tout << mk_pp(t, m) << " ::= (if ";
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
            TRACE("pb",
                  ctx.display_literals_verbose(tout, lits.size(), lits.c_ptr()); tout << "\n";);
            ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX, 0);
        }            

        void add_clause(literal l1, literal l2) {
            add_clause(l1, l2, null_literal);
        }

    };


    void theory_pb::inc_propagations(ineq& c) {
        ++c.m_num_propagations;
#if 1
        if (c.m_compiled == l_false && c.m_num_propagations > c.m_compilation_threshold) {
            c.m_compiled = l_undef;
            m_to_compile.push_back(&c);
        }
#endif
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
        DEBUG_CODE(for (unsigned i = 0; i < c.size(); ++i) SASSERT(c.coeff(i).is_one()); );
        unsigned k = c.k().get_unsigned();
        unsigned num_args = c.size();

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
        TRACE("pb", tout << "at_least: " << mk_pp(out[k-1].get(), m) << "\n";);
        
        literal thl = c.lit();
        se.add_clause(~thl, at_least_k);
        se.add_clause(thl, ~at_least_k);
        TRACE("pb", tout << c.lit() << "\n";);
        // auxiliary clauses get removed when popping scopes.
        // we have to recompile the circuit after back-tracking.
        c.m_compiled = l_false;
        ctx.push_trail(value_trail<context, lbool>(c.m_compiled));
        c.m_compiled = l_true;
    }


    void theory_pb::init_search_eh() {
        m_to_compile.reset();
    }

    void theory_pb::push_scope_eh() {
        m_ineqs_lim.push_back(m_ineqs_trail.size());
        m_assign_ineqs_lim.push_back(m_assign_ineqs_trail.size());
    }

    void theory_pb::pop_scope_eh(unsigned num_scopes) {

        // remove watched literals.
        unsigned new_lim = m_assign_ineqs_lim.size()-num_scopes;
        unsigned sz = m_assign_ineqs_lim[new_lim];
        while (m_assign_ineqs_trail.size() > sz) {
            ineq* c = m_assign_ineqs_trail.back();
            for (unsigned i = 0; i < c->watch_size(); ++i) {
                literal w = c->lit(i);
                ptr_vector<ineq>* ineqs = 0;
                VERIFY(m_watch.find(w.index(), ineqs));
                for (unsigned j = 0; j < ineqs->size(); ++j) {
                    if ((*ineqs)[j] == c) {                        
                        std::swap((*ineqs)[j],(*ineqs)[ineqs->size()-1]);
                        ineqs->pop_back();
                        break;
                    }
                }
            }
            m_assign_ineqs_trail.pop_back();
        }
        m_assign_ineqs_lim.resize(new_lim);

        // remove inequalities.
        new_lim = m_ineqs_lim.size()-num_scopes;
        sz = m_ineqs_lim[new_lim];
        while (m_ineqs_trail.size() > sz) {
            bool_var v = m_ineqs_trail.back();
            ineq* c = 0;
            VERIFY(m_ineqs.find(v, c));
            m_ineqs.remove(v);
            m_ineqs_trail.pop_back(); 
            dealloc(c);
        }
        m_ineqs_lim.resize(new_lim);
    }

    void theory_pb::display(std::ostream& out) const {
        u_map<ptr_vector<ineq>*>::iterator it = m_watch.begin(), end = m_watch.end();
        for (; it != end; ++it) {
            out << "watch: " << to_literal(it->m_key) << " |-> ";
            watch_list const& wl = *it->m_value;
            for (unsigned i = 0; i < wl.size(); ++i) {
                out << wl[i]->lit() << " ";
            }
            out << "\n";
        }
        u_map<ineq*>::iterator itc = m_ineqs.begin(), endc = m_ineqs.end();
        for (; itc != endc; ++itc) {
            ineq& c = *itc->m_value;
            display(out, c);
        }
    }

    std::ostream& theory_pb::display(std::ostream& out, ineq& c, bool values) const {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        out << c.lit();
        if (c.lit() != null_literal) {
            if (values) {
                out << "@(" << ctx.get_assignment(c.lit());
                if (ctx.get_assignment(c.lit()) != l_undef) {
                    out << ":" << ctx.get_assign_level(c.lit());
                }
                out << ")";
            }
            expr_ref tmp(m);
            ctx.literal2expr(c.lit(), tmp);
            out << " " << tmp << "\n";
        }
        else {
            out << " ";
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l(c.lit(i));
            if (!c.coeff(i).is_one()) {
                out << c.coeff(i) << "*";
            }
            out << l;
            if (values) {
                out << "@(" << ctx.get_assignment(l);
                if (ctx.get_assignment(l) != l_undef) {
                    out << ":" << ctx.get_assign_level(l);
                }
                out << ")";
            }
            if (i + 1 < c.size()) {
                out << " + ";
            }
        }
        out << " >= " << c.m_k  << "\n";
        if (c.m_num_propagations)    out << "propagations: " << c.m_num_propagations << " ";
        if (c.max_coeff().is_pos())  out << "max_coeff: "   << c.max_coeff() << " ";
        if (c.watch_size())          out << "watch size: "  << c.watch_size() << " ";
        if (c.max_sum().is_pos())    out << "max-sum: "     << c.max_sum() << " ";
        if (c.m_num_propagations || c.max_coeff().is_pos() || c.watch_size() || c.max_sum().is_pos()) out << "\n";
        return out;
    }


    literal_vector& theory_pb::get_lits() {
        m_literals.reset();
        return m_literals;
    }

    class theory_pb::pb_justification : public theory_propagation_justification {
        ineq& m_ineq;
    public:
        pb_justification(ineq& c, family_id fid, region & r, 
                      unsigned num_lits, literal const * lits, literal consequent):
                      theory_propagation_justification(fid, r, num_lits, lits, consequent),
                      m_ineq(c)
                      {}
        ineq& get_ineq() { return m_ineq; }
    };

    void theory_pb::add_assign(ineq& c, literal_vector const& lits, literal l) {
        inc_propagations(c);
        m_stats.m_num_propagations++;
        context& ctx = get_context();
        TRACE("pb", tout << "#prop:" << c.m_num_propagations << " - "; 
              for (unsigned i = 0; i < lits.size(); ++i) {
                  tout << lits[i] << " ";
              }
              tout << "=> " << l << "\n";
              display(tout, c, true););

        ctx.assign(l, ctx.mk_justification(
                       pb_justification(
                           c, get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), l)));
    }
    
                   

    void theory_pb::add_clause(ineq& c, literal_vector const& lits) {
        inc_propagations(c);
        m_stats.m_num_conflicts++;
        context& ctx = get_context();
        TRACE("pb", tout << "#prop:" << c.m_num_propagations << " - "; 
              for (unsigned i = 0; i < lits.size(); ++i) {
                  tout << lits[i] << " ";
              }
              tout << "\n";
              display(tout, c, true););

        resolve_conflict(c);

        justification* js = 0;
        ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, 0);
        IF_VERBOSE(2, ctx.display_literals_verbose(verbose_stream(), lits.size(), lits.c_ptr());
                   verbose_stream() << "\n";);
    }

    void theory_pb::set_mark(bool_var v, unsigned idx) {
        SASSERT(v != null_bool_var);
        if (v >= static_cast<bool_var>(m_conseq_index.size())) {
            m_conseq_index.resize(v+1, null_index);
        }
        SASSERT(!is_marked(v) || m_conseq_index[v] == idx);
        m_conseq_index[v] = idx;        
    }

    bool theory_pb::is_marked(bool_var v) const {
        return 
            (v < static_cast<bool_var>(m_conseq_index.size())) &&
            (m_conseq_index[v] != null_index);
    }

    void theory_pb::unset_mark(literal l) {
        bool_var v = l.var();
        SASSERT(v != null_bool_var);
        if (v < static_cast<bool_var>(m_conseq_index.size())) {
            m_conseq_index[v] = null_index;
        }
    }

    void theory_pb::process_antecedent(literal l, numeral coeff) {        
        context& ctx = get_context();
        bool_var v = l.var();
        unsigned lvl = ctx.get_assign_level(v);

        if (ctx.get_assignment(l) != l_false) {
            m_lemma.m_k -= coeff;
        }
        else if (lvl > ctx.get_base_level()) {
            if (is_marked(v)) {
                m_lemma.m_args[m_conseq_index[v]].second += coeff;
            }
            else {                
                if (lvl == m_conflict_lvl) {
                    TRACE("pb", tout << "add mark: " << l << " " << coeff << "\n";);
                    ++m_num_marks;
                }
                set_mark(v, m_lemma.size());
                m_lemma.m_args.push_back(std::make_pair(l, coeff));
            }
            TRACE("pb_verbose", tout  
                  << "ante: " << m_lemma.lit(m_conseq_index[v]) << "*" 
                  << m_lemma.coeff(m_conseq_index[v]) << " " << lvl << "\n";);
        }
    }

    void theory_pb::process_ineq(ineq& c, literal conseq, numeral coeff1) {

        //
        // Create CUT.
        //

        // 
        // . find coeff2
        // . find lcm of coefficients to conseq.
        // . multiply m_lemma by lcm/coeff coefficient to align.
        // . create lcm/coeff_2 to multiply on this side.
        // . cut resolve constraints.
        // 

        context& ctx = get_context();
        numeral coeff2 = (conseq==null_literal)?numeral::one():numeral::zero();
        for (unsigned i = 0; i < c.size(); ++i) {
            if (c.lit(i) == conseq) {
                coeff2 = c.coeff(i);
                break;
            }
        }
        SASSERT(coeff2.is_pos());
        numeral lc = lcm(coeff1, coeff2);
        numeral g = lc/coeff1;
        SASSERT(g.is_int());
        if (g > numeral::one()) {
            for (unsigned i = 0; i < m_lemma.size(); ++i) {
                m_lemma.m_args[i].second *= g;
            }
            m_lemma.m_k *= g;
        }
        g = lc/coeff2;
        SASSERT(g.is_int());
        m_lemma.m_k += g*c.k();

        for (unsigned i = 0; i < c.size(); ++i) {
            process_antecedent(c.lit(i), g*c.coeff(i));
        }

        SASSERT(ctx.get_assignment(c.lit()) == l_true);
        if (ctx.get_assign_level(c.lit()) > ctx.get_base_level()) {
            m_ineq_literals.push_back(c.lit());
        }
    }

    //
    // modeled after sat_solver/smt_context
    //
    bool theory_pb::resolve_conflict(ineq& c) {
        
        TRACE("pb", display(tout, c, true););

        bool_var v;
        literal conseq;
        context& ctx = get_context();
        unsigned& lvl = m_conflict_lvl = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            if (ctx.get_assignment(c.lit(i)) == l_false) {
                lvl = std::max(lvl, ctx.get_assign_level(c.lit(i)));
            }
        }
        if (lvl < ctx.get_assign_level(c.lit()) || lvl == ctx.get_base_level()) {
            return false;
        }

        m_num_marks = 0;
        m_lemma.reset();
        m_ineq_literals.reset();
        process_ineq(c, null_literal, numeral::one()); // add consequent to lemma.

        // point into stack of assigned literals
        literal_vector const& lits = ctx.assigned_literals();        
        SASSERT(!lits.empty());
        unsigned idx = lits.size()-1;
   
        while (m_num_marks > 0) {

            m_lemma.normalize();
            SASSERT(m_lemma.well_formed());         

            //
            // find the next marked variable in the assignment stack
            //
            do {
                conseq = lits[idx];
                v = conseq.var();
                --idx;
            }
            while (!is_marked(v));

            unsigned conseq_index = m_conseq_index[v];
            numeral conseq_coeff = m_lemma.coeff(conseq_index);

            TRACE("pb", display(tout, m_lemma, true);
                  tout << "conseq: " << conseq << " at index: " << conseq_index << "\n";);

            SASSERT(~conseq == m_lemma.lit(conseq_index));

            // Remove conseq from lemma:
            unsigned last = m_lemma.size()-1;
            if (conseq_index != last) {
                m_lemma.m_args[conseq_index] = m_lemma.m_args[last];
                m_conseq_index[m_lemma.lit(conseq_index).var()] = conseq_index;
            }
            m_lemma.m_args.pop_back();
            unset_mark(conseq);

            --m_num_marks;
            b_justification js = ctx.get_justification(v);

            //
            // Resolve selected conseq with antecedents.
            // 

            switch(js.get_kind()) {
                
            case b_justification::CLAUSE: {
                clause& cls = *js.get_clause();
                justification* cjs = cls.get_justification();
                if (cjs) {
                    IF_VERBOSE(0, verbose_stream() << "skipping justification for clause over: " << conseq << "\n";);
                    m_ineq_literals.push_back(conseq);
                    break;
                }
                unsigned num_lits = cls.get_num_literals();
                if (cls.get_literal(0) == conseq) {
                    process_antecedent(cls.get_literal(1), conseq_coeff);
                }
                else {
                    SASSERT(cls.get_literal(1) == conseq);
                    process_antecedent(cls.get_literal(0), conseq_coeff);
                }
                for (unsigned i = 2; i < num_lits; ++i) {
                    process_antecedent(cls.get_literal(i), conseq_coeff);
                }
                TRACE("pb", for (unsigned i = 0; i < num_lits; ++i) tout << cls.get_literal(i) << " "; tout << "\n";);
                break;                
            }
            case b_justification::BIN_CLAUSE:
                process_antecedent(~js.get_literal(), conseq_coeff);
                TRACE("pb", tout << "binary: " << js.get_literal() << "\n";);
                break;
            case b_justification::AXIOM:
                if (ctx.get_assign_level(v) > ctx.get_base_level()) {
                    m_ineq_literals.push_back(conseq);
                }
                TRACE("pb", tout << "axiom " << conseq << "\n";);
                break;
            case b_justification::JUSTIFICATION: {
                justification& j = *js.get_justification(); 
                // only process pb justifications.
                if (j.get_from_theory() != get_id()) {
                    IF_VERBOSE(0, verbose_stream() << "skipping justification for theory " << conseq << "\n";);
                    IF_VERBOSE(0, verbose_stream() << j.get_from_theory() << "\n";);
                    m_ineq_literals.push_back(conseq);
                    break;
                }
                pb_justification& pbj = dynamic_cast<pb_justification&>(j);
                // weaken the lemma and resolve.
                TRACE("pb", display(tout, pbj.get_ineq(), true););
                process_ineq(pbj.get_ineq(), conseq, conseq_coeff);
                break;
            }
            default:
                UNREACHABLE();
            }            
        }


        for (unsigned i = 0; i < m_lemma.size(); ++i) {
            unset_mark(m_lemma.lit(i));
        }

        TRACE("pb", 
              for (unsigned i = 0; i < m_ineq_literals.size(); ++i) {
                  tout << m_ineq_literals[i] << " ";
              }
              display(tout << "=> ", m_lemma););

        hoist_maximal_values();

        lbool is_true = m_lemma.normalize();

        IF_VERBOSE(1, display(verbose_stream() << "lemma: ", m_lemma););
        switch(is_true) {
        case l_true:
            UNREACHABLE();
            return false;
        case l_false:
            //add_assign(c, m_ineq_literals, false_literal);
            //break;
        default: {
            app_ref tmp = m_lemma.to_expr(ctx, get_manager());
            internalize_atom(tmp, false);
            ctx.mark_as_relevant(tmp);
            literal l(ctx.get_bool_var(tmp));
            add_assign(c, m_ineq_literals, l);
            break;
        }
        }
        return true;    
    }

    void theory_pb::hoist_maximal_values() {
        for (unsigned i = 0; i < m_lemma.size(); ++i) {
            if (m_lemma.coeff(i) == m_lemma.k()) {
                m_ineq_literals.push_back(~m_lemma.lit(i));
                std::swap(m_lemma.m_args[i], m_lemma.m_args[m_lemma.size()-1]);
                m_lemma.m_args.pop_back();
                --i;
            }
        }
    }
}
