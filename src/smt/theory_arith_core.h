/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_core.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-04-22.

Revision History:

--*/
#ifndef THEORY_ARITH_CORE_H_
#define THEORY_ARITH_CORE_H_

#include"smt_context.h"
#include"theory_arith.h"
#include"ast_pp.h"
#include"ast_ll_pp.h" 
#include"smt_model_generator.h"
#include"ast_smt2_pp.h"

namespace smt {
    
    template<typename Ext>
    void theory_arith<Ext>::found_unsupported_op(app * n) {
        if (!m_found_unsupported_op) {
            TRACE("arith", tout << "found non supported expression:\n" << mk_pp(n, get_manager()) << "\n";);
            get_context().push_trail(value_trail<context, bool>(m_found_unsupported_op));
            m_found_unsupported_op = true;
        }
    }

    template<typename Ext>
    bool theory_arith<Ext>::process_atoms() const {
        if (!adaptive())
            return true;
        unsigned total_conflicts = get_context().get_num_conflicts();
        if (total_conflicts < 10)
            return true;
        double f = static_cast<double>(get_num_conflicts())/static_cast<double>(total_conflicts);
        TRACE_CODE({
            static unsigned counter = 0;
            counter++;
            if (counter % 1000 == 0) {
                TRACE("arith_adaptive", tout << "arith_conflicts: " << get_num_conflicts() << " total_conflicts: " << total_conflicts << " factor: " << f << "\n";);
            }
        });
        return f >= adaptive_assertion_threshold();
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::mk_var(enode * n) {
        theory_var r = theory::mk_var(n);
        SASSERT(r == static_cast<int>(m_columns.size()));
        SASSERT(check_vector_sizes());
        bool is_int  = m_util.is_int(n->get_owner());
        TRACE("mk_arith_var", tout << mk_pp(n->get_owner(), get_manager()) << " is_int: " << is_int << "\n";);
        m_columns          .push_back(column());
        m_data             .push_back(var_data(is_int));
        if (random_initial_value()) {
            unsigned val = (m_random()%(random_upper() - random_lower())) + random_lower();
            m_value        .push_back(inf_numeral(val));
        }
        else {
            m_value        .push_back(inf_numeral());
        }
        m_old_value        .push_back(inf_numeral());
        SASSERT(m_var_occs.size() == static_cast<unsigned>(r));
        m_var_occs         .push_back(atoms());
        SASSERT(m_var_occs.back().empty());
        m_unassigned_atoms .push_back(0);
        m_var_pos          .push_back(-1);
        m_bounds[0]        .push_back(0);
        m_bounds[1]        .push_back(0);
        if (r >= static_cast<int>(m_to_patch.get_bounds()))
            m_to_patch.set_bounds(r + 1);
        m_in_update_trail_stack.assure_domain(r);
        m_left_basis.assure_domain(r);
        m_in_to_check.assure_domain(r);
        if (is_pure_monomial(n->get_owner()))
            m_nl_monomials.push_back(r);
        SASSERT(check_vector_sizes());
        SASSERT(m_var_occs[r].empty());
        TRACE("mk_arith_var", 
              tout << "#" << n->get_owner_id() << " :=\n" << mk_ll_pp(n->get_owner(), get_manager()) << "\n";
              tout << "is_attached_to_var: " << is_attached_to_var(n) << ", var: " << n->get_th_var(get_id()) << "\n";);
        get_context().attach_th_var(n, this, r);
        SASSERT(m_var_occs.back().empty());
        return r;
    }

    template<typename Ext>
    inline bool theory_arith<Ext>::reflection_enabled() const {
        return m_params.m_arith_reflect;
    }

    template<typename Ext>
    inline bool theory_arith<Ext>::reflect(app * n) const {
        if (reflection_enabled())
            return true; // reflect everything
        // Every underspecified operator must be reflected in the egraph.
        // Although it is underspecified, it is still a function.
        // For example, a/b != a/0 then we must have b != 0
        // I use the Egraph to enforce that.
        if (n->get_family_id() == get_id()) {
            switch (n->get_decl_kind()) {
            case OP_DIV:
            case OP_IDIV:
            case OP_REM:
            case OP_MOD:
                return true;
            default:
                break;
            }
        }
        return false;
    }

    template<typename Ext>
    inline bool theory_arith<Ext>::enable_cgc_for(app * n) const {
        // Congruence closure is not enabled for (+ ...) and (* ...) applications.
        return !(n->get_family_id() == get_id() && (n->get_decl_kind() == OP_ADD || n->get_decl_kind() == OP_MUL));
    }

    /**
       \brief Create an enode for n. 
    */
    template<typename Ext>
    enode * theory_arith<Ext>::mk_enode(app * n) {
        context & ctx = get_context();
        if (ctx.e_internalized(n)) 
            return ctx.get_enode(n);
        else
            return ctx.mk_enode(n, !reflect(n), false, enable_cgc_for(n));       
    }

    /**
       \brief Create an enode for n if reflection is enabled.
    */
    template<typename Ext>
    void theory_arith<Ext>::mk_enode_if_reflect(app * n) {
        if (reflection_enabled()) {
            // make sure that n is in the e-graph
            mk_enode(n);
        }
    }

    /**
       \brief Add coeff * v to the row r.
       The column is also updated.
    */
    template<typename Ext>
    template<bool invert>
    void theory_arith<Ext>::add_row_entry(unsigned r_id, numeral const & coeff, theory_var v) {
        row    & r          = m_rows[r_id];
        column & c          = m_columns[v];
        int r_idx;
        row_entry & r_entry = r.add_row_entry(r_idx);
        int c_idx;
        col_entry & c_entry = c.add_col_entry(c_idx);
    
        r_entry.m_var       = v;
        r_entry.m_coeff     = coeff;
        if (invert)
            r_entry.m_coeff .neg();
        r_entry.m_col_idx   = c_idx;
        
        c_entry.m_row_id    = r_id;
        c_entry.m_row_idx   = r_idx;
    }

    /**
       \brief Internalize the monomial of a polynomial. Store the monomial in the given row.
       The monomial is negated before being inserted into the row.
    */
    template<typename Ext>
    void theory_arith<Ext>::internalize_internal_monomial(app * m, unsigned r_id) {
        context & ctx = get_context();
        if (ctx.e_internalized(m)) {
            enode * e    = ctx.get_enode(m);
            if (is_attached_to_var(e)) {
                // there is already a theory variable (i.e., name) for m.
                theory_var v = e->get_th_var(get_id());
                add_row_entry<false>(r_id, numeral::minus_one(), v);
                return;
            }
        }
        rational _val; 
        if (m_util.is_mul(m) && m_util.is_numeral(m->get_arg(0), _val)) {
            SASSERT(m->get_num_args() == 2);
            numeral val(_val);
            theory_var v = internalize_term_core(to_app(m->get_arg(1)));
            if (reflection_enabled()) {
                internalize_term_core(to_app(m->get_arg(0)));
                mk_enode(m);
            }
            add_row_entry<true>(r_id, val, v);
        }
        else {
            theory_var v = internalize_term_core(m);
            add_row_entry<false>(r_id, numeral::minus_one(), v);
        }
    }

    /**
       \brief Internalize a polynomial (+ h t). Return an alias for the monomial, that is,
       a variable v such that v = (+ h t) is a new row in the tableau.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_add(app * n) {
        TRACE("add_bug", tout << "n: " << mk_pp(n, get_manager()) << "\n";);
        CTRACE("internalize_add_bug", n->get_num_args() == 2 && n->get_arg(0) == n->get_arg(1), tout << "n: " << mk_pp(n, get_manager()) << "\n";);
        SASSERT(m_util.is_add(n));
        unsigned r_id = mk_row();
        unsigned num_args = n->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            internalize_internal_monomial(to_app(n->get_arg(i)), r_id);
        }
        enode * e = mk_enode(n);
        theory_var v = e->get_th_var(get_id());
        if (v == null_theory_var) {
            v = mk_var(e);
            add_row_entry<false>(r_id, numeral::one(), v);
            init_row(r_id);
        }
        else {
            // HACK: n was already internalized by the internalize_internal_monomial or internalize_internal_add call above.
            // This can happen when one of calls invoke (indirectly) mk_axiom.
            // For example, they contain a nested to_int(t) term.
            // TODO: reimplement mk_axiom. The current implementation is flaky. 
            // I should cache the axioms that need to be created. They should only be internalized after we finished internalizing the
            // current atom. Several other theories have similar problems.
            del_row(r_id);
        }
        return v;
    }

    /**
       \brief Internalize a term (* x y z) that does not contain a coefficient (numeral).
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_mul_core(app * m) {
        TRACE("internalize_mul_core", tout << "internalizing...\n" << mk_pp(m,get_manager()) << "\n";);
        if (!m_util.is_mul(m))
            return internalize_term_core(m);
        for (unsigned i = 0; i < m->get_num_args(); i++) {
            app * arg = to_app(m->get_arg(i));
            SASSERT(!m_util.is_numeral(arg));
            theory_var v = internalize_term_core(arg);
            if (v == null_theory_var) {
                mk_var(mk_enode(arg));
            }
        }
        enode * e    = mk_enode(m);
        theory_var v = e->get_th_var(get_id());
        if (v == null_theory_var) {
            v = mk_var(e);
        }
        return v;
    }

    /**
       \brief Internalize the terms of the form (* c (* t1 ... tn)) and (* t1 ... tn). 
       Return an alias for the term.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_mul(app * m) {
        rational _val;
        SASSERT(m_util.is_mul(m));
        if (m_util.is_numeral(m->get_arg(0), _val)) {
            SASSERT(m->get_num_args() == 2);
            numeral val(_val);
            SASSERT(!val.is_one());
            unsigned r_id = mk_row();
            if (reflection_enabled())
                internalize_term_core(to_app(m->get_arg(0)));
            theory_var v = internalize_mul_core(to_app(m->get_arg(1)));
            add_row_entry<true>(r_id, val, v);
            enode * e      = mk_enode(m);
            theory_var s   = mk_var(e);
            add_row_entry<false>(r_id, numeral::one(), s);
            init_row(r_id);
            return s;
        }
        else {
            return internalize_mul_core(m);
        }
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::mk_binary_op(app * n) {
        SASSERT(n->get_num_args() == 2);
        context & ctx     = get_context();
        if (ctx.e_internalized(n))
            return expr2var(n);
        ctx.internalize(n->get_arg(0), false);
        ctx.internalize(n->get_arg(1), false);
        enode * e         = mk_enode(n); 
        return mk_var(e);
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_div(app * n) {
        theory_var s      = mk_binary_op(n);
        context & ctx     = get_context();
        if (!ctx.relevancy())
            mk_div_axiom(n->get_arg(0), n->get_arg(1));
        return s;
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_idiv(app * n) {
        theory_var s      = mk_binary_op(n);
        context & ctx     = get_context();
        app * mod         = m_util.mk_mod(n->get_arg(0), n->get_arg(1));
        ctx.internalize(mod, false);
        if (ctx.relevancy())
            ctx.add_relevancy_dependency(n, mod);
        return s;
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_mod(app * n) {
        TRACE("arith_mod", tout << "internalizing...\n" << mk_pp(n, get_manager()) << "\n";);
        theory_var s      = mk_binary_op(n);
        context & ctx     = get_context();
        if (!ctx.relevancy())
            mk_idiv_mod_axioms(n->get_arg(0), n->get_arg(1));
        return s;
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_rem(app * n) {
        theory_var s  = mk_binary_op(n);
        context & ctx = get_context();
        if (!ctx.relevancy()) {
            mk_rem_axiom(n->get_arg(0), n->get_arg(1));
        }
        return s;
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_axiom(expr * ante, expr * conseq) {
        ast_manager & m = get_manager();
        context & ctx   = get_context();
        simplifier & s  = ctx.get_simplifier();
        expr_ref s_ante(m), s_conseq(m);
        expr* s_conseq_n, * s_ante_n;
        bool negated;
        proof_ref pr(m);

        s(ante, s_ante, pr);
        negated = m.is_not(s_ante, s_ante_n);
        if (negated) s_ante = s_ante_n;
        ctx.internalize(s_ante, false);
        literal l_ante = ctx.get_literal(s_ante);
        if (negated) l_ante.neg();

        s(conseq, s_conseq, pr);
        negated = m.is_not(s_conseq, s_conseq_n);
        if (negated) s_conseq = s_conseq_n;
        ctx.internalize(s_conseq, false);
        literal l_conseq = ctx.get_literal(s_conseq);
        if (negated) l_conseq.neg();

        TRACE("arith_axiom", tout << mk_pp(ante, m) << "\n" << mk_pp(conseq, m) << "\n";
              tout << s_ante << "\n" << s_conseq << "\n";);

        literal lits[2] = {l_ante, l_conseq};
        ctx.mk_th_axiom(get_id(), 2, lits);
        if (ctx.relevancy()) {
            if (l_ante == false_literal) {
                ctx.mark_as_relevant(l_conseq);
            }
            else {
                // We must mark the antecedent as relevant, otherwise the 
                // core will not propagate it to the theory of arithmetic.
                // In a previous version, we were not doing that.
                // The core was assigning it to true, this assignment was inconsistent with
                // the state of the theory of arithmetic, but the conflict was not detected
                // because it was not propagated to this theory.
                ctx.mark_as_relevant(l_ante);
                ctx.add_rel_watch(~l_ante, s_conseq); // mark consequent as relevant if antecedent is false.
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_div_axiom(expr * p, expr * q) {
        if (!m_util.is_zero(q)) {
            ast_manager & m    = get_manager();
            expr_ref div(m), zero(m), eqz(m), eq(m);
            TRACE("div_axiom_bug", tout << "expanding div_axiom for: " << mk_pp(p, m) << " / " << mk_pp(q, m) << "\n";); 
            div         = m_util.mk_div(p, q);
            zero        = m_util.mk_numeral(rational(0), false);
            eqz         = m.mk_eq(q, zero);
            eq          = m.mk_eq(m_util.mk_mul(q, div), p);
            TRACE("div_axiom_bug", tout << "eqz: " << mk_pp(eqz, m) << "\neq: " << mk_pp(eq, m) << "\n";);
            mk_axiom(eqz, eq);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_idiv_mod_axioms(expr * dividend, expr * divisor) {
        if (!m_util.is_zero(divisor)) {
            // if divisor is zero, then idiv and mod are uninterpreted functions.
            ast_manager & m = get_manager();
            expr_ref div(m), mod(m), zero(m), abs_divisor(m);
            expr_ref eqz(m), eq(m), lower(m), upper(m);
            div         = m_util.mk_idiv(dividend, divisor);
            mod         = m_util.mk_mod(dividend, divisor);
            zero        = m_util.mk_numeral(rational(0), true);
            abs_divisor = m.mk_ite(m_util.mk_lt(divisor, zero), m_util.mk_sub(zero, divisor), divisor);
            eqz         = m.mk_eq(divisor, zero);
            eq          = m.mk_eq(m_util.mk_add(m_util.mk_mul(divisor, div), mod), dividend);
            lower       = m_util.mk_le(zero, mod);
            upper       = m_util.mk_lt(mod, abs_divisor);
            TRACE("div_axiom_bug", 
                  tout << "eqz:   " << mk_pp(eqz, m) << "\neq: " << mk_pp(eq, m) << "\n";
                  tout << "lower: " << mk_pp(lower, m) << "\n";
                  tout << "upper: " << mk_pp(upper, m) << "\n";);

            mk_axiom(eqz, eq);
            mk_axiom(eqz, lower);
            mk_axiom(eqz, upper);
            rational k;
            if (m_params.m_arith_enum_const_mod && m_util.is_numeral(divisor, k) && 
                k.is_pos() && k < rational(8)) {
                rational j(0);
#if 1
                literal_buffer lits;
                expr_ref mod_j(m);
                context& ctx = get_context();
                while(j < k) {
                    mod_j = m.mk_eq(mod, m_util.mk_numeral(j, true));
                    ctx.internalize(mod_j, false);
                    literal lit(ctx.get_literal(mod_j));
                    lits.push_back(lit);
                    ctx.mark_as_relevant(lit);
                    j += rational(1);
                }
                ctx.mk_th_axiom(get_id(), lits.size(), lits.begin());
                
#else
                // performs slightly worse.
                literal_buffer lits;
                expr_ref mod_j(m), div_j(m), num_j(m), n_mod_j(m), n_div_j(m);
                context& ctx = get_context();
                while(j < k) {
                    num_j = m_util.mk_numeral(j, true);
                    mod_j = m.mk_eq(mod, num_j);
                    div_j = m.mk_eq(dividend, m_util.mk_add(m_util.mk_mul(div, divisor), num_j));
                    n_mod_j = m.mk_not(mod_j);
                    n_div_j = m.mk_not(div_j);
                    mk_axiom(n_mod_j, div_j);
                    mk_axiom(n_div_j, mod_j);
                    j += rational(1);
                }
#endif
            }            
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_rem_axiom(expr * dividend, expr * divisor) {
        // if divisor is zero, then rem is an uninterpreted function.
        ast_manager & m    = get_manager();
        expr * zero        = m_util.mk_numeral(rational(0), true);
        expr * rem         = m_util.mk_rem(dividend, divisor);
        expr * mod         = m_util.mk_mod(dividend, divisor);
        expr_ref dltz(m), eq1(m), eq2(m);
        dltz               = m_util.mk_lt(divisor, zero);
        eq1                = m.mk_eq(rem, mod);
        eq2                = m.mk_eq(rem, m_util.mk_sub(zero, mod));
        // n < 0 || rem(a,n) = mod(a, n)
        mk_axiom(dltz, eq1);
        dltz               = m.mk_not(dltz);
        // !n < 0 || rem(a,n) = -mod(a, n)
        mk_axiom(dltz, eq2);        
    }

    //
    // create the term: s := to_real(to_int(x)) - x
    // add the bounds 0 <= s < 1   
    //
    template<typename Ext>
    void theory_arith<Ext>::mk_to_int_axiom(app * n) {
        SASSERT(m_util.is_to_int(n));
        ast_manager & m    = get_manager();
        expr* x = n->get_arg(0);

        // to_int (to_real x) = x
        if (m_util.is_to_real(x)) {
            mk_axiom(m.mk_false(), m.mk_eq(to_app(x)->get_arg(0), n));
            return;
        }
        expr* to_r = m_util.mk_to_real(n);
        expr_ref lo(m_util.mk_le(to_r, x), m);
        expr_ref hi(m_util.mk_lt(x, m_util.mk_add(to_r, m_util.mk_numeral(rational(1), false))), m);
        mk_axiom(m.mk_false(), lo);
        mk_axiom(m.mk_false(), hi);
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_to_int(app * n) {
        SASSERT(n->get_num_args() == 1);
        context & ctx     = get_context();
        if (ctx.e_internalized(n))
            return expr2var(n);
        /* theory_var arg = */ internalize_term_core(to_app(n->get_arg(0)));
        enode * e      = mk_enode(n);
        theory_var r   = mk_var(e);
        if (!ctx.relevancy())
            mk_to_int_axiom(n);
        return r;
    }

    //
    // Create the axiom (iff (is_int x) (= x (to_real (to_int x))))
    // 

    template<typename Ext>
    void theory_arith<Ext>::mk_is_int_axiom(app * n) {
        SASSERT(m_util.is_is_int(n));
        ast_manager & m    = get_manager();
        expr* x = n->get_arg(0);
        expr* eq = m.mk_eq(m_util.mk_to_real(m_util.mk_to_int(x)), x);
        mk_axiom(m.mk_not(n), eq);
        mk_axiom(m.mk_not(eq), n);
    }

    template<typename Ext>
    void theory_arith<Ext>::internalize_is_int(app * n) {
        SASSERT(n->get_num_args() == 1);
        context & ctx     = get_context();
        if (ctx.b_internalized(n))
            return;
        /* theory_var arg = */ internalize_term_core(to_app(n->get_arg(0)));
        enode * e      = mk_enode(n);
        /* theory_var r   = */ mk_var(e);
        if (!ctx.relevancy())
            mk_is_int_axiom(n);
    }


    // create the row: r - arg = 0
    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_to_real(app * n) {
        SASSERT(n->get_num_args() == 1);
        context & ctx     = get_context();
        if (ctx.e_internalized(n))
            return expr2var(n);
        TRACE("to_real_bug", tout << "to-real\n" << mk_ismt2_pp(n, get_manager()) << "\n";);
        theory_var arg = internalize_term_core(to_app(n->get_arg(0)));
        // n may be internalized by the call above if n is of the form (to_real (to_int t))
        // The internalizer for (to_int t) will create (to_real (to_int t)) and internalize it.
        // This is a recurrent bug in Z3. TODO: I should create a queue of axioms that need to be asserted.
        // This queue is processes only after we finish the internalization of the current assertion.
        if (ctx.e_internalized(n))
            return expr2var(n);
        enode * e      = mk_enode(n);
        theory_var r   = mk_var(e);
        unsigned r_id = mk_row();
        add_row_entry<true>(r_id, numeral(1), arg);
        add_row_entry<false>(r_id, numeral(1), r);
        init_row(r_id);
        return r;
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_numeral(app * n) {
        rational _val;
        VERIFY(m_util.is_numeral(n, _val));
        numeral val(_val);
        SASSERT(!get_context().e_internalized(n));
        enode * e    = mk_enode(n);
        // internalizer is marking enodes as interpreted whenever the associated ast is a value and a constant.
        // e->mark_as_interpreted();
        theory_var v = mk_var(e);
        inf_numeral ival(val);
        bound *    l = alloc(bound, v, ival, B_LOWER, false);
        bound *    u = alloc(bound, v, ival, B_UPPER, false);
        set_bound(l, false);
        set_bound(u, true);
        m_bounds_to_delete.push_back(l);
        m_bounds_to_delete.push_back(u);
        m_value[v]   = ival;
        return v;
    }

    /**
       \brief Internalize the given term and return an alias for it.
       Return null_theory_var if the term was not implemented by the theory yet.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::internalize_term_core(app * n) {
        TRACE("arith_internalize_detail", tout << "internalize_term_core:\n" << mk_pp(n, get_manager()) << "\n";);
        context & ctx = get_context();
        if (ctx.e_internalized(n)) {
            enode * e    = ctx.get_enode(n);
            if (is_attached_to_var(e))
                return e->get_th_var(get_id());
        }

        SASSERT(!m_util.is_sub(n));
        SASSERT(!m_util.is_uminus(n));
        
        if (m_util.is_add(n))
            return internalize_add(n);
        else if (m_util.is_mul(n))
            return internalize_mul(n);
        else if (m_util.is_div(n))
            return internalize_div(n);
        else if (m_util.is_idiv(n))
            return internalize_idiv(n);
        else if (m_util.is_mod(n)) 
            return internalize_mod(n);
        else if (m_util.is_rem(n)) 
            return internalize_rem(n);
        else if (m_util.is_to_real(n))
            return internalize_to_real(n);
        else if (m_util.is_to_int(n))
            return internalize_to_int(n);
        else if (m_util.is_numeral(n))
            return internalize_numeral(n);
        if (m_util.is_power(n)) {
            // unsupported
            found_unsupported_op(n);
            return mk_binary_op(n);
        }
        if (m_util.is_irrational_algebraic_numeral(n)) {
            // unsupported
            found_unsupported_op(n);
            enode * e = mk_enode(n);
            return mk_var(e);
        }
        else {
            TRACE("arith_internalize_detail", tout << "before:\n" << mk_pp(n, get_manager()) << "\n";);
            if (!ctx.e_internalized(n))
                ctx.internalize(n, false);
            TRACE("arith_internalize_detail", tout << "after:\n" << mk_pp(n, get_manager()) << "\n";);
            enode * e    = ctx.get_enode(n);
            if (!is_attached_to_var(e))
                return mk_var(e);
            else
                return e->get_th_var(get_id());
        }
    }

    /**
       \brief Create a new empty row. Return the new row id.
    */
    template<typename Ext>
    unsigned theory_arith<Ext>::mk_row() {
        unsigned r;
        if (m_dead_rows.empty()) {
            r = m_rows.size();
            m_rows.push_back(row());
        }
        else {
            r = m_dead_rows.back();
            m_dead_rows.pop_back();
        }
        m_in_to_check.assure_domain(r);
        SASSERT(m_rows[r].size() == 0);
        SASSERT(m_rows[r].num_entries() == 0);
        return r;
    }

    /**
       \brief Initialize a new row, the last monomial is going to be the owner of the row.
       The last monomial must have coeff 1.
    */
    template<typename Ext>
    void theory_arith<Ext>::init_row(unsigned r_id) {
        row & r = m_rows[r_id];
        SASSERT(r.m_first_free_idx == -1);
        SASSERT(r.size() != 0);
        SASSERT(r.size() == r.num_entries());
        SASSERT(r[r.size() - 1].m_coeff.is_one());
        theory_var s = r[r.size() - 1].m_var;
        r.m_base_var = s;
        set_var_row(s, r_id);
        TRACE("init_row_bug", tout << "before:\n"; display_row_info(tout, r););
        if (lazy_pivoting_lvl() > 2) {
            set_var_kind(s, QUASI_BASE);
            normalize_quasi_base_row(r_id);
            SASSERT(!has_var_kind(get_var_row(s), QUASI_BASE));
        }
        else {
            normalize_base_row(r_id);
            SASSERT(get_var_kind(s) == BASE);
            SASSERT(!has_var_kind(get_var_row(s), BASE));
        }
        TRACE("init_row_bug", tout << "after:\n"; display_row_info(tout, r););
        if (propagation_mode() != BP_NONE)
            mark_row_for_bound_prop(r_id);
        SASSERT(r.is_coeff_of(s, numeral::one()));
        SASSERT(wf_row(r_id));
    }

    /**
       \brief Collect variables in the given row that have the given kind,
       but a different from the row main var (i.e., var that owns the row).
       
       The inv of the coefficients is also stored in result
    */
    template<typename Ext>
    void theory_arith<Ext>::collect_vars(unsigned r_id, var_kind k, buffer<linear_monomial> & result) {
        row & r         = m_rows[r_id];
        theory_var base = r.m_base_var;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        unsigned idx = 0;
        for (; it != end; ++it, ++idx) {
            if (!it->is_dead() && get_var_kind(it->m_var) == k && it->m_var != base) {
                numeral c = it->m_coeff;
                c.neg();
                result.push_back(linear_monomial(c, it->m_var));
            }
        }
    }

    /**
       \brief Normalize row as a quasi base row, it does not contain quasi-base 
       variables different from r.m_base_var.
    */
    template<typename Ext>
    void theory_arith<Ext>::normalize_quasi_base_row(unsigned r_id) {
        buffer<linear_monomial> to_add;
        collect_vars(r_id, QUASI_BASE, to_add);
        add_rows(r_id, to_add.size(), to_add.c_ptr());
        SASSERT(!has_var_kind(r_id, QUASI_BASE));
    }

    /**
       \brief Convert a quasi-base row into a base row.
    */
    template<typename Ext>
    void theory_arith<Ext>::quasi_base_row2base_row(unsigned r_id) {
        TRACE("quasi_base_row2base_row", tout << "quasi_base_row2base_row...\n";);
        buffer<linear_monomial> to_add;
        collect_vars(r_id, BASE, to_add);
        TRACE("quasi_base_bug_detail",
              display_row_info(tout, r_id);
              for (unsigned i = 0; i < to_add.size(); i++) {
                  theory_var v = to_add[i].m_var;
                  SASSERT(is_base(v));
                  SASSERT(!has_var_kind(get_var_row(v), BASE));
                  tout << "coeff: " << to_add[i].m_coeff << ", var: #" << get_enode(v)->get_owner_id() << "\n";
                  display_row_info(tout, get_var_row(v));
                  tout << "\n";
              });
        add_rows(r_id, to_add.size(), to_add.c_ptr());
        theory_var s = m_rows[r_id].get_base_var();
        set_var_kind(s, BASE);
        inf_numeral tmp;
        if (get_implied_old_value(s, tmp)) {
            // This code is necessary because of the method
            // restore_assignment.  That is, the invariant
            // valid_row_assignment() could be invalidated when
            // restore_assignment is executed.
            //
            // Remark: The method restore_assignment will restore the
            // old value of variables, and the value of s should be
            // compatible with them.
            //
            // For example, consider the following scenario:
            //
            // 1) s is a quasi-base var, s depends on x, and value of x is v0
            // 
            // 2) x is updated to v1, but the update does not affect s (s is a quasi-base var).
            //
            // 3) quasi_base_row2base_row is executed, and we compute the value of s using
            // the current value of x (v1).
            //
            // 4) a conflict is detected, and the value of x is restored to v0.
            //
            // 5) if this branch is deleted, the row owned by s will not satisfy
            // valid_row_assignment.
            // 
            m_value[s] = tmp;
            SASSERT(!m_in_update_trail_stack.contains(s));
            save_value(s);
        }
        m_value[s]   = get_implied_value(s);
        TRACE("valid_row_assignment_bug", display_row_info(tout, r_id););
        SASSERT(!has_var_kind(r_id, BASE));
        SASSERT(!has_var_kind(r_id, QUASI_BASE));
        SASSERT(valid_row_assignment(m_rows[r_id]));
    }

    /**
       \brief Normalize row as a base row. A base row does not contain quasi-base and base
       variables different from r.m_base_var.
    */
    template<typename Ext>
    void theory_arith<Ext>::normalize_base_row(unsigned r_id) {
        if (lazy_pivoting_lvl() > 0)
            normalize_quasi_base_row(r_id);
        quasi_base_row2base_row(r_id);
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_clause(literal l1, literal l2, unsigned num_params, parameter * params) {
        get_context().mk_th_axiom(get_id(), l1, l2, num_params, params);
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_clause(literal l1, literal l2, literal l3, unsigned num_params, parameter * params) {
        get_context().mk_th_axiom(get_id(), l1, l2, l3, num_params, params);
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_bound_axioms(atom * a1) {
        theory_var v = a1->get_var();
        atoms & occs = m_var_occs[v];
        //SASSERT(v != 15);
        TRACE("mk_bound_axioms", tout << "add bound axioms for v" << v << " " << a1 << "\n";);
        if (!get_context().is_searching()) {
            //
            // NB. We make an assumption that user push calls propagation 
            // before internal scopes are pushed. This flushes all newly 
            // asserted atoms into the right context.
            //
            m_new_atoms.push_back(a1);
            return;
        }
        inf_numeral const & k1(a1->get_k());
        atom_kind kind1 = a1->get_atom_kind();
        TRACE("mk_bound_axioms", display_atom(tout << "making bound axioms for " << a1 << " ", a1, true); tout << "\n";);
        typename atoms::iterator it  = occs.begin();
        typename atoms::iterator end = occs.end();

        typename atoms::iterator lo_inf = end, lo_sup = end;
        typename atoms::iterator hi_inf = end, hi_sup = end;
        for (; it != end; ++it) {
            atom * a2 = *it;            
            inf_numeral const & k2(a2->get_k());
            atom_kind kind2 = a2->get_atom_kind();
            TRACE("mk_bound_axioms", display_atom(tout << "compare " << a2 << " ", a2, true); tout << "\n";);

            if (k1 == k2 && kind1 == kind2) {
                continue;
            }

            SASSERT(k1 != k2 || kind1 != kind2);
            if (kind2 == A_LOWER) {
                if (k2 < k1) {
                    if (lo_inf == end || k2 > (*lo_inf)->get_k()) {
                        lo_inf = it;
                    }
                }
                else if (lo_sup == end || k2 < (*lo_sup)->get_k()) {
                    lo_sup = it;
                }
            }
            else if (k2 < k1) {
                if (hi_inf == end || k2 > (*hi_inf)->get_k()) {
                    hi_inf = it;
                }
            }
            else if (hi_sup == end || k2 < (*hi_sup)->get_k()) {
                hi_sup = it;
            }
        }        
        if (lo_inf != end) mk_bound_axiom(a1, *lo_inf);
        if (lo_sup != end) mk_bound_axiom(a1, *lo_sup);
        if (hi_inf != end) mk_bound_axiom(a1, *hi_inf);
        if (hi_sup != end) mk_bound_axiom(a1, *hi_sup);
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_bound_axiom(atom* a1, atom* a2) {
        TRACE("mk_bound_axioms", tout << a1 << " " << a2 << "\n";);
        theory_var v = a1->get_var();
        literal   l1(a1->get_bool_var()); 
        literal   l2(a2->get_bool_var()); 
        inf_numeral const & k1(a1->get_k());
        inf_numeral const & k2(a2->get_k());
        atom_kind kind1 = a1->get_atom_kind();
        atom_kind kind2 = a2->get_atom_kind();
        bool v_is_int = is_int(v);
        SASSERT(v == a2->get_var());
        if (k1 == k2 && kind1 == kind2) return;
        SASSERT(k1 != k2 || kind1 != kind2);
        parameter coeffs[3] = { parameter(symbol("farkas")), 
                                parameter(rational(1)), parameter(rational(1)) };

        if (kind1 == A_LOWER) {
            if (kind2 == A_LOWER) {
                if (k2 <= k1) {
                    mk_clause(~l1, l2, 3, coeffs);
                }
                else {
                    mk_clause(l1, ~l2, 3, coeffs);
                }
            }
            else if (k1 <= k2) {
                // k1 <= k2, k1 <= x or x <= k2
                mk_clause(l1, l2, 3, coeffs);
            }
            else {
                // k1 > hi_inf, k1 <= x => ~(x <= hi_inf)
                mk_clause(~l1, ~l2, 3, coeffs);
                if (v_is_int && k1 == k2 + inf_numeral(1)) {
                    // k1 <= x or x <= k1-1
                    mk_clause(l1, l2, 3, coeffs);
                }
            }
        }
        else if (kind2 == A_LOWER) {
            if (k1 >= k2) {
                // k1 >= lo_inf, k1 >= x or lo_inf <= x
                mk_clause(l1, l2, 3, coeffs);
            }
            else {
                // k1 < k2, k2 <= x => ~(x <= k1)
                mk_clause(~l1, ~l2, 3, coeffs); 
                if (v_is_int && k1 == k2 - inf_numeral(1)) {
                    // x <= k1 or k1+l <= x
                    mk_clause(l1, l2, 3, coeffs);
                }

            }
        }
        else {
            // kind1 == A_UPPER, kind2 == A_UPPER
            if (k1 >= k2) {
                // k1 >= k2, x <= k2 => x <= k1
                mk_clause(l1, ~l2, 3, coeffs);
            }
            else {
                // k1 <= hi_sup , x <= k1 =>  x <= hi_sup
                mk_clause(~l1, l2, 3, coeffs);
            }
        }        
    }

    template<typename Ext>
    void theory_arith<Ext>::flush_bound_axioms() {
        CTRACE("arith", !m_new_atoms.empty(), tout << "flush bound axioms\n";);

        while (!m_new_atoms.empty()) {
            ptr_vector<atom> atoms;            
            atoms.push_back(m_new_atoms.back());
            m_new_atoms.pop_back();
            theory_var v = atoms.back()->get_var();
            for (unsigned i = 0; i < m_new_atoms.size(); ++i) {
                if (m_new_atoms[i]->get_var() == v) {
                    atoms.push_back(m_new_atoms[i]);
                    m_new_atoms[i] = m_new_atoms.back();
                    m_new_atoms.pop_back();
                    --i;
                }
            }            
            TRACE("arith", 
                  for (unsigned i = 0; i < atoms.size(); ++i) {
                      atoms[i]->display(*this, tout);
                  });
            ptr_vector<atom> occs(m_var_occs[v]);

            std::sort(atoms.begin(), atoms.end(), compare_atoms());
            std::sort(occs.begin(), occs.end(), compare_atoms());

            typename atoms::iterator begin1 = occs.begin();
            typename atoms::iterator begin2 = occs.begin();
            typename atoms::iterator end = occs.end();
            begin1 = first(A_LOWER, begin1, end);
            begin2 = first(A_UPPER, begin2, end);

            typename atoms::iterator lo_inf = begin1, lo_sup = begin1;
            typename atoms::iterator hi_inf = begin2, hi_sup = begin2;
            typename atoms::iterator lo_inf1 = begin1, lo_sup1 = begin1;
            typename atoms::iterator hi_inf1 = begin2, hi_sup1 = begin2;
            bool flo_inf, fhi_inf, flo_sup, fhi_sup;
            ptr_addr_hashtable<atom> visited;
            for (unsigned i = 0; i < atoms.size(); ++i) {
                atom* a1 = atoms[i];
                lo_inf1 = next_inf(a1, A_LOWER, lo_inf, end, flo_inf);
                hi_inf1 = next_inf(a1, A_UPPER, hi_inf, end, fhi_inf);
                lo_sup1 = next_sup(a1, A_LOWER, lo_sup, end, flo_sup);
                hi_sup1 = next_sup(a1, A_UPPER, hi_sup, end, fhi_sup);
                if (lo_inf1 != end) lo_inf = lo_inf1; 
                if (lo_sup1 != end) lo_sup = lo_sup1; 
                if (hi_inf1 != end) hi_inf = hi_inf1; 
                if (hi_sup1 != end) hi_sup = hi_sup1; 
                if (!flo_inf) lo_inf = end;
                if (!fhi_inf) hi_inf = end;
                if (!flo_sup) lo_sup = end;
                if (!fhi_sup) hi_sup = end;
                visited.insert(a1);
                if (lo_inf1 != end && lo_inf != end && !visited.contains(*lo_inf)) mk_bound_axiom(a1, *lo_inf);
                if (lo_sup1 != end && lo_sup != end && !visited.contains(*lo_sup)) mk_bound_axiom(a1, *lo_sup);
                if (hi_inf1 != end && hi_inf != end && !visited.contains(*hi_inf)) mk_bound_axiom(a1, *hi_inf);
                if (hi_sup1 != end && hi_sup != end && !visited.contains(*hi_sup)) mk_bound_axiom(a1, *hi_sup);
            }                            
        }
    }

    template<typename Ext>
    typename theory_arith<Ext>::atoms::iterator 
    theory_arith<Ext>::first(
        atom_kind kind, 
        typename atoms::iterator it, 
        typename atoms::iterator end) {
        for (; it != end; ++it) {
            atom* a = *it;
            if (a->get_atom_kind() == kind) return it;
        }
        return end;
    }

    template<typename Ext>
    typename theory_arith<Ext>::atoms::iterator 
    theory_arith<Ext>::next_inf(
        atom* a1, 
        atom_kind kind, 
        typename atoms::iterator it, 
        typename atoms::iterator end,
        bool& found_compatible) {
        inf_numeral const & k1(a1->get_k());
        typename atoms::iterator result = end;
        found_compatible = false;
        for (; it != end; ++it) {
            atom * a2 = *it;            
            if (a1 == a2) continue;
            if (a2->get_atom_kind() != kind) continue;
            inf_numeral const & k2(a2->get_k());
            found_compatible = true;
            if (k2 <= k1) {
                result = it;
            }
            else {
                break;
            }
        }
        return result;
    }

    template<typename Ext>
    typename theory_arith<Ext>::atoms::iterator 
    theory_arith<Ext>::next_sup(
        atom* a1, 
        atom_kind kind, 
        typename atoms::iterator it, 
        typename atoms::iterator end,
        bool& found_compatible) {
        inf_numeral const & k1(a1->get_k());
        found_compatible = false;
        for (; it != end; ++it) {
            atom * a2 = *it;            
            if (a1 == a2) continue;
            if (a2->get_atom_kind() != kind) continue;
            inf_numeral const & k2(a2->get_k());
            found_compatible = true;
            if (k1 < k2) {
                return it;
            }
        }
        return end;
    }


    template<typename Ext>
    bool theory_arith<Ext>::internalize_atom(app * n, bool gate_ctx) {
        TRACE("arith_internalize", tout << "internalising atom:\n" << mk_pp(n, this->get_manager()) << "\n";);
        context & ctx = get_context();
        SASSERT(m_util.is_le(n) || m_util.is_ge(n) || m_util.is_is_int(n));
        SASSERT(!ctx.b_internalized(n));
        atom_kind kind;

        if (m_util.is_is_int(n)) {
            internalize_is_int(n);
            if (ctx.b_internalized(n)) {
                TRACE("arith_internalize", tout << "term was re-internalized: #" << n->get_id() << "\n";);
                return true;
            }
            bool_var bv    = ctx.mk_bool_var(n);
            ctx.set_var_theory(bv, get_id());
            return true;
        }
        if (m_util.is_le(n))
            kind = A_UPPER;
        else
            kind = A_LOWER;
        app * lhs      = to_app(n->get_arg(0));
        app * rhs      = to_app(n->get_arg(1));
        SASSERT(m_util.is_numeral(rhs));
        theory_var v   = internalize_term_core(lhs);
        if (v == null_theory_var) {
            TRACE("arith_internalize", tout << "failed to internalize: #" << n->get_id() << "\n";);
            return false;
        }
        if (ctx.b_internalized(n)) {
            TRACE("arith_internalize", tout << "term was re-internalized: #" << n->get_id() << "\n";);
            return true;
        }
        bool_var bv    = ctx.mk_bool_var(n);
        ctx.set_var_theory(bv, get_id());
        rational _k;
        VERIFY(m_util.is_numeral(rhs, _k));
        inf_numeral   k(_k);
        atom * a = alloc(atom, bv, v, k, kind);
        mk_bound_axioms(a);
        m_unassigned_atoms[v]++;
        atoms & occs   = m_var_occs[v];
        occs.push_back(a);
        m_atoms.push_back(a);
        insert_bv2a(bv, a);
        TRACE("arith_internalize", tout << "succeeded... v" << v << " " << kind << " " << k << "\n";
              for (unsigned i = 0; i + 1 < occs.size(); ++i) tout << occs[i] << "\n";);
        return true;
    }

    template<typename Ext>
    bool theory_arith<Ext>::internalize_term(app * term) {
        TRACE("arith_internalize", tout << "internalising term:\n" << mk_pp(term, this->get_manager()) << "\n";);
        theory_var v = internalize_term_core(term);
        TRACE("arith_internalize", tout << "theory_var: " << v << "\n";);
        return v != null_theory_var;
    }

    template<typename Ext>
    void theory_arith<Ext>::internalize_eq_eh(app * atom, bool_var v) {
        if (m_params.m_arith_eager_eq_axioms) {
            context & ctx  = get_context();
            app * lhs      = to_app(atom->get_arg(0));
            app * rhs      = to_app(atom->get_arg(1));
            enode * n1 = ctx.get_enode(lhs);
            enode * n2 = ctx.get_enode(rhs);
            // The expression atom may be a theory axiom. In this case, it may not be in simplified form.
            // So, an atom such as (= a a) may occur. The procedure mk_axioms, expects n1 != n2. 
            // So, we should check it. It doesn't make sense to create an axiom for (= a a) in the arith_eq_adapter.
            if (n1->get_th_var(get_id()) != null_theory_var &&
                n2->get_th_var(get_id()) != null_theory_var &&
                n1 != n2) {
                TRACE("mk_axioms_bug", tout << mk_bounded_pp(atom, get_manager(), 5) << "\n";);
                m_arith_eq_adapter.mk_axioms(n1, n2);
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::apply_sort_cnstr(enode * n, sort * s) {
        // do nothing...
    }
    
    template<typename Ext>
    void theory_arith<Ext>::assign_eh(bool_var v, bool is_true) {
        TRACE("arith", tout << "p" << v << " := " << (is_true?"true":"false") << "\n";);
        atom * a = get_bv2a(v);
        if (!a) return;
        SASSERT(get_context().get_assignment(a->get_bool_var()) != l_undef);
        SASSERT((get_context().get_assignment(a->get_bool_var()) == l_true) == is_true);
        a->assign_eh(is_true, get_epsilon(a->get_var()));
        m_asserted_bounds.push_back(a);
    }

    template<typename Ext>
    void theory_arith<Ext>::relevant_eh(app * n) {
        TRACE("arith_relevant_eh", tout << "relevant_eh: " << mk_pp(n, get_manager()) << "\n";);
        if (m_util.is_mod(n)) 
            mk_idiv_mod_axioms(n->get_arg(0), n->get_arg(1));
        else if (m_util.is_rem(n))
            mk_rem_axiom(n->get_arg(0), n->get_arg(1));
        else if (m_util.is_div(n)) 
            mk_div_axiom(n->get_arg(0), n->get_arg(1));
        else if (m_util.is_to_int(n)) 
            mk_to_int_axiom(n);
        else if (m_util.is_is_int(n))
            mk_is_int_axiom(n);
    }

    template<typename Ext>
    void theory_arith<Ext>::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE("arith_new_eq_eh", tout << "#" << get_enode(v1)->get_owner_id() << " = #" << get_enode(v2)->get_owner_id() << "\n";);
        TRACE("arith_new_eq_eh_detail", tout << mk_pp(get_enode(v1)->get_owner(), get_manager()) << "\n" << 
              mk_pp(get_enode(v2)->get_owner(), get_manager()) << "\n";);

        enode * n1 = get_enode(v1);
                
        if (!m_util.is_int(n1->get_owner()) && 
            !m_util.is_real(n1->get_owner())) {
            return;
        }
        if (m_params.m_arith_eq_bounds) {  
            enode * n2 = get_enode(v2);
            SASSERT(n1->get_root() == n2->get_root());
            if (m_util.is_numeral(n1->get_owner())) {
                std::swap(v1, v2);
                std::swap(n1, n2);
            }
            rational k;
            bound * b1 = 0;
            bound * b2 = 0;
            if (m_util.is_numeral(n2->get_owner(), k)) {
                inf_numeral val(k);
                b1 = alloc(eq_bound, v1, val, B_LOWER, n1, n2);
                b2 = alloc(eq_bound, v1, val, B_UPPER, n1, n2);
            }
            else {
                if (n1->get_owner_id() > n2->get_owner_id())
                    std::swap(n1, n2);
                sort * st       = get_manager().get_sort(n1->get_owner());
                app * minus_one = m_util.mk_numeral(rational::minus_one(), st);
                app * s         = m_util.mk_add(n1->get_owner(), m_util.mk_mul(minus_one, n2->get_owner()));
                context & ctx   = get_context();
                ctx.internalize(s, false);
                enode * e_s     = ctx.get_enode(s);
                ctx.mark_as_relevant(e_s);
                SASSERT(is_attached_to_var(e_s));
                theory_var v_s  = e_s->get_th_var(get_id());
                b1 = alloc(eq_bound, v_s, inf_numeral::zero(), B_LOWER, n1, n2);
                b2 = alloc(eq_bound, v_s, inf_numeral::zero(), B_UPPER, n1, n2);
            }
            m_bounds_to_delete.push_back(b1);
            m_bounds_to_delete.push_back(b2);
            m_asserted_bounds.push_back(b1);
            m_asserted_bounds.push_back(b2);
        }
        else {
            m_arith_eq_adapter.new_eq_eh(v1, v2);
        }
    }

    template<typename Ext>
    bool theory_arith<Ext>::use_diseqs() const {
        return true;
    }

    template<typename Ext>
    void theory_arith<Ext>::new_diseq_eh(theory_var v1, theory_var v2) {
        TRACE("arith_new_diseq_eh", tout << mk_bounded_pp(get_enode(v1)->get_owner(), get_manager()) << "\n" << 
              mk_bounded_pp(get_enode(v2)->get_owner(), get_manager()) << "\n";);
        m_stats.m_assert_diseq++;
        m_arith_eq_adapter.new_diseq_eh(v1, v2);
    }

    template<typename Ext>
    void theory_arith<Ext>::restart_eh() {
        m_arith_eq_adapter.restart_eh();
    }

    template<typename Ext>
    void theory_arith<Ext>::init_search_eh() {
        TRACE("arith_init_search", display(tout););
        m_num_conflicts      = 0;
        m_branch_cut_counter = 0;
        m_eager_gcd          = m_params.m_arith_eager_gcd;
        if (lazy_pivoting_lvl() == 1)
            elim_quasi_base_rows();
        move_unconstrained_to_base();
        m_arith_eq_adapter.init_search_eh();
        m_final_check_idx    = 0;
        m_nl_gb_exhausted    = false;
        m_nl_strategy_idx    = 0;
    }

    template<typename Ext>
    final_check_status theory_arith<Ext>::final_check_core() {
        unsigned old_idx = m_final_check_idx;
        final_check_status result = FC_DONE;
        final_check_status ok;
        do {
            TRACE("final_check_arith", tout << "m_final_check_idx: " << m_final_check_idx << ", result: " << result << "\n";);
            switch (m_final_check_idx) {
            case 0:
                ok = check_int_feasibility();
                TRACE("final_check_arith", tout << "check_int_feasibility(), ok: " << ok << "\n";);
                break;
            case 1:
                if (assume_eqs_core())
                    ok = FC_CONTINUE;
                else
                    ok = FC_DONE;
                TRACE("final_check_arith", tout << "assume_eqs(), ok: " << ok << "\n";);
                break;
            default:
                ok = process_non_linear();
                TRACE("final_check_arith", tout << "non_linear(), ok: " << ok << "\n";);
                break;
            }
            m_final_check_idx = (m_final_check_idx + 1) % 3;
            switch (ok) {
            case FC_DONE:
                break;
            case FC_GIVEUP:
                result = FC_GIVEUP;
                break;
            case FC_CONTINUE:
                TRACE("final_check_arith", 
                      tout << "continue arith..." 
                      << (get_context().inconsistent()?"inconsistent\n":"\n"););
                return FC_CONTINUE;
            }
        }
        while (m_final_check_idx != old_idx);
        if (result == FC_DONE && m_found_unsupported_op) {
            TRACE("arith", tout << "Found unsupported operation\n";);
            result = FC_GIVEUP;
        }
        return result;
    }

    template<typename Ext>
    final_check_status theory_arith<Ext>::final_check_eh() {
        TRACE("arith_eq_adapter_info", m_arith_eq_adapter.display_already_processed(tout););
        TRACE("arith_final_check", display(tout););

        if (!propagate_core()) 
            return FC_CONTINUE; 
        if (delayed_assume_eqs())
            return FC_CONTINUE;
        get_context().push_trail(value_trail<context, unsigned>(m_final_check_idx));
        m_liberal_final_check = true;
        m_changed_assignment  = false;
        final_check_status result = final_check_core();
        if (result != FC_DONE)
            return result;
        if (!m_changed_assignment)
            return FC_DONE;
        m_liberal_final_check = false;
        m_changed_assignment  = false;
        result = final_check_core();
        TRACE("final_check_arith", tout << "result: " << result << "\n";);
        return result;
    }
    
    template<typename Ext>
    bool theory_arith<Ext>::can_propagate() {
        return process_atoms() && m_asserted_qhead < m_asserted_bounds.size();
    }
    
    template<typename Ext>
    void theory_arith<Ext>::propagate() {
        TRACE("arith_propagate", tout << "propagate\n"; display(tout););
        if (!process_atoms())
            return;
        propagate_core();
    }

    template<typename Ext>
    bool theory_arith<Ext>::propagate_core() {
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        
        flush_bound_axioms();
        propagate_linear_monomials();
        while (m_asserted_qhead < m_asserted_bounds.size()) {
            bound * b = m_asserted_bounds[m_asserted_qhead];
            m_asserted_qhead++;
            if (!assert_bound(b)) {
                failed();
                return false; 
            }
        }
        if (!make_feasible()) {
            failed();
            return false;
        }
        if (get_context().get_cancel_flag()) {
            return true;
        }
        CASSERT("arith", satisfy_bounds());
        discard_update_trail();

        SASSERT(m_update_trail_stack.empty());

        propagate_bounds();
        SASSERT(m_asserted_qhead == m_asserted_bounds.size());
        SASSERT(m_update_trail_stack.empty());

        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        CASSERT("arith", satisfy_bounds());
        return true;
    }
    
    template<typename Ext>
    void theory_arith<Ext>::failed() {
        restore_assignment();
        m_to_patch.reset();
        m_to_check.reset();
        m_in_to_check.reset();
    } 
    
    template<typename Ext>
    void theory_arith<Ext>::flush_eh() {
        std::for_each(m_atoms.begin(), m_atoms.end(), delete_proc<atom>());
        m_atoms.reset();
        std::for_each(m_bounds_to_delete.begin(), m_bounds_to_delete.end(), delete_proc<bound>());
        m_bounds_to_delete.reset();
    }
    
    template<typename Ext>
    void theory_arith<Ext>::reset_eh() {
        m_stats.reset();
        m_rows                   .reset();
        m_arith_eq_adapter       .reset_eh();
        m_dead_rows              .reset();
        m_columns                .reset();
        m_data                   .reset();
        m_value                  .reset();
        m_old_value              .reset();
        m_bounds[0]              .reset();
        m_bounds[1]              .reset();
        m_var_occs               .reset();
        m_unassigned_atoms       .reset();
        m_bool_var2atom          .reset();
        m_var_pos                .reset();
        std::for_each(m_atoms.begin(), m_atoms.end(), delete_proc<atom>());
        m_atoms                  .reset();
        std::for_each(m_bounds_to_delete.begin(), m_bounds_to_delete.end(), delete_proc<bound>());
        m_bounds_to_delete.reset();
        m_asserted_bounds        .reset();
        m_asserted_qhead         = 0;
        m_to_patch               .reset();
        m_left_basis             .reset();
        m_blands_rule            = false;
        m_update_trail_stack     .reset();
        m_in_update_trail_stack  .reset();
        m_to_check               .reset();
        m_in_to_check            .reset();
        m_num_conflicts          = 0;
        m_bound_trail            .reset();
        m_unassigned_atoms_trail .reset();
        m_scopes                 .reset();
        m_nl_monomials           .reset();
        m_nl_propagated          .reset();
        m_nl_rounds              = 0;
        m_nl_gb_exhausted        = false;
        m_nl_strategy_idx        = 0;
        theory::reset_eh();
    }

    template<typename Ext>
    bool theory_arith<Ext>::validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
        return true;
    }

    /**
       \brief Compute the value of a base or quasi-base variable using
       the value of the dependent variables.
    */
    template<typename Ext>
    typename theory_arith<Ext>::inf_numeral const & theory_arith<Ext>::get_implied_value(theory_var v) const {
        SASSERT(is_quasi_base(v) || is_base(v));
        inf_numeral & sum = const_cast<theory_arith<Ext> *>(this)->m_tmp;
        sum.reset();
        unsigned r_id = get_var_row(v);
        row const & r   = m_rows[r_id];
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && it->m_var != v) {
                SASSERT(!is_quasi_base(it->m_var));
                SASSERT(get_value(it->m_var) == m_value[it->m_var]);
                sum += it->m_coeff * get_value(it->m_var);
            }
        }
        sum.neg();
        return sum;
    }

    /**
       \brief Compute the value of a base or quasi-base variable using
       the old value of the dependent variables. By old, we mean the
       value of the variable in the beginning of propagate(). Store the
       result in 'result'.

       Return true if the old value is different from the current value.
    */
    template<typename Ext>
    bool theory_arith<Ext>::get_implied_old_value(theory_var v, inf_numeral & result) const {
        SASSERT(is_quasi_base(v) || is_base(v));
        bool is_diff = false;
        result.reset();
        unsigned r_id = get_var_row(v);
        row const & r   = m_rows[r_id];
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && it->m_var != v) {
                theory_var v2 = it->m_var;
                SASSERT(!is_quasi_base(v2));
                SASSERT(get_value(v2) == m_value[v2]);
                if (m_in_update_trail_stack.contains(v2)) {
                    result += it->m_coeff * m_old_value[v2];
                    is_diff = true;
                }
                else {
                    result += it->m_coeff * m_value[v2];
                }
            }
        }
        result.neg();
        return is_diff;
    }
    
    template<typename Ext>
    theory_arith<Ext>::theory_arith(ast_manager & m, theory_arith_params & params):
        theory(m.mk_family_id("arith")),
        m_params(params),
        m_util(m),
        m_arith_eq_solver(m),
        m_found_unsupported_op(false),
        m_arith_eq_adapter(*this, params, m_util),
        m_asserted_qhead(0),
        m_to_patch(1024),
        m_blands_rule(false),
        m_random(params.m_arith_random_seed),
        m_num_conflicts(0),
        m_branch_cut_counter(0),
        m_eager_gcd(m_params.m_arith_eager_gcd),
        m_final_check_idx(0),
        m_antecedents_index(0),
        m_var_value_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)),
        m_liberal_final_check(true),
        m_changed_assignment(false),
        m_assume_eq_head(0),
        m_nl_rounds(0),
        m_nl_gb_exhausted(false),
        m_nl_new_exprs(m),
        m_bound_watch(null_bool_var) {
    }

    template<typename Ext>
    theory_arith<Ext>::~theory_arith() {
    }

    template<typename Ext>
    theory* theory_arith<Ext>::mk_fresh(context* new_ctx) { 
        return alloc(theory_arith<Ext>, new_ctx->get_manager(), m_params); 
    }

    template<typename Ext>
    void theory_arith<Ext>::setup() {
        m_random.set_seed(m_params.m_arith_random_seed);
        theory::setup();
    }

    // -----------------------------------
    //
    // Add Row
    //
    // -----------------------------------
    
    /**
       \brief Set: row1 <- row1 + coeff * row2
    */
    template<typename Ext>
    void theory_arith<Ext>::add_row(unsigned rid1, const numeral & coeff, unsigned rid2, bool apply_gcd_test) {
        m_stats.m_add_rows++;
        if (propagation_mode() != BP_NONE)
            mark_row_for_bound_prop(rid1);
        row & r1 = m_rows[rid1];
        row & r2 = m_rows[rid2];
        CASSERT("row_assignment_bug", valid_row_assignment(r1));
        CASSERT("row_assignment_bug", valid_row_assignment(r2));
        r1.compress_if_needed(m_columns);
        r2.compress_if_needed(m_columns);
        CASSERT("arith", check_null_var_pos());

        r1.save_var_pos(m_var_pos);

        // 
        // loop over variables in row2,
        // add terms in row2 to row1.
        //
#define ADD_ROW(_SET_COEFF_, _ADD_COEFF_)                                       \
    typename vector<row_entry>::const_iterator it  = r2.begin_entries();        \
    typename vector<row_entry>::const_iterator end = r2.end_entries();          \
    for (; it != end; ++it) {                                                   \
        if (!it->is_dead()) {                                                   \
            theory_var v = it->m_var;                                           \
            int pos  = m_var_pos[v];                                            \
            if (pos == -1) {                                                    \
                /* variable v is not in row1 */                                 \
                int row_idx;                                                    \
                row_entry & r_entry = r1.add_row_entry(row_idx);                \
                r_entry.m_var         = v;                                      \
                _SET_COEFF_;                                                    \
                column & c            = m_columns[v];                           \
                int col_idx;                                                    \
                col_entry & c_entry   = c.add_col_entry(col_idx);               \
                r_entry.m_col_idx     = col_idx;                                \
                c_entry.m_row_id      = rid1;                                   \
                c_entry.m_row_idx     = row_idx;                                \
            }                                                                   \
            else {                                                              \
                /* variable v is in row1 */                                     \
                row_entry & r_entry   = r1[pos];                                \
                SASSERT(r_entry.m_var == v);                                    \
                _ADD_COEFF_;                                                    \
                if (r_entry.m_coeff.is_zero()) {                                \
                    int col_idx = r_entry.m_col_idx;                            \
                    r1.del_row_entry(pos);                                      \
                    column & c        = m_columns[v];                           \
                    c.del_col_entry(col_idx);                                   \
                }                                                               \
                m_var_pos[v] = -1;                                              \
            }                                                                   \
        }                                                                       \
    } ((void) 0)

        if (coeff.is_one()) {
            ADD_ROW(r_entry.m_coeff  = it->m_coeff,
                    r_entry.m_coeff += it->m_coeff);
        }
        else if (coeff.is_minus_one()) {
            ADD_ROW(r_entry.m_coeff  = it->m_coeff; r_entry.m_coeff.neg(),
                    r_entry.m_coeff -= it->m_coeff);
        }
        else {
            ADD_ROW(r_entry.m_coeff = it->m_coeff; r_entry.m_coeff *= coeff, 
                    r_entry.m_coeff += it->m_coeff * coeff);
        }
        
        r1.reset_var_pos(m_var_pos);
        CASSERT("arith", check_null_var_pos());
        CASSERT("row_assignment_bug", valid_row_assignment(r1));
        CASSERT("row_assignment_bug", valid_row_assignment(r2));
        if (apply_gcd_test) {
            theory_var v = r1.get_base_var();
            if (is_int(v) && !get_value(v).is_int())
                gcd_test(r1);
        }
    }

    /**
       \brief Set r1 <- r1 + a_xs[0].m_coeff * get_var_row(a_xs[0].m_var) + ... + a_xs[0].m_coeff * get_var_row(a_xs[sz-1].m_var)
       
       \pre For all i in [0..sz-1]. not is_non_base(a_xs[i])
    */
    template<typename Ext>
    void theory_arith<Ext>::add_rows(unsigned r1, unsigned sz, linear_monomial * a_xs) {
        if (sz == 0) 
            return;
        for (unsigned i = 0; i < sz; i++) {
            linear_monomial & m = a_xs[i];
            numeral c           = m.m_coeff;
            theory_var v        = m.m_var;
            SASSERT(!is_non_base(v));
            add_row(r1, c, get_var_row(v), false);
        }
    }

    // -----------------------------------
    //
    // Assignment management
    //
    // -----------------------------------

    template<typename Ext>
    void theory_arith<Ext>::save_value(theory_var v) {
        SASSERT(!is_quasi_base(v));
        if (!m_in_update_trail_stack.contains(v)) {
            m_in_update_trail_stack.insert(v);
            SASSERT(m_value[v] == get_value(v));
            m_old_value[v] = m_value[v];
            m_update_trail_stack.push_back(v);
            TRACE("save_value", tout << "v" << v << " = " << get_value(v) << "\n";);
        }
        m_changed_assignment = true;
    }
    
    template<typename Ext>
    void theory_arith<Ext>::discard_update_trail() {
        m_in_update_trail_stack.reset();
        m_update_trail_stack.reset();
    }

    template<typename Ext>
    void theory_arith<Ext>::restore_assignment() {
        CASSERT("arith", valid_row_assignment());
        TRACE("restore_assignment_bug", tout << "START restore_assignment...\n";);
        typename svector<unsigned>::iterator it  = m_update_trail_stack.begin();
        typename svector<unsigned>::iterator end = m_update_trail_stack.end();
        for(; it != end; ++it) {
            theory_var v = *it;
            TRACE("restore_assignment_bug", tout << "restoring v" << v << " <- " << m_old_value[v] << "\n";);
            SASSERT(!is_quasi_base(v));
            SASSERT(m_in_update_trail_stack.contains(v));
            m_value[v] = m_old_value[v];
        }
        m_update_trail_stack.reset();
        m_in_update_trail_stack.reset();
        CASSERT("arith", valid_row_assignment());
    }

    /**
       \brief m_value[v] += delta
    */
    template<typename Ext>
    void theory_arith<Ext>::update_value_core(theory_var v, inf_numeral const & delta) {
        save_value(v);
        m_value[v] += delta;
        if (is_base(v) && !m_to_patch.contains(v) && (below_lower(v) || above_upper(v))) {
            m_to_patch.insert(v);
        }
    }

    /**
       \brief m_value[v] += delta, and update dependent (non-base) variables. 
    */
    template<typename Ext>
    void theory_arith<Ext>::update_value(theory_var v, inf_numeral const & delta) {
        update_value_core(v, delta);
        
        column & c = m_columns[v];
        c.compress_if_needed(m_rows);
    
        inf_numeral delta2;
        typename svector<col_entry>::const_iterator it  = c.begin_entries();
        typename svector<col_entry>::const_iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                row & r      = m_rows[it->m_row_id];
                theory_var s = r.get_base_var();
                if (s != null_theory_var && !is_quasi_base(s)) {
                    delta2   = delta;
                    delta2  *= r[it->m_row_idx].m_coeff;
                    delta2.neg();
                    update_value_core(s, delta2);
                }
            }
        }
    }

    // -----------------------------------
    //
    // Pivoting
    //
    // -----------------------------------

    /**
       \brief Make x_j the new base variable for row of x_i
       x_j is assumed to have coefficient a_ij.

       Let row_id = m_base_var[x_i]

       rows[row_id] <- rows[row_id] / a_ij

       rows[other] <- row[other] - rows[row_id] * a_kj
       Where a_kj is the coefficient of x_j in row[other]
    */
    template<typename Ext>
    template<bool Lazy>
    void theory_arith<Ext>::pivot(theory_var x_i, theory_var x_j, numeral const & a_ij, bool apply_gcd_test) {
        TRACE("arith_pivot", tout << "pivoting: v" << x_i << ", v" << x_j << "\n";);
        m_stats.m_pivots++;
        SASSERT(is_base(x_i) || is_quasi_base(x_i));
        SASSERT(x_i != x_j);

        int r_id = get_var_row(x_i);
        row & r  = m_rows[r_id];
        
        SASSERT(r.is_coeff_of(x_j, a_ij));

#define DIVIDE_ROW(_ADJUST_COEFF_)                                      \
    typename vector<row_entry>::iterator it  = r.begin_entries();       \
    typename vector<row_entry>::iterator end = r.end_entries();         \
    for (; it != end; ++it) {                                           \
        if (!it->is_dead()) {                                           \
            _ADJUST_COEFF_;                                             \
        }                                                               \
    } ((void) 0)

        if (a_ij.is_minus_one()) {
            DIVIDE_ROW(it->m_coeff.neg());
        }
        else if (!a_ij.is_one()) {
            numeral tmp = a_ij;
            DIVIDE_ROW(it->m_coeff /= tmp);
        }

        set_var_row(x_i, -1);
        set_var_row(x_j, r_id);
        
        SASSERT(r.m_base_var == x_i);
        r.m_base_var  = x_j;

        set_var_kind(x_i, NON_BASE);
        set_var_kind(x_j, BASE);
    
        eliminate<Lazy>(x_j, apply_gcd_test);

        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        TRACE("arith_pivot", tout << "after pivoting:\n";
              display(tout););
        TRACE("pivot_shape", display_rows_shape(tout););
        TRACE("pivot_stats", display_rows_stats(tout););
        TRACE_CODE({
            static unsigned val = 0;
            val ++;
            if (val % 100 == 0) {
                TRACE("pivot_bignums", display_rows_bignums(tout););
            }});
    }

    /**
       \brief Eliminate x_i from the rows different from get_var_row(x_i)
       
       If Lazy = true, then x_i is only eliminated from base rows.
    */
    template<typename Ext>
    template<bool Lazy>
    void theory_arith<Ext>::eliminate(theory_var x_i, bool apply_gcd_test) {
        SASSERT(is_base(x_i) || is_quasi_base(x_i));
        unsigned r_id = get_var_row(x_i);
        column & c    = m_columns[x_i];
        numeral a_kj;
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();
        int i     = 0;
        int s_pos = -1;
        for (; it != end; ++it, ++i) {
            if (!it->is_dead()) {
                if (it->m_row_id != static_cast<int>(r_id)) {
                    row & r2      = m_rows[it->m_row_id];
                    theory_var s2 = r2.m_base_var; 
                    if (s2 != null_theory_var && (!Lazy || is_base(s2))) {
                        a_kj = r2[it->m_row_idx].m_coeff;
                        a_kj.neg();
                        add_row(it->m_row_id, a_kj, r_id, apply_gcd_test);
                    }
                }
                else { 
                    s_pos = i;
                }
            }
        }
        CTRACE("eliminate", !Lazy && c.size() != 1, 
               tout << "eliminating v" << x_i << ", Lazy: " << Lazy << ", c.size: " << c.size() << "\n";
               display(tout););
        SASSERT(Lazy || c.size() == 1);
        if (c.size() == 1) {
            // When lazy pivoting is used, then after pivoting c may
            // not be a singleton
            c.compress_singleton(m_rows, s_pos);
        }
    }

    /**
       \brief Set x_j to be the new base variable of row
       owned by x_i

       a_ij        - coefficient of x_j in the row owned by x_i
       x_i_new_val - new value of x_i
    */
    template<typename Ext>
    void theory_arith<Ext>::update_and_pivot(theory_var x_i, theory_var x_j, numeral const & a_ij, inf_numeral const & x_i_new_val) {
        CASSERT("arith", valid_row_assignment());
        TRACE("update_and_pivot_bug_detail", display(tout););
        SASSERT(is_base(x_i));
        inf_numeral theta = m_value[x_i];
        TRACE("update_and_pivot_bug", tout << "theta 1) " << theta << " " << x_i_new_val << "\n";);
        theta -= x_i_new_val;
        TRACE("update_and_pivot_bug", tout << "theta 2) " << theta << " " << a_ij << "\n";);
        theta /= a_ij;
        TRACE("update_and_pivot_bug", tout << "theta 3) " << theta << "\n";);
        update_value(x_j, theta);
        CTRACE("arith", get_value(x_i) != x_i_new_val,
               tout << "x_i: " << x_i << ", x_j: " << x_j << ", a_ij: " << a_ij << ", x_i_new_val: " << x_i_new_val << "\n";
               tout << "new val: " << get_value(x_i) << ", theta: " << theta << "\n";
               display(tout););
        SASSERT(get_value(x_i) == x_i_new_val);
        if (!m_to_patch.contains(x_j) && (below_lower(x_j) || above_upper(x_j)))
            m_to_patch.insert(x_j);
        pivot<true>(x_i, x_j, a_ij, m_eager_gcd);
        CASSERT("arith", valid_row_assignment());
    }
    
    /**
       \brief Return the number of base variables that are non free and are v dependent.
       The function adds 1 to the result if v is non free.
       The function returns with a partial result r if r > best_so_far.
       This function is used to select the pivot variable.
    */
    template<typename Ext>
    int theory_arith<Ext>::get_num_non_free_dep_vars(theory_var v, int best_so_far) {
        int result = is_non_free(v);
        column & c = m_columns[v];
        typename svector<col_entry>::const_iterator it  = c.begin_entries();
        typename svector<col_entry>::const_iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                row & r      = m_rows[it->m_row_id];
                theory_var s = r.get_base_var();
                if (s != null_theory_var && is_base(s)) {
                    result += is_non_free(s);
                    if (result > best_so_far)
                        return result;
                }
            }
        }
        return result;
    }
    
    /**
       \brief Using Bland's rule, select a variable x_j in the row r defining the base var x_i, 
       s.t. x_j can be used to patch the error in x_i.  Return null_theory_var
       if there is no x_j. Otherwise, return x_j and store its coefficient
       in out_a_ij.
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::select_blands_pivot_core(theory_var x_i, bool is_below, numeral & out_a_ij) {
        SASSERT(is_base(x_i));
        theory_var max    = get_num_vars();
        theory_var result = max;
        row const & r     = m_rows[get_var_row(x_i)];
    
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {                                                                                   
            if (!it->is_dead()) {                                                                                   
                theory_var x_j       = it->m_var;                                                                             
                numeral const & a_ij = it->m_coeff;                
                bool is_neg = is_below ? a_ij.is_neg() : a_ij.is_pos();
                bool is_pos = !is_neg;                                                                              
                if (x_i != x_j && ((is_pos && above_lower(x_j)) || (is_neg && below_upper(x_j)))) {
                    SASSERT(is_non_base(x_j));
                    if (x_j < result) { 
                        result = x_j; 
                        out_a_ij = a_ij; 
                    }
                }
            }
        }
        return result < max ? result : null_theory_var;
    }
    
    /**
       \brief Select a variable x_j in the row r defining the base var x_i, 
       s.t. x_j can be used to patch the error in x_i.  Return null_theory_var
       if there is no x_j. Otherwise, return x_j and store its coefficient
       in out_a_ij.

       The argument is_below is true (false) if x_i is below its lower
       bound (above its upper bound).
    */
    template<typename Ext>
    template<bool is_below>
    theory_var theory_arith<Ext>::select_pivot_core(theory_var x_i, numeral & out_a_ij) {
        SASSERT(is_base(x_i));
        theory_var max    = get_num_vars();
        theory_var result = max;
        row const & r     = m_rows[get_var_row(x_i)];
        int n;
        int best_col_sz    = INT_MAX;
        int best_so_far    = INT_MAX;
        
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
    
        for (; it != end; ++it) {                                                                                   
            if (!it->is_dead()) {                                                                                   
                theory_var x_j       = it->m_var;                                                                             
                numeral const & a_ij = it->m_coeff;  
                                                               
                bool is_neg = is_below ? a_ij.is_neg() : a_ij.is_pos();
                bool is_pos = !is_neg;                                                                              
                if (x_i != x_j && ((is_pos && above_lower(x_j)) || (is_neg && below_upper(x_j)))) {                 
                    int num       = get_num_non_free_dep_vars(x_j, best_so_far);
                    int col_sz    = m_columns[x_j].size();
                    if (num < best_so_far || (num == best_so_far && col_sz < best_col_sz)) {
                        result        = x_j;
                        out_a_ij      = a_ij;
                        best_so_far   = num;
                        best_col_sz   = col_sz;
                        n             = 1;
                    } 
                    else if (num == best_so_far && col_sz == best_col_sz) {
                        n++;
                        if (m_random()%n == 0) {
                            result      = x_j;
                            out_a_ij    = a_ij;
                        }
                    }                              
                }
            }
        }
        return result < max ? result : null_theory_var;
    }
    
    /**
       \brief Wrapper for select_blands_pivot_core and select_pivot_core
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::select_pivot(theory_var x_i, bool is_below, numeral & out_a_ij) {
        TRACE("select_pivot", tout << "m_blands_rule: " << m_blands_rule << " v" << x_i << "\n";);
        CTRACE("select_pivot_info", x_i > 500, get_context().display(tout););
        if (m_blands_rule)
            return select_blands_pivot_core(x_i, is_below, out_a_ij);
        else if (is_below)
            return select_pivot_core<true>(x_i, out_a_ij);
        else
            return select_pivot_core<false>(x_i, out_a_ij);
    }

    // -----------------------------------
    //
    // Make feasible
    //
    // -----------------------------------
    
    /**
       \brief Make the given variable feasible.  This method assumes
       that x_i is a base var.  Return false if it was not possible to
       make x_i feasible.
    */
    template<typename Ext>
    bool theory_arith<Ext>::make_var_feasible(theory_var x_i) {
        CTRACE("arith_bug", !is_base(x_i), 
               tout << "x_i: " << x_i << ", below_lower(x_i): " << below_lower(x_i) << 
               ", above_upper(x_i): " << above_upper(x_i) << "\n"; display(tout););
        SASSERT(is_base(x_i));

        bool is_below;
        if (below_lower(x_i)) {
            is_below = true;
        }
        else if (above_upper(x_i)) {
            is_below = false;
        }
        else {
            // x_i is already feasible
            return true;
        }

        TRACE("make_var_feasible", display_row(tout, get_var_row(x_i), false););

        numeral a_ij;
        theory_var x_j = select_pivot(x_i, is_below, a_ij);
        if (x_j != null_theory_var) {
            SASSERT(is_base(x_i));
            TRACE("pivot_bug", display_row_info(tout, get_var_row(x_i)););
            update_and_pivot(x_i, x_j, a_ij, get_bound(x_i, !is_below)->get_value());
            return true;
        }
        else {
            // conflict detected
            sign_row_conflict(x_i, is_below);
            return false;
        }
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::select_lg_error_var(bool least) {
        TRACE("select_pivot", tout << "starting...\n";);
        theory_var  best = null_theory_var;
        inf_numeral best_error;
        inf_numeral curr_error;
        typename var_heap::iterator it  = m_to_patch.begin();
        typename var_heap::iterator end = m_to_patch.end();
        for (; it != end; ++it) {
            theory_var v = *it;
            if (below_lower(v))
                curr_error = lower(v)->get_value() - get_value(v);
            else if (above_upper(v))
                curr_error = get_value(v) - upper(v)->get_value();
            else
                continue;
            SASSERT(curr_error > inf_numeral(0));
            if (best == null_theory_var || (!least && curr_error > best_error) || (least && curr_error < best_error)) {
                TRACE("select_pivot", tout << "best: " << best << " v" << v 
                      << ", best_error: " << best_error << ", curr_error: " << curr_error << "\n";);
                best = v;
                best_error = curr_error;
            }
        }
        if (best == null_theory_var)
            m_to_patch.clear(); // all variables are satisfied
        else
            m_to_patch.erase(best);
        return best;
    }
    
    template<typename Ext>
    theory_var theory_arith<Ext>::select_smallest_var() {
        return m_to_patch.erase_min();
    }

    template<typename Ext>
    theory_var theory_arith<Ext>::select_var_to_fix() {
        if (m_blands_rule)
            return select_smallest_var();
        switch (m_params.m_arith_pivot_strategy) {
        case ARITH_PIVOT_GREATEST_ERROR: 
            return select_greatest_error_var();
        case ARITH_PIVOT_LEAST_ERROR:
            return select_least_error_var();
        default:
            return select_smallest_var();
        }
    }

    /**
       \brief Return true if it was possible to patch all variables in m_to_patch.
    */
    template<typename Ext>
    bool theory_arith<Ext>::make_feasible() {
        TRACE("arith_make_feasible", tout << "make_feasible\n"; display(tout););
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());

        m_left_basis.reset();
        m_blands_rule    = false;
        unsigned num_repeated = 0;
        while (!m_to_patch.empty()) {
            theory_var v = select_var_to_fix();
            if (v == null_theory_var) {
                // all variables were satisfied...
                SASSERT(m_to_patch.empty());
                break;
            }
            if (!m_blands_rule) {
                if (m_left_basis.contains(v)) {
                    num_repeated++;
                    if (num_repeated > blands_rule_threshold()) {
                        TRACE("blands_rule", tout << "using blands rule, " << num_repeated << "\n";);
                        // std::cerr << "BLANDS RULE...\n";
                        m_blands_rule = true;
                    }
                }
                else {
                    m_left_basis.insert(v);
                }
            }
            if (!make_var_feasible(v)) { 
                TRACE("arith_make_feasible", tout << "make_feasible: unsat\n"; display(tout););
                return false;
            }
            TRACE("arith_make_feasible_detail", display(tout););
            if (get_context().get_cancel_flag()) {
                return true;
            }
        }
        TRACE("arith_make_feasible", tout << "make_feasible: sat\n"; display(tout););
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        CASSERT("arith", satisfy_bounds());
        return true;
    }

    /**
       \brief A row is in a sign inconsistency when it is implying a
       lower (upper) bound on x_i, which is above (below) its known
       upper (lower) bound. 
    */
    template<typename Ext>
    void theory_arith<Ext>::sign_row_conflict(theory_var x_i, bool is_below) {
        inf_numeral delta;
        row const & r         = m_rows[get_var_row(x_i)];
        int idx               = r.get_idx_of(x_i);
        SASSERT(idx >= 0);
        bound * b             = 0;

        // Remark:
        // if x_i is an integer variable, then delta can be negative:
        //
        // Example: x_i <= 0   get_value(x_i) = 1/4
        // 
        // The value is above the upper bound.
        // Since x_i is an integer, get_epsilon(x_i) = 1, and delta = -3/4

        if (is_below) {
            SASSERT(below_lower(x_i));
            b = lower(x_i);
            if (relax_bounds()) {
                delta  = b->get_value();
                delta -= get_value(x_i);
                delta -= get_epsilon(x_i);
                if (delta.is_neg())
                    delta.reset();
            }
        }
        else {
            SASSERT(above_upper(x_i));
            b = upper(x_i);
            if (relax_bounds()) {
                delta  = get_value(x_i);
                delta -= b->get_value();
                delta -= get_epsilon(x_i);
                if (delta.is_neg())
                    delta.reset();
            }
        }

        antecedents ante(*this);
        explain_bound(r, idx, !is_below, delta, ante);
        b->push_justification(ante, numeral(1), coeffs_enabled());
       
        TRACE("sign_row_conflict", tout << "v" << x_i << " is_below: " << is_below << " delta: " << delta << "\n"; display_var(tout, x_i);
              tout << "is_below_lower: " << below_lower(x_i) << ", is_above_upper: " << above_upper(x_i) << "\n";
              ante.display(tout););

        set_conflict(ante, ante, "farkas");
        // display_bounds_in_smtlib();
    }

    // -----------------------------------
    //
    // Assert bound
    //
    // -----------------------------------
    
    /**
       \brief Assert x >= k, return false if a conflict is detected.
    */
    template<typename Ext>
    bool theory_arith<Ext>::assert_lower(bound * b) {
        SASSERT(b->get_bound_kind() == B_LOWER);
        theory_var          v = b->get_var();
        inf_numeral const & k = b->get_value();

        bound * u = upper(v);
        bound * l = lower(v);
        
        if (u && k > u->get_value()) {
            sign_bound_conflict(u, b);
            return false;
        }

        if (l && k <= l->get_value()) {
            // redundant
            return true;
        }
        
        switch (get_var_kind(v)) {
        case QUASI_BASE:
            quasi_base_row2base_row(get_var_row(v));
            SASSERT(get_var_kind(v) == BASE);
        case BASE:
            if (!m_to_patch.contains(v) && get_value(v) < k) {
                TRACE("to_patch_bug", tout << "need to be patched (assert_lower): "; display_var(tout, v););
                m_to_patch.insert(v);
            }
            break;
        case NON_BASE:
            if (get_value(v) < k)
                set_value(v, k);
            break;
        }

        push_bound_trail(v, l, false);
        set_bound(b, false);
    
        if (propagation_mode() != BP_NONE)
            mark_rows_for_bound_prop(v);
        
        return true;
    }

    /**
       \brief Assert x <= k, return false if a conflict is detected.
    */
    template<typename Ext>
    bool theory_arith<Ext>::assert_upper(bound * b) {
        SASSERT(b->get_bound_kind() == B_UPPER);
        theory_var          v = b->get_var();
        inf_numeral const & k = b->get_value();

        bound * u = upper(v);
        bound * l = lower(v);
        
        if (l && k < l->get_value()) {
            sign_bound_conflict(l, b);
            return false;
        }
    
        if (u && k >= u->get_value()) {
            // redundant
            return true;
        }

        switch (get_var_kind(v)) {
        case QUASI_BASE:
            quasi_base_row2base_row(get_var_row(v));
            SASSERT(get_var_kind(v) == BASE);
        case BASE:
            if (!m_to_patch.contains(v) && get_value(v) > k) {
                TRACE("to_patch_bug", tout << "need to be patched (assert upper): "; display_var(tout, v);); 
                m_to_patch.insert(v);
            }
            break;
        case NON_BASE:
            if (get_value(v) > k)
                set_value(v, k);
            break;
        }

        push_bound_trail(v, u, true);
        set_bound(b, true);
        
        if (propagation_mode() != BP_NONE)
            mark_rows_for_bound_prop(v);

        return true;
    } 

    template<typename Ext>
    bool theory_arith<Ext>::assert_bound(bound * b) {
        TRACE("assert_bound", display_bound(tout, b););
        theory_var v = b->get_var();

        if (b->is_atom()) {
            CTRACE("unassigned_atoms", m_unassigned_atoms[v] <= 0, display_var(tout, v););
            SASSERT(m_unassigned_atoms[v] > 0);
            push_dec_unassigned_atoms_trail(v);
            m_unassigned_atoms[v]--;
        }

        bool result = true;
        switch (b->get_bound_kind()) {
        case B_LOWER: 
            m_stats.m_assert_lower++;
            result = assert_lower(b);
            break;
        case B_UPPER:
            m_stats.m_assert_upper++;
            result = assert_upper(b);
            break;
        }
        
        TRACE("arith_assert", tout << "result: " << result << "\n"; display(tout););
        return result;
    }

    /**
       \brief Sign a conflict because the bounds b1 and b2 are contradictory.
    */
    template<typename Ext>
    void theory_arith<Ext>::sign_bound_conflict(bound * b1, bound * b2) {
        SASSERT(b1->get_var() == b2->get_var());
        antecedents ante(*this);
        b1->push_justification(ante, numeral(1), coeffs_enabled());
        b2->push_justification(ante, numeral(1), coeffs_enabled());

        set_conflict(ante, ante, "farkas");
        TRACE("arith_conflict", tout << "bound conflict v" << b1->get_var() << "\n";
              tout << "bounds: " << b1 << " " << b2 << "\n";);
    }

    // -----------------------------------
    //
    // Bound propagation
    //
    // -----------------------------------
    
    /**
       \brief Mark the row r1 for bound propagation.
    */
    template<typename Ext>
    void theory_arith<Ext>::mark_row_for_bound_prop(unsigned r1) {
        if (!m_in_to_check.contains(r1) && m_rows[r1].m_base_var != null_theory_var) {
            m_in_to_check.insert(r1);
            m_to_check.push_back(r1);
        }
    }

    /**
       \brief Mark all rows that contain v for bound propagation. 
    */
    template<typename Ext>
    void theory_arith<Ext>::mark_rows_for_bound_prop(theory_var v) {
        column const & c = m_columns[v];
        typename svector<col_entry>::const_iterator it  = c.begin_entries();
        typename svector<col_entry>::const_iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead())
                mark_row_for_bound_prop(it->m_row_id);
        }
    }

    /**
       \brief Given a row:
       a_1 * x_1 + ... + a_n * x_n = 0

       Claim:
       If forall i in [1..n]. (a_i > 0 => upper(x_i) != oo) and (a_i < 0 => lower(x_i) != -oo)
       Then row implies a lower bound for every monomial in the row.
       Proof:
       Without loss of generality, we consider the monomial a_1 * x_1
       a_1 * x_1 = - a_2 * x_2 - ... - a_n * x_n
                 =  (Sum_{a_i < 0} -a_i * x_i) + (Sum_{a_j > 0} -a_j * x_j)
                 >= (Sum_{a_i < 0} -a_i * lower(x_i)) + (Sum_{a_j > 0} -a_j * upper(x_j))

       If one the condition fails for the monomial a_i * x_i, then the row can still be used
       to imply a lower bound for this monomial.

       -4*x + 2*y - 3*z = 0
       y <= 1
       z >= 1
       -x = -2*y + 3*z  >= -2 + 3 >= 1
       -4*x >= 1

       Remark: the lower bound is not for the variable, but for the monomial.

       Claim:
       If forall i in [1..n]. (a_i > 0 => lower(x_i) != oo) and (a_i < 0 => upper(x_i) != -oo)
       Then row implies a upper bound for every monomial in the row.
       Proof: similar to the previous claim.

       The result is stored in lower_idx and upper_idx
       - lower_idx >= 0  : row can imply a lower bound for the monomial at 'lower_idx'
       - lower_idx == -1 : row can imply a lower bound for every monomial in the row.
       - lower_idx == -2 : row cannot be used to imply a lower bound.
 
       - upper_idx >= 0  : row can imply a upper bound for the monomial at 'upper_idx'
       - upper_idx == -1 : row can imply a upper bound for every monomial in the row.
       - upper_idx == -2 : row cannot be used to imply a upper bound.
    */
    template<typename Ext>
    void theory_arith<Ext>::is_row_useful_for_bound_prop(row const & r, int & lower_idx, int & upper_idx) const {
        lower_idx = -1;
        upper_idx = -1; 
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (int i = 0; it != end; ++it, ++i) {
            if (!it->is_dead()) {
#define UPDATE_IDX(IDX) IDX = IDX == -1 ? i : -2
                if (skip_big_coeffs() && it->m_coeff.is_big()) {
                    TRACE("is_row_useful", tout << "skipping row that contains big number...\n"; display_row_info(tout, r););
                    lower_idx = -2;
                    upper_idx = -2;
                    return;
                }
                bool is_pos = it->m_coeff.is_pos();
                if (lower(it->m_var) == 0) {
                    if (is_pos) {
                        UPDATE_IDX(upper_idx);
                    }
                    else {
                        UPDATE_IDX(lower_idx);
                    }
                }
                if (upper(it->m_var) == 0) {
                    if (is_pos) {
                        UPDATE_IDX(lower_idx);
                    }
                    else {
                        UPDATE_IDX(upper_idx);
                    }
                }
                if (lower_idx == -2 && upper_idx == -2)
                    return;
            }
        }
    }

    /**
       \brief Imply a lower/upper bound for the monomial stored at position idx.
       Then this bound is used to produce a bound for the monomial variable.
    */
    template<typename Ext>
    void theory_arith<Ext>::imply_bound_for_monomial(row const & r, int idx, bool is_lower) {
        row_entry const & entry = r[idx];
        if (m_unassigned_atoms[entry.m_var] > 0) {
            inf_numeral implied_k;
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (int idx2 = 0; it != end; ++it, ++idx2) {
                if (!it->is_dead() && idx != idx2) {
                    bound * b  = get_bound(it->m_var, is_lower ? it->m_coeff.is_pos() : it->m_coeff.is_neg());
                    SASSERT(b);
                    // implied_k -= it->m_coeff * b->get_value();
                    implied_k.submul(it->m_coeff, b->get_value());
                }
            }
            implied_k /= entry.m_coeff;
            if (entry.m_coeff.is_pos() == is_lower) {
                // implied_k is a lower bound for entry.m_var
                bound * curr = lower(entry.m_var);
                if (curr == 0 || implied_k > curr->get_value()) {
                    TRACE("arith_imply_bound", 
                          tout << "implying lower bound for v" << entry.m_var << " " << implied_k << " using row:\n";
                          display_row_info(tout, r);
                          display_var(tout, entry.m_var););
                    mk_implied_bound(r, idx, is_lower, entry.m_var, B_LOWER, implied_k);
                }
            }
            else {
                // implied_k is an upper bound for it->m_var 
                bound * curr = upper(entry.m_var);
                if (curr == 0 || implied_k < curr->get_value()) {
                    TRACE("arith_imply_bound", 
                          tout << "implying upper bound for v" << entry.m_var << " " << implied_k << " using row:\n";
                          display_row_info(tout, r);
                          display_var(tout, entry.m_var););
                    mk_implied_bound(r, idx, is_lower, entry.m_var, B_UPPER, implied_k);
                }
            }
        } 
    }

    /**
       \brief Auxiliary method. See is_row_useful_for_bound_prop 

       If is_lower = true (false), then imply a lower (upper) bound for all
       monomials in the row. The monomial bounds are used to compute bounds
       for the monomial variables.
    */
    template<typename Ext>
    void theory_arith<Ext>::imply_bound_for_all_monomials(row const & r, bool is_lower) {
        // Traverse the row once and compute 
        // bb = (Sum_{a_i < 0} -a_i*lower(x_i)) + (Sum_{a_j > 0} -a_j * upper(x_j))  If is_lower = true
        // bb = (Sum_{a_i > 0} -a_i*lower(x_i)) + (Sum_{a_j < 0} -a_j * upper(x_j))  If is_lower = false
        inf_numeral bb;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                inf_numeral const & b = get_bound(it->m_var, is_lower ? it->m_coeff.is_pos() : it->m_coeff.is_neg())->get_value();
                // bb -= it->m_coeff * b;
                bb.submul(it->m_coeff, b);
            }
        }
        
        inf_numeral implied_k;
        it = r.begin_entries();
        for (int idx = 0; it != end; ++it, ++idx) {
            if (!it->is_dead() && m_unassigned_atoms[it->m_var] > 0) {
                inf_numeral const & b = get_bound(it->m_var, is_lower ? it->m_coeff.is_pos() : it->m_coeff.is_neg())->get_value();
                implied_k  = bb;
                // implied_k += it->m_coeff * b;
                implied_k.addmul(it->m_coeff, b);
                // implied_k is a bound for the monomial in position it
                implied_k /= it->m_coeff;
                TRACE("arith_imply_bound", 
                      display_var(tout, it->m_var);
                      tout << "implied bound: " << (it->m_coeff.is_pos() ? ">=" : "<=") << implied_k << "\n";);
                if (it->m_coeff.is_pos() == is_lower) {
                    // implied_k is a lower bound for it->m_var
                    bound * curr = lower(it->m_var);
                    if (curr == 0 || implied_k > curr->get_value()) {
                        // improved lower bound
                        TRACE("arith_imply_bound",
                              tout << "implying lower bound for v" << it->m_var << " " << implied_k << " using row:\n";
                              display_row_info(tout, r);
                              display_var(tout, it->m_var););
                        mk_implied_bound(r, idx, is_lower, it->m_var, B_LOWER, implied_k);
                    }
                }
                else {
                    // implied_k is an upper bound for it->m_var 
                    bound * curr = upper(it->m_var);
                    if (curr == 0 || implied_k < curr->get_value()) {
                        // improved upper bound
                        TRACE("arith_imply_bound",
                              tout << "implying upper bound for v" << it->m_var << " " << implied_k << " using row:\n";
                              display_row_info(tout, r);
                              display_var(tout, it->m_var););
                        mk_implied_bound(r, idx, is_lower, it->m_var, B_UPPER, implied_k);
                    }
                }
            }
        }
    }

    /**
       \brief Create an explanation for the lower/upper bound of the variable at position idx.
       
       \remark delta is used for relaxing the explanation. That is, the implied bound can be delta weaker the the
       computed value.

       \remark the is_lower parameter is a little bit counterintuitive. It says if the other monomials 
       imply a lower (upper) bound for the monomial at position idx.
       
       Store the result in 'antecedent'
    */
    template<typename Ext>
    void theory_arith<Ext>::explain_bound(row const & r, int idx, bool is_lower, inf_numeral & delta, antecedents& ante) {
        SASSERT(delta >= inf_numeral::zero());
        if (!relax_bounds() && (!ante.lits().empty() || !ante.eqs().empty()))
            return;
        context & ctx = get_context();
        row_entry const & entry = r[idx];
        numeral           coeff = entry.m_coeff; 
        if (relax_bounds()) {
            // if the variable v at position idx can have a delta increase (decrease) of 'delta', then
            // the monomial (coeff * v) at position idx can have a delta increase (decrease) of '|coeff| * delta'
            if (coeff.is_neg())
                coeff.neg();
            delta  *= coeff; // adjust delta
        }
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        TRACE("arith_proof", display_row(tout, r, false); );
        for (int idx2 = 0; it != end; ++it, ++idx2) {
            if (!it->is_dead() && idx != idx2) {
                bound * b  = get_bound(it->m_var, is_lower ? it->m_coeff.is_pos() : it->m_coeff.is_neg());
                SASSERT(b);
                if (!b->has_justification())
                    continue;
                if (!relax_bounds() || delta.is_zero()) {
                    b->push_justification(ante, it->m_coeff, coeffs_enabled());
                    continue;
                }
                numeral coeff = it->m_coeff;
                bool is_b_lower   = b->get_bound_kind() == B_LOWER;
                if (coeff.is_neg())
                    coeff.neg();
                numeral inv_coeff(1);
                inv_coeff /= coeff;
                inf_numeral k_1      = b->get_value();
                inf_numeral limit_k1;
                // if the max decrease (increase) of the curr monomial (coeff * v2) is delta, then
                // the maximal decrease (increase) of v2 is (1/|coeff| * delta)
                if (is_b_lower) {
                    limit_k1 = k_1;
                    // limit_k1 -= delta * coeff;
                    limit_k1.submul(inv_coeff, delta);
                }
                else {
                    limit_k1  = k_1;
                    // limit_k1 += delta * coeff;
                    limit_k1.addmul(inv_coeff, delta);
                }
                TRACE("propagate_bounds_bug", tout << "is_b_lower: " << is_b_lower << " k1: " << k_1 << " limit_k1: " 
                      << limit_k1 << " delta: " << delta << " coeff: " << coeff << "\n";);
                inf_numeral k_2 = k_1;
                atom * new_atom = 0;
                atoms const & as           = m_var_occs[it->m_var];
                typename atoms::const_iterator it  = as.begin();
                typename atoms::const_iterator end = as.end();
                for (; it != end; ++it) {
                    atom * a    = *it;
                    if (a == b)
                        continue;
                    bool_var bv = a->get_bool_var();
                    lbool val   = ctx.get_assignment(bv);
                    if (val == l_undef)
                        continue;
                    // TODO: check if the following line is a bottleneck
                    TRACE("arith", tout << "v" << a->get_bool_var() << " " << (val == l_true) << "\n";);

                    a->assign_eh(val == l_true, get_epsilon(a->get_var()));
                    if (val != l_undef && a->get_bound_kind() == b->get_bound_kind()) {
                        SASSERT((ctx.get_assignment(bv) == l_true) == a->is_true());
                        inf_numeral a_val = a->get_value();
                        if (is_b_lower) {
                            if (a_val >= limit_k1 && a_val < k_2) {
                                k_2      = a_val;
                                new_atom = a;
                            }
                        }
                        else {
                            if (a_val <= limit_k1 && a_val > k_2) {
                                k_2      = a_val;
                                new_atom = a;
                            }
                        }
                    }
                }
                SASSERT(!is_b_lower || k_2 <= k_1);
                SASSERT(is_b_lower  || k_2 >= k_1);
                if (new_atom == 0) {
                    b->push_justification(ante, coeff, coeffs_enabled());
                    continue;
                }
                SASSERT(!is_b_lower || k_2 < k_1);
                SASSERT(is_b_lower  || k_2 > k_1);
                if (is_b_lower) {
                    TRACE("propagate_bounds", tout << "coeff: " << coeff << ", k_1 - k_2: " << k_1 - k_2 << ", delta: " << delta << "\n";);
                    delta -= coeff*(k_1 - k_2);
                }
                else {
                    TRACE("propagate_bounds", tout << "coeff: " << coeff << ", k_2 - k_1: " << k_2 - k_1 << ", delta: " << delta << "\n";);
                    delta -= coeff*(k_2 - k_1);
                }
                TRACE("propagate_bounds", tout << "delta (after replace): " << delta << "\n";);
                new_atom->push_justification(ante, coeff, coeffs_enabled());
                SASSERT(delta >= inf_numeral::zero());
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::mk_implied_bound(row const & r, unsigned idx, bool is_lower, theory_var v, bound_kind kind, inf_numeral const & k) {
        atoms const & as                 = m_var_occs[v];
        inf_numeral const & epsilon      = get_epsilon(v);
        inf_numeral delta;
        typename atoms::const_iterator     it  = as.begin();
        typename atoms::const_iterator     end = as.end();
        for (; it != end; ++it) {
            atom * a = *it;
            bool_var bv = a->get_bool_var();
            literal  l(bv);
            if (get_context().get_assignment(bv) == l_undef) {
                inf_numeral const & k2 = a->get_k();
                delta.reset();
                if (a->get_atom_kind() == A_LOWER) {
                    // v >= k  k >= k2  |-  v >= k2
                    if (kind == B_LOWER && k >= k2) {
                        if (relax_bounds()) {
                            delta  = k;
                            delta -= k2;
                        }
                        TRACE("propagate_bounds", tout << "v" << v << " >= " << k << ", v" << v << " >= " << k2 << ", delta: " << delta << "\n"; 
                              display_row(tout, r););
                        assign_bound_literal(l, r, idx, is_lower, delta);
                    }
                    // v <= k  k <  k2  |-  v < k2  |- not v >= k2
                    if (kind == B_UPPER && k <  k2) {
                        // it is not sufficient to check whether k < k2.
                        // example:
                        //   k = -1/5*epsilon
                        //   k2 = 0
                        //   Thus, v <= -1/5*epsilon  
                        //         (not v >= 0) which is equivalent to v <= -epsilon.
                        delta  = k2;
                        delta -= k;
                        delta -= epsilon;
                        if (delta.is_nonneg()) {
                            TRACE("propagate_bounds", tout << "v" << v << " <= " << k << ", not v" << v << " >= " << k2 << ", delta: " << delta << "\n"; 
                                  display_row(tout, r););
                            assign_bound_literal(~l, r, idx, is_lower, delta);
                        }
                    }
                }
                else {
                    // v >= k  k > k2  |-  v > k2 |- not v <= k2
                    if (kind == B_LOWER && k > k2) {
                        // it is not sufficient to check whether k > k2.
                        // see example above.
                        delta  = k;
                        delta -= k2;
                        delta -= epsilon;
                        if (delta.is_nonneg()) {
                            TRACE("propagate_bounds", tout << "v" << v << " >= " << k << ", not v" << v << " <= " << k2 << ", delta: " << delta << "\n"; 
                                  display_row(tout, r););
                            assign_bound_literal(~l, r, idx, is_lower, delta);
                        }
                    }
                    // v <= k  k <= k2 |-  v <= k2 
                    if (kind == B_UPPER && k <= k2) {
                        if (relax_bounds()) {
                            delta  = k2;
                            delta -= k;
                        }
                        TRACE("propagate_bounds", tout << "v" << v << " <= " << k << ", v" << v << " <= " << k2 << ", delta: " << delta << "\n"; 
                              display_row(tout, r););
                        assign_bound_literal(l, r, idx, is_lower, delta);
                    }
                }
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::dump_lemmas(literal l, antecedents const& ante) {
        context & ctx = get_context();
        if (dump_lemmas()) {
            TRACE("arith", ante.display(tout) << " --> "; ctx.display_detailed_literal(tout, l); tout << "\n";);
            ctx.display_lemma_as_smt_problem(ante.lits().size(), ante.lits().c_ptr(), 
                                             ante.eqs().size(), ante.eqs().c_ptr(), l, 0);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::dump_lemmas(literal l, derived_bound const& ante) {
        context & ctx = get_context();
        if (dump_lemmas()) {
            ctx.display_lemma_as_smt_problem(ante.lits().size(), ante.lits().c_ptr(), 
                                             ante.eqs().size(), ante.eqs().c_ptr(), l, 0);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::assign_bound_literal(literal l, row const & r, unsigned idx, bool is_lower, inf_numeral & delta) {
        m_stats.m_bound_props++;
        context & ctx = get_context();
        antecedents ante(*this);
        explain_bound(r, idx, is_lower, delta, ante);
        dump_lemmas(l, ante);
        
        TRACE("propagate_bounds", 
              ante.display(tout) << " --> ";
              ctx.display_detailed_literal(tout, l); 
              tout << "\n";);
        if (ante.lits().size() < small_lemma_size() && ante.eqs().empty()) {
            literal_vector & lits = m_tmp_literal_vector2;
            lits.reset();
            lits.push_back(l);
            literal_vector::const_iterator it  = ante.lits().begin();
            literal_vector::const_iterator end = ante.lits().end();
            for (; it != end; ++it)
                lits.push_back(~(*it));
            justification * js = 0;
            if (proofs_enabled()) {
                js = alloc(theory_lemma_justification, get_id(), ctx, lits.size(), lits.c_ptr(),
                           ante.num_params(), ante.params("assign-bounds"));
            }
            ctx.mk_clause(lits.size(), lits.c_ptr(), js, CLS_AUX_LEMMA, 0);
        }
        else {
            region & r = ctx.get_region();
            ctx.assign(l, ctx.mk_justification(
                           ext_theory_propagation_justification(
                               get_id(), r, ante.lits().size(), ante.lits().c_ptr(), 
                               ante.eqs().size(), ante.eqs().c_ptr(), l, 
                               ante.num_params(), ante.params("assign-bounds"))));
        }
    }

    /**
       \brief Traverse rows in m_to_check and try do derive improved bounds for
       the variables occurring in them.
    */
    template<typename Ext>
    void theory_arith<Ext>::propagate_bounds() {
        TRACE("propagate_bounds_detail", display(tout););
        typename svector<unsigned>::iterator it  = m_to_check.begin();
        typename svector<unsigned>::iterator end = m_to_check.end();
        for (; it != end; ++it) {
            row & r = m_rows[*it];
            if (r.get_base_var() != null_theory_var) {
                if (r.size() < max_lemma_size()) { // Ignore big rows.
                    int lower_idx;
                    int upper_idx;
                    is_row_useful_for_bound_prop(r, lower_idx, upper_idx);
                    
                    if (lower_idx >= 0) {
                        imply_bound_for_monomial(r, lower_idx, true);
                    }
                    else if (lower_idx == -1) {
                        imply_bound_for_all_monomials(r, true);
                    }
                    
                    if (upper_idx >= 0) {
                        imply_bound_for_monomial(r, upper_idx, false);
                    }
                    else if (upper_idx == -1) {
                        imply_bound_for_all_monomials(r, false);
                    }
                    
                    // sneaking cheap eq detection in this loop 
                    propagate_cheap_eq(*it);
                }
                
#if 0
                theory_var v = r.get_base_var();
                if (!is_int(v) || get_value(v).is_int()) {
                    // If an integer value is not assigned to an integer value, then 
                    // bound propagation can diverge.
                    m_in_to_check.remove(v);
                }
#endif
            }
        }
        m_to_check.reset();
        m_in_to_check.reset();
    }

    // -----------------------------------
    //
    // Justification
    //
    // -----------------------------------

    template<typename Ext>
    void theory_arith<Ext>::set_conflict(antecedents const& ante, antecedents& bounds, char const* proof_rule) {
        dump_lemmas(false_literal, ante);
        set_conflict(ante.lits().size(), ante.lits().c_ptr(), ante.eqs().size(), ante.eqs().c_ptr(), bounds, proof_rule);
    }

    template<typename Ext>
    void theory_arith<Ext>::set_conflict(derived_bound const& ante, antecedents& bounds, char const* proof_rule) {
        dump_lemmas(false_literal, ante);
        set_conflict(ante.lits().size(), ante.lits().c_ptr(), ante.eqs().size(), ante.eqs().c_ptr(), bounds, proof_rule);
    }
    
    template<typename Ext>
    void theory_arith<Ext>::set_conflict(unsigned num_literals, literal const * lits, unsigned num_eqs, enode_pair const * eqs, 
                                         antecedents& bounds, char const* proof_rule) {
        SASSERT(num_literals != 0 || num_eqs != 0);
        context & ctx = get_context();
        m_stats.m_conflicts++;
        m_num_conflicts++;
        TRACE("arith_conflict", 
              for (unsigned i = 0; i < num_literals; i++) {
                  ctx.display_detailed_literal(tout, lits[i]);
                  tout << " ";
                  if (coeffs_enabled()) {
                      tout << "bound: " << bounds.lit_coeffs()[i] << "\n";
                  }
              }
              for (unsigned i = 0; i < num_eqs; i++) {
                  tout << "#" << eqs[i].first->get_owner_id() << "=#" << eqs[i].second->get_owner_id() << " ";
                  if (coeffs_enabled()) {
                      tout << "bound: " << bounds.eq_coeffs()[i] << "\n";
                  }
              }
              for (unsigned i = 0; i < bounds.num_params(); ++i) {
                  tout << bounds.params(proof_rule)[i] << "\n";
              }
              tout << "\n";);
        record_conflict(num_literals, lits, num_eqs, eqs, bounds.num_params(), bounds.params(proof_rule));
        ctx.set_conflict(
            ctx.mk_justification(
                ext_theory_conflict_justification(get_id(), ctx.get_region(), num_literals, lits, num_eqs, eqs, 
                                                  bounds.num_params(), bounds.params(proof_rule))));
    }

    /**
       \brief Collect the proofs for the fixed variables in the given row.  Store
       the proofs in result. 
    */
    template<typename Ext>
        void theory_arith<Ext>::collect_fixed_var_justifications(row const & r, antecedents& antecedents) const {
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && is_fixed(it->m_var)) {
                lower(it->m_var)->push_justification(antecedents, it->m_coeff, coeffs_enabled());
                upper(it->m_var)->push_justification(antecedents, it->m_coeff, coeffs_enabled());                
            }
        }
    }

    // -----------------------------------
    //
    // Model generation
    //
    // -----------------------------------

    //
    // The arithmetic module uses infinitesimals. So,
    // an inf_numeral (n,k) represents  n + k*epsilon
    // where epsilon is a very small number. 
    // In order to generate a model, we need to compute
    // a value for epsilon in a way all bounds remain
    // satisfied.
    //
    // 1) Handling inequalities: (n1, k1) <= (n2, k2)
    // 
    // The only intersting case is n1 < n2 and k1 > k2. 
    // Using the definition of infinitesimal numbers
    // we have:
    // n1 + k1 * epsilon <= n2 + k2 - epsilon
    // Therefore:
    // epsilon <= (n2 - n1) / (k1 - k2)
    // 
    // Starting at Z3 V2.0, we split disequalities.
    // So, we do not need to handle them. If we decide
    // to support them again in the future:
    //
    // 2) Handling disequalities: (n1, k1) /= n2
    // 
    // case a) k1 is positive and n1 < n2
    // Thus, epsilon < (n2 - n1) / k1
    // => epsilon <= (n2 - n1) / 2*k1
    //
    // case b) k1 is negative and n1 > n2
    // Similarly, epsilon <= (n2 - n1) / 2*k1 
    // 

    /**
       \brief Update the value of epsilon using the inequality l <= u
    */
    template<typename Ext>
    void theory_arith<Ext>::update_epsilon(const inf_numeral & l, const inf_numeral & u) {
        if (l.get_rational()      < u.get_rational() &&
            l.get_infinitesimal() > u.get_infinitesimal()) {
            numeral new_epsilon = (u.get_rational() - l.get_rational()) / (l.get_infinitesimal() - u.get_infinitesimal());
            if (new_epsilon < m_epsilon) {
                m_epsilon = new_epsilon;
            }
        }
        SASSERT(m_epsilon.is_pos());
    }
    
    template<typename Ext>
    void theory_arith<Ext>::compute_epsilon() {
        m_epsilon = numeral(1);
        theory_var num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            bound * l = lower(v);
            bound * u = upper(v);
            if (l != 0)
                update_epsilon(l->get_value(), get_value(v));
            if (u != 0)
                update_epsilon(get_value(v), u->get_value());
        }
        TRACE("epsilon_bug", tout << "epsilon: " << m_epsilon << "\n";);
    }

    /**
       The epsilon computed by compute_epsilon may accidentally make two shared
       variables to have the same assignment. This method keeps dividing 
       epsilon by 2 until this "clash" does not occur.
       Here is an example of the problem
       
       Assignment:
       x -> 9.5
       y -> 10 - epsilon 
       
       x and y have different assignments. However, if compute_epsilon sets epsilon
       to 0.5, then x and y become 9.5. However, an equality is not propagated to the core
       since in the assignment above they are assigned to distinct values.
       
       This bug was reported by Marcello Bersani.  
       Remark: this is not really a soundness bug. The result sat/unsat produced by Z3 was still correct.
       However, the model construction was incorrect. Perhaps, this explains why this bug was not 
       detected before.
    */
    template<typename Ext>
    void theory_arith<Ext>::refine_epsilon() {
        while (true) {
            rational2var mapping;
            theory_var num = get_num_vars();
            bool refine = false;
            for (theory_var v = 0; v < num; v++) {
                if (is_int(v))
                    continue;
                if (!get_context().is_shared(get_enode(v)))
                    continue;
                inf_numeral const & val = get_value(v);
                if (Ext::is_infinite(val)) {
                    continue;
                }
                rational value = val.get_rational().to_rational() + m_epsilon.to_rational() * val.get_infinitesimal().to_rational();
                theory_var v2;
                if (mapping.find(value, v2)) {
                    SASSERT(!is_int(v2));
                    if (get_value(v) != get_value(v2)) {
                        // v and v2 are not known to be equal. 
                        // The choice of m_epsilon is making them equal.
                        TRACE("refine_epsilon",
                              tout << "v" << v << " v" << v2 << " " << get_value(v) << " " << get_value(v2) << " " << value << std::endl;
                              );
                        refine = true;
                        break;
                    }
                }
                else {
                    mapping.insert(value, v);
                }
            }
            if (!refine)
                return;
            numeral two(2);
            m_epsilon = m_epsilon / two;
            TRACE("refine_epsilon", tout << "new epsilon..." << m_epsilon << std::endl;);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::init_model(model_generator & m) {
        TRACE("theory_arith", tout << "init model invoked...\n";);
        m_factory = alloc(arith_factory, get_manager());
        m.register_factory(m_factory);
        compute_epsilon();
        refine_epsilon();
    }

    template<typename Ext>
    model_value_proc * theory_arith<Ext>::mk_value(enode * n, model_generator & mg) {
        theory_var v = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        inf_numeral const & val = get_value(v);
        rational num = val.get_rational().to_rational() + m_epsilon.to_rational() * val.get_infinitesimal().to_rational();
        if (is_int(v) && !num.is_int()) {
            TRACE("arith", tout << "Truncating non-integer value. This is possible for non-linear constraints v" << v << " " << num << "\n";);
            num = floor(num);
        }
        return alloc(expr_wrapper_proc, m_factory->mk_value(num, is_int(v)));
    }

    // -----------------------------------
    //
    // Model checker support
    //
    // -----------------------------------

    template<typename Ext>
    bool theory_arith<Ext>::get_value(enode * n, expr_ref & r) {
        theory_var v = n->get_th_var(get_id());
        if (v == null_theory_var) {
            // TODO: generate fresh value different from other get_value(v) for all v.
            return false; 
        }
        inf_numeral const & val = get_value(v);
        if (!val.get_infinitesimal().is_zero()) {
            // TODO: add support for infinitesimals
            return false;
        }
        numeral _val = val.get_rational();
        r = m_util.mk_numeral(_val.to_rational(), is_int(v));
        return true;
    }
    
    // -----------------------------------
    //
    // Backtracking
    //
    // -----------------------------------
    
    template<typename Ext>
    void theory_arith<Ext>::push_scope_eh() {
        theory::push_scope_eh();
        m_scopes.push_back(scope());
        scope & s                      = m_scopes.back();
        s.m_atoms_lim                  = m_atoms.size();
        s.m_bound_trail_lim            = m_bound_trail.size();
        s.m_unassigned_atoms_trail_lim = m_unassigned_atoms_trail.size();
        s.m_asserted_bounds_lim        = m_asserted_bounds.size();
        s.m_asserted_qhead_old         = m_asserted_qhead;
        s.m_bounds_to_delete_lim       = m_bounds_to_delete.size();
        s.m_nl_monomials_lim           = m_nl_monomials.size();
        s.m_nl_propagated_lim          = m_nl_propagated.size();
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        CASSERT("arith", satisfy_bounds());
    }

    template<typename Ext>
    void theory_arith<Ext>::pop_scope_eh(unsigned num_scopes) {
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        TRACE("arith_pop_scope_bug", display(tout););
        // The m_update_trail_stack may not be empty.
        // In an old version, only propagate_core and methods invoked by propagate_core were
        // inserting elements in the m_update_trail_stack stack.
        // This is not true anymore. The method quasi_base_row2base_row also does that.
        // So, restore_assignment must be invoked. In most cases, it is a noop since the stack is empty.
        restore_assignment();
        m_to_patch.reset();
        unsigned lvl     = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl = lvl - num_scopes;
        scope & s        = m_scopes[new_lvl];
        restore_bounds(s.m_bound_trail_lim);
        restore_unassigned_atoms(s.m_unassigned_atoms_trail_lim);
        m_asserted_bounds.shrink(s.m_asserted_bounds_lim);
        m_asserted_qhead = s.m_asserted_qhead_old;
        TRACE("arith_pop_scope_bug", tout << "num_vars: " << get_num_vars() << ", num_old_vars: " << get_old_num_vars(num_scopes) << "\n";);
        restore_nl_propagated_flag(s.m_nl_propagated_lim);
        m_nl_monomials.shrink(s.m_nl_monomials_lim);
        del_atoms(s.m_atoms_lim);
        del_bounds(s.m_bounds_to_delete_lim);
        del_vars(get_old_num_vars(num_scopes));
        m_scopes.shrink(new_lvl);
        theory::pop_scope_eh(num_scopes);
        VERIFY(make_feasible());
        SASSERT(m_to_patch.empty());
        m_to_check.reset();
        m_in_to_check.reset();
        m_new_atoms.reset();
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
        CASSERT("arith", satisfy_bounds());
    }

    template<typename Ext>
    void theory_arith<Ext>::restore_nl_propagated_flag(unsigned old_trail_size) {
        typename svector<theory_var>::iterator begin = m_nl_propagated.begin() + old_trail_size;
        typename svector<theory_var>::iterator it    = m_nl_propagated.end();
        while (it != begin) {
            --it;
            SASSERT(m_data[*it].m_nl_propagated);
            m_data[*it].m_nl_propagated = false;
        }
        m_nl_propagated.shrink(old_trail_size);
    }

    template<typename Ext>
    void theory_arith<Ext>::restore_bounds(unsigned old_trail_size) {
        CASSERT("arith", wf_rows());
        typename svector<bound_trail>::iterator begin = m_bound_trail.begin() + old_trail_size;
        typename svector<bound_trail>::iterator it    = m_bound_trail.end();
        while (it != begin) {
            --it;
            theory_var v = it->get_var();
            bound *    b = it->get_old_bound();
            SASSERT(is_base(v) || is_non_base(v));
            restore_bound(v, b, it->is_upper());
            if (lazy_pivoting_lvl() > 2 && b == 0 && is_base(v) && is_free(v)) {
                SASSERT(!has_var_kind(get_var_row(v), BASE));
                SASSERT(!has_var_kind(get_var_row(v), QUASI_BASE));
                eliminate<false>(v, false);
                SASSERT(m_columns[v].size() == 1);
                SASSERT(!has_var_kind(get_var_row(v), BASE));
                SASSERT(!has_var_kind(get_var_row(v), QUASI_BASE));
                set_var_kind(v, QUASI_BASE);
            }
        }
        m_bound_trail.shrink(old_trail_size);
        CASSERT("arith", wf_rows());
    }

    template<typename Ext>
    void theory_arith<Ext>::restore_unassigned_atoms(unsigned old_trail_size) {
        svector<unsigned>::iterator begin = m_unassigned_atoms_trail.begin() + old_trail_size;
        svector<unsigned>::iterator it    = m_unassigned_atoms_trail.end();
        while (it != begin) {
            --it;
            m_unassigned_atoms[*it]++;
        }
        
        m_unassigned_atoms_trail.shrink(old_trail_size);
    }

    template<typename Ext>
    void theory_arith<Ext>::del_atoms(unsigned old_size) {
        typename atoms::iterator begin = m_atoms.begin() + old_size;
        typename atoms::iterator it    = m_atoms.end();
        while (it != begin) {
            --it;
            atom * a     = *it;
            theory_var v = a->get_var();
            bool_var bv  = a->get_bool_var();
            erase_bv2a(bv);
            SASSERT(m_var_occs[v].back() == a);
            m_var_occs[v].pop_back();
            dealloc(a);
        }    
        m_atoms.shrink(old_size);
    }

    template<typename Ext>
    void theory_arith<Ext>::del_bounds(unsigned old_size) {
        typename ptr_vector<bound>::iterator begin = m_bounds_to_delete.begin() + old_size;
        typename ptr_vector<bound>::iterator it    = m_bounds_to_delete.end();
        while (it != begin) {
            --it;
            bound * b = *it;
            dealloc(b);
        }    
        m_bounds_to_delete.shrink(old_size);
    }

    template<typename Ext>
    void theory_arith<Ext>::del_vars(unsigned old_num_vars) {
        int num_vars = get_num_vars();
        SASSERT(num_vars >= static_cast<int>(old_num_vars));
        if (num_vars != static_cast<int>(old_num_vars)) {
            theory_var v = num_vars;
            while (v > static_cast<int>(old_num_vars)) {
                --v;
                switch (get_var_kind(v)) {
                case QUASI_BASE:
                    SASSERT(m_columns[v].size() == 1);
                    del_row(get_var_row(v));
                    TRACE("arith_make_feasible", tout << "del row v" << v << "\n";);
                    break; 
                case BASE:
                    SASSERT(lazy_pivoting_lvl() != 0 || m_columns[v].size() == 1);
                    if (lazy_pivoting_lvl() > 0)
                        eliminate<false>(v, false);
                    TRACE("arith_make_feasible", tout << "del row v" << v << "\n";);
                    del_row(get_var_row(v));
                    break;
                case NON_BASE: {
                    col_entry const * entry = get_a_base_row_that_contains(v);
                    if (entry) {
                        row & r = m_rows[entry->m_row_id];
                        SASSERT(is_base(r.get_base_var()));
                        SASSERT(r[entry->m_row_idx].m_var == v);
                        pivot<false>(r.get_base_var(), v, r[entry->m_row_idx].m_coeff, false);
                        SASSERT(is_base(v));
                        del_row(get_var_row(v));
                        TRACE("arith_make_feasible", tout << "del row v" << v << "\n";);
                    }
                    else {
                        TRACE("arith_make_feasible", tout << "no row v" << v << "\n";);
                    }
                    break;
                } }
                m_in_update_trail_stack.remove(v);
                m_left_basis.remove(v);
                m_in_to_check.remove(v);
            }
            m_columns         .shrink(old_num_vars);
            m_data            .shrink(old_num_vars);
            m_value           .shrink(old_num_vars);
            m_old_value       .shrink(old_num_vars);
            m_var_occs        .shrink(old_num_vars);
            m_unassigned_atoms.shrink(old_num_vars);
            m_var_pos         .shrink(old_num_vars);
            m_bounds[0]       .shrink(old_num_vars);
            m_bounds[1]       .shrink(old_num_vars);
            SASSERT(check_vector_sizes());
        }
        SASSERT(m_var_occs.size() == old_num_vars);
    }

    template<typename Ext>
    void theory_arith<Ext>::del_row(unsigned r_id) {
        row & r      = m_rows[r_id];
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                theory_var v = it->m_var;
                column & c   = m_columns[v];
                c.del_col_entry(it->m_col_idx);
            }
        }
        r.m_base_var = null_theory_var;
        r.reset();
        m_dead_rows.push_back(r_id);
    }
    
    /**
       \brief reset and retrieve built-in explanation hints for arithmetic lemmmas.
    */

    template<typename Ext>
    theory_arith<Ext>::antecedents::antecedents(theory_arith& th):
        th(th),
        a(th.m_antecedents[th.m_antecedents_index]) {
        SASSERT(th.m_antecedents_index < 3);
        a.reset();
        ++th.m_antecedents_index;
    }

    template<typename Ext>
    theory_arith<Ext>::antecedents::~antecedents() {
        --th.m_antecedents_index;
    }


};

#endif /* THEORY_ARITH_CORE_H_ */

