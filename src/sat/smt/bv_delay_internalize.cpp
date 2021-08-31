/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_delay_internalize.cpp

Abstract:

    Checking of relevant bv nodes, and if required delay axiomatize

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-22

--*/

#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"

namespace bv {

    bool solver::check_delay_internalized(expr* e) {
        if (!ctx.is_relevant(e))
            return true;
        if (get_internalize_mode(e) != internalize_mode::delay_i)
            return true;
        SASSERT(bv.is_bv(e));
        switch (to_app(e)->get_decl_kind()) {
        case OP_BMUL:
            return check_mul(to_app(e));
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BUMUL_NO_OVFL:
            return check_bool_eval(expr2enode(e));
        default:
            return check_bv_eval(expr2enode(e));
        }
        return true;
    }

    bool solver::should_bit_blast(app* e) {
        if (bv.get_bv_size(e) <= 12)
            return true;
        unsigned num_vars = e->get_num_args();
        for (expr* arg : *e) 
            if (!m.is_value(arg))
                --num_vars;
        if (num_vars <= 1) 
            return true;
        if (bv.is_bv_add(e) && num_vars * bv.get_bv_size(e) <= 64)
            return true;
        return false;
    }

    expr_ref solver::eval_args(euf::enode* n, expr_ref_vector& args) {
        for (euf::enode* arg : euf::enode_args(n)) 
            args.push_back(eval_bv(arg));
        expr_ref r(m.mk_app(n->get_decl(), args), m);
        ctx.get_rewriter()(r);
        return r;
    }

    expr_ref solver::eval_bv(euf::enode* n) {
        rational val;        
        theory_var v = n->get_th_var(get_id());
        SASSERT(get_fixed_value(v, val));
        VERIFY(get_fixed_value(v, val));
        return expr_ref(bv.mk_numeral(val, get_bv_size(v)), m);
    }

    bool solver::check_mul(app* e) {
        SASSERT(e->get_num_args() >= 2);
        expr_ref_vector args(m);
        euf::enode* n = expr2enode(e);
        if (!reflect())
            return false;
        auto r1 = eval_bv(n);
        auto r2 = eval_args(n, args);
        if (r1 == r2)
            return true;

        TRACE("bv", tout << mk_bounded_pp(e, m) << " evaluates to " << r1 << " arguments: " << args << "\n";);
        // check x*0 = 0
        if (!check_mul_zero(e, args, r1, r2))
            return false;

        // check x*1 = x
        if (!check_mul_one(e, args, r1, r2))
            return false;

        // Add propagation axiom for arguments
        if (!check_mul_invertibility(e, args, r1))
            return false;

        // Some other possible approaches:
        // algebraic rules:
        // x*(y+z), and there are nodes for x*y or x*z -> x*(y+z) = x*y + x*z
        // compute S-polys for a set of constraints.
      
        // Hensel lifting:
        // The idea is dual to fixing high-order bits. Fix the low order bits where multiplication
        // is correct, and propagate on the next bit that shows a discrepancy.

        // check Montgommery properties: (x*y) mod p = (x mod p)*(y mod p) for small primes p

        // check ranges lo <= x <= hi, lo' <= y <= hi', lo*lo' < x*y <= hi*hi' for non-overflowing values.

        // check tangets hi >= y >= y0 and hi' >= x => x*y >= x*y0


        if (m_cheap_axioms)
            return true;

        set_delay_internalize(e, internalize_mode::no_delay_i);
        internalize_circuit(e);
        return false;
    }

    /**
     * Add invertibility condition for multiplication
     * 
     * x * y = z => (y | -y) & z = z
     * 
     * This propagator relates to Niemetz and Preiner's consistency and invertibility conditions.
     * The idea is that the side-conditions for ensuring invertibility are valid
     * and in some cases are cheap to bit-blast. For multiplication, we include only
     * the _consistency_ condition because the side-constraints for invertibility
     * appear expensive (to paraphrase FMCAD 2020 paper):
     *  x * s = t => (s = 0 or mcb(x << c, y << c))
     * 
     *  for c = ctz(s) and y = (t >> c) / (s >> c)
     *
     * mcb(x,t/s) just mean that the bit-vectors are compatible as ternary bit-vectors, 
     * which for propagation means that they are the same.
     */

    bool solver::check_mul_invertibility(app* n, expr_ref_vector const& arg_values, expr* value) {

        expr_ref inv(m);

        auto invert = [&](expr* s, expr* t) {
            return bv.mk_bv_and(bv.mk_bv_or(s, bv.mk_bv_neg(s)), t);
        };
        auto check_invert = [&](expr* s) {
            inv = invert(s, value);
            ctx.get_rewriter()(inv);
            return inv == value;
        };
        auto add_inv = [&](expr* s) {
            inv = invert(s, n);
            TRACE("bv", tout << "enforce " << inv << "\n";);
            add_unit(eq_internalize(inv, n));
        };
        bool ok = true;
        for (unsigned i = 0; i < arg_values.size(); ++i) {
            if (!check_invert(arg_values[i])) {
                add_inv(n->get_arg(i));
                ok = false;
            }
        }
        return ok;
    }



    /*
    * Check that multiplication with 0 is correctly propagated.
    * If not, create algebraic axioms enforcing 0*x = 0 and x*0 = 0
    * 
    * z = 0, then lsb(x) + 1 + lsb(y) + 1 >= sz

    */
    bool solver::check_mul_zero(app* n, expr_ref_vector const& arg_values, expr* mul_value, expr* arg_value) {
        SASSERT(mul_value != arg_value);
        SASSERT(!(bv.is_zero(mul_value) && bv.is_zero(arg_value)));
        if (bv.is_zero(arg_value)) {
            unsigned sz = n->get_num_args();
            expr_ref_vector args(m, sz, n->get_args());
            for (unsigned i = 0; i < sz && !s().inconsistent(); ++i) {

                args[i] = arg_value;
                expr_ref r(m.mk_app(n->get_decl(), args), m);
                set_delay_internalize(r, internalize_mode::init_bits_only_i); // do not bit-blast this multiplier.
                args[i] = n->get_arg(i);                
                add_unit(eq_internalize(r, arg_value));
            }
            IF_VERBOSE(2, verbose_stream() << "delay internalize @" << s().scope_lvl() << "\n");
            return false;
        }
        if (bv.is_zero(mul_value)) {
            return true;
#if 0
            vector<expr_ref_vector> lsb_bits;
            for (expr* arg : *n) {
                expr_ref_vector bits(m);
                encode_lsb_tail(arg, bits);
                lsb_bits.push_back(bits);
            }
            expr_ref_vector zs(m);
            literal_vector lits;
            expr_ref eq(m.mk_eq(n, mul_value), m);
            lits.push_back(~b_internalize(eq));

            for (unsigned i = 0; i < lsb_bits.size(); ++i) {
            }
            expr_ref z(m.mk_or(zs), m);
            add_clause(lits);
            // sum of lsb should be at least sz
            return true;
#endif
        }
        return true;
    }

    /***
    * check that 1*y = y, x*1 = x
    */
    bool solver::check_mul_one(app* n, expr_ref_vector const& arg_values, expr* mul_value, expr* arg_value) {
        if (arg_values.size() != 2)
            return true;
        if (bv.is_one(arg_values[0])) {
            expr_ref mul1(m.mk_app(n->get_decl(), arg_values[0], n->get_arg(1)), m);
            set_delay_internalize(mul1, internalize_mode::init_bits_only_i);
            add_unit(eq_internalize(mul1, n->get_arg(1)));
            TRACE("bv", tout << mul1 << "\n";);
            return false;
        }
        if (bv.is_one(arg_values[1])) {
            expr_ref mul1(m.mk_app(n->get_decl(), n->get_arg(0), arg_values[1]), m);
            set_delay_internalize(mul1, internalize_mode::init_bits_only_i);
            add_unit(eq_internalize(mul1, n->get_arg(0)));
            TRACE("bv", tout << mul1 << "\n";);
            return false;
        }
        return true;
    }


    /**
    * The i'th bit in xs is 1 if the most significant bit of x is i or higher.
    */
    void solver::encode_msb_tail(expr* x, expr_ref_vector& xs) {
        theory_var v = expr2enode(x)->get_th_var(get_id());
        sat::literal_vector const& bits = m_bits[v];
        if (bits.empty())
            return;
        expr_ref tmp = literal2expr(bits.back());
        for (unsigned i = bits.size() - 1; i-- > 0; ) {
            auto b = bits[i];
            tmp = m.mk_or(literal2expr(b), tmp);
            xs.push_back(tmp);
        }
    };

    /**
     * The i'th bit in xs is 1 if the least significant bit of x is i or lower.
     */
    void solver::encode_lsb_tail(expr* x, expr_ref_vector& xs) {
        theory_var v = expr2enode(x)->get_th_var(get_id());
        sat::literal_vector const& bits = m_bits[v];
        if (bits.empty())
            return;
        expr_ref tmp = literal2expr(bits[0]);
        for (unsigned i = 1; i < bits.size(); ++i) {
            auto b = bits[i];
            tmp = m.mk_or(literal2expr(b), tmp);
            xs.push_back(tmp);
        }
    };

    /**
    * Check non-overflow of unsigned multiplication.
    * 
    * no_overflow(x, y) = > msb(x) + msb(y) <= sz;
    * msb(x) + msb(y) < sz => no_overflow(x,y)
    */
    bool solver::check_umul_no_overflow(app* n, expr_ref_vector const& arg_values, expr* value) {
        SASSERT(arg_values.size() == 2);
        SASSERT(m.is_true(value) || m.is_false(value));
        rational v0, v1;
        unsigned sz;
        VERIFY(bv.is_numeral(arg_values[0], v0, sz));
        VERIFY(bv.is_numeral(arg_values[1], v1));
        unsigned msb0 = v0.get_num_bits();
        unsigned msb1 = v1.get_num_bits();
        expr_ref_vector xs(m), ys(m), zs(m);

        if (m.is_true(value) && msb0 + msb1 > sz && !v0.is_zero() && !v1.is_zero()) {
            sat::literal no_overflow = expr2literal(n);
            encode_msb_tail(n->get_arg(0), xs);
            encode_msb_tail(n->get_arg(1), ys);
            for (unsigned i = 1; i <= sz; ++i) {
                sat::literal bit0 = mk_literal(xs.get(i - 1));
                sat::literal bit1 = mk_literal(ys.get(sz - i));
                add_clause(~no_overflow, ~bit0, ~bit1);
            }
            return false;
        }
        else if (m.is_false(value) && msb0 + msb1 < sz) {
            encode_msb_tail(n->get_arg(0), xs);
            encode_msb_tail(n->get_arg(1), ys);
            sat::literal_vector lits;
            lits.push_back(expr2literal(n));
            for (unsigned i = 1; i < sz; ++i) {
                expr_ref msb_ge_sz(m.mk_and(xs.get(i - 1), ys.get(sz - i - 1)), m);
                lits.push_back(mk_literal(msb_ge_sz));
            }
            add_clause(lits);
            return false;
        }
        return true;
    }

    bool solver::check_bv_eval(euf::enode* n) {
        expr_ref_vector args(m);
        app* a = n->get_app();
        SASSERT(bv.is_bv(a));
        auto r1 = eval_bv(n);
        auto r2 = eval_args(n, args);
        if (r1 == r2)
            return true;
        if (m_cheap_axioms)
            return true;
        set_delay_internalize(a, internalize_mode::no_delay_i);
        internalize_circuit(a);
        return false;
    }

    bool solver::check_bool_eval(euf::enode* n) {
        expr_ref_vector args(m);
        SASSERT(m.is_bool(n->get_expr()));
        sat::literal lit = expr2literal(n->get_expr());
        expr* r1 = m.mk_bool_val(s().value(lit) == l_true);
        auto r2 = eval_args(n, args);
        if (r1 == r2)
            return true;
        app* a = n->get_app();
        if (bv.is_bv_umul_no_ovfl(a) && !check_umul_no_overflow(a, args, r1))
            return false;
        if (m_cheap_axioms)
            return true;
        set_delay_internalize(a, internalize_mode::no_delay_i);
        internalize_circuit(a);
        return false;
    }

    void solver::set_delay_internalize(expr* e, internalize_mode mode) {
        if (!m_delay_internalize.contains(e))
            ctx.push(insert_obj_map<expr, internalize_mode>(m_delay_internalize, e));
        else 
            ctx.push(remove_obj_map<expr, internalize_mode>(m_delay_internalize, e, m_delay_internalize[e]));
        m_delay_internalize.insert(e, mode);
    }

    solver::internalize_mode solver::get_internalize_mode(expr* e) {
        if (!bv.is_bv(e))
            return internalize_mode::no_delay_i;
        if (!get_config().m_bv_delay)
            return internalize_mode::no_delay_i;
        if (!reflect())
            return internalize_mode::no_delay_i;
        internalize_mode mode;
        switch (to_app(e)->get_decl_kind()) {
        case OP_BMUL: 
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BUMUL_NO_OVFL:
        case OP_BSMOD_I:
        case OP_BUREM_I:
        case OP_BSREM_I:
        case OP_BUDIV_I:
        case OP_BSDIV_I: 
        case OP_BADD:
            if (should_bit_blast(to_app(e)))
                return internalize_mode::no_delay_i;
            mode = internalize_mode::delay_i;
            if (!m_delay_internalize.find(e, mode))
                m_delay_internalize.insert(e, mode);
            return mode;        
        default:
            return internalize_mode::no_delay_i;
        }
    }
}
