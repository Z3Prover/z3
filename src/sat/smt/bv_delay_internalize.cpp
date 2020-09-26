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

    bool solver::check_delay_internalized(euf::enode* n) {
        expr* e = n->get_expr();
        SASSERT(bv.is_bv(e));
        SASSERT(get_internalize_mode(e) != internalize_mode::no_delay_i);
        switch (to_app(e)->get_decl_kind()) {
        case OP_BMUL:
            return check_mul(n);
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BUMUL_NO_OVFL:
            return check_bool_eval(n);
        default:
            return check_bv_eval(n);
        }
        return true;
    }

    bool solver::should_bit_blast(expr* e) {
        return bv.get_bv_size(e) <= 2;
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

    bool solver::check_mul(euf::enode* n) {
        SASSERT(n->num_args() >= 2);
        app* e = to_app(n->get_expr());
        expr_ref_vector args(m);
        auto r1 = eval_bv(n);
        auto r2 = eval_args(n, args);
        if (r1 == r2)
            return true;

        // Some possible approaches:

        TRACE("bv", tout << mk_bounded_pp(e, m) << " evaluates to " << r1 << " arguments: " << args << "\n";);
        if (!check_mul_zero(e, args, r1, r2))
            return false;
        if (!check_mul_invertibility(n->get_app(), args, r1))
            return false;
        // check base cases: val_mul = 0 or val = 0, some values in product are 1, 

        // check discrepancies in low-order bits
        // Add axioms for multiplication when fixing high-order bits to 0
      
        // Hensel lifting:
        // The idea is dual to fixing high-order bits. Fix the low order bits where multiplication
        // is correct, and propagate on the next bit that shows a discrepancy.

        // check Montgommery properties: (x*y) mod p = (x mod p)*(y mod p) for small primes p

        // check ranges lo <= x <= hi, lo' <= y <= hi', lo*lo' < x*y <= hi*hi' for non-overflowing values.

        // check tangets hi >= y >= y0 and hi' >= x => x*y >= x*y0

        // compute S-polys for a set of constraints.

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

        expr_ref inv(m), eq(m);

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
            expr_ref eq(m.mk_eq(inv, n), m);
            TRACE("bv", tout << "enforce " << eq << "\n";);
            add_unit(ctx.internalize(eq, false, true, true));            
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
    */
    bool solver::check_mul_zero(app* n, expr_ref_vector const& arg_values, expr* mul_value, expr* arg_value) {
        SASSERT(mul_value != arg_value);
        SASSERT(!(bv.is_zero(mul_value) && bv.is_zero(arg_value)));

        if (bv.is_zero(arg_value)) {
            unsigned sz = n->get_num_args();
            expr_ref_vector args(m, sz, n->get_args());
            for (unsigned i = 0; i < sz && !s().inconsistent(); ++i) {
                expr* arg = args.get(i);
                args[i] = arg_value;
                expr_ref r(m.mk_app(n->get_decl(), args), m);
                expr_ref eq(m.mk_eq(r, arg_value), m);
                args[i] = arg;
                sat::literal lit = ctx.internalize(eq, false, false, false);
                add_unit(lit);
            }
            return false;
        }
        if (bv.is_zero(mul_value)) {
            // sum of lsb should be at least sz
            return true;
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
     * The i'th bit in xs is 1 if the most least bit of x is i or lower.
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

        if (m.is_true(value) && msb0 + msb1 > sz) {
            encode_msb_tail(n->get_arg(0), xs);
            encode_msb_tail(n->get_arg(1), ys);
            for (unsigned i = 0; i < sz; ++i) {
                zs.push_back(m.mk_not(m.mk_and(xs.get(i), ys.get(sz-i))));
            }
            expr_ref z(m.mk_and(zs), m);
            sat::literal bits_are_low = ctx.internalize(z, false, false, false);
            add_clause(~expr2literal(n), bits_are_low);
            return false;
        }
        else if (m.is_false(value) && msb0 + msb1 < sz) {
            encode_msb_tail(n->get_arg(0), xs);
            encode_msb_tail(n->get_arg(1), ys);
            for (unsigned i = 0; i + 1 < sz; ++i) {
                zs.push_back(m.mk_not(m.mk_and(xs.get(i), ys.get(sz - 1 - i))));
            }
            expr_ref z(m.mk_and(zs), m);
            sat::literal bits_are_very_low = ctx.internalize(z, false, false, false);
            add_clause(~bits_are_very_low, expr2literal(n));
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
        set_delay_internalize(a, internalize_mode::no_delay_i);
        internalize_circuit(a);
        return false;
    }

    void solver::set_delay_internalize(expr* e, internalize_mode mode) {
        if (!m_delay_internalize.contains(e))
            ctx.push(insert_obj_map<euf::solver, expr, internalize_mode>(m_delay_internalize, e));
        else 
            ctx.push(remove_obj_map<euf::solver, expr, internalize_mode>(m_delay_internalize, e, m_delay_internalize[e]));
        m_delay_internalize.insert(e, mode);
    }

    solver::internalize_mode solver::get_internalize_mode(expr* e) {
        if (!bv.is_bv(e))
            return internalize_mode::no_delay_i;
        if (!get_config().m_bv_delay)
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
            if (should_bit_blast(e))
                return internalize_mode::no_delay_i;
            mode = internalize_mode::init_bits_i;
            if (!m_delay_internalize.find(e, mode))
                set_delay_internalize(e, mode);
            return mode;
        
        default:
            return internalize_mode::no_delay_i;
        }
    }
}
