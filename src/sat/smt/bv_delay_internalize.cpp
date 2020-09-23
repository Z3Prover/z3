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
        default:
            return check_eval(n);
        }
        return true;
    }

    bool solver::should_bit_blast(expr* e) {
        return bv.get_bv_size(e) <= 10;
    }

    void solver::eval_args(euf::enode* n, vector<rational>& args) {
        rational val;
        for (euf::enode* arg : euf::enode_args(n)) {
            theory_var v = arg->get_th_var(get_id());
            VERIFY(get_fixed_value(v, val));
            args.push_back(val);
        }
    }

    bool solver::check_mul(euf::enode* n) {
        SASSERT(n->num_args() >= 2);
        app* e = to_app(n->get_expr());
        rational val, val_mul(1);        
        vector<rational> args;
        eval_args(n, args);
        for (rational const& val_arg : args)
            val_mul *= val_arg;
        theory_var v = n->get_th_var(get_id());
        VERIFY(get_fixed_value(v, val));
        val_mul = mod(val_mul, power2(get_bv_size(v)));
        IF_VERBOSE(12, verbose_stream() << "check_mul " << mk_bounded_pp(n->get_expr(), m) << " " << args << " = " << val_mul << " =? " << val << "\n");
        if (val_mul == val)
            return true;

        // Some possible approaches:

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
        internalize_circuit(e, v);
        return false;
    }

    bool solver::check_eval(euf::enode* n) {
        expr_ref_vector args(m);
        expr_ref r1(m), r2(m);
        rational val;
        app* a = to_app(n->get_expr());
        theory_var v = n->get_th_var(get_id());
        VERIFY(get_fixed_value(v, val));
        r1 = bv.mk_numeral(val, get_bv_size(v));
        SASSERT(bv.is_bv(a));
        for (euf::enode* arg : euf::enode_args(n)) {
            SASSERT(bv.is_bv(arg->get_expr()));
            theory_var v_arg = arg->get_th_var(get_id());
            VERIFY(get_fixed_value(v_arg, val));
            args.push_back(bv.mk_numeral(val, get_bv_size(v_arg)));
        }
        r2 = m.mk_app(a->get_decl(), args);        
        ctx.get_rewriter()(r2);
        if (r1 == r2)
            return true;
        set_delay_internalize(a, internalize_mode::no_delay_i);
        internalize_circuit(a, v);
        return false;
    }

    void solver::set_delay_internalize(expr* e, internalize_mode mode) {
        if (!m_delay_internalize.contains(e))
            ctx.push(insert_obj_map<euf::solver, expr, internalize_mode>(m_delay_internalize, e));
        m_delay_internalize.insert(e, mode);
    }

    solver::internalize_mode solver::get_internalize_mode(expr* e) {
        if (!bv.is_bv(e))
            return internalize_mode::no_delay_i;
        if (!get_config().m_bv_delay)
            return internalize_mode::no_delay_i;
        switch (to_app(e)->get_decl_kind()) {
        case OP_BMUL: 
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BUMUL_NO_OVFL:
        case OP_BSMOD_I:
        case OP_BUREM_I:
        case OP_BSREM_I:
        case OP_BUDIV_I:
        case OP_BSDIV_I: {
            if (should_bit_blast(e))
                return internalize_mode::no_delay_i;
            internalize_mode mode = internalize_mode::init_bits_i;
            if (!m_delay_internalize.find(e, mode))
                set_delay_internalize(e, mode);
            return mode;
        }
        default:
            return internalize_mode::no_delay_i;
        }
    }


}
