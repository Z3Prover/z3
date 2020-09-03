/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_internalize.cpp

Abstract:

    Internalize utilities for bit-vector solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30

--*/

#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "tactic/tactic_exception.h"

namespace bv {

    class add_var_pos_trail : public trail<euf::solver> {
        solver::bit_atom * m_atom;
    public:
        add_var_pos_trail(solver::bit_atom * a):m_atom(a) {}
        void undo(euf::solver & euf) override {
            SASSERT(m_atom->m_occs);
            m_atom->m_occs = m_atom->m_occs->m_next;
        }
    };

    class mk_atom_trail : public trail<euf::solver> {
        solver& th;
        sat::bool_var m_var;
    public:
        mk_atom_trail(sat::bool_var v, solver& th):m_var(v), th(th) {}
        void undo(euf::solver & euf) override {
            solver::atom * a = th.get_bv2a(m_var);
            a->~atom();
            th.erase_bv2a(m_var);
        }
    };

    euf::theory_var solver::mk_var(euf::enode* n) {
        theory_var r = euf::th_euf_solver::mk_var(n);
        m_find.mk_var();
        m_bits.push_back(sat::literal_vector());
        m_wpos.push_back(0);
        m_zero_one_bits.push_back(zero_one_bits());
        ctx.attach_th_var(n, this, r);
        return r;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        if (!visit_rec(m, e, sign, root, redundant))
            return sat::null_literal;
        return sat::null_literal;
    }

    bool solver::visit(expr* e) {
        if (!bv.is_bv(e)) {
            ctx.internalize(e, false, false, m_is_redundant);
            return true;
        }
        m_args.reset();
        app* a = to_app(e);
        for (expr* arg : *a) {
            euf::enode* n = get_enode(arg);
            if (n)
                m_args.push_back(n);
            else
                m_stack.push_back(sat::eframe(arg));
        }
        if (m_args.size() != a->get_num_args())
            return false;
        if (!smt_params().m_bv_reflect)
            m_args.reset();
        euf::enode* n = mk_enode(a, m_args);
        SASSERT(n->interpreted());
        theory_var v = n->get_th_var(get_id());

        switch (a->get_decl_kind()) {
        case OP_BV_NUM:         internalize_num(a, v); break;
        default:                break;
        }
        return true;
    }

    bool solver::visited(expr* e) {
        return get_enode(e) != nullptr;
    }

    euf::enode * solver::mk_enode(app * n, ptr_vector<euf::enode> const& args) {
        euf::enode * e = ctx.get_enode(n);
        if (!e) {
            e = ctx.mk_enode(n, args.size(), args.c_ptr());
            mk_var(e);
        }
        return e;
    }

    void solver::register_true_false_bit(theory_var v, unsigned idx) {
        SASSERT(s().value(m_bits[v][idx]) != l_undef);
        bool is_true = (s().value(m_bits[v][idx]) == l_true);
        zero_one_bits & bits = m_zero_one_bits[v];
        bits.push_back(zero_one_bit(v, idx, is_true));
    }

    /**
       \brief Add bit l to the given variable.
    */
    void solver::add_bit(theory_var v, literal l) {
        literal_vector & bits = m_bits[v];
        unsigned idx          = bits.size();
        bits.push_back(l);
        if (s().value(l) != l_undef && s().lvl(l) == 0) {
            register_true_false_bit(v, idx);
        }
        else {
            atom * a = get_bv2a(l.var());
            SASSERT(!a || a->is_bit());
            if (a) {
                bit_atom * b = new (get_region()) bit_atom();
                insert_bv2a(l.var(), b);
                ctx.push(mk_atom_trail(l.var(), *this));
                SASSERT(b->m_occs == 0);
                b->m_occs = new (get_region()) var_pos_occ(v, idx);
            }
            else {
                bit_atom * b = static_cast<bit_atom*>(a);
                find_new_diseq_axioms(b->m_occs, v, idx);
                ctx.push(add_var_pos_trail(b));
                b->m_occs = new (get_region()) var_pos_occ(v, idx, b->m_occs);                
            }
        }
    }

    void solver::init_bits(euf::enode * n, expr_ref_vector const & bits) {
        SASSERT(get_bv_size(n) == bits.size());
        SASSERT(euf::null_theory_var != n->get_th_var(get_id()));
        theory_var v = n->get_th_var(get_id());
        unsigned sz = bits.size();
        m_bits[v].reset();
        for (expr* bit : bits)
            add_bit(v, get_literal(bit));
        find_wpos(v);
    }

    unsigned solver::get_bv_size(euf::enode* n) {
        return bv.get_bv_size(n->get_owner());
    }

    unsigned solver::get_bv_size(theory_var v) {
        return get_bv_size(get_enode(v));
    }

    void solver::internalize_num(app* n, theory_var v) {
        numeral val;
        unsigned sz = 0;
        VERIFY(bv.is_numeral(n, val, sz));
        expr_ref_vector bits(m);
        m_bb.num2bits(val, sz, bits); 
        literal_vector & c_bits = m_bits[v];
        SASSERT(bits.size() == sz);
        SASSERT(c_bits.empty());
        for (unsigned i = 0; i < sz; i++) {
            expr * l = bits.get(i);
            SASSERT(m.is_true(l) || m.is_false(l));
            c_bits.push_back(m.is_true(l) ? true_literal : false_literal);
            register_true_false_bit(v, i);
        }
        fixed_var_eh(v);
    }

    void solver::internalize_add(app* n) {}
    void solver::internalize_sub(app* n) {}
    void solver::internalize_mul(app* n) {}
    void solver::internalize_udiv(app* n) {}
    void solver::internalize_sdiv(app* n) {}
    void solver::internalize_urem(app* n) {}
    void solver::internalize_srem(app* n) {}
    void solver::internalize_smod(app* n) {}
    void solver::internalize_shl(app* n) {}
    void solver::internalize_lshr(app* n) {}
    void solver::internalize_ashr(app* n) {}
    void solver::internalize_ext_rotate_left(app* n) {}
    void solver::internalize_ext_rotate_right(app* n) {}
    void solver::internalize_and(app* n) {}
    void solver::internalize_or(app* n) {}
    void solver::internalize_not(app* n) {}
    void solver::internalize_nand(app* n) {}
    void solver::internalize_nor(app* n) {}
    void solver::internalize_xor(app* n) {}
    void solver::internalize_xnor(app* n) {}
    void solver::internalize_concat(app* n) {}
    void solver::internalize_sign_extend(app* n) {}
    void solver::internalize_zero_extend(app* n) {}
    void solver::internalize_extract(app* n) {}
    void solver::internalize_redand(app* n) {}
    void solver::internalize_redor(app* n) {}
    void solver::internalize_comp(app* n) {}
    void solver::internalize_rotate_left(app* n) {}
    void solver::internalize_rotate_right(app* n) {}
    void solver::internalize_bv2int(app* n) {}
    void solver::internalize_int2bv(app* n) {}
    void solver::internalize_mkbv(app* n) {}
    void solver::internalize_umul_no_overflow(app* n) {}
    void solver::internalize_smul_no_overflow(app* n) {}
    void solver::internalize_smul_no_underflow(app* n) {}

}



#if 0

        case OP_BADD:           internalize_add(term); return true;
        case OP_BSUB:           internalize_sub(term); return true;
        case OP_BMUL:           internalize_mul(term); return true;
        case OP_BSDIV_I:        internalize_sdiv(term); return true;
        case OP_BUDIV_I:        internalize_udiv(term); return true;
        case OP_BSREM_I:        internalize_srem(term); return true;
        case OP_BUREM_I:        internalize_urem(term); return true;
        case OP_BSMOD_I:        internalize_smod(term); return true;
        case OP_BAND:           internalize_and(term); return true;
        case OP_BOR:            internalize_or(term); return true;
        case OP_BNOT:           internalize_not(term); return true;
        case OP_BXOR:           internalize_xor(term); return true;
        case OP_BNAND:          internalize_nand(term); return true;
        case OP_BNOR:           internalize_nor(term); return true;
        case OP_BXNOR:          internalize_xnor(term); return true;
        case OP_CONCAT:         internalize_concat(term); return true;
        case OP_SIGN_EXT:       internalize_sign_extend(term); return true;
        case OP_ZERO_EXT:       internalize_zero_extend(term); return true;
        case OP_EXTRACT:        internalize_extract(term); return true;
        case OP_BREDOR:         internalize_redor(term); return true;
        case OP_BREDAND:        internalize_redand(term); return true;
        case OP_BCOMP:          internalize_comp(term); return true;
        case OP_BSHL:           internalize_shl(term); return true;
        case OP_BLSHR:          internalize_lshr(term); return true;
        case OP_BASHR:          internalize_ashr(term); return true;
        case OP_ROTATE_LEFT:    internalize_rotate_left(term); return true;
        case OP_ROTATE_RIGHT:   internalize_rotate_right(term); return true;
        case OP_EXT_ROTATE_LEFT:  internalize_ext_rotate_left(term); return true;
        case OP_EXT_ROTATE_RIGHT: internalize_ext_rotate_right(term); return true;
        case OP_BSDIV0:         return false;
        case OP_BUDIV0:         return false;
        case OP_BSREM0:         return false;
        case OP_BUREM0:         return false;
        case OP_BSMOD0:         return false;
        case OP_MKBV:           internalize_mkbv(term); return true;
        case OP_INT2BV:
            if (params().m_bv_enable_int2bv2int) {
                internalize_int2bv(term);
            }
            return params().m_bv_enable_int2bv2int;
        case OP_BV2INT:
            if (params().m_bv_enable_int2bv2int) {
                internalize_bv2int(term);
            }
            return params().m_bv_enable_int2bv2int;
        default:
            TRACE("bv_op", tout << "unsupported operator: " << mk_ll_pp(term, m) << "\n";);
            UNREACHABLE();
            return false;
    }

}
#endif
