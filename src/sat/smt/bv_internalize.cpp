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

    solver::bit_atom& solver::atom::to_bit() {
        SASSERT(is_bit());
        return dynamic_cast<bit_atom&>(*this);
    }

    solver::def_atom& solver::atom::to_def() {
        SASSERT(!is_bit());
        return dynamic_cast<def_atom&>(*this);
    }

    class solver::add_var_pos_trail : public trail<euf::solver> {
        solver::bit_atom* m_atom;
    public:
        add_var_pos_trail(solver::bit_atom* a) :m_atom(a) {}
        void undo(euf::solver& euf) override {
            SASSERT(m_atom->m_occs);
            m_atom->m_occs = m_atom->m_occs->m_next;
        }
    };

    class solver::mk_atom_trail : public trail<euf::solver> {
        solver& th;
        sat::bool_var m_var;
    public:
        mk_atom_trail(sat::bool_var v, solver& th) : th(th), m_var(v) {}
        void undo(euf::solver& euf) override {
            solver::atom* a = th.get_bv2a(m_var);
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
        
        TRACE("bv", tout << "mk-var: " << r << " " << n->get_expr_id() << " " << mk_pp(n->get_expr(), m) << "\n";);
        return r;
    }

    void solver::apply_sort_cnstr(euf::enode * n, sort * s) {
        get_var(n);
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root, redundant))
            return sat::null_literal;
        return expr2literal(e);
    }

    void solver::internalize(expr* e, bool redundant) {
        visit_rec(m, e, false, false, redundant);
    }

    bool solver::visit(expr* e) {      
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e, m_is_redundant);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());        
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        app* a = to_app(e);
        
        SASSERT(!n || !n->is_attached_to(get_id()));
        bool suppress_args = !get_config().m_bv_reflect && !m.is_considered_uninterpreted(a->get_decl());
        if (!n) 
            n = mk_enode(e, suppress_args);

        SASSERT(!n->is_attached_to(get_id()));
        theory_var v = mk_var(n);
        SASSERT(n->is_attached_to(get_id()));

        std::function<void(unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits)> bin;
        std::function<void(unsigned sz, expr* const* xs, expr* const* ys, expr_ref& bit)> ebin;
        std::function<void(unsigned sz, expr* const* xs, expr_ref_vector& bits)> un;
        std::function<void(unsigned sz, expr* const* xs, unsigned p, expr_ref_vector& bits)> pun;
#define internalize_bin(F) bin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits) { m_bb.F(sz, xs, ys, bits); }; internalize_binary(a, bin);
#define internalize_un(F) un = [&](unsigned sz, expr* const* xs, expr_ref_vector& bits) { m_bb.F(sz, xs, bits);}; internalize_unary(a, un);
#define internalize_ac(F) bin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits) { m_bb.F(sz, xs, ys, bits); }; internalize_ac_binary(a, bin);
#define internalize_pun(F) pun = [&](unsigned sz, expr* const* xs, unsigned p, expr_ref_vector& bits) { m_bb.F(sz, xs, p, bits);}; internalize_par_unary(a, pun);
#define internalize_nfl(F) ebin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref& out) { m_bb.F(sz, xs, ys, out);}; internalize_novfl(a, ebin);

        switch (a->get_decl_kind()) {
        case OP_BV_NUM:           internalize_num(a, v); break;
        case OP_BNOT:             internalize_un(mk_not); break;
        case OP_BREDAND:          internalize_un(mk_redand); break;
        case OP_BREDOR:           internalize_un(mk_redor); break;
        case OP_BSDIV_I:          internalize_bin(mk_sdiv); break;
        case OP_BUDIV_I:          internalize_bin(mk_udiv); break;
        case OP_BUREM_I:          internalize_bin(mk_urem); break;
        case OP_BSREM_I:          internalize_bin(mk_srem); break;
        case OP_BSMOD_I:          internalize_bin(mk_smod); break;
        case OP_BSHL:             internalize_bin(mk_shl); break;
        case OP_BLSHR:            internalize_bin(mk_lshr); break;
        case OP_BASHR:            internalize_bin(mk_ashr); break;
        case OP_EXT_ROTATE_LEFT:  internalize_bin(mk_ext_rotate_left); break;
        case OP_EXT_ROTATE_RIGHT: internalize_bin(mk_ext_rotate_right); break;
        case OP_BADD:             internalize_ac(mk_adder); break;
        case OP_BMUL:             internalize_ac(mk_multiplier); break;
        case OP_BAND:             internalize_ac(mk_and); break;
        case OP_BOR:              internalize_ac(mk_or); break;
        case OP_BXOR:             internalize_ac(mk_xor); break;
        case OP_BNAND:            internalize_bin(mk_nand); break;
        case OP_BNOR:             internalize_bin(mk_nor); break;
        case OP_BXNOR:            internalize_bin(mk_xnor); break;
        case OP_BCOMP:            internalize_bin(mk_comp); break;
        case OP_SIGN_EXT:         internalize_pun(mk_sign_extend); break;
        case OP_ZERO_EXT:         internalize_pun(mk_zero_extend); break;
        case OP_ROTATE_LEFT:      internalize_pun(mk_rotate_left); break;
        case OP_ROTATE_RIGHT:     internalize_pun(mk_rotate_right); break;
        case OP_BUMUL_NO_OVFL:    internalize_nfl(mk_umul_no_overflow); break;
        case OP_BSMUL_NO_OVFL:    internalize_nfl(mk_smul_no_overflow); break;
        case OP_BSMUL_NO_UDFL:    internalize_nfl(mk_smul_no_underflow); break;
        case OP_BIT2BOOL:         internalize_bit2bool(a); break;
        case OP_ULEQ:             internalize_le<false>(a); break;
        case OP_SLEQ:             internalize_le<true>(a); break;
        case OP_XOR3:             internalize_xor3(a); break;
        case OP_CARRY:            internalize_carry(a); break;
        case OP_BSUB:             internalize_sub(a); break;
        case OP_CONCAT:           internalize_concat(a); break;
        case OP_EXTRACT:          internalize_extract(a); break;
        case OP_MKBV:             internalize_mkbv(a); break;
        case OP_INT2BV:           internalize_int2bv(a); break;
        case OP_BV2INT:           internalize_bv2int(a); break;
        case OP_BSDIV0:           break;
        case OP_BUDIV0:           break;
        case OP_BSREM0:           break;
        case OP_BUREM0:           break;
        case OP_BSMOD0:           break;
        default:
            UNREACHABLE();
            break;
        }
        return true;
    }

    void solver::mk_bits(theory_var v) {
        TRACE("bv", tout << "v" << v << "\n";);
        expr* e = var2expr(v);
        unsigned bv_size = get_bv_size(v);
        m_bits[v].reset();
        for (unsigned i = 0; i < bv_size; i++) {
            expr_ref b2b(bv.mk_bit2bool(e, i), m);
            sat::literal lit = ctx.internalize(b2b, false, false, m_is_redundant);
            m_bits[v].push_back(lit);
        }
    }

    euf::theory_var solver::get_var(euf::enode* n) {
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var) {
            v = mk_var(n);
            if (bv.is_bv(n->get_expr())) 
                mk_bits(v);            
        }
        return v;
    }

    euf::enode* solver::get_arg(euf::enode* n, unsigned idx) {
        app* o = to_app(n->get_expr());
        return ctx.get_enode(o->get_arg(idx));
    }

    inline euf::theory_var solver::get_arg_var(euf::enode* n, unsigned idx) {
        return get_var(get_arg(n, idx));
    }

    void solver::get_bits(theory_var v, expr_ref_vector& r) {
        for (literal lit : m_bits[v]) 
            r.push_back(literal2expr(lit));        
    }

    inline void solver::get_bits(euf::enode* n, expr_ref_vector& r) {
        get_bits(get_var(n), r);
    }

    inline void solver::get_arg_bits(app* n, unsigned idx, expr_ref_vector& r) {
        app* arg = to_app(n->get_arg(idx));
        get_bits(ctx.get_enode(arg), r);
    }

    void solver::register_true_false_bit(theory_var v, unsigned idx) {
        SASSERT(s().value(m_bits[v][idx]) != l_undef);
        bool is_true = (s().value(m_bits[v][idx]) == l_true);
        zero_one_bits& bits = m_zero_one_bits[v];
        bits.push_back(zero_one_bit(v, idx, is_true));
    }

    /**
       \brief Add bit l to the given variable.
    */
    void solver::add_bit(theory_var v, literal l) {
        unsigned idx = m_bits[v].size();
        m_bits[v].push_back(l);
        s().set_external(l.var());
        set_bit_eh(v, l, idx);
    }

    void solver::set_bit_eh(theory_var v, literal l, unsigned idx) {
        if (s().value(l) != l_undef && s().lvl(l) == 0) 
            register_true_false_bit(v, idx);
        else {
            atom* a = get_bv2a(l.var());
            if (a && !a->is_bit()) 
                ;
            else if (a) {
                bit_atom* b = &a->to_bit();
                find_new_diseq_axioms(*b, v, idx);
                ctx.push(add_var_pos_trail(b));
                b->m_occs = new (get_region()) var_pos_occ(v, idx, b->m_occs);
            }
            else {
                bit_atom* b = new (get_region()) bit_atom();
                insert_bv2a(l.var(), b);
                ctx.push(mk_atom_trail(l.var(), *this));
                SASSERT(!b->m_occs);
                b->m_occs = new (get_region()) var_pos_occ(v, idx);
            }
        }
    }

    void solver::init_bits(expr* e, expr_ref_vector const& bits) {
        euf::enode* n = expr2enode(e);
        SASSERT(get_bv_size(n) == bits.size());
        SASSERT(euf::null_theory_var != n->get_th_var(get_id()));
        theory_var v = n->get_th_var(get_id());
        m_bits[v].reset();
        for (expr* bit : bits) 
            add_bit(v, ctx.internalize(bit, false, false, m_is_redundant));        
        for (expr* bit : bits)
            get_var(expr2enode(bit));
        SASSERT(get_bv_size(n) == bits.size());
        find_wpos(v);
    }

    unsigned solver::get_bv_size(euf::enode* n) {
        return bv.get_bv_size(n->get_expr());
    }

    unsigned solver::get_bv_size(theory_var v) {
        return get_bv_size(var2enode(v));
    }

    void solver::internalize_num(app* n, theory_var v) {
        numeral val;
        unsigned sz = 0;
        SASSERT(expr2enode(n)->interpreted());
        VERIFY(bv.is_numeral(n, val, sz));
        expr_ref_vector bits(m);
        m_bb.num2bits(val, sz, bits);
        SASSERT(bits.size() == sz);
        SASSERT(m_bits[v].empty());
        sat::literal true_literal = ctx.internalize(m.mk_true(), false, false, false);
        for (unsigned i = 0; i < sz; i++) {
            expr* l = bits.get(i);
            SASSERT(m.is_true(l) || m.is_false(l));
            m_bits[v].push_back(m.is_true(l) ? true_literal : ~true_literal);
            register_true_false_bit(v, i);
        }
        fixed_var_eh(v);
    }

    void solver::internalize_mkbv(app* n) {
        expr_ref_vector bits(m);
        bits.append(n->get_num_args(), n->get_args());
        init_bits(n, bits);
    }

    void solver::internalize_bv2int(app* n) {
        assert_bv2int_axiom(n);
    }

    /**
     * create the axiom:
     * n = bv2int(k) = ite(bit2bool(k[sz-1],2^{sz-1},0) + ... + ite(bit2bool(k[0],1,0))
     */

    void solver::assert_bv2int_axiom(app* n) {
        expr* k = nullptr;        
        VERIFY(bv.is_bv2int(n, k));
        SASSERT(bv.is_bv_sort(m.get_sort(k)));
        expr_ref_vector k_bits(m);
        euf::enode* k_enode = expr2enode(k);
        get_bits(k_enode, k_bits);
        unsigned sz = bv.get_bv_size(k);
        expr_ref_vector args(m);
        expr_ref zero(m_autil.mk_int(0), m);
        unsigned i = 0;        
        for (expr* b : k_bits) 
            args.push_back(m.mk_ite(b, m_autil.mk_int(power2(i++)), zero));        
        expr_ref sum(m_autil.mk_add(sz, args.c_ptr()), m);
        expr_ref eq(m.mk_eq(n, sum), m);
        sat::literal lit = ctx.internalize(eq, false, false, m_is_redundant);
        add_unit(lit);
    }

    void solver::internalize_int2bv(app* n) {
        SASSERT(bv.is_int2bv(n));
        euf::enode* e = expr2enode(n);
        mk_bits(e->get_th_var(get_id()));
        assert_int2bv_axiom(n);
    }

    /**
     * create the axiom:
     *   bv2int(n) = e mod 2^bit_width
     * where n = int2bv(e)
     *
     * Create the axioms:
     *   bit2bool(i,n) == ((e div 2^i) mod 2 != 0)
     * for i = 0,.., sz-1
     */
    void solver::assert_int2bv_axiom(app* n) {
        expr* e = nullptr;
        VERIFY(bv.is_int2bv(n, e));      
        euf::enode* n_enode = expr2enode(n);
        expr_ref lhs(m), rhs(m);
        lhs = bv.mk_bv2int(n);
        unsigned sz = bv.get_bv_size(n);
        numeral mod = power(numeral(2), sz);
        rhs = m_autil.mk_mod(e, m_autil.mk_int(mod));
        expr_ref eq(m.mk_eq(lhs, rhs), m);
        TRACE("bv", tout << eq << "\n";);
        add_unit(ctx.internalize(eq, false, false, m_is_redundant));
       
        expr_ref_vector n_bits(m);
        get_bits(n_enode, n_bits);

        for (unsigned i = 0; i < sz; ++i) {
            numeral div = power2(i);
            rhs = m_autil.mk_idiv(e, m_autil.mk_int(div));
            rhs = m_autil.mk_mod(rhs, m_autil.mk_int(2));
            rhs = m.mk_eq(rhs, m_autil.mk_int(1));
            lhs = n_bits.get(i);
            expr_ref eq(m.mk_eq(lhs, rhs), m);
            TRACE("bv", tout << eq << "\n";);
            add_unit(ctx.internalize(eq, false, false, m_is_redundant));
        }
    }

    template<bool Signed>
    void solver::internalize_le(app* n) {
        SASSERT(n->get_num_args() == 2);
        expr_ref_vector arg1_bits(m), arg2_bits(m);
        get_arg_bits(n, 0, arg1_bits);
        get_arg_bits(n, 1, arg2_bits);
        expr_ref le(m);
        if (Signed)
            m_bb.mk_sle(arg1_bits.size(), arg1_bits.c_ptr(), arg2_bits.c_ptr(), le);
        else
            m_bb.mk_ule(arg1_bits.size(), arg1_bits.c_ptr(), arg2_bits.c_ptr(), le);
        literal def = ctx.internalize(le, false, false, m_is_redundant);
        add_def(def, expr2literal(n));
    }

    void solver::internalize_carry(app* n) {
        SASSERT(n->get_num_args() == 3);
        literal r = ctx.get_literal(n);
        literal l1 = ctx.get_literal(n->get_arg(0));
        literal l2 = ctx.get_literal(n->get_arg(1));
        literal l3 = ctx.get_literal(n->get_arg(2));
        add_clause(~r, l1, l2);
        add_clause(~r, l1, l3);
        add_clause(~r, l2, l3);
        add_clause(r, ~l1, ~l2);
        add_clause(r, ~l1, ~l3);
        add_clause(r, ~l2, ~l3);
    }

    void solver::internalize_xor3(app* n) {
        SASSERT(n->get_num_args() == 3);
        literal r = ctx.get_literal(n);
        literal l1 = expr2literal(n->get_arg(0));
        literal l2 = expr2literal(n->get_arg(1));
        literal l3 = expr2literal(n->get_arg(2));
        add_clause(~r, l1, l2, l3);
        add_clause(~r, ~l1, ~l2, l3);
        add_clause(~r, ~l1, l2, ~l3);
        add_clause(~r, l1, ~l2, ~l3);
        add_clause(r, ~l1, l2, l3);
        add_clause(r, l1, ~l2, l3);
        add_clause(r, l1, l2, ~l3);
        add_clause(r, ~l1, ~l2, ~l3);
    }

    void solver::internalize_unary(app* n, std::function<void(unsigned, expr* const*, expr_ref_vector&)>& fn) {
        SASSERT(n->get_num_args() == 1);
        expr_ref_vector arg1_bits(m), bits(m);
        get_arg_bits(n, 0, arg1_bits);
        fn(arg1_bits.size(), arg1_bits.c_ptr(), bits);
        init_bits(n, bits);
    }

    void solver::internalize_par_unary(app* n, std::function<void(unsigned, expr* const*, unsigned p, expr_ref_vector&)>& fn) {
        SASSERT(n->get_num_args() == 1);
        expr_ref_vector arg1_bits(m), bits(m);
        get_arg_bits(n, 0, arg1_bits);
        unsigned param = n->get_decl()->get_parameter(0).get_int();
        fn(arg1_bits.size(), arg1_bits.c_ptr(), param, bits);
        init_bits(n, bits);
    }

    void solver::internalize_binary(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref_vector&)>& fn) {
        SASSERT(n->get_num_args() == 2);
        expr_ref_vector arg1_bits(m), arg2_bits(m), bits(m);
        get_arg_bits(n, 0, arg1_bits);
        get_arg_bits(n, 1, arg2_bits);
        SASSERT(arg1_bits.size() == arg2_bits.size());
        fn(arg1_bits.size(), arg1_bits.c_ptr(), arg2_bits.c_ptr(), bits);
        init_bits(n, bits);
    }

    void solver::internalize_ac_binary(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref_vector&)>& fn) {
        SASSERT(n->get_num_args() >= 2);
        expr_ref_vector bits(m), new_bits(m), arg_bits(m);
        unsigned i = n->get_num_args() - 1;        
        get_arg_bits(n, i, bits);
        for (; i-- > 0; ) {
            arg_bits.reset();
            get_arg_bits(n, i, arg_bits);
            SASSERT(arg_bits.size() == bits.size());
            new_bits.reset();
            fn(arg_bits.size(), arg_bits.c_ptr(), bits.c_ptr(), new_bits);
            bits.swap(new_bits);
        }
        init_bits(n, bits);
        TRACE("bv_verbose", tout << arg_bits << " " << bits << " " << new_bits << "\n";);
    }

    void solver::internalize_novfl(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref&)>& fn) {
        SASSERT(n->get_num_args() == 2);
        expr_ref_vector arg1_bits(m), arg2_bits(m);
        get_arg_bits(n, 0, arg1_bits);
        get_arg_bits(n, 1, arg2_bits);
        expr_ref out(m);
        fn(arg1_bits.size(), arg1_bits.c_ptr(), arg2_bits.c_ptr(), out);
        sat::literal def = ctx.internalize(out, false, false, m_is_redundant);
        add_def(def, ctx.get_literal(n));
    }

    void solver::add_def(sat::literal def, sat::literal l) {        
        def_atom* a = new (get_region()) def_atom(l, def);
        insert_bv2a(l.var(), a);
        ctx.push(mk_atom_trail(l.var(), *this));
        add_clause(l, ~def);
        add_clause(def, ~l);
    }

    void solver::internalize_concat(app* n) {
        euf::enode* e = expr2enode(n);
        theory_var v = e->get_th_var(get_id());
        m_bits[v].reset();
        for (unsigned i = n->get_num_args(); i-- > 0; ) 
            for (literal lit : m_bits[get_arg_var(e, i)]) 
                add_bit(v, lit);                    
        find_wpos(v);
    }

    void solver::internalize_sub(app* n) {
        SASSERT(n->get_num_args() == 2);
        expr_ref_vector arg1_bits(m), arg2_bits(m), bits(m);
        get_arg_bits(n, 0, arg1_bits);
        get_arg_bits(n, 1, arg2_bits);
        SASSERT(arg1_bits.size() == arg2_bits.size());
        expr_ref carry(m);
        m_bb.mk_subtracter(arg1_bits.size(), arg1_bits.c_ptr(), arg2_bits.c_ptr(), bits, carry);
        init_bits(n, bits);
    }

    void solver::internalize_extract(app* n) {
        SASSERT(n->get_num_args() == 1);
        euf::enode* e = expr2enode(n);
        theory_var v = e->get_th_var(get_id());
        theory_var arg = get_arg_var(e, 0);
        unsigned start = n->get_decl()->get_parameter(1).get_int();
        unsigned end = n->get_decl()->get_parameter(0).get_int();
        SASSERT(start <= end && end < get_bv_size(v));
        m_bits[v].reset();
        for (unsigned i = start; i <= end; ++i)
            add_bit(v, m_bits[arg][i]);
        find_wpos(v);
    }

    void solver::internalize_bit2bool(app* n) {
        unsigned idx = 0;
        expr* arg = nullptr;
        VERIFY(bv.is_bit2bool(n, arg, idx));
        euf::enode* argn = expr2enode(arg);
        if (!argn->is_attached_to(get_id())) {
            mk_var(argn);
        }        
        theory_var v_arg = argn->get_th_var(get_id());
        sat::literal lit = expr2literal(n);
        sat::bool_var b = lit.var();
        bit_atom* a = new (get_region()) bit_atom();
        SASSERT(idx < get_bv_size(v_arg));
        a->m_occs = new (get_region()) var_pos_occ(v_arg, idx);
        insert_bv2a(b, a);
        ctx.push(mk_atom_trail(b, *this));           
        if (idx < m_bits[v_arg].size() && lit != m_bits[v_arg][idx]) {
            add_clause(m_bits[v_arg][idx], ~lit);
            add_clause(~m_bits[v_arg][idx], lit);
        }
        // axiomatize bit2bool on constants.
        rational val;
        unsigned sz;
        if (bv.is_numeral(arg, val, sz)) {
            rational bit;
            div(val, rational::power_of_two(idx), bit);
            mod(bit, rational(2), bit);
            if (bit.is_zero()) lit.neg();
            add_unit(lit);
        }
    }

    void solver::assert_ackerman(theory_var v1, theory_var v2) {
        flet<bool> _red(m_is_redundant, true);
        ++m_stats.m_ackerman;
        expr* o1 = var2expr(v1);
        expr* o2 = var2expr(v2);
        expr_ref oe(m.mk_eq(o1, o2), m);
        literal oeq = ctx.internalize(oe, false, false, m_is_redundant);
        unsigned sz = get_bv_size(v1);
        TRACE("bv", tout << oe << "\n";);
        literal_vector eqs;
        for (unsigned i = 0; i < sz; ++i) {
            literal l1 = m_bits[v1][i];
            literal l2 = m_bits[v2][i];
            expr_ref e1(m), e2(m);
            e1 = bv.mk_bit2bool(o1, i);
            e2 = bv.mk_bit2bool(o2, i);
            expr_ref e(m.mk_eq(e1, e2), m);
            literal eq = ctx.internalize(e, false, false, m_is_redundant);
            add_clause(l1, ~l2, ~eq);
            add_clause(~l1, l2, ~eq);
            add_clause(l1, l2, eq);
            add_clause(~l1, ~l2, eq);
            add_clause(eq, ~oeq);
            eqs.push_back(~eq);
        }
        eqs.push_back(oeq);
        s().add_clause(eqs.size(), eqs.c_ptr(), sat::status::th(m_is_redundant, get_id()));
    }
}
