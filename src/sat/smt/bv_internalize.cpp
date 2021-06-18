/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_internalize.cpp

Abstract:

    Internalize utilities for bit-vector solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30

--*/

#include "params/bv_rewriter_params.hpp"
#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "tactic/tactic_exception.h"

namespace bv {

    class solver::add_var_pos_trail : public trail {
        solver::atom* m_atom;
    public:
        add_var_pos_trail(solver::atom* a) :m_atom(a) {}
        void undo() override {
            SASSERT(m_atom->m_occs);
            m_atom->m_occs = m_atom->m_occs->m_next;
        }
    };

    class solver::add_eq_occurs_trail : public trail {
        atom* m_atom;
    public:
        add_eq_occurs_trail(atom* a) :m_atom(a) {}
        void undo() override {
            SASSERT(m_atom->m_eqs);
            m_atom->m_eqs = m_atom->m_eqs->m_next;
            if (m_atom->m_eqs)  
                m_atom->m_eqs->m_prev = nullptr;
        }
    };    

    class solver::del_eq_occurs_trail : public trail {
        atom* m_atom;
        eq_occurs* m_node;
    public:
        del_eq_occurs_trail(atom* a, eq_occurs* n) : m_atom(a), m_node(n) {}
        void undo() override {
            if (m_node->m_next)
                m_node->m_next->m_prev = m_node;
            if (m_node->m_prev) 
                m_node->m_prev->m_next = m_node;
            else
                m_atom->m_eqs = m_node;
        }
    };

    void solver::del_eq_occurs(atom* a, eq_occurs* occ) {
        eq_occurs* prev = occ->m_prev;
        if (prev)
            prev->m_next = occ->m_next;
        else
            a->m_eqs = occ->m_next;
        if (occ->m_next)
            occ->m_next->m_prev = prev;
        ctx.push(del_eq_occurs_trail(a, occ));
    }

    class solver::mk_atom_trail : public trail {
        solver& th;
        sat::bool_var m_var;
    public:
        mk_atom_trail(sat::bool_var v, solver& th) : th(th), m_var(v) {}
        void undo() override {
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
        TRACE("bv", tout << "mk-var: v" << r << " " << n->get_expr_id() << " " << mk_bounded_pp(n->get_expr(), m) << "\n";);
        return r;
    }

    void solver::apply_sort_cnstr(euf::enode * n, sort * s) {
        force_push();
        get_var(n);
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        force_push();
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root, redundant))
            return sat::null_literal;
        sat::literal lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e, bool redundant) {
        force_push();
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

        if (visited(e))
            return true;

        SASSERT(!n || !n->is_attached_to(get_id()));
        bool suppress_args = !reflect() && !m.is_considered_uninterpreted(a->get_decl());
        if (!n)
            n = mk_enode(e, suppress_args);

        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        SASSERT(n->is_attached_to(get_id()));
        if (internalize_mode::no_delay_i != get_internalize_mode(a)) 
            mk_bits(n->get_th_var(get_id()));
        else
            internalize_circuit(a);
        return true;
    }

    bool solver::internalize_circuit(app* a) {

        std::function<void(unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits)> bin;
        std::function<void(unsigned sz, expr* const* xs, expr* const* ys, expr_ref& bit)> ebin;
        std::function<void(unsigned sz, expr* const* xs, expr_ref_vector& bits)> un;
        std::function<void(unsigned sz, expr* const* xs, unsigned p, expr_ref_vector& bits)> pun;
        std::function<expr*(expr* x, expr* y)> ibin;
        std::function<expr*(expr* x)> iun;

#define internalize_bin(F) bin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits) { m_bb.F(sz, xs, ys, bits); }; internalize_binary(a, bin);
#define internalize_un(F) un = [&](unsigned sz, expr* const* xs, expr_ref_vector& bits) { m_bb.F(sz, xs, bits);}; internalize_unary(a, un);
#define internalize_ac(F) bin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits) { m_bb.F(sz, xs, ys, bits); }; internalize_binary(a, bin);
#define internalize_pun(F) pun = [&](unsigned sz, expr* const* xs, unsigned p, expr_ref_vector& bits) { m_bb.F(sz, xs, p, bits);}; internalize_par_unary(a, pun);
#define internalize_nfl(F) ebin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref& out) { m_bb.F(sz, xs, ys, out);}; internalize_novfl(a, ebin);
#define internalize_int(B, U) ibin = [&](expr* x, expr* y) { return B(x, y); }; iun = [&](expr* x) { return U(x); }; internalize_interp(a, ibin, iun);

        switch (a->get_decl_kind()) {
        case OP_BV_NUM:           internalize_num(a); break;
        case OP_BNOT:             internalize_un(mk_not); break;
        case OP_BNEG:             internalize_un(mk_neg); break;
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
        case OP_ULEQ:             internalize_le<false, false, false>(a); break;
        case OP_SLEQ:             internalize_le<true,  false, false>(a); break;
        case OP_UGEQ:             internalize_le<false, true,  false>(a); break;
        case OP_SGEQ:             internalize_le<true,  true,  false>(a); break;
        case OP_ULT:              internalize_le<false, true,  true>(a); break;
        case OP_SLT:              internalize_le<true,  true,  true>(a); break;
        case OP_UGT:              internalize_le<false, false, true>(a); break;
        case OP_SGT:              internalize_le<true,  false, true>(a); break;
        case OP_XOR3:             internalize_xor3(a); break;
        case OP_CARRY:            internalize_carry(a); break;
        case OP_BSUB:             internalize_sub(a); break;
        case OP_CONCAT:           internalize_concat(a); break;
        case OP_EXTRACT:          internalize_extract(a); break;
        case OP_REPEAT:           internalize_repeat(a); break;
        case OP_MKBV:             internalize_mkbv(a); break;
        case OP_INT2BV:           internalize_int2bv(a); break;
        case OP_BV2INT:           internalize_bv2int(a); break;
        case OP_BUDIV:            internalize_int(bv.mk_bv_udiv_i, bv.mk_bv_udiv0); break;
        case OP_BSDIV:            internalize_int(bv.mk_bv_sdiv_i, bv.mk_bv_sdiv0); break;
        case OP_BSREM:            internalize_int(bv.mk_bv_srem_i, bv.mk_bv_srem0); break;
        case OP_BUREM:            internalize_int(bv.mk_bv_urem_i, bv.mk_bv_urem0); break;
        case OP_BSMOD:            internalize_int(bv.mk_bv_smod_i, bv.mk_bv_smod0); break;
        case OP_BSDIV0:           break;
        case OP_BUDIV0:           break;
        case OP_BSREM0:           break;
        case OP_BUREM0:           break;
        case OP_BSMOD0:           break;
        default:
            IF_VERBOSE(0, verbose_stream() << mk_bounded_pp(a, m) << "\n");
            UNREACHABLE();
            break;
        }
        return true;
    }

    void solver::mk_bits(theory_var v) {
        TRACE("bv", tout << "v" << v << "@" << s().scope_lvl() << "\n";);
        expr* e = var2expr(v);
        unsigned bv_size = get_bv_size(v);
        m_bits[v].reset();
        for (unsigned i = 0; i < bv_size; i++) {
            expr_ref b2b(bv.mk_bit2bool(e, i), m);
            m_bits[v].push_back(sat::null_literal);
            sat::literal lit = ctx.internalize(b2b, false, false, m_is_redundant);
            (void)lit;
            TRACE("bv", tout << "add-bit: " << lit << " " << literal2expr(lit) << "\n";);
            SASSERT(m_bits[v].back() == lit);
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
        sat::literal l = m_bits[v][idx];
        SASSERT(l == mk_true() || ~l == mk_true());
        bool is_true = l == mk_true();
        zero_one_bits& bits = m_zero_one_bits[v];
        TRACE("bv", tout << "register v" << v << " " << l << " " << mk_true() << "\n";);
        bits.push_back(zero_one_bit(v, idx, is_true));
    }

    /**
       \brief Add bit l to the given variable.
    */
    void solver::add_bit(theory_var v, literal l) {
        unsigned idx = m_bits[v].size();
        m_bits[v].push_back(l);
        TRACE("bv", tout << "add-bit: v" << v << "[" << idx << "] " << l << " " << literal2expr(l) << "@" << s().scope_lvl() << "\n";);
        SASSERT(m_num_scopes == 0);
        s().set_external(l.var());
        euf::enode* n = bool_var2enode(l.var());
        if (!n->is_attached_to(get_id())) 
            mk_var(n);

        set_bit_eh(v, l, idx);
    }

    solver::atom* solver::mk_atom(sat::bool_var bv) {
        atom* a = get_bv2a(bv);
        if (a)
            return a;
        a = new (get_region()) atom(bv);
        insert_bv2a(bv, a);
        ctx.push(mk_atom_trail(bv, *this));
        return a;        
    }

    void solver::set_bit_eh(theory_var v, literal l, unsigned idx) {
        SASSERT(m_bits[v][idx] == l);
        if (l.var() == mk_true().var()) 
            register_true_false_bit(v, idx);
        else {
            atom* b = mk_atom(l.var());
            if (b->m_occs)
                find_new_diseq_axioms(*b, v, idx);
            ctx.push(add_var_pos_trail(b));
            b->m_occs = new (get_region()) var_pos_occ(v, idx, b->m_occs);
        }
    }

    void solver::init_bits(expr* e, expr_ref_vector const& bits) {
        euf::enode* n = expr2enode(e);
        SASSERT(get_bv_size(n) == bits.size());
        SASSERT(euf::null_theory_var != n->get_th_var(get_id()));
        theory_var v = n->get_th_var(get_id());
        
        if (!m_bits[v].empty()) {
            SASSERT(bits.size() == m_bits[v].size());
            unsigned i = 0;
            for (expr* bit : bits) {
                sat::literal lit = ctx.internalize(bit, false, false, m_is_redundant);
                TRACE("bv", tout << "set " << m_bits[v][i] << " == " << lit << "\n";);
                add_clause(~lit, m_bits[v][i]);
                add_clause(lit, ~m_bits[v][i]);
                ++i;
            }
            return;
        }
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

    sat::literal solver::mk_true() {
        if (m_true == sat::null_literal) {
            ctx.push(value_trail<sat::literal>(m_true));
            m_true = ctx.internalize(m.mk_true(), false, true, false);
        }
        return m_true;
    }

    void solver::internalize_num(app* a) {
        numeral val;
        unsigned sz = 0;
        euf::enode* n = expr2enode(a);
        theory_var v = n->get_th_var(get_id());
        SASSERT(n->interpreted());
        VERIFY(bv.is_numeral(a, val, sz));
        expr_ref_vector bits(m);
        m_bb.num2bits(val, sz, bits);
        SASSERT(bits.size() == sz);
        SASSERT(m_bits[v].empty());
        sat::literal true_literal = mk_true();
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
        SASSERT(bv.is_bv_sort(k->get_sort()));
        expr_ref_vector k_bits(m);
        euf::enode* k_enode = expr2enode(k);
        get_bits(k_enode, k_bits);
        unsigned sz = bv.get_bv_size(k);
        expr_ref_vector args(m);
        expr_ref zero(m_autil.mk_int(0), m);
        unsigned i = 0;        
        for (expr* b : k_bits) 
            args.push_back(m.mk_ite(b, m_autil.mk_int(power2(i++)), zero));        
        expr_ref sum(m_autil.mk_add(sz, args.data()), m);
        expr_ref eq = mk_eq(n, sum);
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
        expr_ref eq = mk_eq(lhs, rhs);
        TRACE("bv", tout << eq << "\n";);
        add_unit(ctx.internalize(eq, false, false, m_is_redundant));
       
        expr_ref_vector n_bits(m);
        get_bits(n_enode, n_bits);

        for (unsigned i = 0; i < sz; ++i) {
            numeral div = power2(i);
            rhs = (i == 0) ? e : m_autil.mk_idiv(e, m_autil.mk_int(div));
            rhs = m_autil.mk_mod(rhs, m_autil.mk_int(2));
            rhs = mk_eq(rhs, m_autil.mk_int(1));
            lhs = n_bits.get(i);
            expr_ref eq = mk_eq(lhs, rhs);
            TRACE("bv", tout << eq << "\n";);
            add_unit(ctx.internalize(eq, false, false, m_is_redundant));
        }
    }

    template<bool Signed, bool Rev, bool Negated>
    void solver::internalize_le(app* n) {
        SASSERT(n->get_num_args() == 2);
        expr_ref_vector arg1_bits(m), arg2_bits(m);
        get_arg_bits(n, Rev ? 1 : 0, arg1_bits);
        get_arg_bits(n, Rev ? 0 : 1, arg2_bits);
        expr_ref le(m);
        if (Signed)
            m_bb.mk_sle(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), le);
        else
            m_bb.mk_ule(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), le);
        literal def = ctx.internalize(le, false, false, m_is_redundant);
        if (Negated)
            def.neg();
        add_def(def, expr2literal(n));
    }

    void solver::internalize_carry(app* n) {
        SASSERT(n->get_num_args() == 3);
        literal r = expr2literal(n);
        literal l1 = expr2literal(n->get_arg(0));
        literal l2 = expr2literal(n->get_arg(1));
        literal l3 = expr2literal(n->get_arg(2));
        add_clause(~r, l1, l2);
        add_clause(~r, l1, l3);
        add_clause(~r, l2, l3);
        add_clause(r, ~l1, ~l2);
        add_clause(r, ~l1, ~l3);
        add_clause(r, ~l2, ~l3);
    }

    void solver::internalize_xor3(app* n) {
        SASSERT(n->get_num_args() == 3);
        literal r = expr2literal(n);
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

    void solver::internalize_udiv_i(app* a) {
        std::function<void(unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits)> bin;
        bin = [&](unsigned sz, expr* const* xs, expr* const* ys, expr_ref_vector& bits) { m_bb.mk_udiv(sz, xs, ys, bits); }; 
        internalize_binary(a, bin);
    }

    void solver::internalize_interp(app* n, std::function<expr*(expr*, expr*)>& ibin, std::function<expr*(expr*)>& iun) {
        bv_rewriter_params p(s().params());
        expr* arg1 = n->get_arg(0);
        expr* arg2 = n->get_arg(1);
        mk_bits(get_th_var(n));
        if (p.hi_div0()) {
            add_unit(eq_internalize(n, ibin(arg1, arg2)));
            return;
        }
        unsigned sz = bv.get_bv_size(n);
        expr_ref zero(bv.mk_numeral(0, sz), m);
        expr_ref eq(m.mk_eq(arg2, zero), m);
        expr_ref ite(m.mk_ite(eq, iun(arg1), ibin(arg1, arg2)), m);
        add_unit(eq_internalize(n, ite));
    }

    void solver::internalize_unary(app* n, std::function<void(unsigned, expr* const*, expr_ref_vector&)>& fn) {
        SASSERT(n->get_num_args() == 1);
        expr_ref_vector arg1_bits(m), bits(m);
        get_arg_bits(n, 0, arg1_bits);
        fn(arg1_bits.size(), arg1_bits.data(), bits);
        init_bits(n, bits);
    }

    void solver::internalize_par_unary(app* n, std::function<void(unsigned, expr* const*, unsigned p, expr_ref_vector&)>& fn) {
        SASSERT(n->get_num_args() == 1);
        expr_ref_vector arg1_bits(m), bits(m);
        get_arg_bits(n, 0, arg1_bits);
        unsigned param = n->get_decl()->get_parameter(0).get_int();
        fn(arg1_bits.size(), arg1_bits.data(), param, bits);
        init_bits(n, bits);
    }


    void solver::internalize_binary(app* e, std::function<void(unsigned, expr* const*, expr* const*, expr_ref_vector&)>& fn) {
        SASSERT(e->get_num_args() >= 1);
        expr_ref_vector bits(m), new_bits(m), arg_bits(m);
        
        get_arg_bits(e, 0, bits);
        for (unsigned i = 1; i < e->get_num_args(); ++i) {
            arg_bits.reset();
            get_arg_bits(e, i, arg_bits);
            SASSERT(arg_bits.size() == bits.size());
            new_bits.reset();
            fn(bits.size(), bits.data(), arg_bits.data(), new_bits);
            bits.swap(new_bits);
        }        
        init_bits(e, bits);
        TRACE("bv_verbose", tout << arg_bits << " " << bits << " " << new_bits << "\n";);
    }

    void solver::internalize_novfl(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref&)>& fn) {
        SASSERT(n->get_num_args() == 2);
        expr_ref_vector arg1_bits(m), arg2_bits(m);
        get_arg_bits(n, 0, arg1_bits);
        get_arg_bits(n, 1, arg2_bits);
        expr_ref out(m);
        fn(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), out);
        sat::literal def = ctx.internalize(out, false, false, m_is_redundant);
        add_def(def, expr2literal(n));
    }

    void solver::add_def(sat::literal def, sat::literal l) {        
        atom* a = new (get_region()) atom(l.var());
        a->m_var = l;
        a->m_def = def;
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
        m_bb.mk_subtracter(arg1_bits.size(), arg1_bits.data(), arg2_bits.data(), bits, carry);
        init_bits(n, bits);
    }

    void solver::internalize_extract(app* e) {
        expr* arg_e = nullptr;
        unsigned lo = 0, hi = 0;
        VERIFY(bv.is_extract(e, lo, hi, arg_e));
        euf::enode* n = expr2enode(e);
        theory_var v = n->get_th_var(get_id());    
        theory_var arg_v = get_arg_var(n, 0);
        SASSERT(hi - lo + 1 == get_bv_size(v));
        SASSERT(lo <= hi && hi < get_bv_size(arg_v));
        m_bits[v].reset();
        for (unsigned i = lo; i <= hi; ++i) 
            add_bit(v, m_bits[arg_v][i]);
        find_wpos(v);
    }

    void solver::internalize_repeat(app* e) {
        unsigned n = 0;
        expr* arg = nullptr;
        VERIFY(bv.is_repeat(e, arg, n));
        expr_ref_vector conc(m);
        for (unsigned i = 0; i < n; ++i)
            conc.push_back(arg);
        expr_ref r(bv.mk_concat(conc), m);
        mk_bits(get_th_var(e));
        add_unit(eq_internalize(e, r));
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
        unsigned arg_sz = get_bv_size(v_arg);
        SASSERT(idx < arg_sz);
        sat::literal lit = expr2literal(n);
        sat::literal lit0 = m_bits[v_arg][idx];
        if (lit0 == sat::null_literal) {
            m_bits[v_arg][idx] = lit;
            TRACE("bv", tout << "add-bit: " << lit << " " << literal2expr(lit) << "\n";);
            atom* a = new (get_region()) atom(lit.var());
            a->m_occs = new (get_region()) var_pos_occ(v_arg, idx);
            insert_bv2a(lit.var(), a);
            ctx.push(mk_atom_trail(lit.var(), *this));
        }
        else if (lit != lit0) {
            add_clause(lit0, ~lit);
            add_clause(~lit0, lit);
        }

        // validate_atoms();
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

    void solver::eq_internalized(euf::enode* n) {
        SASSERT(m.is_eq(n->get_expr()));
        sat::literal lit = literal(n->bool_var(), false);
        theory_var v1 = n->get_arg(0)->get_th_var(get_id());
        theory_var v2 = n->get_arg(1)->get_th_var(get_id());
        SASSERT(v1 != euf::null_theory_var);
        SASSERT(v2 != euf::null_theory_var);
        
#if 0
        if (!n->is_attached_to(get_id()))
            mk_var(n);
#endif   
        
        unsigned sz = m_bits[v1].size();
        if (sz == 1) {
            literal bit1 = m_bits[v1][0];
            literal bit2 = m_bits[v2][0];
            add_clause(~lit, ~bit1, bit2);
            add_clause(~lit, ~bit2, bit1);
            add_clause(~bit1, ~bit2, lit);
            add_clause(bit2, bit1, lit);
            return;
        }
        for (unsigned i = 0; i < sz; ++i) {
            literal bit1 = m_bits[v1][i];
            literal bit2 = m_bits[v2][i];
            lbool val1 = s().value(bit1);
            lbool val2 = s().value(bit2);
            if (val1 != l_undef)
                eq_internalized(bit2.var(), bit1.var(), i, v2, v1, lit, n);
            else if (val2 != l_undef)
                eq_internalized(bit1.var(), bit2.var(), i, v1, v2, lit, n);
            else if ((s().rand()() % 2) == 0)
                eq_internalized(bit2.var(), bit1.var(), i, v2, v1, lit, n);
            else 
                eq_internalized(bit1.var(), bit2.var(), i, v1, v2, lit, n);
        }
    }

    void solver::eq_internalized(sat::bool_var b1, sat::bool_var b2, unsigned idx, theory_var v1, theory_var v2, literal lit, euf::enode* n) {
        atom* a = mk_atom(b1);
        if (a) {
            ctx.push(add_eq_occurs_trail(a));            
            auto* next = a->m_eqs;
            a->m_eqs = new (get_region()) eq_occurs(b1, b2, idx, v1, v2, lit, n, next);
            if (next)
                next->m_prev = a->m_eqs;
        }        
    }

    void solver::assert_ackerman(theory_var v1, theory_var v2) {
        if (v1 == v2)
            return;
        if (v1 > v2)
            std::swap(v1, v2);
        flet<bool> _red(m_is_redundant, true);
        ++m_stats.m_ackerman;
        expr* o1 = var2expr(v1);
        expr* o2 = var2expr(v2);
        expr_ref oe = mk_var_eq(v1, v2);
        literal oeq = ctx.internalize(oe, false, false, m_is_redundant);
        unsigned sz = m_bits[v1].size();
        TRACE("bv", tout << "ackerman-eq: " << s().scope_lvl() << " " << oe << "\n";);
        literal_vector eqs;
        eqs.push_back(oeq);
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref e1(m), e2(m);
            e1 = bv.mk_bit2bool(o1, i);
            e2 = bv.mk_bit2bool(o2, i);
            expr_ref e = mk_eq(e1, e2);
            literal eq = ctx.internalize(e, false, false, m_is_redundant);
            add_clause(eq, ~oeq);
            eqs.push_back(~eq);
        }
        TRACE("bv", for (auto l : eqs) tout << mk_bounded_pp(literal2expr(l), m) << " "; tout << "\n";);
        s().add_clause(eqs.size(), eqs.data(), sat::status::th(m_is_redundant, get_id()));
    }
}
