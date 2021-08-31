/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_char.cpp

Abstract:

    Solver for characters

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-16

--*/

#include "ast/ast_ll_pp.h"
#include "smt/theory_char.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

namespace smt {
    
    theory_char::theory_char(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("char")),
        seq(m),
        m_bb(m, ctx.get_fparams())
    {
        m_bits2char = symbol("bits2char");
    }

    struct theory_char::reset_bits : public trail {
        theory_char& s;
        unsigned idx;

        reset_bits(theory_char& s, unsigned idx):
            s(s),
            idx(idx)
        {}

        void undo() override {
            s.m_bits[idx].reset();
            s.m_ebits[idx].reset();
        }
    };

    bool theory_char::has_bits(theory_var v) const {
        return (m_bits.size() > (unsigned)v) && !m_bits[v].empty();
    }

    theory_var theory_char::mk_var(enode* n) {
        if (is_attached_to_var(n)) 
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;    
    }

    bool theory_char::internalize_atom(app * term, bool gate_ctx) { 
        for (auto arg : *term)         
            mk_var(ensure_enode(arg));
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
        if (seq.is_char_le(term)) 
            internalize_le(literal(bv, false), term);
        if (seq.is_char_is_digit(term))
            internalize_is_digit(literal(bv, false), term);
        return true;
    }

    bool theory_char::internalize_term(app * term) { 
        for (auto arg : *term)         
            mk_var(ensure_enode(arg));

        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, m.is_bool(term), true);
        
        theory_var v = mk_var(e);
        unsigned c = 0;
        if (seq.is_const_char(term, c))
            new_const_char(v, c);
        expr* n = nullptr;
        if (seq.is_char2int(term, n)) 
            new_char2int(v, n);
        return true;
    }

    /**
     * Initialize bits associated with theory variable v.
     * add also the equality bits2char(char2bit(e, 0),..., char2bit(e, 15)) = e
     * to have congruence closure propagate equalities when the bits of two vectors
     * end up having the same values. This, together with congruence closure over char2bit 
     * should ensure that two characters have the same bit-vector assignments if and only
     * if they are equal. Nevertheless, the code also checks for these constraints
     * independently and adds Ackerman axioms on demand.
     */

    void theory_char::init_bits(theory_var v) {
        if (has_bits(v))
            return;

        expr* e = get_expr(v);
        m_bits.reserve(v + 1);
        auto& bits = m_bits[v];
        while ((unsigned) v >= m_ebits.size())
            m_ebits.push_back(expr_ref_vector(m));
        
        ctx.push_trail(reset_bits(*this, v));
        auto& ebits = m_ebits[v];
        SASSERT(ebits.empty());

        bool is_bits2char = seq.is_skolem(e) && to_app(e)->get_decl()->get_parameter(0).get_symbol() == m_bits2char;
        if (is_bits2char) {
            for (expr* arg : *to_app(e)) {
                ebits.push_back(arg);
                bits.push_back(literal(ctx.get_bool_var(arg)));
            }            
        }
        else {            
            for (unsigned i = 0; i < seq.num_bits(); ++i) 
                ebits.push_back(seq.mk_char_bit(e, i));
            ctx.internalize(ebits.data(), ebits.size(), true);
            for (expr* arg : ebits)
                bits.push_back(literal(ctx.get_bool_var(arg)));            
            for (literal bit : bits)
                ctx.mark_as_relevant(bit);
            expr_ref bits2char(seq.mk_skolem(m_bits2char, ebits.size(), ebits.data(), e->get_sort()), m);
            ctx.mark_as_relevant(bits2char.get());
            enode* n1 = ensure_enode(e);
            enode* n2 = ensure_enode(bits2char);
            justification* j = 
                ctx.mk_justification(
                    ext_theory_eq_propagation_justification(get_id(), ctx.get_region(), n1, n2));
            ctx.assign_eq(n1, n2, eq_justification(j));
        }
        ++m_stats.m_num_blast;
    }

    void theory_char::internalize_le(literal lit, app* term) {
        expr* x = nullptr, *y = nullptr;
        VERIFY(seq.is_char_le(term, x, y));
        theory_var v1 = ctx.get_enode(x)->get_th_var(get_id());
        theory_var v2 = ctx.get_enode(y)->get_th_var(get_id());
        init_bits(v1);
        init_bits(v2);
        auto const& b1 = get_ebits(v1);
        auto const& b2 = get_ebits(v2);
        expr_ref e(m);
        m_bb.mk_ule(b1.size(), b1.data(), b2.data(), e);
        literal le = mk_literal(e);
        ctx.mark_as_relevant(le);
        ctx.mk_th_axiom(get_id(), ~lit, le);
        ctx.mk_th_axiom(get_id(), lit, ~le);
    }

    void theory_char::internalize_is_digit(literal lit, app* term) {
        expr* x = nullptr;
        VERIFY(seq.is_char_is_digit(term, x));
        enode* zero = ensure_enode(seq.mk_char('0'));
        enode* nine = ensure_enode(seq.mk_char('9'));
        theory_var v = ctx.get_enode(x)->get_th_var(get_id());        
        theory_var z = zero->get_th_var(get_id());
        theory_var n = nine->get_th_var(get_id());
        init_bits(v);
        init_bits(z);
        init_bits(n);
        auto const& bv = get_ebits(v);
        auto const& zv = get_ebits(z);
        auto const& nv = get_ebits(n);
        expr_ref le1(m), le2(m);
        m_bb.mk_ule(bv.size(), zv.data(), bv.data(), le1);
        m_bb.mk_ule(bv.size(), bv.data(), nv.data(), le2);
        literal lit1 = mk_literal(le1);
        literal lit2 = mk_literal(le2);
        ctx.mk_th_axiom(get_id(), ~lit, lit1);
        ctx.mk_th_axiom(get_id(), ~lit, lit2);
        ctx.mk_th_axiom(get_id(), ~lit1, ~lit2, lit);
    }

    literal_vector const& theory_char::get_bits(theory_var v) {
        init_bits(v);
        return m_bits[v];
    }

    expr_ref_vector const& theory_char::get_ebits(theory_var v) {
        init_bits(v);
        return m_ebits[v];
    }
        
    // = on characters
    void theory_char::new_eq_eh(theory_var v, theory_var w) {  
        if (has_bits(v) && has_bits(w)) {
            auto& a = get_bits(v);
            auto& b = get_bits(w);            
            literal _eq = null_literal;
            auto eq = [&]() {
                if (_eq == null_literal) {
                    _eq = mk_literal(m.mk_eq(get_expr(v), get_expr(w)));
                    ctx.mark_as_relevant(_eq);
                }
                return _eq;
            };
            for (unsigned i = a.size(); i-- > 0; ) {
                lbool v1 = ctx.get_assignment(a[i]);
                lbool v2 = ctx.get_assignment(b[i]);
                if (v1 != l_undef && v2 != l_undef && v1 != v2) {
                    enforce_ackerman(v, w);
                    return;
                }
                if (v1 == l_true) 
                    ctx.mk_th_axiom(get_id(), ~eq(), ~a[i], b[i]);
                if (v1 == l_false) 
                    ctx.mk_th_axiom(get_id(), ~eq(), a[i], ~b[i]);
                if (v2 == l_true) 
                    ctx.mk_th_axiom(get_id(), ~eq(), a[i], ~b[i]);
                if (v2 == l_false) 
                    ctx.mk_th_axiom(get_id(), ~eq(), ~a[i], b[i]);
            }            
        }
    }

    // != on characters
    void theory_char::new_diseq_eh(theory_var v, theory_var w) {  
        if (has_bits(v) && has_bits(w)) {
            auto& a = get_bits(v);
            auto& b = get_bits(w);
            for (unsigned i = a.size(); i-- > 0; ) {
                lbool v1 = ctx.get_assignment(a[i]);
                lbool v2 = ctx.get_assignment(b[i]);
                if (v1 == l_undef || v2 == l_undef || v1 != v2)
                    return;
            }
            enforce_ackerman(v, w);
        }
    }

    void theory_char::new_const_char(theory_var v, unsigned c) {
        auto& bits = get_bits(v);
        for (auto b : bits) {
            bool bit = (0 != (c & 1));
            ctx.assign(bit ? b : ~b, nullptr);
            c >>= 1;                
        }
    }

    void theory_char::new_char2int(theory_var v, expr* c) {
        theory_var w = ctx.get_enode(c)->get_th_var(get_id());
        init_bits(w);
        auto const& bits = get_ebits(w);
        expr_ref_vector sum(m);
        unsigned p = 0;
        arith_util a(m);
        for (auto b : bits) {
            sum.push_back(m.mk_ite(b, a.mk_int(1 << p), a.mk_int(0)));
            p++;
        }
        expr_ref sum_bits(a.mk_add(sum), m);
        enode* n1 = get_enode(v);
        enode* n2 = ensure_enode(sum_bits);
        justification* j = 
            ctx.mk_justification(
                ext_theory_eq_propagation_justification(get_id(), ctx.get_region(), n1, n2));
        ctx.assign_eq(n1, n2, eq_justification(j));
    }


    /**
     * 1. Check that values of classes are unique.
     *    Check that values within each class is the same. 
     *    Enforce that values are within max_char.
     * 2. Assign values to characters that haven't been assigned.
     */
    bool theory_char::final_check() {   
        TRACE("seq", tout << "final check " << get_num_vars() << "\n";);
        m_var2value.reset();
        m_var2value.resize(get_num_vars(), UINT_MAX);
        m_value2var.reset();

        // extract the initial set of constants.
        uint_set values;
        unsigned c = 0, d = 0;
        for (unsigned v = get_num_vars(); v-- > 0; ) {
            expr* e = get_expr(v);
            if (seq.is_char(e) && m_var2value[v] == UINT_MAX && get_char_value(v, c)) {
                CTRACE("seq_verbose", seq.is_char(e), tout << mk_pp(e, m) << " root: " << get_enode(v)->is_root() << " is_value: " << get_char_value(v, c) << "\n";);
                enode* r = get_enode(v)->get_root();
                m_value2var.reserve(c + 1, null_theory_var);
                theory_var u = m_value2var[c];
                if (u != null_theory_var && r != get_enode(u)->get_root()) {
                    enforce_ackerman(u, v);
                    return false;
                }
                if (c > seq.max_char()) {
                    enforce_value_bound(v);
                    return false;
                }
                for (enode* n : *r) {
                    u = n->get_th_var(get_id());
                    if (u == null_theory_var)
                        continue;
                    if (get_char_value(u, d) && d != c) {
                        enforce_ackerman(u, v);
                        return false;
                    }
                    m_var2value[u] = c;
                }
                values.insert(c);
                m_value2var[c] = v;
            }
        }
        
        // assign values to other unassigned nodes
        c = 'A';
        for (unsigned v = get_num_vars(); v-- > 0; ) {
            expr* e = get_expr(v);
            if (seq.is_char(e) && m_var2value[v] == UINT_MAX) {
                d = c;
                while (values.contains(c)) {
                    c = (c + 1) % seq.max_char();
                    if (d == c) {
                        enforce_bits();
                        return false;
                    }                    
                }
                TRACE("seq", tout << "fresh: " << mk_pp(e, m) << " := " << c << "\n";);
                for (enode* n : *get_enode(v)) 
                    m_var2value[n->get_th_var(get_id())] = c;
                m_value2var.reserve(c + 1, null_theory_var);
                m_value2var[c] = v;
                values.insert(c);
            }                       
        }
        return true;
    }

    void theory_char::enforce_bits() {
        TRACE("seq", tout << "enforce bits\n";);
        for (unsigned v = get_num_vars(); v-- > 0; ) {
            expr* e = get_expr(v);
            if (seq.is_char(e) && get_enode(v)->is_root() && !has_bits(v))
                init_bits(v);
        }        
    }

    void theory_char::enforce_value_bound(theory_var v) {
        TRACE("seq", tout << "enforce bound " << v << "\n";);
        enode* n = ensure_enode(seq.mk_char(seq.max_char()));
        theory_var w = n->get_th_var(get_id());                    
        SASSERT(has_bits(w));
        init_bits(v);
        auto const& mbits = get_ebits(w);
        auto const& bits = get_ebits(v);
        expr_ref le(m);
        m_bb.mk_ule(bits.size(), bits.data(), mbits.data(), le);
        ctx.assign(mk_literal(le), nullptr);
        ++m_stats.m_num_bounds;
    }

    void theory_char::enforce_ackerman(theory_var v, theory_var w) {
        if (v > w) 
            std::swap(v, w);
        TRACE("seq", tout << "enforce ackerman " << v << " " << w << "\n";);
        literal eq = mk_literal(m.mk_eq(get_expr(v), get_expr(w)));
        ctx.mark_as_relevant(eq);
        literal_vector lits;
        init_bits(v);
        init_bits(w);
        auto& a = get_ebits(v);
        auto& b = get_ebits(w);
        for (unsigned i = a.size(); i-- > 0; ) {
            // eq => a = b
            literal beq = mk_eq(a[i], b[i], false);
            lits.push_back(~beq);
            ctx.mark_as_relevant(beq);
            ctx.mk_th_axiom(get_id(), ~eq, beq);
        }        
        // a = b => eq
        lits.push_back(eq);
        ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
        ++m_stats.m_num_ackerman;
    }
    
    unsigned theory_char::get_char_value(theory_var v) {
        return m_var2value[v];
    }

    bool theory_char::get_char_value(theory_var v, unsigned& c) {
        if (!has_bits(v))
            return false;
        auto const & b = get_bits(v);
        c = 0;
        unsigned p = 1;
        for (literal lit : b) {
            if (ctx.get_assignment(lit) == l_true)
                c += p;
            p *= 2;
        }
        return true;
    }

    // a stand-alone theory.
    void theory_char::init_model(model_generator & mg) {
        m_factory = alloc(char_factory, get_manager(), get_family_id());
        mg.register_factory(m_factory);
        for (auto val : m_var2value) 
            if (val != UINT_MAX)
                m_factory->register_value(val);
    }

    model_value_proc * theory_char::mk_value(enode * n, model_generator & mg) {
        unsigned ch = get_char_value(n->get_th_var(get_id()));
        app* val = seq.str.mk_char(ch);
        m_factory->add_trail(val);
        return alloc(expr_wrapper_proc, val);
    }
         
    void theory_char::collect_statistics(::statistics& st) const {
        st.update("seq char ackerman", m_stats.m_num_ackerman);
        st.update("seq char bounds",   m_stats.m_num_bounds);
        st.update("seq char2bit",      m_stats.m_num_blast);
    }
}

