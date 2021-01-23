/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_char.cpp

Abstract:

    Solver for characters

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-16

--*/

#include "ast/bv_decl_plugin.h"
#include "smt/seq_char.h"
#include "smt/smt_context.h"

namespace smt {

    seq_char::seq_char(theory& th):
        th(th),
        m(th.get_manager()),
        seq(m),
        m_bb(m, ctx().get_fparams())
    {
        bv_util bv(m);
        sort_ref b8(bv.mk_sort(8), m);
        m_enabled = !seq.is_char(b8);
        m_bits2char = symbol("bits2char");
    }

    struct seq_char::reset_bits : public trail<context> {
        seq_char& s;
        unsigned idx;

        reset_bits(seq_char& s, unsigned idx):
            s(s),
            idx(idx)
        {}

        void undo(context& ctx) override {
            s.m_bits[idx].reset();
            s.m_ebits[idx].reset();
        }
    };

    bool seq_char::has_bits(theory_var v) const {
        return (m_bits.size() > (unsigned)v) && !m_bits[v].empty();
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

    void seq_char::init_bits(theory_var v) {
        if (has_bits(v))
            return;

        expr* e = th.get_expr(v);
        m_bits.reserve(v + 1);
        auto& bits = m_bits[v];
        while ((unsigned) v >= m_ebits.size())
            m_ebits.push_back(expr_ref_vector(m));
        
        ctx().push_trail(reset_bits(*this, v));
        auto& ebits = m_ebits[v];
        SASSERT(ebits.empty());

        bool is_bits2char = seq.is_skolem(e) && to_app(e)->get_decl()->get_parameter(0).get_symbol() == m_bits2char;
        if (is_bits2char) {
            for (expr* arg : *to_app(e)) {
                ebits.push_back(arg);
                bits.push_back(literal(ctx().get_bool_var(arg)));
            }            
        }
        else {            
            for (unsigned i = 0; i < seq.num_bits(); ++i) 
                ebits.push_back(seq.mk_char_bit(e, i));
            ctx().internalize(ebits.c_ptr(), ebits.size(), true);
            for (expr* arg : ebits)
                bits.push_back(literal(ctx().get_bool_var(arg)));            
            for (literal bit : bits)
                ctx().mark_as_relevant(bit);
            expr_ref bits2char(seq.mk_skolem(m_bits2char, ebits.size(), ebits.c_ptr(), m.get_sort(e)), m);
            ctx().mark_as_relevant(bits2char.get());
            enode* n1 = th.ensure_enode(e);
            enode* n2 = th.ensure_enode(bits2char);
            justification* j = 
                ctx().mk_justification(
                    ext_theory_eq_propagation_justification(th.get_id(), ctx().get_region(), n1, n2));
            ctx().assign_eq(n1, n2, eq_justification(j));
        }
        ++m_stats.m_num_blast;
    }

    void seq_char::internalize_le(literal lit, app* term) {
        expr* x = nullptr, *y = nullptr;
        VERIFY(seq.is_char_le(term, x, y));
        theory_var v1 = ctx().get_enode(x)->get_th_var(th.get_id());
        theory_var v2 = ctx().get_enode(y)->get_th_var(th.get_id());
        init_bits(v1);
        init_bits(v2);
        auto const& b1 = get_ebits(v1);
        auto const& b2 = get_ebits(v2);
        expr_ref e(m);
        m_bb.mk_ule(b1.size(), b1.c_ptr(), b2.c_ptr(), e);
        literal le = th.mk_literal(e);
        ctx().mark_as_relevant(le);
        ctx().mk_th_axiom(th.get_id(), ~lit, le);
        ctx().mk_th_axiom(th.get_id(), lit, ~le);
    }

    literal_vector const& seq_char::get_bits(theory_var v) {
        init_bits(v);
        return m_bits[v];
    }

    expr_ref_vector const& seq_char::get_ebits(theory_var v) {
        init_bits(v);
        return m_ebits[v];
    }
        
    // = on characters
    void seq_char::new_eq_eh(theory_var v, theory_var w) {  
        if (has_bits(v) && has_bits(w)) {
            auto& a = get_bits(v);
            auto& b = get_bits(w);            
            literal _eq = null_literal;
            auto eq = [&]() {
                if (_eq == null_literal) {
                    _eq = th.mk_literal(m.mk_eq(th.get_expr(v), th.get_expr(w)));
                    ctx().mark_as_relevant(_eq);
                }
                return _eq;
            };
            for (unsigned i = a.size(); i-- > 0; ) {
                lbool v1 = ctx().get_assignment(a[i]);
                lbool v2 = ctx().get_assignment(b[i]);
                if (v1 != l_undef && v2 != l_undef && v1 != v2) {
                    enforce_ackerman(v, w);
                    return;
                }
                if (v1 == l_true) 
                    ctx().mk_th_axiom(th.get_id(), ~eq(), ~a[i], b[i]);
                if (v1 == l_false) 
                    ctx().mk_th_axiom(th.get_id(), ~eq(), a[i], ~b[i]);
                if (v2 == l_true) 
                    ctx().mk_th_axiom(th.get_id(), ~eq(), a[i], ~b[i]);
                if (v2 == l_false) 
                    ctx().mk_th_axiom(th.get_id(), ~eq(), ~a[i], b[i]);
            }            
        }
    }

    // != on characters
    void seq_char::new_diseq_eh(theory_var v, theory_var w) {  
        if (has_bits(v) && has_bits(w)) {
            auto& a = get_bits(v);
            auto& b = get_bits(w);
            for (unsigned i = a.size(); i-- > 0; ) {
                lbool v1 = ctx().get_assignment(a[i]);
                lbool v2 = ctx().get_assignment(b[i]);
                if (v1 == l_undef || v2 == l_undef || v1 != v2)
                    return;
            }
            enforce_ackerman(v, w);
        }
    }

    void seq_char::new_const_char(theory_var v, unsigned c) {
        auto& bits = get_bits(v);
        for (auto b : bits) {
            bool bit = (0 != (c & 1));
            ctx().assign(bit ? b : ~b, nullptr);
            c >>= 1;                
        }
    }

    /**
     * 1. Check that values of classes are unique.
     *    Check that values within each class is the same. 
     *    Enforce that values are within max_char.
     * 2. Assign values to characters that haven't been assigned.
     */
    bool seq_char::final_check() {   
        m_var2value.reset();
        m_var2value.resize(th.get_num_vars(), UINT_MAX);
        m_value2var.reset();

        // extract the initial set of constants.
        uint_set values;
        unsigned c = 0, d = 0;
        for (unsigned v = th.get_num_vars(); v-- > 0; ) {
            expr* e = th.get_expr(v);
            if (seq.is_char(e) && m_var2value[v] == UINT_MAX && get_value(v, c)) {
                CTRACE("seq", seq.is_char(e), tout << mk_pp(e, m) << " root: " << th.get_enode(v)->is_root() << " is_value: " << get_value(v, c) << "\n";);
                enode* r = th.get_enode(v)->get_root();
                m_value2var.reserve(c + 1, null_theory_var);
                theory_var u = m_value2var[c];
                if (u != null_theory_var && r != th.get_enode(u)->get_root()) {
                    enforce_ackerman(u, v);
                    return false;
                }
                if (c >= seq.max_char()) {
                    enforce_value_bound(v);
                    return false;
                }
                for (enode* n : *r) {
                    u = n->get_th_var(th.get_id());
                    if (u == null_theory_var)
                        continue;
                    if (get_value(u, d) && d != c) {
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
        c = 'a';
        for (unsigned v = th.get_num_vars(); v-- > 0; ) {
            expr* e = th.get_expr(v);
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
                for (enode* n : *th.get_enode(v)) 
                    m_var2value[n->get_th_var(th.get_id())] = c;
                m_value2var.reserve(c + 1, null_theory_var);
                m_value2var[c] = v;
                values.insert(c);
            }                       
        }
        return true;
    }

    void seq_char::enforce_bits() {
        TRACE("seq", tout << "enforce bits\n";);
        for (unsigned v = th.get_num_vars(); v-- > 0; ) {
            expr* e = th.get_expr(v);
            if (seq.is_char(e) && th.get_enode(v)->is_root() && !has_bits(v))
                init_bits(v);
        }        
    }

    void seq_char::enforce_value_bound(theory_var v) {
        TRACE("seq", tout << "enforce bound " << v << "\n";);
        enode* n = th.ensure_enode(seq.mk_char(seq.max_char()));
        theory_var w = n->get_th_var(th.get_id());                    
        SASSERT(has_bits(w));
        init_bits(v);
        auto const& mbits = get_ebits(w);
        auto const& bits = get_ebits(v);
        expr_ref le(m);
        m_bb.mk_ule(bits.size(), bits.c_ptr(), mbits.c_ptr(), le);
        ctx().assign(th.mk_literal(le), nullptr);
        ++m_stats.m_num_bounds;
    }

    void seq_char::enforce_ackerman(theory_var v, theory_var w) {
        if (v > w) 
            std::swap(v, w);
        TRACE("seq", tout << "enforce ackerman " << v << " " << w << "\n";);
        literal eq = th.mk_literal(m.mk_eq(th.get_expr(v), th.get_expr(w)));
        ctx().mark_as_relevant(eq);
        literal_vector lits;
        init_bits(v);
        init_bits(w);
        auto& a = get_ebits(v);
        auto& b = get_ebits(w);
        for (unsigned i = a.size(); i-- > 0; ) {
            // eq => a = b
            literal beq = th.mk_eq(a[i], b[i], false);
            lits.push_back(~beq);
            ctx().mark_as_relevant(beq);
            ctx().mk_th_axiom(th.get_id(), ~eq, beq);
        }        
        // a = b => eq
        lits.push_back(eq);
        ctx().mk_th_axiom(th.get_id(), lits.size(), lits.c_ptr());
        ++m_stats.m_num_ackerman;
    }
    
    unsigned seq_char::get_value(theory_var v) {
        return m_var2value[v];
    }

    bool seq_char::get_value(theory_var v, unsigned& c) {
        if (!has_bits(v))
            return false;
        auto const & b = get_bits(v);
        c = 0;
        unsigned p = 1;
        for (literal lit : b) {
            if (ctx().get_assignment(lit) == l_true)
                c += p;
            p *= 2;
        }
        return true;
    }

    void seq_char::collect_statistics(::statistics& st) const {
        st.update("seq char ackerman", m_stats.m_num_ackerman);
        st.update("seq char bounds",   m_stats.m_num_bounds);
        st.update("seq char2bit",      m_stats.m_num_blast);
    }
}

