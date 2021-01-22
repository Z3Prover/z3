/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_unicode.cpp

Abstract:

    Solver for unicode characters

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-16

--*/

#include "smt/seq_unicode.h"
#include "smt/smt_context.h"
#include "util/trail.h"

namespace smt {

    seq_unicode::seq_unicode(theory& th):
        th(th),
        m(th.get_manager()),
        seq(m),
        bv(m),
        m_bb(m, ctx().get_fparams())
    {
        m_enabled = gparams::get_value("unicode") == "true";
    }


    struct seq_unicode::reset_bits : public trail<context> {
        seq_unicode& s;
        unsigned idx;

        reset_bits(seq_unicode& s, unsigned idx):
            s(s),
            idx(idx)
        {}

        void undo(context& ctx) override {
            s.m_bits[idx].reset();
            s.m_ebits[idx].reset();
        }
    };

    bool seq_unicode::has_bits(theory_var v) const {
        return (m_bits.size() > (unsigned)v) && !m_bits[v].empty();
    }

    void seq_unicode::init_bits(theory_var v) {
        if (has_bits(v))
            return;
        m_bits.reserve(v + 1);
        auto& bits = m_bits[v];
        expr* e = th.get_expr(v);
        while ((unsigned) v >= m_ebits.size())
            m_ebits.push_back(expr_ref_vector(m));
        ctx().push_trail(reset_bits(*this, v));
        auto& ebits = m_ebits[v];
        SASSERT(ebits.empty());
        for (unsigned i = 0; i < zstring::num_bits(); ++i) 
            ebits.push_back(seq.mk_char_bit(e, i));
        ctx().internalize(ebits.c_ptr(), ebits.size(), true);
        for (expr* arg : ebits)
            bits.push_back(literal(ctx().get_bool_var(arg)));            
        for (literal bit : bits)
            ctx().mark_as_relevant(bit);
    }

    void seq_unicode::internalize_le(literal lit, app* term) {
        expr* x = nullptr, *y = nullptr;
        VERIFY(seq.is_char_le(term, x, y));
        theory_var v1 = ctx().get_enode(x)->get_th_var(th.get_id());
        theory_var v2 = ctx().get_enode(y)->get_th_var(th.get_id());
        auto const& b1 = get_ebits(v1);
        auto const& b2 = get_ebits(v2);
        expr_ref e(m);
        m_bb.mk_ule(b1.size(), b1.c_ptr(), b2.c_ptr(), e);
        literal le = th.mk_literal(e);
        ctx().mk_th_axiom(th.get_id(), ~lit, le);
        ctx().mk_th_axiom(th.get_id(), lit, ~le);
    }

    literal_vector const& seq_unicode::get_bits(theory_var v) {
        init_bits(v);
        return m_bits[v];
    }

    expr_ref_vector const& seq_unicode::get_ebits(theory_var v) {
        init_bits(v);
        return m_ebits[v];
    }
        
    // = on characters
    void seq_unicode::new_eq_eh(theory_var v, theory_var w) {  
        if (has_bits(v) && has_bits(w)) {
            auto& a = get_bits(v);
            auto& b = get_bits(w);
            unsigned i = a.size();
            literal _eq = null_literal;
            auto eq = [&]() {
                if (_eq == null_literal) 
                    _eq = th.mk_literal(m.mk_eq(th.get_expr(v), th.get_expr(w)));
                return _eq;
            };
            for (; i-- > 0; ) {
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
    void seq_unicode::new_diseq_eh(theory_var v, theory_var w) {  
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

    void seq_unicode::new_const_char(theory_var v, unsigned c) {
        auto& bits = get_bits(v);
        for (auto b : bits) {
            bool bit = (0 != (c & 1));
            ctx().assign(bit ? b : ~b, nullptr);
            c >>= 1;                
        }
    }

    /**
     * 1. Extract values of roots.
     *    Check that values of roots are unique.
     *    Check that values assigned to non-roots align with root values.
     *    Enforce that values of roots are within max_char.
     * 2. Assign values to other roots that haven't been assigned.
     * 3. Assign values to non-roots using values of roots.
     */
    bool seq_unicode::final_check() {   
        m_var2value.reset();
        m_var2value.resize(th.get_num_vars(), UINT_MAX);
        m_value2var.reset();

        // extract the initial set of constants.
        uint_set values;
        unsigned c = 0, d = 0;
        bool requires_fix = false;
        for (unsigned v = th.get_num_vars(); v-- > 0; ) {
            expr* e = th.get_expr(v);
            if (seq.is_char(e) && m_var2value[v] == UINT_MAX && get_value(v, c)) {
                CTRACE("seq", seq.is_char(e), tout << mk_pp(e, m) << " root: " << th.get_enode(v)->is_root() << " is_value: " << get_value(v, c) << "\n";);
                enode* r = th.get_enode(v)->get_root();
                m_value2var.reserve(c + 1, null_theory_var);
                theory_var u = m_value2var[c];
                if (u != null_theory_var && r != th.get_enode(u)->get_root()) {
                    enforce_ackerman(u, v);
                    requires_fix = true;
                    continue;
                }
                if (c >= zstring::max_char()) {
                    enforce_value_bound(v);
                    requires_fix = true;
                    continue;
                }

                for (enode* n : *r) {
                    u = n->get_th_var(th.get_id());
                    if (get_value(u, d) && d != c) {
                        enforce_ackerman(u, v);
                        requires_fix = true;
                        break;
                    }
                    m_var2value[u] = c;
                }
                values.insert(c);
                m_value2var[c] = v;
            }
        }
        if (requires_fix)
            return false;
        
        // assign values to other unassigned nodes
        c = 'a';
        for (unsigned v = th.get_num_vars(); v-- > 0; ) {
            expr* e = th.get_expr(v);
            if (seq.is_char(e) && m_var2value[v] == UINT_MAX) {
                d = c;
                while (values.contains(c)) {
                    c = (c + 1) % zstring::max_char();
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

    void seq_unicode::enforce_bits() {
        TRACE("seq", tout << "enforce bits\n";);
        for (unsigned v = th.get_num_vars(); v-- > 0; ) {
            expr* e = th.get_expr(v);
            if (seq.is_char(e) && th.get_enode(v)->is_root() && !has_bits(v))
                init_bits(v);
        }        
    }

    void seq_unicode::enforce_value_bound(theory_var v) {
        TRACE("seq", tout << "enforce bound " << v << "\n";);
        enode* n = th.ensure_enode(seq.mk_char(zstring::max_char()));
        theory_var w = n->get_th_var(th.get_id());                    
        SASSERT(has_bits(w));
        auto const& mbits = get_ebits(w);
        auto const& bits = get_ebits(v);
        expr_ref le(m);
        m_bb.mk_ule(bits.size(), bits.c_ptr(), mbits.c_ptr(), le);
        ctx().assign(th.mk_literal(le), nullptr);
    }

    void seq_unicode::enforce_ackerman(theory_var v, theory_var w) {
        TRACE("seq", tout << "enforce ackerman " << v << " " << w << "\n";);
        literal eq = th.mk_literal(m.mk_eq(th.get_expr(v), th.get_expr(w)));
        ctx().mark_as_relevant(eq);
        literal_vector lits;
        auto& a = get_ebits(v);
        auto& b = get_ebits(w);
        for (unsigned i = a.size(); i-- > 0; ) {
            literal beq = th.mk_eq(a[i], b[i], false);
            ctx().mark_as_relevant(beq);
            lits.push_back(~beq);
            // eq => a = b
            ctx().mk_th_axiom(th.get_id(), ~eq, beq);
        }        
        // a = b => eq
        lits.push_back(eq);
        ctx().mk_th_axiom(th.get_id(), lits.size(), lits.c_ptr());
    }
    
    unsigned seq_unicode::get_value(theory_var v) {
        return m_var2value[v];
    }

    bool seq_unicode::get_value(theory_var v, unsigned& c) {
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
}

