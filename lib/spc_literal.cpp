/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_literal.cpp

Abstract:

    Superposition Calculus literal

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#include"spc_literal.h"
#include"ast_pp.h"

namespace spc {

    void literal::try_to_orient(order & o) {
        ast_manager & m = o.get_manager();
        if (!m_sign && m.is_eq(m_atom)) {
            expr * lhs = to_app(m_atom)->get_arg(0);
            expr * rhs = to_app(m_atom)->get_arg(1);
            TRACE("spc_orient", tout << "trying to orient:\n" << mk_pp(lhs, m) << "\n" << mk_pp(rhs, m) << "\n";);
            switch (o.compare(lhs, rhs)) {
            case order::GREATER:
                m_oriented = true;
                m_left     = true;
                TRACE("spc_orient", tout << "greater\n";);
                return;
            case order::LESSER:
                m_oriented = true;
                m_left     = false;
                TRACE("spc_orient", tout << "smaller\n";);
                return;
            default:
                return;
            }
        }
    }
        
    void literal::get_stat(literal_stat & stat) {
        get_expr_stat(m_atom, stat);
        m_stats       = true;
        m_ground      = stat.m_ground;
        m_sym_count   = stat.m_sym_count   > SYM_COUNT_MAX   ? SYM_COUNT_MAX   : stat.m_sym_count;
        m_depth       = stat.m_depth       > DEPTH_MAX       ? DEPTH_MAX       : stat.m_depth;
        m_const_count = stat.m_const_count > CONST_COUNT_MAX ? CONST_COUNT_MAX : stat.m_const_count;
    }
    
    expr * literal::to_expr(ast_manager & m) const {
        if (is_true(m)) 
            return m.mk_true();
        else if (is_false(m))
            return m.mk_false();
        else if (m_sign)
            return m.mk_not(m_atom);
        else
            return m_atom;
    }

    void literal::display(std::ostream & out, ast_manager & m, bool detailed) const {
        pp_params p;
        p.m_pp_single_line = true;
        
        if (m_sign) 
            out << "(not ";
        
        if (m_oriented) {
            expr * lhs = to_app(m_atom)->get_arg(0);
            expr * rhs = to_app(m_atom)->get_arg(1);
            if (!m_left)
                std::swap(lhs, rhs);
            out << "(-> ";
            ast_pp(out, lhs, m, p);
            out << " ";
            ast_pp(out, rhs, m, p);
            out << ")";
        }
        else {
            ast_pp(out, m_atom, m, p);            
        }

        if (m_sign) 
            out << ")";
    
        if (detailed && m_stats) {
            out << "[" << m_ground << ", " << m_depth << ", " << m_sym_count << ", " << m_const_count << "]";
        }
    
        if (m_selected)
            out << "$";
        if (m_p_indexed)
            out << "!";
        if (m_r_indexed)
            out << "@";
    }

    void display(std::ostream & out, unsigned num_lists, literal * lits, ast_manager & m, bool detailed) {
        for (unsigned i = 0; i < num_lists; i++) {
            if (i > 0) out << " ";
            lits[i].display(out, m, detailed);
        }
    }

    /**
       \brief Given an eq literal store in lhs and rhs the left and right hand sides. If they can be oriented
       given the substitution s, then return true, and make lhs the maximal one.
    */
    bool can_orient(order & o, literal const & l, unsigned offset, substitution * s, expr * & lhs, expr * & rhs) {
        SASSERT(o.get_manager().is_eq(l.atom()));
        lhs = l.lhs();
        rhs = l.rhs();
        if (l.is_oriented()) {
            if (!l.is_left())
                std::swap(lhs, rhs);
            return true;
        }
        else {
            order::result comp = o.compare(lhs, rhs, offset, s);
            if (comp == order::GREATER)
                return true;
            else if (comp == order::LESSER) {
                std::swap(lhs, rhs);
                return true;
            }
            return false;
        }
    }

    /**
       \brief Compare literal signs. Negative sign is bigger than the positive one.
    */
    inline order::result compare_signs(bool sign1, bool sign2) {
        if (sign1 && !sign2)
            return order::GREATER;
        else if (!sign1 && sign2)
            return order::LESSER;
        else
            return order::EQUAL;
    }

    /**
       \brief Compare two literals (modulo a substitution) using the given term ordering.
    */
    order::result compare(order & o, literal const & l1, literal const & l2, unsigned offset, substitution * s) {
        ast_manager & m = o.get_manager();
        expr * n1 = l1.atom();
        expr * n2 = l2.atom();
        bool is_eq1 = m.is_eq(n1);
        bool is_eq2 = m.is_eq(n2);
        if (is_eq1 && is_eq2) {
            expr * lhs1 = 0;
            expr * rhs1 = 0;
            expr * lhs2 = 0;
            expr * rhs2 = 0;
            bool oriented1 = can_orient(o, l1, offset, s, lhs1, rhs1);
            bool oriented2 = can_orient(o, l2, offset, s, lhs2, rhs2);
            if (oriented1) {
                // equation 1 can be oriented
                if (oriented2) {
                    // equation 2 can be oriented
                    // both equations are oriented
                    SASSERT(oriented1);
                    SASSERT(oriented2);
                    order::result r = o.compare(lhs1, lhs2, offset, s);
                    if (r == order::EQUAL) {
                        if (l1.pos()) {
                            if (l2.pos()) 
                                return o.compare(rhs1, rhs2, offset, s);
                            else
                                return order::LESSER;
                        }
                        else {
                            if (l2.pos())
                                return order::GREATER;
                            else
                                return o.compare(rhs1, rhs2, offset, s);
                        }
                    }
                    return r;
                }
                else {
                    // equation 2 cannot be oriented
                    SASSERT(oriented1);
                    SASSERT(!oriented2);
                    SASSERT(o.compare(lhs1, rhs1, offset, s) == order::GREATER);
                    if (o.equal(lhs1, lhs2, offset, s)) {
                        order::result r = o.compare(rhs1, rhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    if (o.equal(lhs1, rhs2, offset, s)) {
                        order::result r = o.compare(rhs1, lhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    order::result lhs1_lhs2 = o.compare(lhs1, lhs2, offset, s);
                    order::result lhs1_rhs2 = o.compare(lhs1, rhs2, offset, s);
                    if (lhs1_lhs2 == lhs1_rhs2) 
                        return lhs1_lhs2;
                    order::result rhs1_rhs2 = o.compare(rhs1, rhs2, offset, s);
                    if (lhs1_lhs2 == rhs1_rhs2)
                        return lhs1_lhs2;
                    if (lhs1_rhs2 == order::LESSER && rhs1_rhs2 == order::LESSER)
                        return order::LESSER;
                    order::result rhs1_lhs2 = o.compare(rhs1, lhs2, offset, s);
                    if (lhs1_lhs2 == order::LESSER && rhs1_lhs2 == order::LESSER)
                        return order::LESSER;
                    return order::UNCOMPARABLE;
                }
            }
            else {
                // equation 1 cannot be oriented
                if (oriented2) {
                    SASSERT(!oriented1);
                    SASSERT(oriented2);
                    // equation 2 can be oriented
                    if (o.equal(lhs1, lhs2, offset, s)) {
                        order::result r = o.compare(rhs1, rhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    if (o.equal(rhs1, lhs2, offset, s)) {
                        order::result r = o.compare(lhs1, rhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    order::result lhs1_lhs2 = o.compare(lhs1, lhs2, offset, s);
                    order::result rhs1_lhs2 = o.compare(rhs1, lhs2, offset, s);
                    if (lhs1_lhs2 == rhs1_lhs2)
                        return lhs1_lhs2;
                    order::result rhs1_rhs2 = o.compare(rhs1, rhs2, offset, s);
                    if (lhs1_lhs2 == rhs1_rhs2)
                        return lhs1_lhs2;
                    if (rhs1_lhs2 == order::GREATER && rhs1_rhs2 == order::GREATER)
                        return order::GREATER;
                    order::result lhs1_rhs2 = o.compare(lhs1, rhs2, offset, s);
                    if (lhs1_lhs2 == order::GREATER && lhs1_rhs2 == order::GREATER)
                        return order::GREATER;
                    return order::UNCOMPARABLE;
                }
                else {
                    SASSERT(!oriented1);
                    SASSERT(!oriented2);
                    if (o.equal(lhs1, lhs2, offset, s)) {
                        order::result r = o.compare(rhs1, rhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    if (o.equal(rhs1, lhs2, offset, s)) {
                        order::result r = o.compare(lhs1, rhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    if (o.equal(lhs1, rhs2, offset, s)) {
                        order::result r = o.compare(rhs1, lhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    if (o.equal(rhs1, rhs2, offset, s)) {
                        order::result r = o.compare(lhs1, lhs2, offset, s);
                        if (r == order::EQUAL)
                            return compare_signs(l1.sign(), l2.sign());
                        return r;
                    }
                    
                    order::result r;
                    order::result aux;
                    switch (o.compare(lhs1, lhs2, offset, s)) {
                    case order::GREATER:
                        r   = o.compare(lhs1, rhs2, offset, s);
                        if (r == order::GREATER)
                            return order::GREATER;
                        aux = o.compare(rhs1, rhs2, offset, s);
                        if (aux == order::GREATER)
                            return order::GREATER;
                        if (r == order::LESSER && aux == order::LESSER)
                            return order::LESSER;
                        SASSERT(r   != order::EQUAL);
                        SASSERT(aux != order::EQUAL);
                        return order::UNCOMPARABLE;
                    case order::LESSER:
                        r   = o.compare(rhs1, lhs2, offset, s);
                        if (r == order::LESSER)
                            return order::LESSER;
                        aux = o.compare(rhs1, rhs2, offset, s);
                        if (aux == order::LESSER)
                            return order::LESSER;
                        if (r == order::GREATER && aux == order::GREATER)
                            return order::GREATER;
                        SASSERT(r   != order::EQUAL);
                        SASSERT(aux != order::EQUAL);
                        return order::UNCOMPARABLE;
                    case order::EQUAL:
                        UNREACHABLE();
                        return order::UNKNOWN;
                    default:
                        switch (o.compare(lhs1, rhs2, offset, s)) {
                        case order::GREATER:
                            if (o.compare(rhs1, lhs2, offset, s) == order::GREATER)
                                return order::GREATER;
                            return order::UNCOMPARABLE;
                        case order::LESSER:
                            if (o.compare(rhs1, lhs2, offset, s) == order::LESSER ||
                                o.compare(rhs1, rhs2, offset, s) == order::LESSER)
                                return order::LESSER;
                            return order::UNCOMPARABLE;
                        case order::EQUAL:
                            UNREACHABLE();
                            return order::UNKNOWN;
                        default:
                            if (o.compare(rhs1, lhs2, offset, s) == order::GREATER &&
                                o.compare(rhs1, rhs2, offset, s) == order::GREATER)
                                return order::GREATER;
                            return order::UNCOMPARABLE;
                        }
                    }
                }
            }
        }
        else if (is_eq1) {
            expr * lhs1 = l1.lhs();
            expr * rhs1 = l1.rhs();
            if (l1.is_oriented() && !l1.is_left())
                std::swap(lhs1, rhs1);
            order::result r = o.compare(lhs1, n2, offset, s);
            if (!l1.is_oriented() || r != order::GREATER) {
                order::result r2 = o.compare(rhs1, n2, offset, s);
                if (r2 == order::GREATER)
                    return order::GREATER;
                else if (r != r2)
                    return order::UNCOMPARABLE;
            }
            return r;
        }
        else if (is_eq2) {
            expr * lhs2 = l2.lhs();
            expr * rhs2 = l2.rhs();
            if (l2.is_oriented() && !l2.is_left())
                std::swap(lhs2, rhs2);
            order::result r = o.compare(n1, lhs2, offset, s);
            if (!l1.is_oriented() || r != order::LESSER) {
                order::result r2 = o.compare(n1, rhs2, offset, s);
                if (r2 == order::LESSER)
                    return order::LESSER;
                else if (r != r2)
                    return order::UNCOMPARABLE;
            }
            return r;
        }
        else {
            order::result r = o.compare(n1, n2, offset, s);
            if (r == order::EQUAL)
                return compare_signs(l1.sign(), l2.sign());
            return r;
        }
    }

    bool greater(order & o, literal const & l1, literal const & l2, unsigned offset, substitution * s) {
        order::result r = compare(o, l1, l2, offset, s);
        TRACE("literal_order", ast_manager & m = o.get_manager();
              tout << "comparing ";
              l1.display(tout, m);
              tout << " ";
              l2.display(tout, m);
              tout << " : " << r << "\n";);
        return r == order::GREATER;
    }

    void found_literals::insert(literal const & l) {
        unsigned id = l.get_id();
        m_marks.reserve(id+1);
        if (!m_marks.get(id)) {
            m_marks.set(id);
            m_lit_ids.push_back(id);
        }
    }

    bool found_literals::contains(literal const & l) const {
        unsigned id = l.get_id();
        return id < m_marks.size() && m_marks.get(id);
    }

    bool found_literals::contains_neg(literal const & l) const {
        unsigned id = l.get_neg_id();
        return id < m_marks.size() && m_marks.get(id);
    }
    
    void found_literals::reset() {
        unsigned_vector::iterator it  = m_lit_ids.begin();
        unsigned_vector::iterator end = m_lit_ids.end();
        for (; it != end; ++it) 
            m_marks.unset(*it);
        m_lit_ids.reset();
    }

    void literal_buffer::reset() { 
        buffer<literal>::iterator it  = m_lits.begin();
        buffer<literal>::iterator end = m_lits.end();
        for (; it != end; ++it) 
            m_manager.dec_ref(it->atom());
        m_lits.reset();
    }


    expr * mk_or(ast_manager & m, unsigned num_lists, literal * lits) {
        if (num_lists == 0) 
            return m.mk_false();
        else if (num_lists == 1)
            return lits[0].to_expr(m);
        else {
            ptr_buffer<expr> new_exprs;
            for (unsigned i = 0; i < num_lists; i++)
                new_exprs.push_back(lits[i].to_expr(m));
            return m.mk_or(new_exprs.size(), new_exprs.c_ptr());
        }
    }

};
