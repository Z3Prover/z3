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
#include "smt/smt_arith_value.h"
#include "util/trail.h"

namespace smt {

    seq_unicode::seq_unicode(theory& th):
        th(th),
        m(th.get_manager()),
        seq(m),
        m_qhead(0),
        m_var_value_hash(*this),
        m_var_value_eq(*this),
        m_var_value_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_var_value_hash, m_var_value_eq)
    {}

    // <= atomic constraints on characters
    void seq_unicode::assign_le(theory_var v1, theory_var v2, literal lit) {
        dl.init_var(v1);
        dl.init_var(v2);
        ctx().push_trail(push_back_vector<context, svector<theory_var>>(m_asserted_edges));
        m_asserted_edges.push_back(dl.add_edge(v1, v2, s_integer(0), lit));
    }

    // < atomic constraint on characters
    void seq_unicode::assign_lt(theory_var v1, theory_var v2, literal lit) {
        dl.init_var(v1);
        dl.init_var(v2);
        ctx().push_trail(push_back_vector<context, svector<theory_var>>(m_asserted_edges));
        m_asserted_edges.push_back(dl.add_edge(v1, v2, s_integer(1), lit));
    }

    literal seq_unicode::mk_literal(expr* e) { 
        expr_ref _e(e, m);
        th.ensure_enode(e);
        return ctx().get_literal(e);
    }

    void seq_unicode::adapt_eq(theory_var v1, theory_var v2) {
        expr* e1 = th.get_expr(v1);
        expr* e2 = th.get_expr(v2);
        literal eq = th.mk_eq(e1, e2, false);
        literal le = mk_literal(seq.mk_le(e1, e2));
        literal ge = mk_literal(seq.mk_le(e2, e1));
        add_axiom(~eq, le);
        add_axiom(~eq, ge);
        add_axiom(le, ge, eq);
    }
        
    // = on characters
    void seq_unicode::new_eq_eh(theory_var v1, theory_var v2) {
        adapt_eq(v1, v2);
    }

    // != on characters
    void seq_unicode::new_diseq_eh(theory_var v1, theory_var v2) {  
        adapt_eq(v1, v2);
    }

    bool seq_unicode::final_check() {
        // ensure all variables are above 0 and less than zstring::max_char()
        bool added_constraint = false;
        // TBD: shift assignments on variables that are not lower-bounded, so that they are "nice" (have values 'a', 'b', ...)
        // TBD: set "zero" to a zero value.
        // TBD: ensure that unicode constants have the right values
        arith_util a(m);
        arith_value avalue(m);
        avalue.init(&ctx());
        for (unsigned v = 0; !ctx().inconsistent() && v < th.get_num_vars(); ++v) {
            if (!seq.is_char(th.get_expr(v)))
                continue;
            dl.init_var(v);
            auto val = dl.get_assignment(v).get_int();
            if (val > static_cast<int>(zstring::max_char())) {
                expr_ref ch(seq.str.mk_char(zstring::max_char()), m);
                enode* n = th.ensure_enode(ch);
                theory_var v_max = n->get_th_var(th.get_id());
                assign_le(v, v_max, null_literal);
                added_constraint = true;
                continue;
            }
            if (val < 0) {
                expr_ref ch(seq.str.mk_char(0), m);
                enode* n = th.ensure_enode(ch);
                theory_var v_min = n->get_th_var(th.get_id());
                assign_le(v_min, v, null_literal);
                dl.init_var(v_min);
                dl.set_to_zero(v_min);
                added_constraint = true;
                continue;
            }
            // ensure str.to_code(unit(v)) = val
            expr_ref ch(m);
            if (false) {
                /// m_rewrite.coalesce_chars();
                ch = seq.str.mk_string(zstring(val));
            }
            else {
                ch = seq.str.mk_unit(seq.str.mk_char(val));
            }
            expr_ref code(seq.str.mk_to_code(ch), m);
            rational val2;
            if (avalue.get_value(code, val2) && val2 == rational(val))
                continue;
            add_axiom(th.mk_eq(code, a.mk_int(val), false));
            added_constraint = true;
        }
        if (added_constraint)
            return false;
        
        // ensure equalities over shared symbols
        if (th.assume_eqs(m_var_value_table))
            return false;
        
        return true;
    }
    
    void seq_unicode::propagate() {
        return;
        ctx().push_trail(value_trail<smt::context, unsigned>(m_qhead));
        for (; m_qhead < m_asserted_edges.size() && !ctx().inconsistent(); ++m_qhead) {
            propagate(m_asserted_edges[m_qhead]);
        }        
    }
    
    void seq_unicode::propagate(edge_id edge) {
        return;
        if (dl.enable_edge(edge)) 
            return;
        dl.traverse_neg_cycle2(false, m_nc_functor);
        literal_vector const & lits = m_nc_functor.get_lits();
        vector<parameter> params;
        if (m.proofs_enabled()) {
            params.push_back(parameter(symbol("farkas")));
            for (unsigned i = 0; i <= lits.size(); ++i) {
                params.push_back(parameter(rational(1)));
            }
        }
        ctx().set_conflict(
            ctx().mk_justification(
                ext_theory_conflict_justification(
                    th.get_id(), ctx().get_region(),
                    lits.size(), lits.c_ptr(), 
                    0, nullptr, 
                    params.size(), params.c_ptr())));;
    }

    unsigned seq_unicode::get_value(theory_var v) {
        dl.init_var(v);
        auto val = dl.get_assignment(v);
        return val.get_int();
    }

}

