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

#define NICE_MIN 97
#define NICE_MAX 122

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
    edge_id seq_unicode::assign_le(theory_var v1, theory_var v2, literal lit) {
        dl.init_var(v1);
        dl.init_var(v2);
        return add_edge(v1, v2, 0, lit);
    }

    // < atomic constraint on characters
    edge_id seq_unicode::assign_lt(theory_var v1, theory_var v2, literal lit) {
        dl.init_var(v1);
        dl.init_var(v2);
        return add_edge(v1, v2, -1, lit);
    }

    edge_id seq_unicode::add_edge(theory_var v1, theory_var v2, int diff, literal lit) {
        ctx().push_trail(push_back_vector<context, svector<theory_var>>(m_asserted_edges));
        edge_id new_edge = dl.add_edge(v2, v1, s_integer(diff), lit);
        m_asserted_edges.push_back(new_edge);
        return new_edge;
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

    bool seq_unicode::try_bound(theory_var v, unsigned min, unsigned max) {
        push_scope();
        dl.init_var(v);
        theory_var v0 = ensure0();
        bool sat = dl.enable_edge(dl.add_edge(v, v0, s_integer(-1 * min), null_literal));
        if (!sat) {
            pop_scope(1);
            return false;
        }
        sat = dl.enable_edge(dl.add_edge(v0, v, s_integer(max), null_literal));
        if (!sat) {
            pop_scope(1);
            return false;
        }
        pop_scope(1);
        return true;
    }

    bool seq_unicode::try_assignment(theory_var v, unsigned ch) {
        return try_bound(v, ch, ch);
    }

    void seq_unicode::try_make_nice(svector<theory_var> char_vars) {

        // Try for each character
        unsigned i = 0;
        for (auto v : char_vars) {

            // Skip character constants, since they can't be changed
            if (seq.is_any_const_char(th.get_expr(v))) continue;

            // Check if the value is already nice
            int val = get_value(v);
            if (val <= NICE_MAX && val >= NICE_MIN) continue;

            // Try assigning the variable to a nice value
            if (try_bound(v, NICE_MIN, NICE_MAX)) {
                try_assignment(v, NICE_MIN + i);
                i++;
            }
        }
    }


    bool seq_unicode::enforce_char_range(svector<theory_var> char_vars) {

        // Continue checking until convergence or inconsistency
        bool done = false;
        while (!done) {
            done = true;

            // Iterate over variables and ensure that their values are in 0 <= v <= zstring::max_char()
            for (auto v : char_vars) {
                int val = get_value(v);
                if (val < 0) {
                    done = false;

                    // v0 = 0
                    theory_var v0 = ensure0();

                    // Add constraint on v and check consistency
                    propagate(assign_le(v0, v, null_literal));
                    if (ctx().inconsistent()) return false;
                }
                if (val > static_cast<int>(zstring::max_char())) {
                    done = false;

                    // v_maxchar = zstring::max_char()
                    expr_ref ch(seq.str.mk_char(zstring::max_char()), m);
                    enode* n = th.ensure_enode(ch);
                    theory_var v_maxchar = n->get_th_var(th.get_id());

                    // Add constraint on v and check consistency
                    propagate(assign_le(v, v_maxchar, null_literal));
                    if (ctx().inconsistent()) return false;
                }
            }
        }
        return true;
    }

    bool seq_unicode::enforce_char_codes(svector<theory_var> char_vars) {

        // Iterate over all theory variables until the context is inconsistent
        bool success = true;
        arith_util a(m);
        arith_value avalue(m);
        avalue.init(&ctx());
        uint_set seen;
        for (auto v : char_vars) {
            if (ctx().inconsistent()) break;

            // Make sure we haven't seen this value already
            int val = get_value(v);
            if (seen.contains(val)) continue;
            seen.insert(val);

            // Ensure str.to_code(unit(v)) = val
            expr_ref ch(seq.str.mk_unit(seq.str.mk_char(val)), m);
            expr_ref code(seq.str.mk_to_code(ch), m);
            rational val2;

            if (avalue.get_value(code, val2) && val2 == rational(val)) continue;

            add_axiom(th.mk_eq(code, a.mk_int(val), false));
            success = false;
        }

        // If a constraint was added without being propagated, we can't be finished yet
        return success;
    }

    bool seq_unicode::final_check() {

        // Get character variables
        svector<theory_var> char_vars;
        for (unsigned v = 0; v < th.get_num_vars(); ++v) {
            if(seq.is_char(th.get_expr(v))) char_vars.push_back(v);
        }

        // Shift assignments on variables, so that they are "nice" (have values 'a', 'b', ...)
        try_make_nice(char_vars);

        // Validate that all variables must be in 0 <= v <= zstring::max_char()
        if (!enforce_char_range(char_vars)) return false;

        // Make sure str.to_code(unit(v)) = val for all character variables
        if (!enforce_char_codes(char_vars)) return false;

        // Enforce equalities over shared symbols
        if (th.assume_eqs(m_var_value_table)) return false;

        // If all checks pass, we're done
        return true;
    }

    void seq_unicode::enforce_is_value(app* n, unsigned ch) {
        enode* e = th.ensure_enode(n);
        theory_var v = e->get_th_var(th.get_id());
        if (v == null_theory_var)
            return;
        enforce_tv_is_value(v, ch);
    }

    void seq_unicode::enforce_tv_is_value(theory_var v, unsigned ch) {
        dl.init_var(v);
        if (ch == 0) {
            dl.set_to_zero(v);
        }
        else {
            theory_var v0 = ensure0();
            add_edge(v, v0, ch, null_literal);  // v - v0 <= ch
            add_edge(v0, v, -static_cast<int>(ch), null_literal);  // v0 - v <= -ch
        }
    }

    theory_var seq_unicode::ensure0() {
        expr_ref ch(seq.str.mk_char(0), m);
        enode* n = th.ensure_enode(ch);
        theory_var v0 = n->get_th_var(th.get_id());
        dl.init_var(v0);
        dl.set_to_zero(v0);
        return v0;
    }

    void seq_unicode::propagate() {
        ctx().push_trail(value_trail<smt::context, unsigned>(m_qhead));
        for (; m_qhead < m_asserted_edges.size() && !ctx().inconsistent(); ++m_qhead) {
            propagate(m_asserted_edges[m_qhead]);
        }
    }

    void seq_unicode::propagate(edge_id edge) {
        TRACE("seq", dl.display(tout << "propagate " << edge << " "););
        if (dl.enable_edge(edge))
            return;
        m_nc_functor.reset();
        dl.traverse_neg_cycle2(false, m_nc_functor);
        literal_vector const & lits = m_nc_functor.get_lits();
        vector<parameter> params;
        if (m.proofs_enabled()) {
            params.push_back(parameter(symbol("farkas")));
            for (unsigned i = 0; i <= lits.size(); ++i) {
                params.push_back(parameter(rational(1)));
            }
        }
        TRACE("seq", tout << "conflict " << lits << "\n";);
        ctx().set_conflict(
            ctx().mk_justification(
                ext_theory_conflict_justification(
                    th.get_id(), ctx().get_region(),
                    lits.size(), lits.c_ptr(),
                    0, nullptr,
                    params.size(), params.c_ptr())));
        SASSERT(ctx().inconsistent());
    }

    unsigned seq_unicode::get_value(theory_var v) {
        dl.init_var(v);
        auto val = dl.get_assignment(v);
        return val.get_int();
    }

    void seq_unicode::push_scope() {
        dl.push();
    }

    void seq_unicode::pop_scope(unsigned n) {
        dl.pop(n);
    }


}
