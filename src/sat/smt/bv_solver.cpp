/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_internalize.cpp

Abstract:

    Internalize utilities for bit-vector solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-02

--*/

#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "tactic/tactic_exception.h"

namespace bv {

    void solver::fixed_var_eh(theory_var v) {
        
    }

    /**
       \brief Find an unassigned bit for m_wpos[v], if such bit cannot be found invoke fixed_var_eh
    */
    void solver::find_wpos(theory_var v) {
        literal_vector const & bits = m_bits[v];
        unsigned sz                 = bits.size();
        unsigned & wpos             = m_wpos[v];
        unsigned init               = wpos;
        for (; wpos < sz; wpos++) {
            TRACE("find_wpos", tout << "curr bit: " << bits[wpos] << "\n";);
            if (s().value(bits[wpos]) == l_undef) {
                TRACE("find_wpos", tout << "moved wpos of v" << v << " to " << wpos << "\n";);
                return;
            }
        }
        wpos = 0;
        for (; wpos < init; wpos++) {
            if (s().value(bits[wpos]) == l_undef) {
                TRACE("find_wpos", tout << "moved wpos of v" << v << " to " << wpos << "\n";);
                return;
            }
        }
        TRACE("find_wpos", tout << "v" << v << " is a fixed variable.\n";);
        fixed_var_eh(v);
    }

    /**
   \brief v[idx] = ~v'[idx], then v /= v' is a theory axiom.
*/
    void solver::find_new_diseq_axioms(var_pos_occ* occs, theory_var v, unsigned idx) {
        literal l = m_bits[v][idx];
        l.neg();
        while (occs) {
            theory_var v2 = occs->m_var;
            unsigned   idx2 = occs->m_idx;
            if (idx == idx2 && m_bits[v2][idx2] == l && get_bv_size(v2) == get_bv_size(v))
                mk_new_diseq_axiom(v, v2, idx);
            occs = occs->m_next;
        }
    }


    /**
       \brief v1[idx] = ~v2[idx], then v1 /= v2 is a theory axiom.
    */
    void solver::mk_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx) {
        if (!get_config().m_bv_eq_axioms)
            return;

        // TBD: disabled until new literal creation is supported
        return;
        SASSERT(m_bits[v1][idx] == ~m_bits[v2][idx]);
        TRACE("bv_solver", tout << "found new diseq axiom\n" << pp(v1) << pp(v2);); 
        m_stats.m_num_diseq_static++;
        expr_ref eq(m.mk_eq(get_expr(v1), get_expr(v2)), m);
        sat::literal not_eq = ctx.internalize(eq, true, false, m_is_redundant);
        s().add_clause(1, &not_eq, sat::status::th(m_is_redundant, get_id()));
    }

    std::ostream& solver::display(std::ostream& out, theory_var v) const {
        out << "v";
        out.width(4);
        out << std::left << v;
        out << " #";
        out.width(4);
        out << get_enode(v)->get_owner_id() << " -> #";
        out.width(4);
#if 0
        out << get_enode(find(v))->get_owner_id();
        out << std::right << ", bits:";
        literal_vector const& bits = m_bits[v];
        for (literal lit : bits) {
            out << " " << lit << ":";
            ctx.display_literal(out, lit);
        }
        numeral val;
        if (get_fixed_value(v, val))
            out << ", value: " << val;
        out << "\n";
#endif
        return out;
    }
}
