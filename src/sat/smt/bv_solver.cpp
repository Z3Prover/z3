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
        numeral val;
        VERIFY(get_fixed_value(v, val));
        euf::enode* n = get_enode(v);
        unsigned sz = m_bits[v].size();
        value_sort_pair key(val, sz);
        theory_var v2;
        if (m_fixed_var_table.find(key, v2)) {
            numeral val2;
            if (v2 < static_cast<int>(get_num_vars()) && is_bv(v2) &&
                get_bv_size(v2) == sz && get_fixed_value(v2, val2) && val == val2) {
                if (n->get_root() != get_enode(v2)->get_root()) {
                    SASSERT(get_bv_size(v) == get_bv_size(v2));
                    TRACE("fixed_var_eh", tout << "detected equality: v" << v << " = v" << v2 << "\n" << pp(v) << pp(v2););
                    m_stats.m_num_th2core_eq++;
                    add_fixed_eq(v, v2);
#if 0
                    // TODO
                    justification* js = ctx.mk_justification(fixed_eq_justification(*this, v, v2));
                    ctx.assign_eq(get_enode(v), get_enode(v2), eq_justification(js));
#endif
                    m_fixed_var_table.insert(key, v2);
                }
                else {
                    // the original fixed variable v2 was deleted or it is not fixed anymore.
                    m_fixed_var_table.erase(key);
                    m_fixed_var_table.insert(key, v);
                }
            }
            else {
                m_fixed_var_table.insert(key, v);
            }
        }
    }

    void solver::add_fixed_eq(theory_var v1, theory_var v2) {
        if (!get_config().m_bv_eq_axioms)
            return;

        if (v1 > v2) {
            std::swap(v1, v2);
        }

        unsigned act = m_eq_activity[hash_u_u(v1, v2) & 0xFF]++;
        if ((act & 0xFF) != 0xFF) {
            return;
        }
        ++m_stats.m_num_eq_dynamic;
        expr* o1 = get_expr(v1);
        expr* o2 = get_expr(v2);
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
            add_binary(eq, ~oeq);
            eqs.push_back(~eq);
        }
        eqs.push_back(oeq);
        s().add_clause(eqs.size(), eqs.c_ptr(), sat::status::th(m_is_redundant, get_id()));
    }

    bool solver::get_fixed_value(theory_var v, numeral& result) const {
        result.reset();
        unsigned i = 0;
        for (literal b : m_bits[v]) {
            switch (ctx.s().value(b)) {
            case l_false:
                break;
            case l_undef:
                return false;
            case l_true: {
                for (unsigned j = m_power2.size(); j <= i; ++j)
                    m_power2.push_back(m_bb.power(j));
                result += m_power2[i];
                break;
            }
            }
            ++i;
        }
        return true;
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
        sat::literal neq = ctx.internalize(eq, true, false, m_is_redundant);
        s().add_clause(1, &neq, sat::status::th(m_is_redundant, get_id()));
    }

    std::ostream& solver::display(std::ostream& out, theory_var v) const {
        out << "v";
        out.width(4);
        out << std::left << v;
        out << " #";
        out.width(4);
        out << get_enode(v)->get_owner_id() << " -> #";
        out.width(4);
        out << get_enode(find(v))->get_owner_id();
        out << std::right << ", bits:";
        literal_vector const& bits = m_bits[v];
        for (literal lit : bits) {
            out << " " << lit << ":" << get_expr(lit) << "\n";
        }
        numeral val;
        if (get_fixed_value(v, val))
            out << ", value: " << val;
        out << "\n";
        return out;
    }

    double solver::get_reward(literal l, sat::ext_constraint_idx idx, sat::literal_occs_fun& occs) const { return 0; }
    bool solver::is_extended_binary(sat::ext_justification_idx idx, literal_vector& r) { return false; }
    bool solver::is_external(bool_var v) { return true; }
    bool solver::propagate(literal l, sat::ext_constraint_idx idx) { return false; }
    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r) {}
    void solver::asserted(literal l) {}
    sat::check_result solver::check() { return sat::check_result::CR_DONE; }
    void solver::push() {}
    void solver::pop(unsigned n) {}
    void solver::pre_simplify() {}
    void solver::simplify() {}
    void solver::clauses_modifed() {}
    lbool solver::get_phase(bool_var v) { return l_undef; }
    std::ostream& solver::display(std::ostream& out) const { return out; }
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { return out; }
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { return out; }
    void solver::collect_statistics(statistics& st) const {}
    sat::extension* solver::copy(sat::solver* s) { return nullptr; }
    void solver::pop_reinit() {}
    bool solver::validate() { return true; }
    void solver::init_use_list(sat::ext_use_list& ul) {}
    bool solver::is_blocked(literal l, sat::ext_constraint_idx) { return false; }
    bool solver::check_model(sat::model const& m) const { return true; }
    unsigned solver::max_var(unsigned w) const { return 0;}
 
}
