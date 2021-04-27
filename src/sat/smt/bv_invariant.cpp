/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_invariant.cpp

Abstract:

    Invariants for bv_solver

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-28

--*/

#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"

namespace bv {

    void solver::validate_atoms() const {
        sat::bool_var v = 0;
        for (auto* a : m_bool_var2atom) {
            if (a) {
                for (auto vp : *a) {
                    SASSERT(m_bits[vp.first][vp.second].var() == v);
                    VERIFY(m_bits[vp.first][vp.second].var() == v);
                }
            }
            ++v;
        }
    }

    void solver::check_missing_propagation() const {
        for (euf::enode* n : ctx.get_egraph().nodes()) {
            expr* e = n->get_expr(), *a = nullptr, *b = nullptr;
            if (m.is_eq(e, a, b) && bv.is_bv(a) && s().value(expr2literal(e)) == l_undef) {
                theory_var v1 = n->get_arg(0)->get_th_var(get_id());
                theory_var v2 = n->get_arg(1)->get_th_var(get_id());
                SASSERT(v1 != euf::null_theory_var);
                SASSERT(v2 != euf::null_theory_var);
                unsigned sz = m_bits[v1].size();
                for (unsigned i = 0; i < sz; ++i) {
                    lbool val1 = s().value(m_bits[v1][i]);
                    lbool val2 = s().value(m_bits[v2][i]);
                    if (val1 != l_undef && val2 != l_undef && val1 != val2) {
                        IF_VERBOSE(0, verbose_stream() << "missing " << mk_bounded_pp(e, m) << "\n");
                        break;
                    }
                }
            }
        }
    }

    /**
        \brief Check whether m_zero_one_bits is an accurate summary of the bits in the
        equivalence class rooted by v.
        \remark The method does nothing if v is not the root of the equivalence class.
    */
    bool solver::check_zero_one_bits(theory_var v) {
        if (s().inconsistent())
            return true; // property is only valid if the context is not in a conflict.
        if (!is_root(v) || !is_bv(v))
            return true;
        bool_vector bits[2];
        unsigned      num_bits = 0;
        unsigned      bv_sz = get_bv_size(v);
        bits[0].resize(bv_sz, false);
        bits[1].resize(bv_sz, false);

        sat::literal_vector assigned;
        theory_var curr = v;
        do {
            literal_vector const& lits = m_bits[curr];
            for (unsigned i = 0; i < lits.size(); i++) {
                literal l = lits[i];
                if (l.var() == mk_true().var()) {
                    assigned.push_back(l);
                    unsigned is_true = s().value(l) == l_true;
                    if (bits[!is_true][i]) {
                        // expect a conflict later on.
                        return true;
                    }
                    if (!bits[is_true][i]) {
                        bits[is_true][i] = true;
                        num_bits++;
                    }
                }
            }
            curr = m_find.next(curr);
        } while (curr != v);

        zero_one_bits const& _bits = m_zero_one_bits[v];
        if (_bits.size() != num_bits) {
            std::cout << "v" << v << " " << _bits.size() << " " << num_bits << "\n";
            std::cout << "true: " << mk_true() << "\n";
            do {
                std::cout << "v" << curr << ": " << m_bits[curr] << "\n";
                curr = m_find.next(curr);
            }
            while (curr != v);
        }
        SASSERT(_bits.size() == num_bits);
        VERIFY(_bits.size() == num_bits);
        bool_vector already_found;
        already_found.resize(bv_sz, false);
        for (auto& zo : _bits) {
            SASSERT(find(zo.m_owner) == v);
            SASSERT(bits[zo.m_is_true][zo.m_idx]);
            SASSERT(!already_found[zo.m_idx]);
            already_found[zo.m_idx] = true;
        }
        return true;
    }

}
