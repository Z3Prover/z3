/*---
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat_egraph.cpp

Abstract:

    PolySAT interface to bit-vector

Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26


--*/

#include "ast/euf/euf_bv_plugin.h"
#include "sat/smt/polysat_solver.h"
#include "sat/smt/euf_solver.h"

namespace polysat {

    struct solver::scoped_eq_justification {
        eq_justification& j;
        euf::enode* a, * b;
        scoped_eq_justification(solver& s, eq_justification& j, euf::enode* a, euf::enode* b) :
            j(j), a(a), b(b) {
            if (a != b)
                j.push_back({ s.get_th_var(a), s.get_th_var(b) });
        }
        ~scoped_eq_justification() {
            if (a != b)
                j.pop_back();
        }
    };
    
    void solver::get_subslices(pvar pv, subslice_infos& slices) {
        theory_var v = m_pddvar2var[pv];
        unsigned lo, hi;
        expr* e = nullptr;
        euf::enode* n = var2enode(v);
        slices.push_back({ n, 0, {} });

        for (unsigned i = 0; i < slices.size(); ++i) {
            auto [n, offset, just] = slices[i];
            if (n->get_root()->is_marked1())
                continue;
            n->get_root()->mark1();
            for (auto sib : euf::enode_class(n)) {
                if (bv.is_concat(sib->get_expr())) {
                    unsigned delta = 0;
                    scoped_eq_justification sp(*this, just, n, sib);
                    for (unsigned j = sib->num_args(); j-- > 0; ) {
                        auto arg = sib->get_arg(j);
                        slices.push_back({ arg, offset + delta, just });
                        delta += bv.get_bv_size(arg->get_expr());
                    }
                }
            }
            for (auto p : euf::enode_parents(n->get_root())) {
                if (p->is_marked1())
                    continue;
                if (bv.is_extract(p->get_expr(), lo, hi, e)) {
                    auto child = expr2enode(e);
                    SASSERT(n == child->get_root());
                    scoped_eq_justification sp(*this, just, child, n);
                    slices.push_back({ p, offset + lo, just });
                }
            }
        }
        for (auto const& [n,offset,d] : slices)
            n->get_root()->unmark1();
    }


    // walk the egraph starting with pvar for overlaps.
    void solver::get_bitvector_suffixes(pvar pv, justified_slices& out) {
        subslice_infos slices;
        get_subslices(pv, slices);

        for (auto& [n, offset, just] : slices) {
            if (offset != 0)
                continue;
            auto w = n->get_th_var(get_id());
            if (w == euf::null_theory_var)
                continue;
            auto const& p = m_var2pdd[w];
            if (p.is_var())
                out.push_back({ p.var(), dependency(just, s().scope_lvl())}); // approximate to current scope
        }
    }

    // walk the e-graph to retrieve fixed overlaps
    void solver::get_fixed_bits(pvar pv, justified_fixed_bits& out) {
        subslice_infos slices;
        get_subslices(pv, slices);

        for (auto& [n, offset, just] : slices) {
            if (offset != 0)
                continue;
            n = n->get_root();
            if (!n->interpreted())
                continue;
            auto w = n->get_th_var(get_id());
            if (w == euf::null_theory_var)
                continue;
            auto const& p = m_var2pdd[w];
            if (!p.is_var())
                continue;
            unsigned lo = offset, hi = bv.get_bv_size(n->get_expr());
            rational value;
            VERIFY(bv.is_numeral(n->get_expr(), value));
            out.push_back({ fixed_bits(lo, hi, value), dependency(just, s().scope_lvl()) }); // approximate level
        }
    }

}
