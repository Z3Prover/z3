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

    // walk the egraph starting with pvar for overlaps.
    void solver::get_bitvector_suffixes(pvar pv, justified_slices& out) {
        theory_var v = m_pddvar2var[pv];
        svector<std::pair<euf::enode*, eq_justification>> todo;       
        uint_set seen;
        unsigned lo, hi;
        expr* e = nullptr;
        euf::enode* n = var2enode(v);
        todo.push_back({ n, {}});

        for (unsigned i = 0; i < todo.size(); ++i) {
            auto [n, just] = todo[i];
            scoped_eq_justification sp(*this, just, n, n->get_root());
            n = n->get_root();
            if (n->is_marked1())
                continue;
            n->mark1();
            for (auto sib : euf::enode_class(n)) {
                theory_var w = sib->get_th_var(get_id());

                // identify prefixes
                if (bv.is_concat(sib->get_expr())) {
                    scoped_eq_justification sp(*this, just, n, sib);
                    todo.push_back({ sib->get_arg(sib->num_args() - 1), just });
                }
                if (w == euf::null_theory_var)
                    continue;
                if (seen.contains(w))
                    continue;
                seen.insert(w);
                auto const& p = m_var2pdd[w];
                if (p.is_var())
                    out.push_back({ p.var(), dependency(just, s().scope_lvl())}); // approximate to current scope
            }
            for (auto p : euf::enode_parents(n)) {
                if (p->is_marked1())
                    continue;
                // find prefixes: e[hi:0] a parent of n
                if (bv.is_extract(p->get_expr(), lo, hi, e) && lo == 0) {
                    auto child = expr2enode(e);
                    SASSERT(n == child->get_root());
                    scoped_eq_justification sp(*this, just, child, n);
                    todo.push_back({ p, just });
                }
            }  
        }
        for (auto n : todo)
            n.first->get_root()->unmark1();
    }

    // walk the e-graph to retrieve fixed overlaps
    void solver::get_fixed_bits(pvar pv, justified_fixed_bits& out) {
        theory_var v = m_pddvar2var[pv];
        svector<std::tuple<euf::enode*, unsigned, eq_justification>> todo;
        uint_set seen;
        unsigned lo, hi;
        expr* e = nullptr;
        euf::enode* n = var2enode(v);
        todo.push_back({ n, 0, {} });

        for (unsigned i = 0; i < todo.size(); ++i) {
            auto [n, offset, just] = todo[i];
            scoped_eq_justification sp(*this, just, n, n->get_root());
            n = n->get_root();
            if (n->is_marked1())
                continue;
            n->mark1();
            for (auto sib : euf::enode_class(n)) {
                if (bv.is_concat(sib->get_expr())) {
                    unsigned delta = 0;
                    scoped_eq_justification sp(*this, just, n, sib);
                    for (unsigned j = sib->num_args(); j-- > 0; ) {
                        auto arg = sib->get_arg(j);
                        todo.push_back({ arg, offset + delta, just });
                        delta += bv.get_bv_size(arg->get_expr());
                    }
                }if (!sib->interpreted())
                    continue;
                theory_var w = sib->get_th_var(get_id());
                if (w == euf::null_theory_var)
                    continue;
                if (seen.contains(w))
                    continue;
                seen.insert(w);
                
                auto const& p = m_var2pdd[w];
                if (p.is_var()) {
                    unsigned lo = offset, hi = bv.get_bv_size(sib->get_expr());
                    rational value;
                    VERIFY(bv.is_numeral(sib->get_expr(), value));
                    out.push_back({ fixed_bits(lo, hi, value), dependency(just, s().scope_lvl()) }); // approximate level
                }
                
            }
            for (auto p : euf::enode_parents(n)) {
                if (p->is_marked1())
                    continue;
                if (bv.is_extract(p->get_expr(), lo, hi, e)) {
                    auto child = expr2enode(e);
                    SASSERT(n == child->get_root());
                    scoped_eq_justification sp(*this, just, child, n);
                    todo.push_back({ p, offset + lo, just });
                }
            }
        }
        for (auto const& [n,offset,d] : todo)
            n->get_root()->unmark1();
    }

}
