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

    // walk the egraph starting with pvar for suffix overlaps.
    void solver::get_bitvector_suffixes(pvar pv, offset_slices& out) {       
        uint_set seen;
        std::function<bool(euf::enode*, unsigned)> consume_slice = [&](euf::enode* n, unsigned offset) {
            if (offset != 0)
                return false;
            for (auto sib : euf::enode_class(n)) {
                auto w = sib->get_th_var(get_id());
                if (w == euf::null_theory_var)
                    continue;
                if (seen.contains(w))
                    continue;
                seen.insert(w);
                auto const& p = m_var2pdd[w];
                if (!p.is_var())
                    continue;
                out.push_back({ p.var(), offset });
            }
            return true;
        };
        theory_var v = m_pddvar2var[pv];
        m_bv_plugin->sub_slices(var2enode(v), consume_slice);
    }

    // walk the egraph starting with pvar for any overlaps.
    void solver::get_bitvector_sub_slices(pvar pv, offset_slices& out) {
        uint_set seen;
        std::function<bool(euf::enode*, unsigned)> consume_slice = [&](euf::enode* n, unsigned offset) {
            for (auto sib : euf::enode_class(n)) {
                auto w = sib->get_th_var(get_id());
                if (w == euf::null_theory_var)
                    continue;
                if (seen.contains(w))
                    continue;
                seen.insert(w);
                auto const& p = m_var2pdd[w];
                if (!p.is_var())
                    continue;
                out.push_back({ p.var(), offset });
            }
            return true;
        };
        theory_var v = m_pddvar2var[pv];
        m_bv_plugin->sub_slices(var2enode(v), consume_slice);
    }

    // walk the egraph for bit-vectors that contain pv.
    void solver::get_bitvector_super_slices(pvar pv, offset_slices& out) {
        uint_set seen;
        std::function<bool(euf::enode*, unsigned)> consume_slice = [&](euf::enode* n, unsigned offset) {
            for (auto sib : euf::enode_class(n)) {
                auto w = sib->get_th_var(get_id());
                if (w == euf::null_theory_var)
                    continue;
                if (seen.contains(w))
                    continue;
                seen.insert(w);
                auto const& p = m_var2pdd[w];
                if (!p.is_var())
                    continue;
                out.push_back({ p.var(), offset });
            }
            return true;
            };
        theory_var v = m_pddvar2var[pv];
        m_bv_plugin->super_slices(var2enode(v), consume_slice);

    }

    // walk the e-graph to retrieve fixed overlaps
    void solver::get_fixed_bits(pvar pv, fixed_bits_vector& out) {
        theory_var v = m_pddvar2var[pv];
        euf::enode* b = var2enode(v);
        std::function<bool(euf::enode*, unsigned)> consume_slice = [&](euf::enode* n, unsigned offset) {
            auto r = n->get_root();
            if (!r->interpreted())
                return true;
            auto w = r->get_th_var(get_id());
            if (w == euf::null_theory_var)
                return true;
            unsigned length = bv.get_bv_size(r->get_expr());
            rational value;
            VERIFY(bv.is_numeral(r->get_expr(), value));
            out.push_back({ fixed_slice(value, offset, length) });
            return false;
        };
   
        m_bv_plugin->sub_slices(b, consume_slice);
        m_bv_plugin->super_slices(b, consume_slice);
    }
    
    void solver::explain_slice(pvar pv, pvar pw, unsigned offset, std::function<void(euf::enode*, euf::enode*)>& consume_eq) {
        euf::theory_var v = m_pddvar2var[pv];
        euf::theory_var w = m_pddvar2var[pw];
        m_bv_plugin->explain_slice(var2enode(v), offset, var2enode(w), consume_eq);
    }

    void solver::explain_fixed(pvar pv, fixed_slice const& slice, std::function<void(euf::enode*, euf::enode*)>& consume_eq) {
        euf::theory_var v = m_pddvar2var[pv];
        expr_ref val(bv.mk_numeral(slice.value, slice.length), m);
        euf::enode* b = ctx.get_egraph().find(val);
        SASSERT(b);
        m_bv_plugin->explain_slice(var2enode(v), slice.offset, b, consume_eq);
    }

}
