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

    unsigned solver::merge_level(euf::enode* a, euf::enode* b) {
        sat::literal_vector r;
        ctx.get_eq_antecedents(a, b, r);
        unsigned level = 0;
        for (sat::literal lit : r)
            level = std::max(level, s().lvl(lit));
        return level;
    }

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

    // walk the e-graph to retrieve fixed sub-slices along with justifications,
    // as well as pvars that correspond to these sub-slices.
    void solver::get_fixed_sub_slices(pvar pv, fixed_slice_extra_vector& fixed, offset_slice_extra_vector& subslices) {
        #define GET_FIXED_SUB_SLICES_DISPLAY 1
        auto consume_slice = [&](euf::enode* n, unsigned offset) -> bool {
            euf::enode* r = n->get_root();
            if (!r->interpreted())
                return true;
            euf::theory_var w = r->get_th_var(get_id());
            if (w == euf::null_theory_var)
                return true;
            unsigned length = bv.get_bv_size(r->get_expr());
            rational value;
            VERIFY(bv.is_numeral(r->get_expr(), value));

            unsigned level = merge_level(n, r);

            euf::theory_var u = n->get_th_var(get_id());
            dependency dep = (u == euf::null_theory_var) ? dependency::axiom() : dependency(u, w);   // TODO: probably need an enode_pair instead?

#if GET_FIXED_SUB_SLICES_DISPLAY
            verbose_stream() << "    " << value << "[" << length << "]@" << offset;
            verbose_stream() << "  node " << ctx.bpp(n);
            verbose_stream() << "  tv " << u;
            if (u != euf::null_theory_var)
                verbose_stream() << " := " << m_var2pdd[u];
            verbose_stream() << "  merge-level " << level;
            verbose_stream() << "\n";
            fixed.push_back(fixed_slice_extra(value, offset, length, level, dep));
#endif

            for (euf::enode* sib : euf::enode_class(n)) {
                euf::theory_var s = sib->get_th_var(get_id());
                if (s == euf::null_theory_var)
                    continue;
                auto const& p = m_var2pdd[s];
                if (!p.is_var())
                    continue;
                unsigned p_level = merge_level(sib, r);
#if GET_FIXED_SUB_SLICES_DISPLAY
                verbose_stream() << "        pvar " << p;
                verbose_stream() << "  node " << ctx.bpp(sib);
                verbose_stream() << "  tv " << s;
                verbose_stream() << "  merge-level " << p_level;
                verbose_stream() << "\n";
#endif
                subslices.push_back(offset_slice_extra(p.var(), offset, p_level));
            }

            return true;
        };
#if GET_FIXED_SUB_SLICES_DISPLAY
        verbose_stream() << "fixed subslices of v" << pv << ":\n";
#endif
        theory_var v = m_pddvar2var[pv];
        m_bv_plugin->sub_slices(var2enode(v), consume_slice);
    }
    
    void solver::explain_slice(pvar pv, pvar pw, unsigned offset, std::function<void(euf::enode*, euf::enode*)> const& consume_eq) {
        euf::theory_var v = m_pddvar2var[pv];
        euf::theory_var w = m_pddvar2var[pw];
        m_bv_plugin->explain_slice(var2enode(v), offset, var2enode(w), consume_eq);
    }

    void solver::explain_fixed(pvar pv, fixed_slice const& slice, std::function<void(euf::enode*, euf::enode*)> const& consume_eq) {
        euf::theory_var v = m_pddvar2var[pv];
        expr_ref val(bv.mk_numeral(slice.value, slice.length), m);
        euf::enode* b = ctx.get_egraph().find(val);
        if (!b) {
            verbose_stream() << v << " " << val << "\n";
            ctx.get_egraph().display(verbose_stream());
        }

        SASSERT(b);
        m_bv_plugin->explain_slice(var2enode(v), slice.offset, b, consume_eq);
    }

}
