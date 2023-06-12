/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polysat slicing

Author:

    Jakob Rath 2023-06-01

--*/

#include "math/polysat/slicing.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    void slicing::push_var() {
        m_stack.push_scope();           // TODO: we don't need a scope for each variable
#if 0
        m_src.push_back(null_var);
        m_hi.push_back(0);
        m_lo.push_back(0);
#endif
        pvar const v = m_var_slices.size();
        slice_idx const s = alloc_slice();
        m_var_slices.push_back(s);
    }
    
    void slicing::pop_var() {
#if 0
        if (m_src != null_var) {
            extract_key key{m_src.back(), m_hi.back(), m_lo.back()};
            m_extracted.remove(key);
        }
        m_src.pop_back();
        m_hi.pop_back();
        m_lo.pop_back();
#endif
        m_var_slices.pop_back();
        m_stack.pop_scope(1);
    }

    slicing::slice_idx slicing::alloc_slice() {
        slice_idx const s = m_slices_uf.mk_var();
        SASSERT_EQ(s, m_slices.size());
        m_slices.push_back({});
        m_stack.push_ptr(&m_alloc_slice_trail);
        return s;
    }

    void slicing::alloc_slice_trail::undo() {
        m_owner.m_slices.pop_back();
    }

    void slicing::set_extract(pvar v, pvar src, unsigned hi, unsigned lo) {
#if 0
        SASSERT(!is_extract(v));
        SASSERT(lo < hi && hi <= s.size(src));
        SASSERT_EQ(hi - lo, s.size(v));
        SASSERT(src < v);
        SASSERT(!m_extracted.contains(extract_key{src, hi, lo}));
#if 0  // try without this first
        if (is_extract(src)) {
            // y = (x[k:m])[h:l] = x[h+m:l+m]
            unsigned const offset = m_lo[src];
            set_extract(m_src[src], hi + offset, lo + offset);
            return;
        }
#endif
        m_extracted.insert({src, hi, lo}, v);
        m_src[v] = src;
        m_hi[v] = hi;
        m_lo[v] = lo;
#endif
    }

    slicing::slice_info slicing::var2slice(pvar v) const {
        slice_info si;
        si.idx = m_var_slices[v];
        si.hi = s.size(v) - 1;
        si.lo = 0;
        return si;
    }

    slicing::slice_info slicing::sub_hi(slice_info const& parent) const {
        SASSERT(has_sub(parent));
        slice const& parent_slice = m_slices[parent.idx];
        slice_info si;
        si.idx = parent_slice.sub;
        si.hi = parent.hi;
        si.lo = parent_slice.cut + 1;
        SASSERT(si.hi >= si.lo);
        return si;
    }

    slicing::slice_info slicing::sub_lo(slice_info const& parent) const {
        SASSERT(has_sub(parent));
        slice const& parent_slice = m_slices[parent.idx];
        slice_info si;
        si.idx = parent_slice.sub + 1;
        si.hi = parent_slice.cut;
        si.lo = parent.lo;
        SASSERT(si.hi >= si.lo);
        return si;
    }

    unsigned slicing::get_cut(slice_info const& si) const {
        SASSERT(has_sub(si));
        return m_slices[si.idx].cut;
    }

    void slicing::split(slice_info const& si, unsigned const cut) {
        SASSERT(!has_sub(si));
        SASSERT(si.hi > cut); SASSERT(cut >= si.lo);
        slice_idx const sub1 = alloc_slice();
        slice_idx const sub2 = alloc_slice();
        slice& s = m_slices[si.idx];
        s.cut = cut;
        s.sub = sub1;
        SASSERT_EQ(sub2, sub1 + 1);
    }

    void slicing::mk_slice(slice_info const& src, unsigned const hi, unsigned const lo, vector<slice_info>& out)
    {
        // extracted range must be fully contained inside the src slice
        SASSERT(src.hi >= hi); SASSERT(hi >= lo); SASSERT(lo >= src.lo);
        if (src.hi == hi && src.lo == lo) {
            out.push_back(src);
            return;
        }
        if (has_sub(src)) {
            // src is split into [src.hi, cut+1] and [cut, src.lo]
            unsigned const cut = get_cut(src);
            if (lo >= cut + 1)
                return mk_slice(sub_hi(src), hi, lo, out);
            else if (cut >= hi)
                return mk_slice(sub_lo(src), hi, lo, out);
            else {
                SASSERT(hi > cut && cut >= lo);
                // desired range spans over the cutpoint, so we get multiple slices in the result
                mk_slice(sub_hi(src), hi, cut + 1, out);
                mk_slice(sub_lo(src), cut, lo, out);
                return;
            }
        }
        else {
            // [src.hi, src.lo] has no subdivision yet
            if (src.hi > hi) {
                split(src, hi);
                mk_slice(sub_lo(src), hi, lo, out);
                return;
            }
            else {
                SASSERT(src.hi == hi);
                SASSERT(lo > src.lo);
                split(src, lo - 1);
                slice_info si = sub_hi(src);
                SASSERT_EQ(si.hi, hi); SASSERT_EQ(si.lo, lo);
                out.push_back(si);
                return;
            }
        }
        UNREACHABLE();
    }

    pvar slicing::mk_extract_var(pvar src, unsigned hi, unsigned lo) {
        vector<slice_info> slices;
        mk_slice(var2slice(src), hi, lo, slices);
        // src[hi:lo] is the concatenation of the returned slices
        // TODO: for each slice, set_extract

#if 0
        extract_key key{src, hi, lo};
        auto it = m_extracted.find_iterator(key);
        if (it != m_extracted.end())
            return it->m_value;
        pvar v = s.add_var(hi - lo);
        set_extract(v, src, hi, lo);
        return v;
#endif
    }

    pdd slicing::mk_extract(pvar src, unsigned hi, unsigned lo) {
        return s.var(mk_extract_var(src, hi, lo));
    }

    pdd slicing::mk_extract(pdd const& p, unsigned hi, unsigned lo) {
        if (!lo) {
            // TODO: we could push the extract down into variables of the term instead of introducing a name.
        }
        pvar const v = s.m_names.mk_name(p);
        return mk_extract(v, hi, lo);
    }

    pdd slicing::mk_concat(pdd const& p, pdd const& q) {
#if 0
        // v := p ++ q      (new variable of size |p| + |q|)
        // v[:|q|] = p
        // v[|q|:] = q
        unsigned const p_sz = p.power_of_2();
        unsigned const q_sz = q.power_of_2();
        unsigned const v_sz = p_sz + q_sz;
        // TODO: lookup to see if we can reuse a variable
        //       either:
        //          - table of concats
        //          - check for variable with v[:|q|] = p and v[|q|:] = q in extract table  (probably better)
        pvar const v = s.add_var(v_sz);

        // TODO: probably wrong to use names for p, q.
        //       we should rather check if there's already an extraction for v[...] and reuse that variable.
        pvar const p_name = s.m_names.mk_name(p);
        pvar const q_name = s.m_names.mk_name(q);
        set_extract(p_name, v, v_sz, q_sz);
        set_extract(q_name, v, q_sz, 0);
#endif
        NOT_IMPLEMENTED_YET();
    }

    void slicing::propagate(pvar v) {
    }

}
