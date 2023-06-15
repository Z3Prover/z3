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

    void slicing::push_scope() {
        m_scopes.push_back(m_trail.size());
    }

    void slicing::pop_scope(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        unsigned const lvl = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned const target_lvl = lvl - num_scopes;
        unsigned const target_size = m_scopes[target_lvl];
        while (m_trail.size() > target_size) {
            switch (m_trail.back()) {
            case trail_item::add_var:       undo_add_var();     break;
            case trail_item::alloc_slice:   undo_alloc_slice(); break;
            case trail_item::split_slice:   undo_split_slice(); break;
            case trail_item::merge_class:   undo_merge_class(); break;
            default: UNREACHABLE();
            }
            m_trail.pop_back();
        }
        m_scopes.shrink(target_lvl);
    }

    void slicing::add_var(unsigned bit_width) {
        // pvar const v = m_var2slice.size();
        slice const s = alloc_slice();
        m_slice_width[s] = bit_width;
        m_var2slice.push_back(s);
    }

    void slicing::undo_add_var() {
        m_var2slice.pop_back();
    }

    slicing::slice slicing::alloc_slice() {
        slice const s = m_slice_cut.size();
        m_slice_width.push_back(0);
        m_slice_cut.push_back(null_cut);
        m_slice_sub.push_back(null_slice);
        m_find.push_back(s);
        m_size.push_back(1);
        m_next.push_back(s);
        m_trail.push_back(trail_item::alloc_slice);
        return s;
    }

    void slicing::undo_alloc_slice() {
        m_slice_width.pop_back();
        m_slice_cut.pop_back();
        m_slice_sub.pop_back();
        m_find.pop_back();
        m_size.pop_back();
        m_next.pop_back();
    }

    slicing::slice slicing::find_sub_hi(slice parent) const {
        SASSERT(has_sub(parent));
        return find(m_slice_sub[parent]);
    }

    slicing::slice slicing::find_sub_lo(slice parent) const {
        SASSERT(has_sub(parent));
        return find(m_slice_sub[parent] + 1);
    }

    void slicing::split(slice s, unsigned cut) {
        SASSERT(!has_sub(s));
        SASSERT(width(s) - 1 >= cut + 1);
        slice const sub1 = alloc_slice();
        slice const sub2 = alloc_slice();
        m_slice_cut[s] = cut;
        m_slice_sub[s] = sub1;
        SASSERT_EQ(sub2, sub1 + 1);
        m_slice_width[sub1] = width(s) - cut - 1;
        m_slice_width[sub2] = cut + 1;
        m_trail.push_back(trail_item::split_slice);
        m_split_trail.push_back(s);
    }

    void slicing::undo_split_slice() {
        slice s = m_split_trail.back();
        m_split_trail.pop_back();
        m_slice_cut[s] = null_cut;
        m_slice_sub[s] = null_slice;
    }

    slicing::slice slicing::find(slice s) const {
        while (true) {
            SASSERT(s < m_find.size());
            slice const new_s = m_find[s];
            if (new_s == s)
                return s;
            s = new_s;
        }
    }

    void slicing::merge(slice s1, slice s2) {
        SASSERT_EQ(width(s1), width(s2));
        SASSERT(!has_sub(s1));
        SASSERT(!has_sub(s2));
        slice r1 = find(s1);
        slice r2 = find(s2);
        if (r1 == r2)
            return;
        if (m_size[r1] > m_size[r2])
            std::swap(r1, r2);
        // r2 becomes the representative of the merged class
        m_find[r1] = r2;
        m_size[r2] += m_size[r1];
        std::swap(m_next[r1], m_next[r2]);
        m_trail.push_back(trail_item::merge_class);
        m_merge_trail.push_back(r1);
    }

    void slicing::undo_merge_class() {
        slice r1 = m_merge_trail.back();
        m_merge_trail.pop_back();
        slice r2 = m_find[r1];
        SASSERT(find(r2) == r2);
        m_find[r1] = r1;
        m_size[r2] -= m_size[r1];
        std::swap(m_next[r1], m_next[r2]);
    }

    void slicing::merge(slice_vector& xs, slice_vector& ys) {
        // LOG_H2("Merging " << xs << " with " << ys);
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            slice x = xs.back();
            slice y = ys.back();
            xs.pop_back();
            ys.pop_back();
            SASSERT(!has_sub(x));
            SASSERT(!has_sub(y));
            if (width(x) == width(y)) {
                // LOG("Match " << x << " and " << y);
                merge(x, y);
            }
            else if (width(x) > width(y)) {
                // need to split x according to y
                // LOG("Splitting " << x << " to fit " << y);
                mk_slice(x, width(y) - 1, 0, xs, true);
                ys.push_back(y);
            }
            else {
                SASSERT(width(y) > width(x));
                // need to split y according to x
                // LOG("Splitting " << y << " to fit " << x);
                mk_slice(y, width(x) - 1, 0, ys, true);
                xs.push_back(x);
            }
        }
        SASSERT(ys.empty());
    }

    void slicing::merge(slice_vector& xs, slice y) {
        slice_vector tmp;
        tmp.push_back(y);
        merge(xs, tmp);
    }

    void slicing::find_base(slice src, slice_vector& out_base) const {
        // splits are only stored for the representative
        SASSERT_EQ(src, find(src));
        if (!has_sub(src)) {
            out_base.push_back(src);
            return;
        }
        slice_vector& todo = m_tmp1;
        SASSERT(todo.empty());
        todo.push_back(src);
        while (!todo.empty()) {
            slice s = todo.back();
            todo.pop_back();
            if (!has_sub(s))
                out_base.push_back(s);
            else {
                todo.push_back(find_sub_lo(s));
                todo.push_back(find_sub_hi(s));
            }
        }
        SASSERT(todo.empty());
    }

    void slicing::mk_slice(slice src, unsigned const hi, unsigned const lo, slice_vector& out_base, bool output_full_src) {
        SASSERT(hi >= lo);
        SASSERT_EQ(src, find(src));  // splits are only stored for the representative
        SASSERT(width(src) > hi);  // extracted range must be fully contained inside the src slice
        if (lo == 0 && width(src) - 1 == hi) {
            find_base(src, out_base);
            return;
        }
        if (has_sub(src)) {
            // src is split into [src.width-1, cut+1] and [cut, 0]
            unsigned const cut = m_slice_cut[src];
            if (lo >= cut + 1) {
                // target slice falls into upper subslice
                mk_slice(find_sub_hi(src), hi - cut - 1, lo - cut - 1, out_base);
                if (output_full_src)
                    out_base.push_back(find_sub_lo(src));
                return;
            }
            else if (cut >= hi) {
                // target slice falls into lower subslice
                if (output_full_src)
                    out_base.push_back(find_sub_hi(src));
                mk_slice(find_sub_lo(src), hi, lo, out_base);
                return;
            }
            else {
                SASSERT(hi > cut && cut >= lo);
                // desired range spans over the cutpoint, so we get multiple slices in the result
                mk_slice(find_sub_hi(src), hi - cut - 1, 0, out_base);
                mk_slice(find_sub_lo(src), cut, lo, out_base);
                return;
            }
        }
        else {
            // [src.width-1, 0] has no subdivision yet
            if (width(src) - 1 > hi) {
                split(src, hi);
                if (output_full_src)
                    out_base.push_back(find_sub_hi(src));
                mk_slice(find_sub_lo(src), hi, lo, out_base);  // recursive call to take care of case lo > 0
                return;
            }
            else {
                SASSERT(lo > 0);
                split(src, lo - 1);
                out_base.push_back(find_sub_hi(src));
                if (output_full_src)
                    out_base.push_back(find_sub_lo(src));
                return;
            }
        }
        UNREACHABLE();
    }

    pvar slicing::mk_extract_var(pvar src, unsigned hi, unsigned lo) {
        slice_vector slices;
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

#if 0
    pdd slicing::mk_extract(pvar src, unsigned hi, unsigned lo) {
        return m_solver.var(mk_extract_var(src, hi, lo));
    }

    pdd slicing::mk_extract(pdd const& p, unsigned hi, unsigned lo) {
        if (!lo) {
            // TODO: we could push the extract down into variables of the term instead of introducing a name.
        }
        pvar const v = m_solver.m_names.mk_name(p);
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
#endif

    void slicing::set_extract(pvar v, pvar src, unsigned hi, unsigned lo) {
#if 0
        SASSERT(!is_extract(v));
        SASSERT(lo < hi && hi <= s.size(src));
        SASSERT_EQ(hi - lo + 1, s.size(v));
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

    void slicing::propagate(pvar v) {
    }

    std::ostream& slicing::display(std::ostream& out) const {
        slice_vector base;
        for (pvar v = 0; v < m_var2slice.size(); ++v) {
            out << "v" << v << ":";
            base.reset();
            find_base(var2slice(v), base);
            for (slice s : base)
                display(out << " ", s);
            out << "\n";
        }
        return out;
    }

    std::ostream& slicing::display(std::ostream& out, slice s) const {
        return out << "{id:" << s << ",w:" << width(s) << "}";
    }

}
