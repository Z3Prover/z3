/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polysat slicing

Author:

    Jakob Rath 2023-06-01

--*/




/*

                (x=y)
        x  <===========  y
       /    \           / \
      x[7:4] x[3:0]       y[3:0]
                <==========
                   (by x=y)

Try later:
  Congruence closure with "virtual concat" terms
    x = x[7:4] ++ x[3:0]
    y = y[7:4] ++ y[3:0]
    x[7:4] = y[7:4]
    x[3:0] = y[3:0]
    => x = y

Recycle the z3 egraph?
    - x = x[7:4] ++ x[3:0]
    - Add instance euf_egraph.h
    - What do we need from the egraph?
        - backtracking trail to check for new equalities

*/


#include "math/polysat/slicing.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    void* slicing::encode_dep(dep_t d) {
        if (d == null_dep)
            return nullptr;
        else
            return reinterpret_cast<void*>(static_cast<std::uintptr_t>(d.to_uint()) + 1);
        static_assert( sizeof(void*) >= sizeof(std::uintptr_t) );
        static_assert( sizeof(std::uintptr_t) > sizeof(decltype(d.to_uint())) );
    }

    slicing::dep_t slicing::decode_dep(void* d) {
        if (!d)
            return null_dep;
        else
            return sat::to_literal(reinterpret_cast<std::uintptr_t>(d) - 1);
    }

    slicing::slicing(solver& s):
        m_solver(s),
        m_egraph(m_ast),
        // m_slice2app(m_ast),
        m_expr_storage(m_ast)
    {
        m_slice_sort = m_ast.mk_uninterpreted_sort(symbol("slice"));
    }

    func_decl* slicing::get_concat_decl(unsigned arity) {
        SASSERT(arity >= 2);
        func_decl* decl = m_concat_decls.get(arity, nullptr);
        if (!decl) {
            ptr_vector<sort> domain;
            for (unsigned i = arity; i-- > 0; )
                domain.push_back(m_slice_sort);
            SASSERT_EQ(arity, domain.size());
            // TODO: mk_fresh_func_decl("concat", ...) if overload doesn't work
            func_decl* decl = m_ast.mk_func_decl(symbol("slice-concat"), arity, domain.data(), m_slice_sort);
            m_concat_decls.setx(arity, decl, nullptr);
        }
        return decl;
    }

    void slicing::push_scope() {
        m_scopes.push_back(m_trail.size());
        m_expr_scopes.push_back(m_expr_storage.size());
        m_egraph.push();
    }

    void slicing::pop_scope(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        unsigned const lvl = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned const target_lvl = lvl - num_scopes;
        unsigned const target_size = m_scopes[target_lvl];
        unsigned const target_expr_size = m_expr_scopes[target_lvl];
        m_scopes.shrink(target_lvl);
        m_expr_scopes.shrink(target_lvl);
        while (m_trail.size() > target_size) {
            switch (m_trail.back()) {
            case trail_item::add_var:           undo_add_var();         break;
            case trail_item::alloc_slice:       undo_alloc_slice();     break;
            case trail_item::split_core:        undo_split_core();      break;
            // case trail_item::merge_base:        undo_merge_base();      break;
            // case trail_item::mk_value_slice:    undo_mk_value_slice();  break;
            default: UNREACHABLE();
            }
            m_trail.pop_back();
        }
        m_egraph.pop(num_scopes);
        m_expr_storage.shrink(target_expr_size);
    }

    void slicing::add_var(unsigned bit_width) {
        pvar const v = m_var2slice.size();
        slice const s = alloc_slice(bit_width);
        m_slice2var[s] = v;
        m_var2slice.push_back(s);
    }

    void slicing::undo_add_var() {
        m_var2slice.pop_back();
    }

    slicing::slice slicing::alloc_slice(unsigned width) {
        SASSERT(width > 0);
        slice const s = m_slice_cut.size();
        m_slice_width.push_back(width);
        m_slice_cut.push_back(null_cut);
        m_slice_sub.push_back(null_slice);
        m_slice2var.push_back(null_var);
        // m_mark.push_back(0);
        app* a = m_ast.mk_fresh_const("s", m_slice_sort, false);  // TODO: what's the effect of "skolem = true"?
        m_expr_storage.push_back(a);
        euf::enode* n = m_egraph.mk(a, 0, 0, nullptr);
        m_slice2enode.push_back(n);
        SASSERT(!m_enode2slice.contains(n));
        m_enode2slice.insert(n, s);
        m_trail.push_back(trail_item::alloc_slice);
        return s;
    }

    void slicing::undo_alloc_slice() {
        m_slice_width.pop_back();
        m_slice_cut.pop_back();
        m_slice_sub.pop_back();
        m_slice2var.pop_back();
        euf::enode* n = m_slice2enode.back();
        SASSERT_EQ(m_enode2slice[n], m_slice_cut.size());
        m_enode2slice.remove(n);
        m_slice2enode.pop_back();
        // m_mark.pop_back();
    }

    slicing::slice slicing::sub_hi(slice parent) const {
        SASSERT(has_sub(parent));
        return m_slice_sub[parent];
    }

    slicing::slice slicing::sub_lo(slice parent) const {
        SASSERT(has_sub(parent));
        return m_slice_sub[parent] + 1;
    }

    euf::enode* slicing::sub_hi(euf::enode* n) const {
        return slice2enode(sub_hi(enode2slice(n)));
    }

    euf::enode* slicing::sub_lo(euf::enode* n) const {
        return slice2enode(sub_lo(enode2slice(n)));
    }

    slicing::slice slicing::find_sub_hi(slice parent) const {
        return find(sub_hi(parent));
    }

    slicing::slice slicing::find_sub_lo(slice parent) const {
        return find(sub_lo(parent));
    }

    // split a single slice without updating any equivalences
    void slicing::split_core(slice s, unsigned cut) {
        SASSERT(!has_sub(s));
        SASSERT(width(s) - 1 >= cut + 1);
        slice const sub_hi = alloc_slice(width(s) - cut - 1);
        slice const sub_lo = alloc_slice(cut + 1);
        m_slice_cut[s] = cut;
        m_slice_sub[s] = sub_hi;
        SASSERT_EQ(sub_lo, sub_hi + 1);
        m_trail.push_back(trail_item::split_core);
        m_split_trail.push_back(s);
        // if (has_value(s)) {
        //     rational const& val = get_value(s);
        //     // set_value(sub_lo, mod2k(val, cut + 1));
        //     // set_value(sub_hi, machine_div2k(val, cut + 1));
        // }

        // // s = hi ++ lo     ... TODO: necessary??? probably not
        // euf::enode* s_n = slice2enode(s);
        // euf::enode* hi_n = slice2enode(sub_hi);
        // euf::enode* lo_n = slice2enode(sub_lo);
        // app* a = m_ast.mk_app(get_concat_decl(2), hi_n->get_expr(), lo_n->get_expr());
        // auto args = {hi_n, lo_n};
        // euf::enode* concat_n = m_egraph.mk(a, 0, args.size(), blup.begin());
        // m_egraph.merge(s_n, concat_n, nullptr);
        // SASSERT(!concat_n->is_root());  // else we have to register it in enode2slice
    }

    void slicing::undo_split_core() {
        slice s = m_split_trail.back();
        m_split_trail.pop_back();
        m_slice_cut[s] = null_cut;
        m_slice_sub[s] = null_slice;
    }

    void slicing::split(slice s, unsigned cut) {
        euf::enode* sn = slice2enode(s);
        // split all slices in the equivalence class
        for (euf::enode* n : euf::enode_class(sn)) {
            split_core(enode2slice(n), cut);
        }
        // propagate the proper equivalences
        for (euf::enode* n : euf::enode_class(sn)) {
            euf::enode* target = n->get_target();
            if (!target)
                continue;
            euf::justification j = n->get_justification();
            SASSERT(j.is_external());  // cannot be a congruence since the slice wasn't split before.
            m_egraph.merge(sub_hi(n), sub_hi(target), j.ext<void>());
            m_egraph.merge(sub_lo(n), sub_lo(target), j.ext<void>());
        }
        m_egraph.propagate();  // TODO: could do this later
    }

#if 0
    slicing::slice slicing::mk_value_slice(rational const& val, unsigned bit_width) {
        SASSERT(0 <= val && val < rational::power_of_two(bit_width));
        val2slice_key key(val, bit_width);
        auto it = m_val2slice.find_iterator(key);
        if (it != m_val2slice.end())
            return it->m_value;
        slice s = alloc_slice();
        m_slice_width[s] = bit_width;
        m_slice2val[s] = val;
        // m_value_root[s] = s;
        m_val2slice.insert(key, s);
        m_val2slice_trail.push_back(std::move(key));
        m_trail.push_back(trail_item::mk_value_slice);
        return s;
    }

    void slicing::undo_mk_value_slice() {
        m_val2slice.remove(m_val2slice_trail.back());
        m_val2slice_trail.pop_back();
    }
#endif

    slicing::slice slicing::find(slice s) const {
        return enode2slice(slice2enode(s)->get_root());
    }

#if 1
    bool slicing::merge_base(slice s1, slice s2, dep_t dep) {
        SASSERT_EQ(width(s1), width(s2));
        SASSERT(!has_sub(s1));
        SASSERT(!has_sub(s2));
        m_egraph.merge(slice2enode(s1), slice2enode(s2), encode_dep(dep));
        m_egraph.propagate();  // TODO: could do this later maybe
        return !m_egraph.inconsistent();
    }

#if 0
    bool slicing::merge_value(slice s0, rational val0, dep_t dep) {
        vector<std::pair<slice, rational>> todo;
        todo.push_back({find(s0), std::move(val0)});
        // check compatibility for sub-slices
        for (unsigned i = 0; i < todo.size(); ++i) {
            auto const& [s, val] = todo[i];
            if (has_value(s)) {
                if (get_value(s) != val) {
                    // TODO: conflict
                    NOT_IMPLEMENTED_YET();
                    return false;
                }
                SASSERT_EQ(get_value(s), val);
                continue;
            }
            if (has_sub(s)) {
                // s is split into [s.width-1, cut+1] and [cut, 0]
                unsigned const cut = m_slice_cut[s];
                todo.push_back({find_sub_lo(s), mod2k(val, cut + 1)});
                todo.push_back({find_sub_hi(s), machine_div2k(val, cut + 1)});
            }
        }
        // all succeeded, so apply the values
        for (auto const& [s, val] : todo) {
            if (has_value(s)) {
                SASSERT_EQ(get_value(s), val);
                continue;
            }
            // set_value(s, val);
        }
        return true;
    }
#endif

#if 0
    void slicing::push_reason(slice s, dep_vector& out_deps) {
        dep_t reason = m_proof_reason[s];
        if (reason == null_dep)
            return;
        out_deps.push_back(reason);
    }

    void slicing::explain_equal(slice x, slice y, dep_vector& out_deps) {
        // TODO: we currently get duplicates in out_deps (if parents are merged, the subslices are all merged due to the same reason)
        SASSERT(is_equal(x, y));
        slice_vector& xs = m_tmp2;
        slice_vector& ys = m_tmp3;
        SASSERT(xs.empty());
        SASSERT(ys.empty());
        xs.push_back(x);
        ys.push_back(y);
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            slice const x = xs.back(); xs.pop_back();
            slice const y = ys.back(); ys.pop_back();
            if (x == y)
                continue;
            if (width(x) == width(y)) {
                slice const rx = find(x);
                slice const ry = find(y);
                if (rx == ry)
                    explain_class(x, y, out_deps);
                else {
                    xs.push_back(sub_hi(rx));
                    xs.push_back(sub_lo(rx));
                    ys.push_back(sub_hi(ry));
                    ys.push_back(sub_lo(ry));
                }
            }
            else if (width(x) > width(y)) {
                slice const rx = find(x);
                xs.push_back(sub_hi(rx));
                xs.push_back(sub_lo(rx));
                ys.push_back(y);
            }
            else {
                SASSERT(width(x) < width(y));
                xs.push_back(x);
                slice const ry = find(y);
                ys.push_back(sub_hi(ry));
                ys.push_back(sub_lo(ry));
            }
        }
        SASSERT(ys.empty());
    }
#endif

    bool slicing::merge(slice_vector& xs, slice_vector& ys, dep_t dep) {
        // LOG_H2("Merging " << xs << " with " << ys);
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            slice x = xs.back();
            slice y = ys.back();
            xs.pop_back();
            ys.pop_back();
            if (x == y) {
                // merge upper level?
                // but continue loop
            }
            if (has_sub(x)) {
                find_base(x, xs);
                x = xs.back();
                xs.pop_back();
            }
            if (has_sub(y)) {
                find_base(y, ys);
                y = ys.back();
                ys.pop_back();
            }
            SASSERT(!has_sub(x));
            SASSERT(!has_sub(y));
            if (width(x) == width(y)) {
                // LOG("Match " << x << " and " << y);
                if (!merge_base(x, y, dep))
                    return false;
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
        return true;
    }

    bool slicing::merge(slice_vector& xs, slice y, dep_t dep) {
        slice_vector& ys = m_tmp2;
        SASSERT(ys.empty());
        ys.push_back(y);
        return merge(xs, ys, dep);  // will clear xs and ys
    }

    bool slicing::merge(slice x, slice y, dep_t dep) {
        SASSERT_EQ(width(x), width(y));
        if (!has_sub(x) && !has_sub(y))
            return merge_base(x, y, dep);
        slice_vector& xs = m_tmp2;
        slice_vector& ys = m_tmp3;
        SASSERT(xs.empty());
        SASSERT(ys.empty());
        xs.push_back(x);
        ys.push_back(y);
        return merge(xs, ys, dep);  // will clear xs and ys
    }

    bool slicing::is_equal(slice x, slice y) {
        SASSERT_EQ(width(x), width(y));
        x = find(x);
        y = find(y);
        if (x == y)
            return true;
        slice_vector& xs = m_tmp2;
        slice_vector& ys = m_tmp3;
        SASSERT(xs.empty());
        SASSERT(ys.empty());
        find_base(x, xs);
        find_base(y, ys);
        SASSERT(all_of(xs, [this](slice s) { return s == find(s); }));
        SASSERT(all_of(ys, [this](slice s) { return s == find(s); }));
        bool result = (xs == ys);
        xs.clear();
        ys.clear();
        if (result) {
            // TODO: merge equivalence class of x, y (on upper level)? but can we always combine the sub-trees?
        }
        return result;
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

    void slicing::mk_slice(slice src, unsigned const hi, unsigned const lo, slice_vector& out, bool output_full_src, bool output_base) {
        SASSERT(hi >= lo);
        SASSERT_EQ(src, find(src));  // splits are only stored for the representative
        SASSERT(width(src) > hi);  // extracted range must be fully contained inside the src slice
        auto output_slice = [this, output_base, &out](slice s) {
            if (output_base)
                find_base(s, out);
            else
                out.push_back(s);
        };
        if (lo == 0 && width(src) - 1 == hi) {
            output_slice(src);
            return;
        }
        if (has_sub(src)) {
            // src is split into [src.width-1, cut+1] and [cut, 0]
            unsigned const cut = m_slice_cut[src];
            if (lo >= cut + 1) {
                // target slice falls into upper subslice
                mk_slice(find_sub_hi(src), hi - cut - 1, lo - cut - 1, out, output_full_src, output_base);
                if (output_full_src)
                    output_slice(find_sub_lo(src));
                return;
            }
            else if (cut >= hi) {
                // target slice falls into lower subslice
                if (output_full_src)
                    output_slice(find_sub_hi(src));
                mk_slice(find_sub_lo(src), hi, lo, out, output_full_src, output_base);
                return;
            }
            else {
                SASSERT(hi > cut && cut >= lo);
                // desired range spans over the cutpoint, so we get multiple slices in the result
                mk_slice(find_sub_hi(src), hi - cut - 1, 0, out, output_full_src, output_base);
                mk_slice(find_sub_lo(src), cut, lo, out, output_full_src, output_base);
                return;
            }
        }
        else {
            // [src.width-1, 0] has no subdivision yet
            if (width(src) - 1 > hi) {
                split(src, hi);
                SASSERT(!has_sub(find_sub_hi(src)));
                if (output_full_src)
                    out.push_back(find_sub_hi(src));
                mk_slice(find_sub_lo(src), hi, lo, out, output_full_src, output_base);  // recursive call to take care of case lo > 0
                return;
            }
            else {
                SASSERT(lo > 0);
                split(src, lo - 1);
                out.push_back(find_sub_hi(src));
                SASSERT(!has_sub(find_sub_lo(src)));
                if (output_full_src)
                    out.push_back(find_sub_lo(src));
                return;
            }
        }
        UNREACHABLE();
    }

    pvar slicing::mk_slice_extract(slice src, unsigned hi, unsigned lo) {
        slice_vector slices;
        mk_slice(src, hi, lo, slices, false, true);
        if (slices.size() == 1) {
            slice s = slices[0];
            if (slice2var(s) != null_var)
                return slice2var(s);
            // TODO: optimization: could save a slice-tree by directly assigning slice2var(s) = v for new var v.
        }
        pvar v = m_solver.add_var(hi - lo + 1);
        VERIFY(merge(slices, var2slice(v), null_dep));
        return v;
    }

    pvar slicing::mk_extract_var(pvar src, unsigned hi, unsigned lo) {
        return mk_slice_extract(var2slice(src), hi, lo);
    }

    pdd slicing::mk_extract(pvar src, unsigned hi, unsigned lo) {
        return m_solver.var(mk_extract_var(src, hi, lo));
    }

    pdd slicing::mk_extract(pdd const& p, unsigned hi, unsigned lo) {
        SASSERT(hi >= lo);
        SASSERT(p.power_of_2() > hi);
        if (p.is_val()) {
            // p[hi:lo] = (p >> lo) % 2^(hi - lo + 1)
            rational q = mod2k(machine_div2k(p.val(), lo), hi - lo + 1);
            return p.manager().mk_val(q);
        }
        if (!lo) {
            // TODO: we could push the extract down into variables of the term instead of introducing a name.
        }
        return m_solver.var(mk_slice_extract(pdd2slice(p), hi, lo));
    }

    slicing::slice slicing::pdd2slice(pdd const& p) {
        pvar const v = m_solver.m_names.mk_name(p);
        return var2slice(v);
    }

    pdd slicing::mk_concat(pdd const& p, pdd const& q) {
        // v := p ++ q      (new variable of size |p| + |q|)
        // v[:|q|] = p
        // v[|q|:] = q
        unsigned const p_sz = p.power_of_2();
        unsigned const q_sz = q.power_of_2();
        unsigned const v_sz = p_sz + q_sz;
        if (p.is_val() && q.is_val()) {
            rational const val = p.val() * rational::power_of_two(q_sz) + q.val();
            return m_solver.sz2pdd(v_sz).mk_val(val);
        }
        if (p.is_val()) {
        }
        if (q.is_val()) {
        }
        pvar const v = m_solver.add_var(v_sz);
        slice_vector tmp;
        tmp.push_back(pdd2slice(p));
        tmp.push_back(pdd2slice(q));
        VERIFY(merge(tmp, var2slice(v), null_dep));
        return m_solver.var(v);
    }

    void slicing::add_constraint(signed_constraint c) {
        // TODO: evaluate under current assignment?
        if (!c->is_eq())
            return;
        pdd const& p = c->to_eq();
        auto& m = p.manager();
        for (auto& [a, x] : p.linear_monomials()) {
            if (a != 1 && a != m.max_value())
                continue;
            pdd body = a.is_one() ? (m.mk_var(x) - p) : (m.mk_var(x) + p);
            // c is either x = body or x != body, depending on polarity
            LOG("Equation from constraint " << c << ": v" << x << " = " << body);
            slice const sx = var2slice(x);
            if (body.is_val()) {
                // Simple assignment x = value
                // TODO: set fixed bits
                continue;
            }
            pvar const y = m_solver.m_names.get_name(body);
            if (y == null_var) {
                // TODO: register name trigger (if a name for value 'body' is created later, then merge x=y at that time)
                continue;
            }
            slice const sy = var2slice(y);
            if (c.is_positive()) {
                if (!merge(sx, sy, c.blit()))
                    return;
            }
            else {
                SASSERT(c.is_negative());
                if (is_equal(sx, sy)) {
                    // TODO: conflict
                    NOT_IMPLEMENTED_YET();
                    return;
                }
            }
        }
    }

    void slicing::add_value(pvar v, rational const& value) {
        // go through all existing nodes, and evaluate v?
        // can do that externally
    }

    std::ostream& slicing::display(std::ostream& out) const {
        slice_vector base;
        for (pvar v = 0; v < m_var2slice.size(); ++v) {
            out << "v" << v << ":";
            base.reset();
            slice const vs = var2slice(v);
            find_base(vs, base);
            for (slice s : base)
                display(out << " ", s);
            // if (has_value(vs)) {
            //     out << "        -- (val:" << get_value(vs) << ")";
            // }
            out << "\n";
        }
        return out;
    }

    std::ostream& slicing::display_tree(std::ostream& out) const {
        for (pvar v = 0; v < m_var2slice.size(); ++v) {
            out << "v" << v << ":\n";
            slice const s = var2slice(v);
            display_tree(out, s, 4, width(s) - 1, 0);
        }
        return out;
    }

    std::ostream& slicing::display_tree(std::ostream& out, slice s, unsigned indent, unsigned hi, unsigned lo) const {
        out << std::string(indent, ' ') << "[" << hi << ":" << lo << "]";
        out << " id=" << s;
        out << " w=" << width(s);
        if (find(s) != s)
            out << " root=" << find(s);
        // if (has_value(s))
        //     out << " value=" << get_value(s);
        out << "\n";
        if (has_sub(s)) {
            unsigned cut = m_slice_cut[s];
            display_tree(out, sub_hi(s), indent + 4, hi, cut + 1 + lo);
            display_tree(out, sub_lo(s), indent + 4, cut + lo, lo);
        }
        return out;
    }

    std::ostream& slicing::display(std::ostream& out, slice s) const {
        out << "{id:" << s << ",w:" << width(s);
        // if (has_value(s))
        //     out << ",val:" << get_value(s);
        out << "}";
        return out;
    }

    bool slicing::invariant() const {
        VERIFY(m_tmp1.empty());
        VERIFY(m_tmp2.empty());
        VERIFY(m_tmp3.empty());
        for (slice s = 0; s < m_slice_cut.size(); ++s) {
            // if the slice is equivalent to a variable, then the variable's slice is in the equivalence class
            pvar const v = slice2var(s);
            SASSERT_EQ(v != null_var, find(var2slice(v)) == find(s));
            // properties below only matter for representatives
            if (s != find(s))
                continue;
            // if slice has a value, it should be propagated to its sub-slices
            // if (has_value(s)) {
            //     VERIFY(has_value(find_sub_hi(s)));
            //     VERIFY(has_value(find_sub_lo(s)));
            // }
        }
        return true;
    }
#endif

}
