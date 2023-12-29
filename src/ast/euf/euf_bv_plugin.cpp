/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_bv_plugin.cpp

Abstract:

    plugin structure for bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-08
    Jakob Rath 2023-11-08

Objective:

satisfies extract/concat axioms.
  - concat(n{I],n[J]) = n[IJ] for I, J consecutive.
  - concat(v1, v2) = 2^width(v1)*v2 + v1
  - concat(n[width(n)-1:0]) = n
  - concat(a, b)[I] = concat(a[I1], b[I2])
  - concat(a, concat(b, c)) = concat(concat(a, b), c)

E-graph:

The E-graph contains node definitions of the form

   n := f(n1,n2,..)

and congruences:

   n ~ n' means root(n) = root(n')

Saturated state:

   1. n := n1[I], n' := n2[J], n1 ~ n2 => root(n1) contains tree refining both I, J from smaller intervals

   2. n := concat(n1[I], n2[J]), n1 ~ n2 ~ n3 I and J are consecutive => n ~ n3[IJ]

   3. n := concat(n1[I], n2[J]), I and J are consecutive & n1 ~ n2, n1[I] ~ v1, n1[J] ~ v2 => n ~ 2^width(v1)*v2 + v1

   4. n := concat(n1[I], n2[J], I, J are consecutive, n1 ~ n2, n ~ v => n1[I] ~ v mod 2^width(n1[I]), n2[J] ~ v div 2^width(n1[I])

   5. n' := n[I] => n ~ n[width(n)-1:0]

   6. n := concat(a, concat(b, c)) => n ~ concat(concat(a, b), c)
      - handled by rewriter pre-processing for inputs
      - terms created internally are not equated modulo associativity

   7, n := concat(n1, n2)[I] => n ~ concat(n1[I1],n2[I2]) or n[I1] or n[I2]
      - handled by rewriter pre-processing

Example:
   x == (x1 x2) x3
   y == y1 (y2 y3)
   x1 == y1, x2 == y2, x3 == y3
   =>
   x = y

   by x2 == y2, x3 == y3 => (x2 x3) = (y2 y3)
   by (2) => x[I23] = (x2 x3)
   by (2) => x[I123] = (x1 (x2 x3))
   by (5) => x = x[I123]

The formal properties of saturation have to be established.

- Saturation does not complete with respect to associativity.
Instead the claim is along the lines that the resulting E-graph can be used as a canonizer.
If given a set of equations E that are saturated, and terms t1, t2 that are 
both simplified with respect to left-associativity of concatenation, and t1, t2 belong to the E-graph,
then t1 = t2 iff t1 ~ t2 in the E-graph.

TODO: Is saturation for (7) overkill for the purpose of canonization?

TODO: revisit re-entrancy during register_node. It can be called when creating internal extract terms.
Instead of allowing re-entrancy we can accumulate nodes that are registered during recursive calls 
and have the main call perform recursive slicing.

--*/


#include "ast/euf/euf_bv_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    bv_plugin::bv_plugin(egraph& g):
        plugin(g),
        bv(g.get_manager())
    {}

    enode* bv_plugin::mk_value_concat(enode* a, enode* b) {
        auto v1 = get_value(a);
        auto v2 = get_value(b);
        auto v3 = v1 + v2 * power(rational(2), width(a));
        return mk_value(v3, width(a) + width(b));
    }

    enode* bv_plugin::mk_value(rational const& v, unsigned sz) {
        auto e = bv.mk_numeral(v, sz);
        return mk(e, 0, nullptr);
    }

    void bv_plugin::merge_eh(enode* x, enode* y) {
        if (!bv.is_bv(x->get_expr()))
            return;

        TRACE("bv", tout << "merge_eh " << g.bpp(x) << " == " << g.bpp(y) << "\n");
        SASSERT(!m_internal);
        flet<bool> _internal(m_internal, true);

        propagate_values(x);

        // ensure slices align
        if (has_sub(x) || has_sub(y)) {
            enode_vector& xs = m_xs, & ys = m_ys;
            xs.reset();
            ys.reset();
            xs.push_back(x);
            ys.push_back(y);
            merge(xs, ys, justification::equality(x, y));
        }

        // ensure p := concat(n1[I], n2[J]), n1 ~ n2 ~ n3 I and J are consecutive => p ~ n3[IJ]
        for (auto* n : enode_class(x))
            propagate_extract(n);
    }

    // enforce concat(v1, v2) = v2*2^|v1| + v1
    void bv_plugin::propagate_values(enode* x) {
        if (!is_value(x))
            return;
        
        enode* a, * b;
        for (enode* p : enode_parents(x))
            if (is_concat(p, a, b) && is_value(a) && is_value(b) && !is_value(p))
                push_merge(mk_concat(a->get_interpreted(), b->get_interpreted()), mk_value_concat(a, b));
        
        for (enode* sib : enode_class(x)) {
            if (is_concat(sib, a, b)) {
                if (!is_value(a) || !is_value(b)) {
                    auto val = get_value(x);
                    auto v1 = mod2k(val, width(a));
                    auto v2 = machine_div2k(val, width(a));
                    push_merge(mk_concat(mk_value(v1, width(a)), mk_value(v2, width(b))), x->get_interpreted());
                }
            }
        }
    }

    //
    // p := concat(n1[I], n2[J]), n1 ~ n2 ~ n3 I and J are consecutive => p ~ n3[IJ]
    // 
    // n is of form arg[I]
    // p is of form concat(n, b) or concat(a, n)
    // b is congruent to arg[J], I is consecutive with J => ensure that arg[IJ] = p
    // a is congruent to arg[J], J is consecutive with I => ensure that arg[JI] = p
    // 

    void bv_plugin::propagate_extract(enode* n) {
        unsigned lo1, hi1, lo2, hi2;
        enode* a, * b;
        if (!is_extract(n, lo1, hi1))
            return;

        enode* arg = n->get_arg(0);
        enode* arg_r = arg->get_root();       
        enode* n_r = n->get_root();

        auto ensure_concat = [&](unsigned lo, unsigned mid, unsigned hi) {
            TRACE("bv", tout << "ensure-concat " << lo << " " << mid << " " << hi << "\n");
            unsigned lo_, hi_;
            for (enode* p1 : enode_parents(n))
                if (is_extract(p1, lo_, hi_) && lo_ == lo && hi_ == hi && p1->get_arg(0)->get_root() == arg_r)
                    return;
            // add the axiom instead of merge(p, mk_extract(arg, lo, hi)), which would require tracking justifications
            push_merge(mk_concat(mk_extract(arg, lo, mid), mk_extract(arg, mid + 1, hi)), mk_extract(arg, lo, hi));
        };

        auto propagate_left = [&](enode* b) {
            TRACE("bv", tout << "propagate-left " << g.bpp(b) << "\n");
            for (enode* sib : enode_class(b))
                if (is_extract(sib, lo2, hi2) && sib->get_arg(0)->get_root() == arg_r && hi1 + 1 == lo2)
                    ensure_concat(lo1, hi1, hi2);
        };

        auto propagate_right = [&](enode* a) {
            TRACE("bv", tout << "propagate-right " << g.bpp(a) << "\n");
            for (enode* sib : enode_class(a))
                if (is_extract(sib, lo2, hi2) && sib->get_arg(0)->get_root() == arg_r && hi2 + 1 == lo1)
                    ensure_concat(lo2, hi2, hi1);
        };
        
        for (enode* p : enode_parents(n)) {
            if (is_concat(p, a, b)) {
                if (a->get_root() == n_r)
                    propagate_left(b);
                if (b->get_root() == n_r)
                    propagate_right(a);
            }
        }
    }

    void bv_plugin::push_undo_split(enode* n) { 
        m_undo_split.push_back(n);
        push_plugin_undo(bv.get_family_id());
    }

    void bv_plugin::undo() {
        enode* n = m_undo_split.back();
        m_undo_split.pop_back();
        auto& i = info(n);
        i.lo = nullptr;
        i.hi = nullptr;
        i.cut = null_cut;       
    }
    
    void bv_plugin::register_node(enode* n) {
        TRACE("bv", tout << "register " << g.bpp(n) << "\n");
        auto& i = info(n);
        i.value = n;    
        enode* a, * b;
        if (is_concat(n, a, b)) {
            i.lo = a;
            i.hi = b;
            i.cut = width(a);
            push_undo_split(n);
        }
        unsigned lo, hi;
        if (is_extract(n, lo, hi) && (lo != 0 || hi + 1 != width(n->get_arg(0)))) {
            enode* arg = n->get_arg(0);   
            unsigned w = width(arg);
            if (all_of(enode_parents(arg), [&](enode* p) { unsigned _lo, _hi;  return !is_extract(p, _lo, _hi) || _lo != 0 || _hi + 1 != w; }))
                push_merge(mk_extract(arg, 0, w - 1), arg);
            ensure_slice(arg, lo, hi);
        }
    }

    //
    // Ensure that there are slices at boundaries of n[hi:lo]
    //
    void bv_plugin::ensure_slice(enode* n, unsigned lo, unsigned hi) {
        enode* r = n;
        unsigned lb = 0, ub = width(n) - 1;
        while (true) {   
            TRACE("bv", tout << "ensure slice " << g.bpp(n) << " " << lb << " [" << lo << ", " << hi << "] " << ub << "\n");
            SASSERT(lb <= lo && hi <= ub);
            SASSERT(ub - lb + 1 == width(r));
            if (lb == lo && ub == hi)
                return;
            slice_info& i = info(r);
            if (!i.lo) {
                if (lo > lb) {
                    split(r, lo - lb);
                    if (hi < ub) // or split(info(r).hi, ...)                       
                        ensure_slice(n, lo, hi);                    
                }
                else if (hi < ub)
                    split(r, ub - hi);
                break;
            }
            auto cut = i.cut;
            if (cut + lb <= lo) {
                lb += cut;
                r = i.hi;
                continue;
            }
            if (cut + lb > hi) {
                ub = cut + lb - 1;
                r = i.lo;
                continue;
            }
            SASSERT(lo < cut + lb && cut + lb <= hi);
            ensure_slice(n, lo, cut + lb - 1);
            ensure_slice(n, cut + lb, hi);
            break;
        }
    }

    enode* bv_plugin::mk_extract(enode* n, unsigned lo, unsigned hi) { 
        SASSERT(lo <= hi && width(n) > hi - lo);
        unsigned lo1, hi1;
        while (is_extract(n, lo1, hi1)) {
            lo += lo1;
            hi += lo1;
            n = n->get_arg(0);
        }
        return mk(bv.mk_extract(hi, lo, n->get_expr()), 1, &n);
    }

    enode* bv_plugin::mk_concat(enode* lo, enode* hi) { 
        enode* args[2] = { lo, hi }; 
        return mk(bv.mk_concat(lo->get_expr(), hi->get_expr()), 2, args); 
    }

    void bv_plugin::merge(enode_vector& xs, enode_vector& ys, justification dep) {  
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            auto x = xs.back();
            auto y = ys.back();
            if (unfold_sub(x, xs))
                continue;
            else if (unfold_sub(y, ys))
                continue;
            else if (unfold_width(x, xs, y, ys))
                continue;
            else if (unfold_width(y, ys, x, xs))
                continue;
            else if (x->get_root() != y->get_root()) 
                push_merge(x, y, dep);            
            xs.pop_back();
            ys.pop_back();
        }
        SASSERT(ys.empty());
    }

    bool bv_plugin::unfold_sub(enode* x, enode_vector& xs) {
        if (!has_sub(x))
            return false;
        xs.pop_back();
        xs.push_back(sub_hi(x));
        xs.push_back(sub_lo(x));
        return true;
    }

    bool bv_plugin::unfold_width(enode* x, enode_vector& xs, enode* y, enode_vector& ys) {
        if (width(x) <= width(y))
            return false;            
        split(x, width(y));
        xs.pop_back();
        xs.push_back(sub_hi(x));
        xs.push_back(sub_lo(x));
        return true;
    }

    void bv_plugin::split(enode* n, unsigned cut) {
        TRACE("bv", tout << "split: " << g.bpp(n) << " " << cut << "\n");
        unsigned w = width(n);
        SASSERT(!info(n).hi);
        SASSERT(0 < cut && cut < w);
        enode* hi = mk_extract(n, cut, w - 1);
        enode* lo = mk_extract(n, 0, cut - 1);        
        auto& i = info(n);
        if (!i.value)
            i.value = n;
        i.hi = hi;
        i.lo = lo;
        i.cut = cut;
        push_undo_split(n);
        push_merge(mk_concat(lo, hi), n);        
    }

    void bv_plugin::sub_slices(enode* n, std::function<bool(enode*, unsigned)>& consumer) {
        m_todo.push_back({ n, 0 });
        unsigned lo, hi;
        expr* e;

        for (unsigned i = 0; i < m_todo.size(); ++i) {
            auto [n, offset] = m_todo[i];
            m_offsets.reserve(n->get_root_id() + 1);
            auto& offsets = m_offsets[n->get_root_id()];
            if (offsets.contains(offset))
                continue;
            offsets.push_back(offset);
            if (!consumer(n, offset))
                continue;
            for (auto sib : euf::enode_class(n)) {
                if (bv.is_concat(sib->get_expr())) {
                    unsigned delta = 0;
                    for (unsigned j = sib->num_args(); j-- > 0; ) {
                        auto arg = sib->get_arg(j);
                        m_todo.push_back({ arg, offset + delta });
                        delta += width(arg);
                    }
                }
            }
            for (auto p : euf::enode_parents(n->get_root())) {
                if (bv.is_extract(p->get_expr(), lo, hi, e)) {
                    SASSERT(g.find(e)->get_root() == n->get_root());
                    m_todo.push_back({ p, offset + lo });
                }
            }
        }
        clear_offsets();
    }

    void bv_plugin::super_slices(enode* n, std::function<bool(enode*, unsigned)>& consumer) {
        m_todo.push_back({ n, 0 });
        unsigned lo, hi;
        expr* e;

        for (unsigned i = 0; i < m_todo.size(); ++i) {
            auto [n, offset] = m_todo[i];
            m_offsets.reserve(n->get_root_id() + 1);
            auto& offsets = m_offsets[n->get_root_id()];
            if (offsets.contains(offset))
                continue;
            offsets.push_back(offset);
            if (!consumer(n, offset))
                continue;
            for (auto sib : euf::enode_class(n)) {
                if (bv.is_extract(sib->get_expr(), lo, hi, e)) {
                    auto child = g.find(e);
                    m_todo.push_back({ child, offset + lo });
                }
            }
            for (auto p : euf::enode_parents(n->get_root())) {
                if (bv.is_concat(p->get_expr())) {
                    unsigned delta = 0;
                    for (unsigned j = p->num_args(); j-- > 0; ) {
                        auto arg = p->get_arg(j);
                        if (arg->get_root() == n->get_root()) 
                            m_todo.push_back({ p, offset + delta });
                        delta += width(arg);                   
                    }
                }
            }
        }
        clear_offsets();
    }

    //
    // Explain that a is a subslice of b at offset
    // or that b is a subslice of a at offset
    // 
    void bv_plugin::explain_slice(enode* a, unsigned offset, enode* b, std::function<void(enode*, enode*)>& consumer) {
        if (width(a) < width(b))
            std::swap(a, b);
        SASSERT(width(a) >= width(b));
        svector<std::tuple<enode*, enode*, unsigned>> just;
        m_jtodo.push_back({ a, 0, UINT_MAX });
        unsigned lo, hi;
        expr* e;

        for (unsigned i = 0; i < m_jtodo.size(); ++i) {
            auto [n, offs, j] = m_jtodo[i];
            m_offsets.reserve(n->get_root_id() + 1);
            auto& offsets = m_offsets[n->get_root_id()];
            if (offsets.contains(offs))
                continue;
            offsets.push_back(offs);
            if (n->get_root() == b->get_root() && offs == offset) {
                while (j != UINT_MAX) {
                    auto [x, y, j2] = just[j];
                    consumer(x, y);
                    j = j2;
                }
                for (auto const& [n, offset, j] : m_jtodo) {
                    m_offsets.reserve(n->get_root_id() + 1);
                    m_offsets[n->get_root_id()].reset();
                }
                m_jtodo.reset();
                return;
            }
            for (auto sib : euf::enode_class(n)) {
                if (bv.is_concat(sib->get_expr())) {
                    unsigned delta = 0;
                    unsigned j2 = just.size();
                    just.push_back({ n, sib, j });
                    for (unsigned j = sib->num_args(); j-- > 0; ) {
                        auto arg = sib->get_arg(j);
                        m_jtodo.push_back({ arg, offset + delta, j2 });
                        delta += width(arg);
                    }
                }
            }
            for (auto p : euf::enode_parents(n->get_root())) {
                if (bv.is_extract(p->get_expr(), lo, hi, e)) {
                    SASSERT(g.find(e)->get_root() == n->get_root());
                    unsigned j2 = just.size();
                    just.push_back({ g.find(e), n, j});
                    m_jtodo.push_back({ p, offset + lo, j2});
                }
            }
        }
        UNREACHABLE();
    }

    void bv_plugin::clear_offsets() {
        for (auto const& [n, offset] : m_todo) {
            m_offsets.reserve(n->get_root_id() + 1);
            m_offsets[n->get_root_id()].reset();
        }
        m_todo.reset();
    }

    std::ostream& bv_plugin::display(std::ostream& out) const {
        out << "bv\n";
        for (auto const& i : m_info) 
            if (i.lo)            
                out << g.bpp(i.value) << " cut " << i.cut << " lo " << g.bpp(i.lo) << " hi " << g.bpp(i.hi) << "\n";        
        return out;
    }
}
