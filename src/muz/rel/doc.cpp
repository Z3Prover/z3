/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    doc.cpp

Abstract:

    difference of cubes.

Author:

    Nuno Lopes (a-nlopes) 2013-03-01
    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:

    Based on ternary_diff_bitvector by Nuno Lopes.

--*/

#include "doc.h"

doc_manager::doc_manager(unsigned n): m(n), m_alloc("doc") {
    m_full = m.allocateX();
}

doc_manager::~doc_manager() {
    m.deallocate(m_full);
}

doc* doc_manager::allocate() {
    return allocate(m.allocate());
}
doc* doc_manager::allocate1() {
    return allocate(m.allocate1());
}
doc* doc_manager::allocate0() {
    return allocate(m.allocate0());
}
doc* doc_manager::allocateX() {
    return allocate(m.allocateX());
}
doc* doc_manager::allocate(doc const& src) {
    doc* r = allocate(m.allocate(src.pos()));
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        r->neg().push_back(m.allocate(src.neg()[i]));
    }
    return r;
}
doc* doc_manager::allocate(tbv* t) {
    void* mm = m_alloc.allocate(sizeof(doc));
    return new (mm) doc(t);
}
doc* doc_manager::allocate(tbv const& src) {
    return allocate(m.allocate(src));
}
doc* doc_manager::allocate(uint64 n) {
    return allocate(m.allocate(n));
}
doc* doc_manager::allocate(rational const& r) {
    return allocate(m.allocate(r));
}
doc* doc_manager::allocate(uint64 n, unsigned hi, unsigned lo) {
    return allocate(m.allocate(n, hi, lo));
}
doc* doc_manager::allocate(doc const& src, unsigned const* permutation) {
    doc* r = allocate(m.allocate(src.pos(), permutation));
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        r->neg().push_back(m.allocate(src.neg()[i], permutation));
    }
    return r;
}
void doc_manager::deallocate(doc* src) {
    if (!src) return;
    m.deallocate(&src->pos());
    src->neg().reset(m);
    m_alloc.deallocate(sizeof(doc), src);
    //    dealloc(src);
}
void doc_manager::copy(doc& dst, doc const& src)  {
    m.copy(dst.pos(), src.pos());
    unsigned n = std::min(src.neg().size(), dst.neg().size());
    for (unsigned i = 0; i < n; ++i) {
        m.copy(dst.neg()[i], src.neg()[i]);
    }
    for (unsigned i = n; i < dst.neg().size(); ++i) {
        dst.neg().erase(m, dst.neg().size()-1);
    }
    for (unsigned i = n; i < src.neg().size(); ++i) {
        dst.neg().push_back(m.allocate(src.neg()[i]));
    }
}
doc& doc_manager::fill0(doc& src) {
    src.neg().reset(m);
    m.fill0(src.pos());
    return src;
}
doc& doc_manager::fill1(doc& src) {
    src.neg().reset(m);
    m.fill1(src.pos());
    return src;
}
doc& doc_manager::fillX(doc& src) {
    src.neg().reset(m);
    m.fillX(src.pos());
    return src;
}
bool doc_manager::set_and(doc& dst, doc const& src)  {
    // (A \ B) & (C \ D) = (A & C) \ (B u D)
    if (!m.set_and(dst.pos(), src.pos())) return false;
    for (unsigned i = 0; i < dst.neg().size(); ++i) {
        if (!m.set_and(dst.neg()[i], dst.pos())) {
            dst.neg().erase(m, i);
            --i;
        }
    }
    tbv_ref t(m);
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        t = m.allocate(src.neg()[i]);
        if (m.set_and(*t, dst.pos())) {
            dst.neg().insert(m, t.detach());
        }
    }
    return (src.neg().is_empty() || fold_neg(dst));
}

bool doc_manager::well_formed(doc const& d) const {
    if (!m.is_well_formed(d.pos())) return false;
    for (unsigned i = 0; i < d.neg().size(); ++i) {
        if (!m.is_well_formed(d.neg()[i])) return false;
        if (!m.contains(d.pos(), d.neg()[i])) return false;
    }
    return true;
}

bool doc_manager::fold_neg(doc& dst) {
 start_over:
    for (unsigned i = 0; i < dst.neg().size(); ++i) {
        unsigned index;
        unsigned count = diff_by_012(dst.pos(), dst.neg()[i], index);
        if (count != 2) {
            if (count == 0) {
                return false;
            }
            else if (count == 3) {
                dst.neg().erase(tbvm(), i);
                --i;
            }
            else { // count == 1:
                dst.pos().set(index, neg(dst.neg()[i][index]));
                dst.neg().erase(tbvm(), i);
                goto start_over;
            }
        }
    }
    return true;
}

unsigned doc_manager::diff_by_012(tbv const& pos, tbv const& neg, unsigned& index) {
    unsigned n = num_tbits();
    unsigned count = 0;
    for (unsigned i = 0; i < n; ++i) {
        tbit b1 = pos[i];
        tbit b2 = neg[i];
        SASSERT(b1 != BIT_z && b2 != BIT_z);
        if (b1 != b2) {
            if (count == 1) return 2;
            if (b1 == BIT_x) {
                index = i;
                count = 1;
            }
            else if (b2 != BIT_x) {
                return 3;
            }
        }
    }
    return count;
}

void doc_manager::set(doc& d, unsigned idx, tbit value) {
    d.pos().set(idx, value);
    for (unsigned i = 0; i < d.neg().size(); ++i) {
        d.neg()[i].set(idx, value);
    }
}

//
// merge range from [lo:lo+length-1] with each index in equivalence class.
// under assumption of equalities and columns that are discarded.
//
bool doc_manager::merge(
    doc& d, unsigned lo, unsigned length, 
    subset_ints const& equalities, bit_vector const& discard_cols) {
    for (unsigned i = 0; i < length; ++i) {
        unsigned idx = lo + i;
        if (!merge(d, lo + i, equalities, discard_cols)) return false;
    }
    return true;
}
bool doc_manager::merge(doc& d, unsigned idx, subset_ints const& equalities, 
                        bit_vector const& discard_cols) {
    unsigned root = equalities.find(idx);
    idx = root;
    unsigned num_x = 0;
    unsigned root1;
    tbit value = BIT_x;
    do {
        switch (d[idx]) {
        case BIT_0:
            if (value == BIT_1) return false;
            value = BIT_0;
            break;
        case BIT_1:
            if (value == BIT_0) return false;
            value = BIT_1;
            break;
        case BIT_x:
            if (!discard_cols.get(idx)) {
                ++num_x;
                root1 = idx;
            }
            break;
        default:
            break;
        }
        idx = equalities.next(idx);
    }
    while (idx != root);

    if (num_x == 0) {
        // nothing to do.
    }
    else if (value != BIT_x) {
        do {
            if (d[idx] == BIT_x) {
                set(d, idx, value);
            }
            idx = equalities.next(idx);
        }
        while (idx != root);
    }
    else {
        do {
            if (!discard_cols.get(idx) && idx != root1) {
                tbv* t = tbvm().allocate(d.pos());
                t->set(idx, BIT_0);
                t->set(root1, BIT_1);
                d.neg().insert(tbvm(), t);
                t = tbvm().allocate(d.pos());
                t->set(idx, BIT_1);
                t->set(root1, BIT_0);
                d.neg().insert(tbvm(), t);                
            }
            idx = equalities.next(idx);
        }
        while (idx != root);
    }
    return true;
}

bool doc_manager::intersect(doc const& A, doc const& B, doc& result) {
    copy(result, A);
    return set_and(result, B);
}

//
// 1. If n = 0,1: can project directly.
// 2. If tbv_i uses X in all positions with vars or constant where tbv is constant: can project directly.
// 3. Perform resolution on remaining tbv_i 
//
// tbv & ~tbv1 & ~tbv2 & .. & ~tbv_n
// Semantics of ~tbv1 is that it is a clause of literals.
//   indices where BIT_1 is set are negative.
//   indices where BIT_0 is set are positive.
//

doc* doc_manager::project(doc_manager& dstm, unsigned n, bool const* to_delete, doc const& src) {
    tbv_manager& dstt = dstm.m;
    doc* r = dstm.allocate(dstt.project(n, to_delete, src.pos()));

    if (src.neg().is_empty()) {
        return r;
    }
    if (src.neg().size() == 1) {
        r->neg().push_back(dstt.project(n, to_delete, src.neg()[0]));
        return r;
    }
    
    //
    // All negations can be projected if they are sign compatible.
    //
    tbv_ref bits(tbvm(), tbvm().allocateX());
    for (unsigned i = 0; i < src.neg().size(); ++i) {        
        tbvm().set_and(*bits, src.neg()[i]);
    }
    bool can_project_const = true;
    for (unsigned i = 0; can_project_const && i < n; ++i) {
        can_project_const = !to_delete[i] || (*bits)[i] == BIT_x;
    }
    if (can_project_const) {
        for (unsigned i = 0; i < src.neg().size(); ++i) {        
            r->neg().push_back(dstt.project(n, to_delete, src.neg()[i]));
        }
        return r;
    }

    // 
    // A negation can be projected directly if it does not constrain
    // deleted variables.
    // 
    ptr_vector<tbv> todo;
    for (unsigned i = 0; i < src.neg().size(); ++i) {        
        if (can_project_neg(src.pos(), n, to_delete, src.neg()[i])) {
            r->neg().push_back(dstt.project(n, to_delete, src.neg()[i]));
        }
        else {
            todo.push_back(tbvm().allocate(src.neg()[i]));
        }
    }
    if (todo.empty()) {
        return r;
    }
    ptr_vector<tbv> new_todo;
    utbv pos, neg;
    tbv_ref t1(tbvm()), t2(tbvm());
    for (unsigned i = 0; i < n; ++i) {
        if (to_delete[i] && (*bits)[i] != BIT_x) {
            TRACE("doc", tout << "delete " << i << " ";
                  for (unsigned j = 0; j < todo.size(); ++j) {
                      tbvm().display(tout, *todo[j]) << " ";
                  }
                  tout << "\n";);
            SASSERT(pos.is_empty());
            SASSERT(neg.is_empty());
            SASSERT(new_todo.empty());
            while (!todo.empty()) {
                tbv* t = todo.back();
                todo.pop_back();
                switch((*t)[i]) {
                case BIT_x: new_todo.push_back(t); break;
                case BIT_0: neg.push_back(t); break;
                case BIT_1: pos.push_back(t); break;
                default: UNREACHABLE(); break;                    
                }
            }
            if (pos.is_empty() || neg.is_empty()) {
                std::swap(new_todo, todo);
                pos.reset(tbvm());
                neg.reset(tbvm());
                continue;
            }
            TRACE("doc",
                  tout << "pos: ";
                  for (unsigned i = 0; i < pos.size(); ++i) {
                      tbvm().display(tout, pos[i]) << " ";
                  }
                  tout << "\nneg: ";
                  for (unsigned i = 0; i < neg.size(); ++i) {
                      tbvm().display(tout, neg[i]) << " ";
                  }
                  tout << "\n";
                  );
                  
            for (unsigned j = 0; j < pos.size(); ++j) {
                for (unsigned k = 0; k < neg.size(); ++k) {
                    t1 = tbvm().allocate(pos[j]);
                    (*t1).set(i, BIT_x);
                    if (tbvm().set_and(*t1, neg[k])) {
                        (*t1).set(i, BIT_x);
                        new_todo.push_back(t1.detach());
                    }
                }                
            }
            pos.reset(tbvm());
            neg.reset(tbvm());
            std::swap(todo, new_todo);
        }
    }
    for (unsigned i = 0; i < todo.size(); ++i) {
        r->neg().push_back(dstt.project(n, to_delete, *todo[i]));
        tbvm().deallocate(todo[i]);
    }
    return r;
}

bool doc_manager::can_project_neg(tbv const& pos, unsigned n, bool const* to_delete, tbv const& neg) {
    for (unsigned i = 0; i < n; ++i) {
        if (to_delete[i] && BIT_x != neg[i] && BIT_x == pos[i]) return false;
    }
    return true;
}
    

void doc_manager::complement(doc const& src, ptr_vector<doc>& result) {
    result.reset();
    if (is_full(src)) {
        return;
    }
    doc* r = allocateX();
    r->neg().push_back(m.allocate(src.pos()));
    result.push_back(r);
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        result.push_back(allocate(src.neg()[i]));
    }
}
void doc_manager::subtract(doc const& A, doc const& B, ptr_vector<doc>& result) {
    doc_ref r(*this), r2(*this);
    r = allocate(A);
    if (r->neg().insert(m, m.allocate(B.pos()))) {
        result.push_back(r.detach());
        r = allocate(A);
    }
    for (unsigned i = 0; i < B.neg().size(); ++i) {
        r2 = allocate(B.neg()[i]);
        if (set_and(*r, *r2)) {
            result.push_back(r.detach());
        }
        r = allocate(A);
    }
}
bool doc_manager::equals(doc const& a, doc const& b) const {
    if (!m.equals(a.pos(), b.pos())) return false;
    if (a.neg().size() != b.neg().size()) return false;
    for (unsigned i = 0; i < a.neg().size(); ++i) {
        if (!m.equals(a.neg()[i], b.neg()[i])) return false;
    }
    return true;
}
bool doc_manager::is_full(doc const& src) const {
    return src.neg().is_empty() && m.equals(src.pos(), *m_full);
}
unsigned doc_manager::hash(doc const& src) const {
    unsigned r = 0;
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        r = 2*r + m.hash(src.neg()[i]);
    }
    return r + m.hash(src.pos());
}
// approximation
// A \ (A1 u A2) contains B \ (B1 u B2)
// if
// A contains B
// B1 contains A1 or B2 contains A1
// B1 contains A2 or B2 contains A2
bool doc_manager::contains(doc const& a, doc const& b) const {
    if (!m.contains(a.pos(), b.pos())) return false;
    for (unsigned i = 0; i < a.neg().size(); ++i) {
        bool found = false;
        for (unsigned j = 0; !found && j < b.neg().size(); ++j) {
            found = m.contains(b.neg()[i],a.neg()[j]);
        }
        if (!found) return false;
    }
    return true;
}
std::ostream& doc_manager::display(std::ostream& out, doc const& b) const {
    m.display(out, b.pos());
    if (b.neg().is_empty()) return out;
    out << " \\ ";
    b.neg().display(m, out);
    return out;
}

