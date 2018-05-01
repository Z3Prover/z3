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

#include "muz/rel/doc.h"
#include "smt/smt_kernel.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "smt/params/smt_params.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"

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
    SASSERT(t);
    void* mm = m_alloc.allocate(sizeof(doc));
    return new (mm) doc(t);
}
doc* doc_manager::allocate(tbv const& src) {
    return allocate(m.allocate(src));
}
doc* doc_manager::allocate(uint64_t n) {
    return allocate(m.allocate(n));
}
doc* doc_manager::allocate(rational const& r) {
    return allocate(m.allocate(r));
}
doc* doc_manager::allocate(uint64_t n, unsigned hi, unsigned lo) {
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
    src->~doc();
    m_alloc.deallocate(sizeof(doc), src);
}
void doc_manager::copy(doc& dst, doc const& src)  {
    m.copy(dst.pos(), src.pos());
    dst.neg().reset(m);
    for (unsigned i = 0; i < src.neg().size(); ++i) {
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

unsigned doc_manager::get_size_estimate_bytes(const doc& d) const {
    return m.get_size_estimate_bytes(d.pos())
        + d.neg().get_size_estimate_bytes(m)
        + sizeof(doc);
}

bool doc_manager::set_and(doc& dst, doc const& src)  {
    // (A \ B) & (C \ D) = (A & C) \ (B u D)
    if (!m.set_and(dst.pos(), src.pos())) return false;
    dst.neg().intersect(m, dst.pos());
    tbv_ref t(m);
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        t = m.allocate(src.neg()[i]);
        if (m.set_and(*t, dst.pos())) {
            dst.neg().insert(m, t.detach());
        }
    }
    return fold_neg(dst);
}
bool doc_manager::set_and(doc& dst, tbv const& src)  {
    // (A \ B) & C  = (A & C) \ (B & C)
    if (!m.set_and(dst.pos(), src)) return false;
    dst.neg().intersect(m, src);
    return fold_neg(dst);
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
        if (m.contains(dst.neg()[i], dst.pos()))
            return false;

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
                m.set(dst.pos(), index, neg(dst.neg()[i][index]));
                dst.neg().intersect(tbvm(), dst.pos());
                goto start_over;
            }
        }
    }
    SASSERT(well_formed(dst));
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
    m.set(d.pos(), idx, value);
    for (unsigned i = 0; i < d.neg().size(); ++i) {
        tbit b = d.neg()[i][idx];
        if (b != BIT_x && value != BIT_x && value != b) {
            d.neg().erase(tbvm(), i);
            --i;
        }
        else {
            m.set(d.neg()[i], idx, value);
        }
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
        if (!merge(d, idx, equalities, discard_cols)) return false;
    }
    return true;
}
bool doc_manager::merge(doc& d, unsigned idx, subset_ints const& equalities, 
                        bit_vector const& discard_cols) {
    unsigned root = equalities.find(idx);
    idx = root;
    unsigned num_x = 0;
    unsigned root1 = root;
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
            ++num_x;
            if (!discard_cols.get(idx)) {
                root1 = idx;
            }
            break;
        default:
            UNREACHABLE();
            break;
        }
        idx = equalities.next(idx);
    }
    while (idx != root);

    TRACE("doc", tout << "num_x: " << num_x << " value: " << value << "\n";);
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
        bool all_x = true;
        if (!d.neg().is_empty()) {
            idx = root;
            do {
                for (unsigned i = 0; all_x && i < d.neg().size(); ++i) {
                    all_x = (BIT_x == d.neg()[i][idx]);
                }
                idx = equalities.next(idx);
            }
            while (idx != root && all_x);
        }
        idx = root;
        do {
            if ((!discard_cols.get(idx) || !all_x) &&  idx != root1) {
                tbv* t = m.allocate(d.pos());
                m.set(*t, idx, BIT_0);
                m.set(*t, root1, BIT_1);
                d.neg().insert(tbvm(), t);
                t = m.allocate(d.pos());
                m.set(*t, idx, BIT_1);
                m.set(*t, root1, BIT_0);
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

doc* doc_manager::project(doc_manager& dstm, bit_vector const& to_delete, doc const& src) {
    tbv_manager& dstt = dstm.m;    
    tbv_ref t(dstt);
    t = dstt.project(to_delete, src.pos());
    doc* r = dstm.allocate(t.detach());
    SASSERT(r);

    if (src.neg().is_empty()) {
        return r;
    }

    // 
    // A negation can be projected directly if it does not constrain
    // deleted variables.
    // 
    tbv_vector todo, new_todo;
    for (unsigned i = 0; i < src.neg().size(); ++i) {        
        todo.push_back(tbvm().allocate(src.neg()[i]));
    }
    unsigned idx;
    bool done = false;
    while (!todo.empty() && !done) {
        switch(pick_resolvent(src.pos(), todo, to_delete, idx)) {
        case project_is_empty: 
            t = dstt.allocate(r->pos());
            r->neg().push_back(t.detach());
            done = true;
            break;
        case project_monolithic:
            done = true;
            break;
        case project_neg:
        case project_pos:
            for (unsigned i = 0; i < todo.size(); ++i) {
                tbv& tx = *todo[i];
                if (tx[idx] == BIT_x) {
                    new_todo.push_back(&tx);
                }
                else {
                    m.deallocate(&tx);
                }
            }
            std::swap(new_todo, todo);
            new_todo.reset();
            break;        
        case project_resolve: {
            utbv pos, neg;
            for (unsigned i = 0; i < todo.size(); ++i) {
                tbv& tx = *todo[i];
                switch(tx[idx]) {
                case BIT_x: new_todo.push_back(&tx); break;
                case BIT_0: neg.push_back(&tx); break;
                case BIT_1: pos.push_back(&tx); break;
                default: UNREACHABLE(); break;                    
                }
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
            SASSERT(pos.size() > 0 && neg.size() > 0);
            tbv_ref t1(m);
            for (unsigned j = 0; j < pos.size(); ++j) {
                for (unsigned k = 0; k < neg.size(); ++k) {
                    t1 = m.allocate(pos[j]);
                    m.set(*t1, idx, BIT_x);
                    if (tbvm().set_and(*t1, neg[k])) {
                        m.set(*t1, idx, BIT_x);
                        new_todo.push_back(t1.detach());
                    }
                }       
            }         
            pos.reset(m);
            neg.reset(m);
            std::swap(todo, new_todo);
            new_todo.reset();
            break;
        }
        case project_done: {
            for (unsigned i = 0; i < todo.size(); ++i) {
                t = dstt.project(to_delete, *todo[i]);
                if (dstt.equals(r->pos(), *t)) {
                    r->neg().reset(dstt);
                    r->neg().push_back(t.detach());
                    break;
                }
                if (r->neg().size() > 0 && dstt.equals(r->neg()[0], *t)) {
                    continue;
                }
                r->neg().push_back(t.detach());
            }
            done = true;
            break;
        }
        }
    }
    for (unsigned i = 0; i < todo.size(); ++i) {
        m.deallocate(todo[i]);
    }
    return r;
}

doc* doc_manager::join(const doc& d1, const doc& d2, doc_manager& dm1,
                       const unsigned_vector& cols1,
                       const unsigned_vector& cols2) {
    doc_ref d(*this, allocateX());
    tbv_ref t(m);
    tbv& pos = d->pos();
    utbv& neg = d->neg();
    unsigned mid = dm1.num_tbits();
    unsigned hi = num_tbits();
    m.set(pos, d1.pos(), mid - 1, 0);
    m.set(pos, d2.pos(), hi - 1, mid);
    SASSERT(well_formed(*d));

    // first fix bits
    for (unsigned i = 0; i < cols1.size(); ++i) {
        unsigned idx1 = cols1[i];
        unsigned idx2 = mid + cols2[i];
        tbit v1 = pos[idx1];
        tbit v2 = pos[idx2];

        if (v1 == BIT_x) {
            if (v2 != BIT_x)
                m.set(pos, idx1, v2);
        }
        else if (v2 == BIT_x) {
            m.set(pos, idx2, v1);
        }
        else if (v1 != v2) {
            // columns don't match
            return nullptr;
        }
        SASSERT(well_formed(*d));
    }

    // fix equality of don't care columns
    for (unsigned i = 0; i < cols1.size(); ++i) {
        unsigned idx1 = cols1[i];
        unsigned idx2 = mid + cols2[i];
        unsigned v1 = pos[idx1];
        unsigned v2 = pos[idx2];

        if (v1 == BIT_x && v2 == BIT_x) {
            // add to subtracted TBVs: 1xx0 and 0xx1
            t = m.allocate(pos);
            m.set(*t, idx1, BIT_0);
            m.set(*t, idx2, BIT_1);
            neg.push_back(t.detach());
            t = m.allocate(pos);
            m.set(*t, idx1, BIT_1);
            m.set(*t, idx2, BIT_0);
            neg.push_back(t.detach());
        }
        SASSERT(well_formed(*d));
    }

    // handle subtracted TBVs:  1010 -> 1010xxx
    for (unsigned i = 0; i < d1.neg().size(); ++i) {
        t = m.allocateX();
        m.set(*t, d1.neg()[i], mid - 1, 0);
        if (m.set_and(*t, pos))
            neg.push_back(t.detach());
        SASSERT(well_formed(*d));
    }
    for (unsigned i = 0; i < d2.neg().size(); ++i) {
        t = m.allocateX();
        m.set(*t, d2.neg()[i], hi - 1, mid);
        if (m.set_and(*t, pos))
            neg.push_back(t.detach());
        SASSERT(well_formed(*d));
    }
    SASSERT(well_formed(*d));

    return d.detach();
}

doc_manager::project_action_t 
doc_manager::pick_resolvent(
    tbv const& pos, tbv_vector const& neg, bit_vector const& to_delete, unsigned& idx) {
    if (neg.empty()) return project_done;
    for (unsigned j = 0; j < neg.size(); ++j) {
        if (m.equals(pos, *neg[j])) return project_is_empty;   
    } 

    unsigned best_pos = UINT_MAX;
    unsigned best_neg = UINT_MAX;
    unsigned best_idx = UINT_MAX;
    for (unsigned i = 0; i < num_tbits(); ++i) {
        if (!to_delete.get(i)) continue;
        if (pos[i] != BIT_x) continue;
        unsigned num_pos = 0, num_neg = 0;
        tbit b1 = (*neg[0])[i];
        if (b1 == BIT_0) num_neg++; 
        if (b1 == BIT_1) num_pos++;
        bool monolithic = true;
        for (unsigned j = 1; j < neg.size(); ++j) {
            tbit b2 = (*neg[j])[i];
            if (b1 != b2) {
                monolithic = false;
            }
            if (b2 == BIT_0) num_neg++; 
            if (b2 == BIT_1) num_pos++;
        }
        if (monolithic && b1 != BIT_x) {
            idx = i;
            return project_monolithic;
        }
        if (monolithic && b1 == BIT_x) {
            continue;
        }
        SASSERT(!monolithic);
        if (num_pos == 0) {
            SASSERT(num_neg > 0);
            idx = i;
            return project_neg;
        }
        if (num_neg == 0) {
            SASSERT(num_pos > 0);
            idx = i;
            return project_pos;
        }
        if ((best_pos >= num_pos && best_neg >= num_neg) ||
            num_neg == 1 || num_pos == 1) {
            best_pos = num_pos;
            best_neg = num_neg;
            best_idx = i;
        }
    }
    if (best_idx != UINT_MAX) {
        idx = best_idx;
        return project_resolve;
    }
    else {
        return project_done;
    }
}



void doc_manager::complement(doc const& src, doc_vector& result) {
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
// (A \ {A1}) \ (B \ {B1})
// (A & !A1 & & !B) |  (A & B1 & !A1)
// A \ {A1 u B} u (A & B1) \ {A1}
void doc_manager::subtract(doc const& A, doc const& B, doc_vector& result) {
    doc_ref r(*this);
    tbv_ref t(m);
    r = allocate(A);
    t = m.allocate(B.pos());
    if (m.set_and(*t, A.pos())) {
        r->neg().insert(m, t.detach());
    }
    if (fold_neg(*r))
        result.push_back(r.detach());

    for (unsigned i = 0; i < B.neg().size(); ++i) {
        r = allocate(A);
        if (set_and(*r, B.neg()[i])) {
            result.push_back(r.detach());
        }
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
bool doc_manager::is_empty_complete(ast_manager& m, doc const& src)  {
    if (src.neg().size() == 0) return false;

    smt_params fp;
    smt::kernel s(m, fp);
    expr_ref fml = to_formula(m, src);
    s.assert_expr(fml);
    lbool res = s.check();
    if (res == l_true) {
        return false;
    }
    SASSERT(res == l_false);
    return true;
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
            found = m.contains(b.neg()[j],a.neg()[i]);
        }
        if (!found) return false;
    }
    return true;
}

bool doc_manager::contains(doc const& a, unsigned_vector const& colsa,
                           doc const& b, unsigned_vector const& colsb) const {
    if (!m.contains(a.pos(), colsa, b.pos(), colsb))
        return false;

    for (unsigned i = 0; i < a.neg().size(); ++i) {
        bool found = false;
        for (unsigned j = 0; !found && j < b.neg().size(); ++j) {
            found = m.contains(b.neg()[j], colsb, a.neg()[i], colsa);
        }
        if (!found) return false;
    }
    return true;
}

std::ostream& doc_manager::display(std::ostream& out, doc const& b) const {
    if (num_tbits() == 0) return out << "[]";
    return display(out, b, num_tbits()-1, 0);
}

std::ostream& doc_manager::display(std::ostream& out, doc const& b, unsigned hi, unsigned lo) const {
    m.display(out, b.pos(), hi, lo);
    if (b.neg().is_empty()) return out;
    out << " \\ ";
    b.neg().display(m, out, hi, lo);
    return out;
}


void doc_manager::verify_project(ast_manager& m, doc_manager& dstm, bit_vector const& to_delete, doc const& src, doc const& dst) {
    expr_ref fml1 = to_formula(m, src);
    expr_ref fml2 = dstm.to_formula(m, dst);
    project_rename(fml2, to_delete);
    project_expand(fml1, to_delete);   
    check_equiv(m, fml1, fml2);
}

void doc_manager::check_equiv(ast_manager& m, expr* fml1, expr* fml2) {
    smt_params fp;
    smt::kernel solver(m, fp);
    expr_ref fml(m);
    fml = m.mk_not(m.mk_eq(fml1, fml2));
    solver.assert_expr(fml);
    lbool res = solver.check();
    if (res != l_false) {        
        TRACE("doc",
              tout << mk_pp(fml1, m) << "\n";
              tout << mk_pp(fml2, m) << "\n";
              );
        UNREACHABLE();
        throw 0;
    }
    SASSERT(res == l_false);
}

expr_ref doc_manager::to_formula(ast_manager& m, doc const& src) {
    expr_ref result(m);
    expr_ref_vector conj(m);
    conj.push_back(tbvm().to_formula(m, src.pos()));
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        conj.push_back(m.mk_not(tbvm().to_formula(m, src.neg()[i])));
    }
    result = mk_and(m, conj.size(), conj.c_ptr());
    return result;
}
    
void doc_manager::project_expand(expr_ref& fml, bit_vector const& to_delete) {
    ast_manager& m = fml.get_manager();
    expr_ref tmp1(m), tmp2(m);
    for (unsigned i = 0; i < num_tbits(); ++i) {
        if (to_delete.get(i)) {
            expr_safe_replace rep1(m), rep2(m);
            rep1.insert(tbvm().mk_var(m, i), m.mk_true());
            rep1(fml, tmp1);
            rep2.insert(tbvm().mk_var(m, i), m.mk_false());
            rep2(fml, tmp2);
            if (tmp1 == tmp2) {
                fml = tmp1;
            }
            else {
                fml = m.mk_or(tmp1, tmp2);
            }
        }
    }
}

void doc_manager::project_rename(expr_ref& fml, bit_vector const& to_delete) {
    ast_manager& m = fml.get_manager();
    expr_safe_replace rep(m);
    for (unsigned i = 0, j = 0; i < num_tbits(); ++i) {
        if (!to_delete.get(i)) {
            rep.insert(tbvm().mk_var(m, j), tbvm().mk_var(m, i));
            ++j;
        }
    }
    rep(fml);
}
