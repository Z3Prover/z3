/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    tbv.cpp

Abstract:

    ternary bit-vector utilities.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:


--*/

#include "tbv.h"
#include "hashtable.h"
#include "ast_util.h"


static bool s_debug_alloc = false;

void tbv_manager::debug_alloc() {
    s_debug_alloc = true;
}

tbv_manager::~tbv_manager() {    
    DEBUG_CODE(
        ptr_vector<tbv>::iterator it = allocated_tbvs.begin();
        ptr_vector<tbv>::iterator end = allocated_tbvs.end();
        for (; it != end; ++it) {
            std::cout << "dangling: " << (*it) << "\n";
            TRACE("doc", tout << "dangling: " << (*it) << "\n";);
        });
}

void tbv_manager::reset() {
    m.reset();
}
tbv* tbv_manager::allocate() {
    tbv* r = reinterpret_cast<tbv*>(m.allocate());
    DEBUG_CODE(
        if (s_debug_alloc) {
            TRACE("doc", tout << allocated_tbvs.size() << " " << r << "\n";);
        }
        allocated_tbvs.insert(r);
        );
    return r;
}
tbv* tbv_manager::allocate1() {
    tbv* v = allocate();
    fill1(*v);
    return v;
}
tbv* tbv_manager::allocate0() {
    tbv* v = allocate();
    fill0(*v);
    return v;
}
tbv* tbv_manager::allocateX() {
    tbv* v = allocate();
    fillX(*v);
    return v;
}
tbv* tbv_manager::allocate(tbv const& bv) {
    tbv* r = allocate();
    copy(*r, bv);
    return r;
}
tbv* tbv_manager::allocate(uint64 val) {
    tbv* v = allocate0();
    for (unsigned bit = num_tbits(); bit > 0;) {
        --bit;
        if (val & (1ULL << bit)) {                        
            set(*v, bit, BIT_1);
        } else {
            set(*v, bit, BIT_0);
        }
    }
    return v;
}

tbv* tbv_manager::allocate(uint64 val, unsigned hi, unsigned lo) {
    tbv* v = allocateX();
    SASSERT(64 >= num_tbits() && num_tbits() > hi && hi >= lo);
    set(*v, val, hi, lo);
    return v;
}
tbv* tbv_manager::allocate(tbv const& bv, unsigned const* permutation) {
    tbv* r = allocate();
    unsigned sz = num_tbits();
    for (unsigned i = 0; i < sz; ++i) {
        set(*r, permutation[i], bv[i]);
    }
    return r;
}
tbv* tbv_manager::project(bit_vector const& to_delete, tbv const& src) {
    tbv* r = allocate();
    unsigned i, j;
    unsigned n = to_delete.size();
    for (i = 0, j = 0; i < n; ++i) {
        if (!to_delete.get(i)) {
            set(*r, j, src[i]);
            ++j;
        }
    }
    SASSERT(num_tbits() == j);
    return r;
}

void tbv_manager::set(tbv& dst, unsigned index, tbit value) {
    SASSERT(index < num_tbits());
    m.set(dst, 2*index,   (value & 2) != 0);
    m.set(dst, 2*index+1, (value & 1) != 0);    
}


void tbv_manager::set(tbv& dst, uint64 val, unsigned hi, unsigned lo) {
    SASSERT(lo <= hi && hi < num_tbits());
    for (unsigned i = 0; i < hi - lo + 1; ++i) {
        set(dst, lo + i, (val & (1ULL << i))?BIT_1:BIT_0);
    }
}
void tbv_manager::set(tbv& dst, rational const& r, unsigned hi, unsigned lo) {
    SASSERT(lo <= hi && hi < num_tbits());
    if (r.is_uint64()) {
        set(dst, r.get_uint64(), hi, lo);
        return;
    }
    for (unsigned i = 0; i < hi - lo + 1; ++i) {
        if (bitwise_and(r, rational::power_of_two(i)).is_zero())
            set(dst, lo + i, BIT_0);
        else
            set(dst, lo + i, BIT_1);
    }
}

void tbv_manager::set(tbv& dst, tbv const& other, unsigned hi, unsigned lo) {
    dst.set(other, 2*hi+1, 2*lo);
}


tbv* tbv_manager::allocate(rational const& r) {
    if (r.is_uint64()) {
        return allocate(r.get_uint64());
    }
    tbv* v = allocate0();
    for (unsigned bit = num_tbits(); bit > 0; ) {
        --bit;
        if (bitwise_and(r, rational::power_of_two(bit)).is_zero()) {
            set(*v, bit, BIT_0);
        } else {
            set(*v, bit, BIT_1);
        }
    }            
    return v;
}
void tbv_manager::deallocate(tbv* bv) {
    DEBUG_CODE(
        if (!allocated_tbvs.contains(bv)) {
            std::cout << "double deallocate: " << bv << "\n";
            UNREACHABLE();
        }
        if (s_debug_alloc) {
            TRACE("doc", tout << "deallocate: " << bv << "\n";);
        }
        allocated_tbvs.erase(bv););
    m.deallocate(bv);
}    
void tbv_manager::copy(tbv& dst, tbv const& src) const {
    m.copy(dst, src);
}    
tbv& tbv_manager::fill0(tbv& bv) const { 
    // 10101010 = 2 + 8 + 32 + 128
    memset(bv.m_data, 2 + 8 + 32 + 128, m.num_bytes());
    return bv; 
}
tbv& tbv_manager::fill1(tbv& bv) const {  
    // 01010101 = 1 + 4 + 16 + 64
    memset(bv.m_data, 1 + 4 + 16 + 64, m.num_bytes());
    return bv; 
}
tbv& tbv_manager::fillX(tbv& bv) const { 
    m.fill1(bv); 
    return bv; 
}

tbv& tbv_manager::set_or(tbv& dst,  tbv const& src) const {
    m.set_or(dst, src); 
    return dst;
}
bool tbv_manager::set_and(tbv& dst,  tbv const& src) const {
    m.set_and(dst, src); 
    return is_well_formed(dst);
}

bool tbv_manager::is_well_formed(tbv const& dst) const {
    unsigned nw = m.num_words();
    unsigned w;
    for (unsigned i = 0; i + 1 < nw; ++i) {
        w = dst.get_word(i);
        w = w | (w << 1) | 0x55555555;
        if (w != 0xFFFFFFFF) return false;
    }
    if (nw > 0) {        
        w = m.last_word(dst);
        w = w | (w << 1) | 0x55555555 | ~m.get_mask();
        if (w != 0xFFFFFFFF) return false;
    }
    return true;
}

void tbv_manager::complement(tbv const& src, ptr_vector<tbv>& result) {
    tbv* r;
    unsigned n = num_tbits();
    for (unsigned i = 0; i < n; ++i) {
        switch (src.get(i)) {
        case BIT_0:
            r = allocate(src);
            set(*r, i, BIT_1);
            result.push_back(r);
            break;
        case BIT_1:
            r = allocate(src);
            set(*r, i, BIT_0);
            result.push_back(r);
            break;
        default:
            break;
        }
    }
}

bool tbv_manager::equals(tbv const& a, tbv const& b) const {
    return m.equals(a, b);
}
unsigned tbv_manager::hash(tbv const& src) const {
    return m.hash(src);
}
bool tbv_manager::contains(tbv const& a, tbv const& b) const {
    return m.contains(a, b);
}

bool tbv_manager::contains(tbv const& a, unsigned_vector const& colsa,
                           tbv const& b, unsigned_vector const& colsb) const {
    for (unsigned i = 0; i < colsa.size(); ++i) {
        tbit bit_a = a[colsa[i]];
        if (bit_a == BIT_x) continue;
        if (bit_a != b[colsb[i]]) return false;
    }
    return true;
}

bool tbv_manager::intersect(tbv const& a, tbv const& b, tbv& result) {
    copy(result, a);
    return set_and(result, b);
}

std::ostream& tbv_manager::display(std::ostream& out, tbv const& b, unsigned hi, unsigned lo) const {
    SASSERT(lo <= hi && hi < num_tbits());
    for (unsigned i = hi+1; i-- > lo; ) {
        switch (b.get(i)) {
        case BIT_0:
            out << '0';
            break;
        case BIT_1:
            out << '1';
            break;
        case BIT_x:
            out << 'x';
            break;
        case BIT_z:
            out << 'z';
            break;
        default:
            UNREACHABLE();
        }
    }
    return out;
}

std::ostream& tbv_manager::display(std::ostream& out, tbv const& b) const {
    if (num_tbits() == 0) return out << "[]";
    return display(out, b, num_tbits()-1, 0);
}

expr_ref tbv_manager::to_formula(ast_manager& m, tbv const& src) {
    expr_ref result(m);
    expr_ref_vector conj(m);
    for (unsigned i = 0; i < num_tbits(); ++i) {
        switch (src[i]) {
        case BIT_0:
            conj.push_back(m.mk_not(m.mk_const(symbol(i), m.mk_bool_sort())));
            break;
        case BIT_1:
            conj.push_back(m.mk_const(symbol(i), m.mk_bool_sort()));
            break;
        default:
            break;
        }
    }
    result = mk_and(m, conj.size(), conj.c_ptr());
    return result;
}

expr_ref tbv_manager::mk_var(ast_manager& m, unsigned i) {
    return expr_ref(m.mk_const(symbol(i), m.mk_bool_sort()), m);
}
