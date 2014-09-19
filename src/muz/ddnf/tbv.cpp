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


tbv_manager::~tbv_manager() {    
#if 0
    ptr_vector<tbv>::iterator it = allocated_tbvs.begin(), end = allocated_tbvs.end();
    for (; it != end; ++it) {
        std::cout << "dangling: " << (*it) << "\n";
    }
#endif
}

void tbv_manager::reset() {
    m.reset();
}
tbv* tbv_manager::allocate() {
    tbv* r = reinterpret_cast<tbv*>(m.allocate());
    //std::cout << allocated_tbvs.size() << " " << r << "\n";
    //allocated_tbvs.insert(r);
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
            v->set(bit, BIT_1);
        } else {
            v->set(bit, BIT_0);
        }
    }
    return v;
}

tbv* tbv_manager::allocate(uint64 val, unsigned hi, unsigned lo) {
    tbv* v = allocateX();
    SASSERT(64 >= num_tbits() && num_tbits() > hi && hi >= lo);
    v->set(val, hi, lo);
    return v;
}
tbv* tbv_manager::allocate(tbv const& bv, unsigned const* permutation) {
    tbv* r = allocate();
    for (unsigned i = 0; i < num_tbits(); ++i) {
        r->set(permutation[i], bv[i]);
    }
    return r;
}
tbv* tbv_manager::project(unsigned n, bool const* to_delete, tbv const& src) {
    tbv* r = allocate();
    unsigned i, j;
    for (i = 0, j = 0; i < n; ++i) {
        if (!to_delete[i]) {
            r->set(j, src[i]);
            ++j;
        }
    }
    SASSERT(num_tbits() == j);
    return r;
}

void tbv::set(uint64 val, unsigned hi, unsigned lo) {
    for (unsigned i = 0; i < hi - lo + 1; ++i) {
        set(lo + i, (val & (1ULL << i))?BIT_1:BIT_0);
    }
}
void tbv::set(rational const& r, unsigned hi, unsigned lo) {
    if (r.is_uint64()) {
        set(r.get_uint64(), hi, lo);
        return;
    }
    for (unsigned i = 0; i < hi - lo + 1; ++i) {
        if (bitwise_and(r, rational::power_of_two(i)).is_zero())
            set(lo + i, BIT_0);
        else
            set(lo + i, BIT_1);
    }
}

void tbv::set(tbv const& other, unsigned hi, unsigned lo) {
    for (unsigned i = 0; i < hi - lo + 1; ++i) {
        set(lo + i, other[i]);
    }
}


tbv* tbv_manager::allocate(rational const& r) {
    if (r.is_uint64()) {
        return allocate(r.get_uint64());
    }
    tbv* v = allocate0();
    for (unsigned bit = num_tbits(); bit > 0; ) {
        --bit;
        if (bitwise_and(r, rational::power_of_two(bit)).is_zero()) {
            v->set(bit, BIT_0);
        } else {
            v->set(bit, BIT_1);
        }
    }            
    return v;
}
void tbv_manager::deallocate(tbv* bv) {
#if 0
    if (!allocated_tbvs.contains(bv)) {
        std::cout << "double deallocate: " << bv << "\n";
        UNREACHABLE();
    }
    allocated_tbvs.erase(bv);
#endif
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
    for (unsigned i = 0; i < num_tbits(); ++i) {
        if (dst[i] == BIT_z) return false;
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
            r->set(i, BIT_1);
            result.push_back(r);
            break;
        case BIT_1:
            r = allocate(src);
            r->set(i, BIT_0);
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
bool tbv_manager::intersect(tbv const& a, tbv const& b, tbv& result) {
    copy(result, a);
    return set_and(result, b);
}

std::ostream& tbv_manager::display(std::ostream& out, tbv const& b) const {
    for (unsigned i = 0; i < num_tbits(); ++i) {
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
