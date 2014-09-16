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

tbv* tbv_manager::allocate() {
    return reinterpret_cast<tbv*>(m.allocate());
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
    return reinterpret_cast<tbv*>(m.allocate(bv));
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
    m.deallocate(bv);
}    
void tbv_manager::copy(tbv& dst, tbv const& src) const {
    m.copy(dst, src);
}    
tbv& tbv_manager::fill0(tbv& bv) const { 
    // 01010101 = 1 + 4 + 16 + 64
    memset(bv.m_data, 1 + 4 + 16 + 64, m.num_bytes());
    return bv; 
}
tbv& tbv_manager::fill1(tbv& bv) const { 
    // 10101010 = 2 + 8 + 32 + 128
    memset(bv.m_data, 2 + 8 + 32 + 128, m.num_bytes());
    return bv; 
}
tbv& tbv_manager::fillX(tbv& bv) const { 
    m.fill1(bv); 
    return bv; 
}
tbv& tbv_manager::set_and(tbv& dst, tbv const& src) const {
    m.set_and(dst, src); 
    return dst;
}
tbv& tbv_manager::set_or(tbv& dst,  tbv const& src) const {
    m.set_or(dst, src); 
    return dst;
}
tbv& tbv_manager::set_neg(tbv& dst) const {
    m.set_neg(dst); 
    return dst;
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
    set_and(result, b);
    for (unsigned i = 0; i < num_tbits(); ++i) {
        if (result.get(i) == BIT_z) return false;
    }
    return true;
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
