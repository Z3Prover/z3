/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    tbv.h

Abstract:

    ternary bit-vector utilities.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:


--*/

#ifndef _TBV_H_
#define _TBV_H_

#include "fixed_bit_vector.h"
#include "rational.h"

class tbv;

class tbv_manager {
    friend class tbv;
    static const unsigned BIT_0 = 0x1;
    static const unsigned BIT_1 = 0x2;
    static const unsigned BIT_x = 0x3;
    static const unsigned BIT_z = 0x0;
    fixed_bit_vector_manager m;
public:
    tbv_manager(unsigned n): m(2*n) {}
    void reset();
    tbv* allocate();
    tbv* allocate1();
    tbv* allocate0();
    tbv* allocateX();
    tbv* allocate(tbv const& bv);
    tbv* allocate(uint64 n);
    tbv* allocate(rational const& r);
    tbv* allocate(uint64 n, unsigned hi, unsigned lo);

    void deallocate(tbv* bv);
        
    void copy(tbv& dst, tbv const& src) const;
    unsigned num_tbits() const { return m.num_bits()/2; }
    tbv& reset(tbv& bv) const { return fill0(bv); }
    tbv& fill0(tbv& bv) const;
    tbv& fill1(tbv& bv) const;
    tbv& fillX(tbv& bv) const;
    bool set_and(tbv& dst,  tbv const& src) const;
    tbv& set_or(tbv& dst,  tbv const& src) const;
    void complement(tbv const& src, ptr_vector<tbv>& result);
    bool equals(tbv const& a, tbv const& b) const;
    unsigned hash(tbv const& src) const;
    bool contains(tbv const& a, tbv const& b) const;
    bool intersect(tbv const& a, tbv const& b, tbv& result);
    std::ostream& display(std::ostream& out, tbv const& b) const;
};

class tbv: private fixed_bit_vector {
    friend class fixed_bit_vector_manager;
    friend class tbv_manager;

public:

    static const unsigned BIT_0 = tbv_manager::BIT_0;
    static const unsigned BIT_1 = tbv_manager::BIT_1;
    static const unsigned BIT_x = tbv_manager::BIT_x;
    static const unsigned BIT_z = tbv_manager::BIT_z;

    struct eq {
        tbv_manager& m;
        eq(tbv_manager& m):m(m) {}
        bool operator()(tbv const& d1, tbv const& d2) const {
            return m.equals(d1, d2);
        }
    };

    struct hash {
        tbv_manager& m;
        hash(tbv_manager& m):m(m) {}
        unsigned operator()(tbv const& d) const {
            return m.hash(d);
        }
    };
        
    void set(uint64 n, unsigned hi, unsigned lo);
    void set(rational const& r, unsigned hi, unsigned lo);
    void set(tbv const& other, unsigned hi, unsigned lo);

    unsigned operator[](unsigned idx) { return get(idx); }
    void set(unsigned index, unsigned value) {
        SASSERT(value <= 3);
        fixed_bit_vector::set(2*index,   (value & 2) != 0);
        fixed_bit_vector::set(2*index+1, (value & 1) != 0);
    }

private:

    unsigned get(unsigned index) const {
        index *= 2;
        return (fixed_bit_vector::get(index) << 1) | (unsigned)fixed_bit_vector::get(index+1);
    }
};


#endif /* _TBV_H_ */
