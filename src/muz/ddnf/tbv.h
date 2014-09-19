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

enum tbit {
    BIT_z = 0x0,
    BIT_0 = 0x1,
    BIT_1 = 0x2,
    BIT_x = 0x3
};

inline tbit neg(tbit t) {
    return (tbit)(t ^ 0x3);
}

class tbv_manager {
    friend class tbv;
    fixed_bit_vector_manager m;
    //    ptr_vector<tbv> allocated_tbvs;
public:
    tbv_manager(unsigned n): m(2*n) {}
    ~tbv_manager();
    void reset();
    tbv* allocate();
    tbv* allocate1();
    tbv* allocate0();
    tbv* allocateX();
    tbv* allocate(tbv const& bv);
    tbv* allocate(uint64 n);
    tbv* allocate(rational const& r);
    tbv* allocate(uint64 n, unsigned hi, unsigned lo);
    tbv* allocate(tbv const& bv, unsigned const* permutation);

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
    tbv* project(unsigned n, bool const* to_delete, tbv const& src);
    bool is_well_formed(tbv const& b) const; // - does not contain BIT_z;
};

class tbv: private fixed_bit_vector {
    friend class fixed_bit_vector_manager;
    friend class tbv_manager;

public:

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

    tbit operator[](unsigned idx) const { return (tbit)get(idx); }
    void set(unsigned index, tbit value) {
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

class tbv_ref {
    tbv_manager& mgr;
    tbv* d;
public:
    tbv_ref(tbv_manager& mgr):mgr(mgr),d(0) {}
    tbv_ref(tbv_manager& mgr, tbv* d):mgr(mgr),d(d) {}
    ~tbv_ref() {
        if (d) mgr.deallocate(d);
    }
    tbv_ref& operator=(tbv* d2) {
        if (d) mgr.deallocate(d);
        d = d2;
        return *this;
    }
    tbv& operator*() { return *d; }
    tbv* get() { return d; }
    tbv* detach() { tbv* result = d; d = 0; return result; }
};


#endif /* _TBV_H_ */
