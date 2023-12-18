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

#pragma once

#include "util/fixed_bit_vector.h"
#include "util/bit_vector.h"
#include "util/rational.h"

class tbv;

enum tbit {
    BIT_z = 0x0, // unknown
    BIT_0 = 0x1, // for sure 0
    BIT_1 = 0x2, // for sure 1
    BIT_x = 0x3  // don't care
};

inline tbit neg(tbit t) {
    return (tbit)(t ^ 0x3);
}

class tbv_manager {
    friend class tbv;
    fixed_bit_vector_manager m;
    ptr_vector<tbv> allocated_tbvs;
public:
    tbv_manager(unsigned n): m(2*n) {}
    tbv_manager(tbv_manager const& m) = delete;
    ~tbv_manager();
    void reset();
    tbv* allocate();
    tbv* allocate1();
    tbv* allocate0();
    tbv* allocateX();
    tbv* allocate(tbv const& bv);
    tbv* allocate(uint64_t n);
    tbv* allocate(rational const& r);
    tbv* allocate(uint64_t n, unsigned hi, unsigned lo);
    tbv* allocate(tbv const& bv, unsigned const* permutation);
    tbv* allocate(char const* bv);

    void deallocate(tbv* bv);

    unsigned get_size_estimate_bytes(const tbv&) const { return m.num_bytes(); }
        
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
    bool contains(tbv const& a, unsigned_vector const& colsa,
                  tbv const& b, unsigned_vector const& colsb) const;
    bool intersect(tbv const& a, tbv const& b, tbv& result);
    std::ostream& display(std::ostream& out, tbv const& b) const;
    std::ostream& display(std::ostream& out, tbv const& b, unsigned hi, unsigned lo) const;
    tbv* project(bit_vector const& to_delete, tbv const& src);
    bool is_well_formed(tbv const& b) const; // - does not contain BIT_z;
    void set(tbv& dst, uint64_t n, unsigned hi, unsigned lo);
    void set(tbv& dst, rational const& r, unsigned hi, unsigned lo);
    void set(tbv& dst, tbv const& other, unsigned hi, unsigned lo);
    void set(tbv& dst, unsigned index, tbit value);

    static void debug_alloc();
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
        bool operator()(tbv const* d1, tbv const* d2) const {
            return m.equals(*d1, *d2);
        }
    };

    struct hash {
        tbv_manager& m;
        hash(tbv_manager& m):m(m) {}
        unsigned operator()(tbv const& d) const {
            return m.hash(d);
        }
        unsigned operator()(tbv const* d) const {
            return m.hash(*d);
        }
    };
        

    tbit operator[](unsigned idx) const { return (tbit)get(idx); }


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
    tbv_ref(tbv_manager& mgr) : mgr(mgr), d(nullptr) {}
    tbv_ref(tbv_manager& mgr, tbv* d) : mgr(mgr), d(d) {}
    tbv_ref(tbv_ref&& d) noexcept : mgr(d.mgr), d(d.detach()) {}
    ~tbv_ref() {
        if (d) mgr.deallocate(d);
    }
    tbv_ref& operator=(tbv* d2) {
        if (d) mgr.deallocate(d);
        d = d2;
        return *this;
    }
    tbv& operator*() { return *d; }
    tbv* operator->() { return d; }
    tbit operator[](unsigned idx) const { return (*d)[idx]; }
    tbv* get() const { return d; }
    tbv* detach() { tbv* result = d; d = nullptr; return result; }
    tbv_manager& manager() const { return mgr; }
    unsigned num_tbits() const { return mgr.num_tbits(); }
};

inline std::ostream& operator<<(std::ostream& out, tbv_ref const& c) {
    char const* names[] = { "z", "0", "1", "x" };
    for (unsigned i = c.num_tbits(); i-- > 0; ) {
        out << names[static_cast<unsigned>(c[i])];
    }
    return out;
}
