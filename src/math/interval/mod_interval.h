/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    mod_interval.h

Abstract:

    Modular interval for bit-vector comparisons

Author:

    Nikolaj and Nuno 

--*/

#pragma once

namespace bv {

    template<typename T, typename Base>
    struct interval_tpl : public Base {
        T l, h;
        unsigned sz = 0;
        bool tight = true;
        
        interval_tpl(T const& l, T const& h, unsigned sz, bool tight = false): l(l), h(h), sz(sz), tight(tight) {}
        interval_tpl() = default;

        bool invariant() const {
            return 
                0 <= l && (l <= Base::bound(sz)) &&
                0 <= h && (h <= Base::bound(sz)) &&
                (!is_wrapped() || l != h + 1);
        }

        bool is_full() const { 
            return l == 0 && h == Base::bound(sz); 
        }
        bool is_wrapped() const { return l > h; }
        bool is_singleton() const { return l == h; }

        bool operator==(const interval_tpl<T, Base>& b) const {
            SASSERT(sz == b.sz);
            return l == b.l && h == b.h && tight == b.tight;
        }
        bool operator!=(const interval_tpl& b) const { return !(*this == b); }

        bool implies(const interval_tpl<T, Base>& b) const {
            if (b.is_full())
                return true;
            else if (is_full())
                return false;
            else if (is_wrapped()) 
                // l >= b.l >= b.h >= h
                return b.is_wrapped() && h <= b.h && l >= b.l;            
            else if (b.is_wrapped()) 
                // b.l > b.h >= h >= l
                // h >= l >= b.l > b.h
                return h <= b.h || l >= b.l;            
            else 
                return l >= b.l && h <= b.h;            
        }

        /// return false if intersection is unsat
        bool intersect(const interval_tpl<T, Base>& b, interval_tpl& result) const {
            if (is_full() || *this == b) {
                result = b;
                return true;
            }
            if (b.is_full()) {
                result = *this;
                return true;
            }

            if (is_wrapped()) {
                if (b.is_wrapped()) {
                    if (h >= b.l)
                        result = b;
                    else if (b.h >= l)
                        result = *this;
                    else
                        result = interval_tpl(std::max(l, b.l), std::min(h, b.h), sz);
                }
                else 
                    return b.intersect(*this, result);                
            } 
            else if (b.is_wrapped()) {
                // ... b.h ... l ... h ... b.l ..
                if (h < b.l && l > b.h)
                    return false;                
                // ... l ... b.l ... h ...
                if (h >= b.l && l <= b.h)
                    result = b;
                else if (h >= b.l) 
                    result = interval_tpl(b.l, h, sz);
                else {
                    // ... l .. b.h .. h .. b.l ...
                    SASSERT(l <= b.h);
                    result = interval_tpl(l, std::min(h, b.h), sz);
                }
            } else {
                if (l > b.h || h < b.l)
                    return false;

                // 0 .. l.. l' ... h ... h'
                result = interval_tpl(std::max(l, b.l), std::min(h, b.h), sz, tight && b.tight);
            }
            return true;
        }

        /// return false if negation is empty
        bool negate(interval_tpl<T, Base>& result) const {
            if (!tight) 
                result = interval_tpl(Base::zero(), Base::bound(sz), sz, true);
            else if (is_full())
                return false;
            else if (l == 0 && Base::bound(sz) == h) 
                result = interval_tpl(Base::zero(), Base::bound(sz), sz);
            else if (l == 0)
                result = interval_tpl(h + 1, Base::bound(sz), sz);
            else if (Base::bound(sz) == h) 
                result = interval_tpl(Base::zero(), l - 1, sz);
            else
                result = interval_tpl(h + 1, l - 1, sz);            
            return true;
        }


    };

    struct rinterval_base {
        static rational bound(unsigned sz) {
            return rational::power_of_two(sz) - 1;
        }

        static rational zero() { return rational::zero(); }
    };

    struct rinterval : public interval_tpl<rational, rinterval_base> {
        rinterval(rational const& l, rational const& h, unsigned sz, bool tight = false) {
            this->l = l; this->h = h; this->sz = sz; this->tight = tight;
        }
        rinterval() { l = 0; h = 0; tight = true; }
    };

    struct iinterval_base {
        static uint64_t uMaxInt(unsigned sz) {
            SASSERT(sz <= 64);
            return ULLONG_MAX >> (64u - sz);
        }

        static uint64_t bound(unsigned sz) { return uMaxInt(sz); }
        static uint64_t zero() { return 0; }
    };

    struct iinterval : public interval_tpl<uint64_t, iinterval_base> {
        iinterval(uint64_t l, uint64_t h, unsigned sz, bool tight = false) {
            this->l = l; this->h = h; this->sz = sz; this->tight = tight;
        }
        iinterval() { l = 0; h = 0; sz = 0; tight = true; }
    };

    struct interval {
        bool is_small = true;
        iinterval i;
        rinterval r;
        
        interval() = default;
           
        interval(rational const& l, rational const& h, unsigned sz, bool tight = false) {
            if (sz <= 64) {
                is_small = true;
                i.l = l.get_uint64();
                i.h = h.get_uint64();
                i.tight = tight;
                i.sz = sz;
            }
            else {
                is_small = false;
                r.l = l;
                r.h = h;
                r.tight = tight;
                r.sz = sz;
            }
        }
       
        unsigned size() const {
            return is_small ? i.sz : r.sz;
        }

        bool negate(interval& result) const {
            result.is_small = is_small;
            if (is_small)
                return i.negate(result.i);
            else
                return r.negate(result.r);
        }
        
        bool intersect(interval const& b, interval & result) const {
            result.is_small = is_small;
            SASSERT(b.is_small == is_small);
            if (is_small)
                return i.intersect(b.i, result.i);
            else
                return r.intersect(b.r, result.r);
        }
        
        bool operator==(interval const& other) const {
            SASSERT(is_small == other.is_small);
            return is_small ? i == other.i : r == other.r;
        }

        bool operator!=(interval const& other) const {
            return !(*this == other);
        }
        
        bool is_singleton() const { return is_small ? i.is_singleton() : r.is_singleton(); }

        bool is_full() const { return is_small ? i.is_full() : r.is_full(); }
        
        bool tight() const { return is_small ? i.tight : r.tight; }

        bool implies(const interval& b) const {
            SASSERT(is_small == b.is_small);
            return is_small ? i.implies(b.i) : r.implies(b.r);
        }

        rational lo() const { return is_small ? rational(i.l, rational::ui64()) : r.l; }
        rational hi() const { return is_small ? rational(i.h, rational::ui64()) : r.h; }
    };


    inline std::ostream& operator<<(std::ostream& o, const interval& I) {
        if (I.is_small)
            return o << "[" << I.i.l << ", " << I.i.h << "]";
        else
            return o << "[" << I.r.l << ", " << I.r.h << "]";
    }
}
