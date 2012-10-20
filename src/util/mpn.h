/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mpn.h

Abstract:

    Multi Precision Natural Numbers

Author:

    Christoph Wintersteiger (cwinter) 2011-11-16.

Revision History:

--*/
#ifndef _MPN_H_
#define _MPN_H_

#include<ostream>
#include"util.h"
#include"buffer.h"

// we supply a definition of a basic max because mpz relies on it.
#define max(a,b)    (((a) > (b)) ? (a) : (b))

typedef unsigned int mpn_digit;

class mpn_manager {
public:
    mpn_manager();
    ~mpn_manager();

    int compare(mpn_digit const * a, size_t const lnga,
                mpn_digit const * b, size_t const lngb) const;

    bool add(mpn_digit const * a, size_t const lnga,
             mpn_digit const * b, size_t const lngb,
             mpn_digit *c, size_t const lngc_alloc,
             size_t * plngc) const;

    bool sub(mpn_digit const * a, size_t const lnga,
             mpn_digit const * b, size_t const lngb,
             mpn_digit * c, mpn_digit * pborrow) const;

    bool mul(mpn_digit const * a, size_t const lnga,
             mpn_digit const * b, size_t const lngb,
             mpn_digit * c) const;

    bool div(mpn_digit const * numer, size_t const lnum,
             mpn_digit const * denom, size_t const lden,
             mpn_digit * quot,
             mpn_digit * rem);

    char * to_string(mpn_digit const * a, size_t const lng,
                     char * buf, size_t const lbuf) const;

private:
    #ifdef _AMD64_
    class  mpn_sbuffer : public sbuffer<mpn_digit> {
    public:
        mpn_sbuffer() : sbuffer<mpn_digit>() {}

        mpn_sbuffer(size_t nsz, const mpn_digit & elem = 0) :
          sbuffer<mpn_digit>(static_cast<unsigned>(nsz), elem)
        {
        }
        void resize(size_t nsz, const mpn_digit & elem = 0) {
            sbuffer<mpn_digit>::resize(static_cast<unsigned>(nsz), elem);
        }

        mpn_digit & operator[](size_t idx) {
            return sbuffer<mpn_digit>::operator[](static_cast<unsigned>(idx));
        }

        const mpn_digit & operator[](size_t idx) const {
            return sbuffer<mpn_digit>::operator[](static_cast<unsigned>(idx));
        }
    };
    #else
    typedef sbuffer<mpn_digit> mpn_sbuffer;
    #endif

    static const mpn_digit zero;
    mpn_sbuffer u, v, t_ms, t_ab;
    void display_raw(std::ostream & out, mpn_digit const * a, size_t const lng) const;

    size_t div_normalize(mpn_digit const * numer, size_t const lnum,
                         mpn_digit const * denom, size_t const lden,
                         mpn_sbuffer & n_numer,
                         mpn_sbuffer & n_denom) const;

    void div_unnormalize(mpn_sbuffer & numer, mpn_sbuffer & denom,
                         size_t const d, mpn_digit * rem) const;

    bool div_1(mpn_sbuffer & numer, mpn_digit const denom,
               mpn_digit * quot) const;

    bool div_n(mpn_sbuffer & numer, mpn_sbuffer const & denom,
               mpn_digit * quot, mpn_digit * rem);

    #ifdef _DEBUG
    mutable char char_buf[4096];
    bool trace_enabled;
    #endif

    void trace(mpn_digit const * a, size_t const lnga, 
               mpn_digit const * b, size_t const lngb, 
               const char * op) const;

    void trace(mpn_digit const * a, size_t const lnga) const;
    void trace_nl(mpn_digit const * a, size_t const lnga) const;

public:
    // This function is needed because of the static_mpn_manager global variable.
    // It must be invoked by the memory_manager during finalization.
    // After we remove MSBignum from the code base, the global variable will
    // not be needed anymore, and we will be able to eliminate this function.
    void finalize() {
        u.finalize();
        v.finalize();
        t_ms.finalize();
        t_ab.finalize();
    }
};


// MSBignum compatible interface
// Note: The `owner' parameter is ignored. We use separate mpn_manager objects for the
// same purpose. Multiple owners are not supported in these compatibility functions, 
// instead a static mpn_manager is used.

extern mpn_manager static_mpn_manager;

typedef unsigned int digit_t;    

typedef struct {
    mpn_digit multiplier;
    size_t  shiftamt;
} reciprocal_1_t;

#define reciprocal_1_NULL ((reciprocal_1_t*)0)

inline int compare_diff(digit_t const * a, size_t const lnga,
                        digit_t const * b, size_t const lngb)
{
    return static_mpn_manager.compare(a, lnga, b, lngb);
}

inline char * mp_decimal(digit_t const * a, size_t const lng, // Number to be converted and its length
                         char * buf, size_t const lbuf, // output buffer and its length
                         int owner)
{
    return static_mpn_manager.to_string(a, lng, buf, lbuf);
}

inline bool add_full(digit_t const * a, size_t const lnga,
                     digit_t const * b, size_t const lngb,
                     digit_t *c, size_t const lngc_alloc, 
                     size_t * plngc,
                     int owner)
{
    return static_mpn_manager.add(a, lnga, b, lngb, c, lngc_alloc, plngc);
}

inline bool sub_diff(digit_t const * a, size_t const lnga,
                     digit_t const * b, size_t const lngb,
                     digit_t * c, digit_t * pborrow,
                     int owner)
{
    return static_mpn_manager.sub(a, lnga, b, lngb, c, pborrow);
}

inline bool multiply(digit_t const * a, size_t const lnga,
                     digit_t const * b, size_t const lngb,
                     digit_t * c, 
                     int owner)
{
    return static_mpn_manager.mul(a, lnga, b, lngb, c);
}

inline bool divide(digit_t const * numer, size_t const lnum,
                   digit_t const * denom, size_t const lden,
                   reciprocal_1_t const * supplied_reciprocal, /* reciprocal_t struct for this denominator,
                                                                   or reciprocal_1_NULL
                                                                   if not previously precomputed */
                   digit_t * quot, /* Quotient -- length MAX(lnum - lden + 1, 0) */
                   digit_t * rem, /* Remainder -- length lden  */
                   int owner)
{
    return static_mpn_manager.div(numer, lnum, denom, lden, quot, rem);
}

#endif
