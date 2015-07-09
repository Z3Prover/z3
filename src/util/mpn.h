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
#ifndef MPN_H_
#define MPN_H_

#include<ostream>
#include"util.h"
#include"buffer.h"
#include"z3_omp.h"

typedef unsigned int mpn_digit;

class mpn_manager {
#ifndef _NO_OMP_
    omp_nest_lock_t m_lock;
#endif
#define MPN_BEGIN_CRITICAL() omp_set_nest_lock(&m_lock);
#define MPN_END_CRITICAL() omp_unset_nest_lock(&m_lock);

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
               mpn_digit * quot, mpn_digit * rem,
               mpn_sbuffer & ms, mpn_sbuffer & ab) const;

    void trace(mpn_digit const * a, size_t const lnga, 
               mpn_digit const * b, size_t const lngb, 
               const char * op) const;

    void trace(mpn_digit const * a, size_t const lnga) const;
    void trace_nl(mpn_digit const * a, size_t const lnga) const;
};

#endif
