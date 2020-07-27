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
#pragma once

#include<ostream>
#include "util/util.h"
#include "util/buffer.h"

typedef unsigned int mpn_digit;

class mpn_manager {

public:
    mpn_manager();
    ~mpn_manager();

    int compare(mpn_digit const * a, size_t lnga,
                mpn_digit const * b, size_t lngb) const;

    bool add(mpn_digit const * a, size_t lnga,
             mpn_digit const * b, size_t lngb,
             mpn_digit *c, size_t lngc_alloc,
             size_t * plngc) const;

    bool sub(mpn_digit const * a, size_t lnga,
             mpn_digit const * b, size_t lngb,
             mpn_digit * c, mpn_digit * pborrow) const;

    bool mul(mpn_digit const * a, size_t lnga,
             mpn_digit const * b, size_t lngb,
             mpn_digit * c) const;

    bool div(mpn_digit const * numer, size_t lnum,
             mpn_digit const * denom, size_t lden,
             mpn_digit * quot,
             mpn_digit * rem);

    char * to_string(mpn_digit const * a, size_t lng,
                     char * buf, size_t lbuf) const;
private:
    #if defined(__LP64__) || defined(_WIN64)
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
    void display_raw(std::ostream & out, mpn_digit const * a, size_t lng) const;

    size_t div_normalize(mpn_digit const * numer, size_t lnum,
                         mpn_digit const * denom, size_t lden,
                         mpn_sbuffer & n_numer,
                         mpn_sbuffer & n_denom) const;

    void div_unnormalize(mpn_sbuffer & numer, mpn_sbuffer & denom,
                         size_t d, mpn_digit * rem) const;

    bool div_1(mpn_sbuffer & numer, mpn_digit denom,
               mpn_digit * quot) const;

    bool div_n(mpn_sbuffer & numer, mpn_sbuffer const & denom,
               mpn_digit * quot, mpn_digit * rem,
               mpn_sbuffer & ms, mpn_sbuffer & ab) const;

    void trace(mpn_digit const * a, size_t lnga,
               mpn_digit const * b, size_t lngb,
               const char * op) const;

    void trace(mpn_digit const * a, size_t lnga) const;
    void trace_nl(mpn_digit const * a, size_t lnga) const;
};

