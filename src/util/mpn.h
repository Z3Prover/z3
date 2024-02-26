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
    int compare(mpn_digit const * a, unsigned lnga,
                mpn_digit const * b, unsigned lngb) const;

    bool add(mpn_digit const * a, unsigned lnga,
             mpn_digit const * b, unsigned lngb,
             mpn_digit *c, unsigned lngc_alloc,
             unsigned * plngc) const;

    bool sub(mpn_digit const * a, unsigned lnga,
             mpn_digit const * b, unsigned lngb,
             mpn_digit * c, mpn_digit * pborrow) const;

    bool mul(mpn_digit const * a, unsigned lnga,
             mpn_digit const * b, unsigned lngb,
             mpn_digit * c) const;

    bool div(mpn_digit const * numer, unsigned lnum,
             mpn_digit const * denom, unsigned lden,
             mpn_digit * quot,
             mpn_digit * rem);

    char * to_string(mpn_digit const * a, unsigned lng,
                     char * buf, unsigned lbuf) const;
private:
    using mpn_sbuffer = sbuffer<mpn_digit>;

    void display_raw(std::ostream & out, mpn_digit const * a, unsigned lng) const;

    unsigned div_normalize(mpn_digit const * numer, unsigned lnum,
                         mpn_digit const * denom, unsigned lden,
                         mpn_sbuffer & n_numer,
                         mpn_sbuffer & n_denom) const;

    void div_unnormalize(mpn_sbuffer & numer, mpn_sbuffer & denom,
                         unsigned d, mpn_digit * rem) const;

    bool div_1(mpn_sbuffer & numer, mpn_digit denom,
               mpn_digit * quot) const;

    bool div_n(mpn_sbuffer & numer, mpn_sbuffer const & denom,
               mpn_digit * quot, mpn_digit * rem,
               mpn_sbuffer & ms, mpn_sbuffer & ab) const;

    void trace(mpn_digit const * a, unsigned lnga,
               mpn_digit const * b, unsigned lngb,
               const char * op) const;

    void trace(mpn_digit const * a, unsigned lnga) const;
    void trace_nl(mpn_digit const * a, unsigned lnga) const;
};
