/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    im_float_config.h

Abstract:

    Auxiliary class for testing intervals with software floats end points.

Author:

    Leonardo de Moura (leonardo) 2012-08-21.

Revision History:

--*/
#ifndef _IM_FLOAT_CONFIG_H_
#define _IM_FLOAT_CONFIG_H_

#include"f2n.h"
#include"mpf.h"
#include"hwf.h"

template<typename f_manager>
class im_float_config {
    f2n<f_manager>  m_manager;
public:
    typedef f2n<f_manager>              numeral_manager;
    typedef typename f_manager::numeral numeral;

    im_float_config(f_manager & m, unsigned ebits = 11, unsigned sbits = 53):m_manager(m, ebits, sbits) {}
    
    struct interval {
        numeral   m_lower;
        numeral   m_upper;
    };

    void round_to_minus_inf() { m_manager.round_to_minus_inf(); }
    void round_to_plus_inf() { m_manager.round_to_plus_inf(); }
    void set_rounding(bool up) { m_manager.set_rounding(up); }

    // Getters
    numeral const & lower(interval const & a) const { return a.m_lower; }
    numeral const & upper(interval const & a) const { return a.m_upper; }
    numeral & lower(interval & a) { return a.m_lower; }
    numeral & upper(interval & a) { return a.m_upper; }
    bool lower_is_inf(interval const & a) const { return m_manager.m().is_ninf(a.m_lower); }
    bool upper_is_inf(interval const & a) const { return m_manager.m().is_pinf(a.m_upper); }
    bool lower_is_open(interval const & a) const { return lower_is_inf(a); }
    bool upper_is_open(interval const & a) const { return upper_is_inf(a); }

    // Setters
    void set_lower(interval & a, numeral const & n) { m_manager.set(a.m_lower, n); }
    void set_upper(interval & a, numeral const & n) { m_manager.set(a.m_upper, n); }
    void set_lower_is_open(interval & a, bool v) {}
    void set_upper_is_open(interval & a, bool v) {}
    void set_lower_is_inf(interval & a, bool v) { if (v) m_manager.m().mk_ninf(m_manager.ebits(), m_manager.sbits(), a.m_lower); }
    void set_upper_is_inf(interval & a, bool v) { if (v) m_manager.m().mk_pinf(m_manager.ebits(), m_manager.sbits(), a.m_upper); }
    
    // Reference to numeral manager
    numeral_manager & m() const { return const_cast<numeral_manager&>(m_manager); }
};

template<typename fmanager>
inline void del_f_interval(im_float_config<fmanager> & cfg, typename im_float_config<fmanager>::interval & a) {
    cfg.m().del(a.m_lower);
    cfg.m().del(a.m_upper);
}

#endif
