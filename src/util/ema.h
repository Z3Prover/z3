/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    ema.h

Abstract:

    Exponential moving average based on CaDiCal.
    The exponential scheme used to adjust beta to alpha is 
    described in Biere & Froelich, POS (Pragmatics of SAT) 2016.

Author:

    Nikolaj Bjorner (nbjorner) 2018-05-03

Revision History:

--*/
#ifndef EMA_H_
#define EMA_H_

class ema {
    double m_alpha, m_beta, m_value;
    unsigned m_period, m_wait;
    bool invariant() const { return 0 <= m_alpha && m_alpha <= m_beta && m_beta <= 1; }
 public:
    ema(): m_alpha(0), m_beta(1), m_value(0), m_period(0), m_wait(0) {
        SASSERT(invariant());
    }

    ema(double alpha): 
        m_alpha(alpha), m_beta(1), m_value(0), 
        m_period(0), m_wait(0) {
        SASSERT(invariant());
    }

    void set_alpha(double alpha) { 
        m_alpha = alpha; 
        SASSERT(invariant());
    }

    operator double () const { return m_value; }

    void update(double x) {
        SASSERT(invariant());
        m_value += m_beta * (x - m_value);
        if (m_beta <= m_alpha || m_wait--) return;
        m_wait = m_period = 2*(m_period + 1) - 1;
        m_beta *= 0.5;
        if (m_beta < m_alpha) m_beta = m_alpha;        
    }

    void set(double x) {
        m_value = x;
    }
};

#endif
