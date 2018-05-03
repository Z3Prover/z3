/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    ema.h

Abstract:

    Exponential moving average in the style of CaDiCal.

Author:

    Nikolaj Bjorner (nbjorner) 2018-05-03

Revision History:

--*/
#ifndef EMA_H_
#define EMA_H_

class ema {
    double m_alpha, m_beta, m_value;
    unsigned m_period, m_wait;

 public:
    ema() { memset(this, 0, sizeof(*this)); }

    ema(double alpha): 
        m_alpha(alpha), m_beta(1), m_value(0), 
        m_period(0), m_wait(0) {}

    double operator() const { return m_value; }

    void update(double x) {
        m_value += m_beta * (x - m_value);
        if (m_beta <= m_alpha || m_wait--) return;
        m_wait = m_period = 2*(m_period + 1) - 1;
        m_beta *= 0.5;
        if (m_beta < m_alpha) m_beta = m_alpha;        
    }
};

#endif
