/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_datatype_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-11-04.

Revision History:

--*/
#ifndef THEORY_DATATYPE_PARAMS_H_
#define THEORY_DATATYPE_PARAMS_H_

struct theory_datatype_params {
    unsigned   m_dt_lazy_splits;

    theory_datatype_params():
        m_dt_lazy_splits(1) {
    }

#if 0
    void register_params(ini_params & p) {
        p.register_unsigned_param("dt_lazy_splits", m_dt_lazy_splits, "How lazy datatype splits are performed: 0- eager, 1- lazy for infinite types, 2- lazy");
    }
#endif

    void display(std::ostream & out) const { out << "m_dt_lazy_splits=" << m_dt_lazy_splits << std::endl; }
};


#endif /* THEORY_DATATYPE_PARAMS_H_ */

