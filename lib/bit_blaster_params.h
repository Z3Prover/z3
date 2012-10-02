/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_blaster_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-02.

Revision History:

--*/
#ifndef _BIT_BLASTER_PARAMS_H_
#define _BIT_BLASTER_PARAMS_H_

#include"ini_file.h"

struct bit_blaster_params {
    bool  m_bb_eager;
    bool  m_bb_ext_gates;
    bool  m_bb_quantifiers;
    bit_blaster_params():
        m_bb_eager(false),
        m_bb_ext_gates(false),
        m_bb_quantifiers(false) {
    }
    void register_params(ini_params & p) {
        p.register_bool_param("BB_EAGER", m_bb_eager, "eager bit blasting");
        p.register_bool_param("BB_EXT_GATES", m_bb_ext_gates, "use extended gates during bit-blasting");
        p.register_bool_param("BB_QUANTIFIERS", m_bb_quantifiers, "convert bit-vectors to Booleans in quantifiers");
    }
};

#endif /* _BIT_BLASTER_PARAMS_H_ */

