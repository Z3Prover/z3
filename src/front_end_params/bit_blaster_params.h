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

struct bit_blaster_params {
    bool  m_bb_ext_gates;
    bool  m_bb_quantifiers;
    bit_blaster_params():
        m_bb_ext_gates(false),
        m_bb_quantifiers(false) {
    }
#if 0
    void register_params(ini_params & p) {
        p.register_bool_param("bb_ext_gates", m_bb_ext_gates, "use extended gates during bit-blasting");
        p.register_bool_param("bb_quantifiers", m_bb_quantifiers, "convert bit-vectors to Booleans in quantifiers");
    }
#endif
};

#endif /* _BIT_BLASTER_PARAMS_H_ */

