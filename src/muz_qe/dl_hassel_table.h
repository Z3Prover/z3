/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_hassel_table.h

Abstract:

    <abstract>

Revision History:

--*/

#ifndef _DL_HASSEL_TABLE_H_
#define _DL_HASSEL_TABLE_H_

#include "dl_hassel_common.h"

namespace datalog {

    class hassel_table;
    typedef union_ternary_bitvector<ternary_bitvector> union_ternary_bitvectors;

    class hassel_table : public common_hassel_table<union_ternary_bitvectors> {
    public:
        hassel_table(table_plugin & p, const table_signature & sig) :
            common_hassel_table(p, sig) {}
    };

    class hassel_table_plugin : public common_hassel_table_plugin<hassel_table> {
    public:
        hassel_table_plugin(relation_manager & manager);
    };

}

#endif
