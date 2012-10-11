/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datalog_frontend.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/
#ifndef _DATALOG_FRONTEND_H_
#define _DATALOG_FRONTEND_H_

struct datalog_params {
    symbol m_default_table;
    bool   m_default_table_checked;
    datalog_params();
    virtual void register_params(ini_params& p);        
};

unsigned read_datalog(char const * file, datalog_params const& dl_params, front_end_params & front_end_params);


#endif /* _DATALOG_FRONTEND_H_ */

