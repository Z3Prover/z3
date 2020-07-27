/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_failure.h

Abstract:

    Failures
    
Author:

    Leonardo de Moura (leonardo) 2012-02-09.

Revision History:

--*/
#pragma once

namespace smt {

    /**
       \brief Reason for a l_undef result in the check method.
    */
    enum failure {
        OK,
        UNKNOWN,
        MEMOUT,     
        CANCELED,      //!< External cancel flag was set
        NUM_CONFLICTS, //!< Maximum number of conflicts was reached
        THEORY,        //!< Theory is incomplete
        RESOURCE_LIMIT,
        QUANTIFIERS    //!< Logical context contains universal quantifiers.
    };

};

