/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    error_codes.h

Abstract:

    Error codes produced by Z3.

Author:

    Leonardo de Moura (leonardo) 2007-09-04.

Revision History:

--*/
#ifndef _ERROR_CODES_H_
#define _ERROR_CODES_H_

#define ERR_OK                  0
#define ERR_MEMOUT              101
#define ERR_TIMEOUT             102
#define ERR_PARSER              103
#define ERR_UNSOUNDNESS         104
#define ERR_INCOMPLETENESS      105
#define ERR_INI_FILE            106 
#define ERR_NOT_IMPLEMENTED_YET 107 
#define ERR_OPEN_FILE           108
#define ERR_CMD_LINE            109
#define ERR_INTERNAL_FATAL      110
#define ERR_TYPE_CHECK          111
#define ERR_UNKNOWN_RESULT      112
#define ERR_ALLOC_EXCEEDED      113

#endif /* _ERROR_CODES_H_ */

