/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    occurs.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-07.

Revision History:

--*/
#ifndef _OCCURS_H_
#define _OCCURS_H_

class expr; 
class func_decl;

/**
   \brief Return true if n1 occurs in n2
*/
bool occurs(expr * n1, expr * n2);

/**
   \brief Return true if d is used in n
*/
bool occurs(func_decl * d, expr * n);

#endif /* _OCCURS_H_ */

