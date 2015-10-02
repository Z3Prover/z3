/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    luby.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-04.

Revision History:

--*/
#ifndef LUBY_H_
#define LUBY_H_

/**
   \brief Return the i-th element of the Luby sequence: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...

   get_luby(i) = 2^{i-1}                     if  i = 2^k -1
   get_luby(i) = get_luby(i - 2^{k-1} + 1)   if  2^{k-1} <= i < 2^k - 1
*/
unsigned get_luby(unsigned i);

#endif /* LUBY_H_ */

