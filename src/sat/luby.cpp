/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    luby.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-04.

Revision History:

--*/
#include<cmath>

unsigned get_luby(unsigned i) {
    if (i == 1) 
        return 1;
    double k = log(static_cast<double>(i+1))/log(static_cast<double>(2));
    
    if (k == floor(k + 0.5))
        return static_cast<unsigned>(pow(2,k-1));
    else {
        k = static_cast<unsigned>(floor(k));
        return get_luby(i - static_cast<unsigned>(pow(2, k)) + 1);
    }
}

