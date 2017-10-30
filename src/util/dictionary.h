/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dictionary.h

Abstract:

Author:

    Leonardo (leonardo) 2011-03-01

Notes:

--*/
#ifndef DICTIONARY_H_
#define DICTIONARY_H_

#include "util/map.h"
#include "util/symbol.h"

template<typename T>
class dictionary : public map<symbol, T, symbol_hash_proc, symbol_eq_proc> {
public:
    dictionary() {}
};

#endif
