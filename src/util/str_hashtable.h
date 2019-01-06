/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    str_hashtable.h

Abstract:

    String hashtable. It uses Jenkin's hash function and the optimized hashtable module.

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/
#ifndef STR_HASHTABLE_H_
#define STR_HASHTABLE_H_

#include<string.h>

#include "util/hashtable.h"
#include "util/hash.h"

struct str_hash_proc { 
    unsigned operator()(char const * s) const { return string_hash(s, static_cast<unsigned>(strlen(s)), 17); } 
};
struct str_eq_proc { bool operator()(char const * s1, char const * s2) const { return strcmp(s1, s2) == 0; } }; 
typedef ptr_hashtable<const char, str_hash_proc, str_eq_proc> str_hashtable;

#endif /* STR_HASHTABLE_H_ */

