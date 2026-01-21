/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    hash.cpp

Abstract:

    Basic hash computation support.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/

#include "util/debug.h"
#include "util/hash.h"
#include <string.h>

static unsigned read_unsigned(const char *s) {
  unsigned n;
  memcpy(&n, s, sizeof(unsigned));
  return n;
}

// I'm using Bob Jenkin's hash function.
// http://burtleburtle.net/bob/hash/doobs.html
unsigned string_hash(std::string_view str, unsigned init_value) {
    unsigned a, b, c, len;
    const char * data = str.data();
    unsigned length = static_cast<unsigned>(str.length());

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = init_value;      /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    SASSERT(sizeof(unsigned) == 4);
    while (len >= 12) {
        a += read_unsigned(data);
        b += read_unsigned(data+4);
        c += read_unsigned(data+8);
        mix(a,b,c);
        data += 12; len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch(len) {        /* all the case statements fall through */
    case 11: 
        c+=((unsigned)data[10]<<24);
        Z3_fallthrough;
    case 10: 
        c+=((unsigned)data[9]<<16);
        Z3_fallthrough;
    case 9 : 
        c+=((unsigned)data[8]<<8);
        Z3_fallthrough;
        /* the first byte of c is reserved for the length */
    case 8 : 
        b+=((unsigned)data[7]<<24);
        Z3_fallthrough;
    case 7 : 
        b+=((unsigned)data[6]<<16);
        Z3_fallthrough;
    case 6 : 
        b+=((unsigned)data[5]<<8);
        Z3_fallthrough;
    case 5 : 
        b+=data[4];
        Z3_fallthrough;
    case 4 : 
        a+=((unsigned)data[3]<<24);
        Z3_fallthrough;
    case 3 : 
        a+=((unsigned)data[2]<<16);
        Z3_fallthrough;
    case 2 : 
        a+=((unsigned)data[1]<<8);
        Z3_fallthrough;
    case 1 : 
        a+=data[0];
        /* case 0: nothing left to add */
        break;
    }
    mix(a,b,c);
    /*-------------------------------------------- report the result */
    return c;
}

