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

#include"debug.h"
#include"hash.h"
#include <string.h>

static unsigned read_unsigned(const char *s) {
  unsigned n;
  memcpy(&n, s, sizeof(unsigned));
  return n;
}

// I'm using Bob Jenkin's hash function.
// http://burtleburtle.net/bob/hash/doobs.html
unsigned string_hash(const char * str, unsigned length, unsigned init_value) {
    unsigned a, b, c, len;

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = init_value;      /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    SASSERT(sizeof(unsigned) == 4);
    while (len >= 12) {
        a += read_unsigned(str);
        b += read_unsigned(str+4);
        c += read_unsigned(str+8);
        mix(a,b,c);
        str += 12; len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch(len) {        /* all the case statements fall through */
    case 11: 
        c+=((unsigned)str[10]<<24);
        Z3_fallthrough;
    case 10: 
        c+=((unsigned)str[9]<<16);
        Z3_fallthrough;
    case 9 : 
        c+=((unsigned)str[8]<<8);
        Z3_fallthrough;
        /* the first byte of c is reserved for the length */
    case 8 : 
        b+=((unsigned)str[7]<<24);
        Z3_fallthrough;
    case 7 : 
        b+=((unsigned)str[6]<<16);
        Z3_fallthrough;
    case 6 : 
        b+=((unsigned)str[5]<<8);
        Z3_fallthrough;
    case 5 : 
        b+=str[4];
        Z3_fallthrough;
    case 4 : 
        a+=((unsigned)str[3]<<24);
        Z3_fallthrough;
    case 3 : 
        a+=((unsigned)str[2]<<16);
        Z3_fallthrough;
    case 2 : 
        a+=((unsigned)str[1]<<8);
        Z3_fallthrough;
    case 1 : 
        a+=str[0];
        Z3_fallthrough;
        /* case 0: nothing left to add */
    }
    mix(a,b,c);
    /*-------------------------------------------- report the result */
    return c;
}

