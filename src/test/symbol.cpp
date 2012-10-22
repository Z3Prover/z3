/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_symbol.cpp

Abstract:

    Test symbol class.

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/
#include<iostream>
#include"symbol.h"
#include"debug.h"

static void tst1() {
    symbol s1("foo");
    symbol s2("boo");
    symbol s3("foo");
    SASSERT(s1 != s2);
    SASSERT(s1 == s3);
    std::cout << s1 << " " << s2 << " " << s3 << "\n";
    SASSERT(s1 == "foo");
    SASSERT(s1 != "boo");
    SASSERT(s2 != "foo");
    SASSERT(s3 == "foo");
    SASSERT(s2 == "boo");

    SASSERT(lt(s2, s1));
    SASSERT(!lt(s1, s2));
    SASSERT(!lt(s1, s3));
    SASSERT(lt(symbol("abcc"), symbol("abcd")));
    SASSERT(!lt(symbol("abcd"), symbol("abcc")));
    SASSERT(lt(symbol("abc"), symbol("abcc")));
    SASSERT(!lt(symbol("abcd"), symbol("abc")));
    SASSERT(lt(symbol(10), s1));
    SASSERT(!lt(s1, symbol(10)));
    SASSERT(lt(symbol(10), symbol(20)));
    SASSERT(!lt(symbol(20), symbol(10)));
    SASSERT(!lt(symbol(10), symbol(10)));
    SASSERT(lt(symbol("a"), symbol("b")));
    SASSERT(!lt(symbol("z"), symbol("b")));
    SASSERT(!lt(symbol("zzz"), symbol("b")));
    SASSERT(lt(symbol("zzz"), symbol("zzzb")));
}

void tst_symbol() {
    tst1();
}



