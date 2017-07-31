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
#include "util/symbol.h"
#include "util/debug.h"

static void tst1() {
    symbol s1("foo");
    symbol s2("boo");
    symbol s3("foo");
    ENSURE(s1 != s2);
    ENSURE(s1 == s3);
    std::cout << s1 << " " << s2 << " " << s3 << "\n";
    ENSURE(s1 == "foo");
    ENSURE(s1 != "boo");
    ENSURE(s2 != "foo");
    ENSURE(s3 == "foo");
    ENSURE(s2 == "boo");

    ENSURE(lt(s2, s1));
    ENSURE(!lt(s1, s2));
    ENSURE(!lt(s1, s3));
    ENSURE(lt(symbol("abcc"), symbol("abcd")));
    ENSURE(!lt(symbol("abcd"), symbol("abcc")));
    ENSURE(lt(symbol("abc"), symbol("abcc")));
    ENSURE(!lt(symbol("abcd"), symbol("abc")));
    ENSURE(lt(symbol(10), s1));
    ENSURE(!lt(s1, symbol(10)));
    ENSURE(lt(symbol(10), symbol(20)));
    ENSURE(!lt(symbol(20), symbol(10)));
    ENSURE(!lt(symbol(10), symbol(10)));
    ENSURE(lt(symbol("a"), symbol("b")));
    ENSURE(!lt(symbol("z"), symbol("b")));
    ENSURE(!lt(symbol("zzz"), symbol("b")));
    ENSURE(lt(symbol("zzz"), symbol("zzzb")));
}

void tst_symbol() {
    tst1();
}



