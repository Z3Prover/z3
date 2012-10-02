/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_string_buffer.cpp

Abstract:

    Test string buffer

Author:

    Leonardo de Moura (leonardo) 2006-10-14.

Revision History:

--*/
#include<cstdlib>
#include"debug.h"
#include"string_buffer.h"
#include"trace.h"

static void tst1() {
  string_buffer<> b;
  b << "Testing" << 10 << true;
  SASSERT(strcmp(b.c_str(), "Testing10true") == 0);
}

static void tst2() {
  string_buffer<> b;
  for (unsigned i = 0; i < 10000; i++) {
    int r = rand() % 10;
    b << r;
  }
  TRACE("string_buffer", tout << b.c_str() << "\n";);
  SASSERT(strlen(b.c_str()) == 10000);
}

static void tst3() {
  string_buffer<32> b;
  string_buffer<128> b2;
  b2 << "World";
  b << "Hello" << " " << b2;
  SASSERT(strcmp(b.c_str(), "Hello World") == 0);
}

void tst_string_buffer() {
  tst1();
  tst2();
  tst3();
}
