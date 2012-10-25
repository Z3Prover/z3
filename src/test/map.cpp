/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_map.cpp

Abstract:

    Test simple mapping.

Author:

    Leonardo de Moura (leonardo) 2006-10-14.

Revision History:

--*/
#include"map.h"
#include"str_hashtable.h"

static void tst1() {
  map<char const *, int, str_hash_proc, str_eq_proc> str2int;
  str2int.insert("foo", 35);
  SASSERT(str2int.contains("foo"));
  SASSERT(str2int.find_iterator("foo") != str2int.end());
  SASSERT((*(str2int.find_iterator("foo"))).m_value == 35);
  SASSERT(str2int.size() == 1);
  str2int.insert("boo", 32);
  SASSERT(str2int.contains("foo"));
  SASSERT(str2int.find_iterator("foo") != str2int.end());
  SASSERT((*(str2int.find_iterator("foo"))).m_value == 35);
  SASSERT(str2int.contains("boo"));
  SASSERT(str2int.find_iterator("boo") != str2int.end());
  SASSERT((*(str2int.find_iterator("boo"))).m_value == 32);
  SASSERT(str2int.size() == 2);
  str2int.remove("boo");
  SASSERT(str2int.size() == 1);
  SASSERT(!str2int.contains("boo"));
  SASSERT(str2int.contains("foo"));
}

void tst_map() {
  tst1();
}
