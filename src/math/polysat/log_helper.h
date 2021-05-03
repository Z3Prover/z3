/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Logging support

Abstract:

    Utilities for logging.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include <iostream>
#include "util/util.h"

template <typename T>
struct show_deref_t {
  T* ptr;
};

template <typename T>
std::ostream& operator<<(std::ostream& os, show_deref_t<T> s) {
  if (s.ptr)
    return os << *s.ptr;
  else
    return os << "<null>";
}

template <typename T>
show_deref_t<T> show_deref(T* ptr) {
  return show_deref_t<T>{ptr};
}

template <typename T>
show_deref_t<T> show_deref(scoped_ptr<T> const& ptr) {
  return show_deref_t<T>{ptr.get()};
}
