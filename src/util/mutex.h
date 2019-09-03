/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    mutex.h

Abstract:

    Auxiliary macros for mutual exclusion

--*/
#pragma once

#ifdef SINGLE_THREAD

template<typename T> using atomic = T;

struct mutex {
  void lock() {}
  void unlock() {}
};

struct lock_guard {
  lock_guard(mutex &) {}
};

#define DECLARE_MUTEX(name) mutex *name = nullptr
#define DECLARE_INIT_MUTEX(name) mutex *name = nullptr
#define ALLOC_MUTEX(name) (void)0
#define DEALLOC_MUTEX(name) (void)0

#else
#include <atomic>
#include <mutex>

template<typename T> using atomic = std::atomic<T>;
typedef std::mutex mutex;
typedef std::lock_guard<std::mutex> lock_guard;

#define DECLARE_MUTEX(name) mutex *name = nullptr
#define DECLARE_INIT_MUTEX(name) mutex *name = new mutex
#define ALLOC_MUTEX(name) name = alloc(mutex)
#define DEALLOC_MUTEX(name) dealloc(name)

#endif
