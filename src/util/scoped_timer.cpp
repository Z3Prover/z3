/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_timer.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-26.

Revision History:

--*/
#ifdef _CYGWIN
// Hack to make CreateTimerQueueTimer available on cygwin
#define _WIN32_WINNT 0x0600
#endif

#include "util/z3_exception.h"
#include "util/z3_omp.h"
#if defined(_WINDOWS) || defined(_CYGWIN)
// Windows
#include<windows.h>
#elif defined(__APPLE__) && defined(__MACH__)
// Mac OS X
#include<mach/mach.h>
#include<mach/clock.h>
#include<sys/time.h>
#include<sys/errno.h>
#include<pthread.h>
#elif defined(_LINUX_) || defined(_FREEBSD_) || defined(_NetBSD_)
// Linux & FreeBSD & NetBSD
#include<errno.h>
#include<pthread.h>
#include<sched.h>
#include<time.h>
// ---------
#else
// Other platforms
#endif 

#include "util/scoped_timer.h"
#ifdef _CYGWIN
#undef min
#undef max
#endif
#include "util/util.h"
#include<limits.h>
#include "util/z3_omp.h"

struct scoped_timer::imp {
    event_handler *  m_eh;
#if defined(_WINDOWS) || defined(_CYGWIN)
    HANDLE           m_timer;
    bool             m_first;
#elif defined(__APPLE__) && defined(__MACH__)
    // Mac OS X
    pthread_t        m_thread_id;
    pthread_attr_t   m_attributes;
    unsigned         m_interval;    
    pthread_mutex_t  m_mutex;
    pthread_cond_t   m_condition_var;
    struct timespec  m_end_time;
#elif defined(_LINUX_) || defined(_FREEBSD_) || defined(_NETBSD_)
    // Linux & FreeBSD & NetBSD
    pthread_t       m_thread_id;
    pthread_mutex_t m_mutex;
    pthread_cond_t  m_cond;
    unsigned        m_ms;
    bool            m_initialized;
    bool            m_signal_sent;
#else
    // Other
#endif

#if defined(_WINDOWS) || defined(_CYGWIN)
    static void CALLBACK abort_proc(PVOID param, BOOLEAN timer_or_wait_fired) {
        imp * obj = static_cast<imp*>(param);
        if (obj->m_first) {
            obj->m_first = false;
        }
        else {
            obj->m_eh->operator()(TIMEOUT_EH_CALLER);
        }
    }
#elif defined(__APPLE__) && defined(__MACH__)
    // Mac OS X
    static void * thread_func(void * arg) {
        scoped_timer::imp * st = static_cast<scoped_timer::imp*>(arg);  

        pthread_mutex_lock(&st->m_mutex);

        int e = pthread_cond_timedwait(&st->m_condition_var, &st->m_mutex, &st->m_end_time);
        if (e != 0 && e != ETIMEDOUT)
            throw default_exception("failed to start timed wait");
        st->m_eh->operator()(TIMEOUT_EH_CALLER);

        pthread_mutex_unlock(&st->m_mutex);

        return st;
    }
#elif defined(_LINUX_) || defined(_FREEBSD_) || defined(_NETBSD_)
    static void* thread_func(void *arg) {
        scoped_timer::imp *st = static_cast<scoped_timer::imp*>(arg);

        struct timespec end_time;
        clock_gettime(CLOCK_REALTIME, &end_time);
        end_time.tv_sec  += st->m_ms / 1000u;
        end_time.tv_nsec += (st->m_ms % 1000u) * 1000000ull;
        // check for overflow
        if (end_time.tv_nsec >= 1000000000) {
            ++end_time.tv_sec;
            end_time.tv_nsec -= 1000000000;
        }

        pthread_mutex_lock(&st->m_mutex);
        st->m_initialized = true;
        int e = 0;
        // `pthread_cond_timedwait()` may spuriously wake even if the signal
        // was not sent so we loop until a timeout occurs or the signal was
        // **really** sent.
        while (!(e == 0 && st->m_signal_sent)) {
          e = pthread_cond_timedwait(&st->m_cond, &st->m_mutex, &end_time);
          ENSURE(e == 0 || e == ETIMEDOUT);
          if (e == ETIMEDOUT)
            break;
        }
        pthread_mutex_unlock(&st->m_mutex);

        if (e == ETIMEDOUT)
            st->m_eh->operator()(TIMEOUT_EH_CALLER);
        return 0;
    }
#else
    // Other
#endif


    imp(unsigned ms, event_handler * eh):
        m_eh(eh) {
#if defined(_WINDOWS) || defined(_CYGWIN)
        m_first = true;
        CreateTimerQueueTimer(&m_timer,
                              NULL,
                              abort_proc,
                              this,
                              0,
                              ms,
                              WT_EXECUTEINTIMERTHREAD);
#elif defined(__APPLE__) && defined(__MACH__)
        // Mac OS X
        m_interval = ms?ms:0xFFFFFFFF;
        if (pthread_attr_init(&m_attributes) != 0)
            throw default_exception("failed to initialize timer thread attributes");
        if (pthread_cond_init(&m_condition_var, nullptr) != 0)
            throw default_exception("failed to initialize timer condition variable");
        if (pthread_mutex_init(&m_mutex, nullptr) != 0)
            throw default_exception("failed to initialize timer mutex");

        clock_serv_t host_clock;
        mach_timespec_t now;
        unsigned long long nano = static_cast<unsigned long long>(m_interval) * 1000000ull;
        
        host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &host_clock);
        m_end_time.tv_sec  = nano / 1000000000ull;
        m_end_time.tv_nsec = nano % 1000000000ull;
        clock_get_time(host_clock, &now);
        ADD_MACH_TIMESPEC(&m_end_time, &now);


        if (pthread_create(&m_thread_id, &m_attributes, &thread_func, this) != 0)
            throw default_exception("failed to start timer thread");
#elif defined(_LINUX_) || defined(_FREEBSD_) || defined(_NETBSD_)
        // Linux & FreeBSD & NetBSD
        m_ms = ms;
        m_initialized = false;
        m_signal_sent = false;
        ENSURE(pthread_mutex_init(&m_mutex, NULL) == 0);
        ENSURE(pthread_cond_init(&m_cond, NULL) == 0);
        ENSURE(pthread_create(&m_thread_id, NULL, &thread_func, this) == 0);
#else
    // Other platforms
#endif
    }

    ~imp() {
#if defined(_WINDOWS) || defined(_CYGWIN)
        DeleteTimerQueueTimer(NULL,
                              m_timer,
                              INVALID_HANDLE_VALUE);
#elif defined(__APPLE__) && defined(__MACH__)
        // Mac OS X

        // If the waiting-thread is not up and waiting yet, 
        // we can make sure that it finishes quickly by 
        // setting the end-time to zero.
        m_end_time.tv_sec = 0;
        m_end_time.tv_nsec = 0;

        // Otherwise it's already up and waiting, and
        // we can send a signal on m_condition_var:
        pthread_mutex_lock(&m_mutex);
        pthread_cond_signal(&m_condition_var);
        pthread_mutex_unlock(&m_mutex);

        if (pthread_join(m_thread_id, nullptr) != 0) {
            warning_msg("failed to join thread");
            return;
        }
        if (pthread_mutex_destroy(&m_mutex) != 0) {
            warning_msg("failed to destroy pthread mutex");
            return;
        }
        if (pthread_cond_destroy(&m_condition_var) != 0) {
            warning_msg("failed to destroy pthread condition variable");
            return;
        }
        if (pthread_attr_destroy(&m_attributes) != 0) {
            warning_msg("failed to destroy pthread attributes object");
            return;
        }
#elif defined(_LINUX_) || defined(_FREEBSD_) || defined(_NETBSD_)
        // Linux & FreeBSD & NetBSD
        bool init = false;

        // spin until timer thread has been created
        while (!init) {
            pthread_mutex_lock(&m_mutex);
            init = m_initialized;
            pthread_mutex_unlock(&m_mutex);
            if (!init)
                sched_yield();
        }
        pthread_mutex_lock(&m_mutex);
        m_signal_sent = true;
        pthread_mutex_unlock(&m_mutex);
        // Perform signal outside of lock to avoid waking timing thread twice.
        pthread_cond_signal(&m_cond);

        pthread_join(m_thread_id, NULL);
        pthread_cond_destroy(&m_cond);
        pthread_mutex_destroy(&m_mutex);
#else
    // Other Platforms
#endif
    }

};

scoped_timer::scoped_timer(unsigned ms, event_handler * eh) {
    if (ms != UINT_MAX && ms != 0)
        m_imp = alloc(imp, ms, eh);
    else
        m_imp = nullptr;
}
    
scoped_timer::~scoped_timer() {
    if (m_imp)
        dealloc(m_imp);
}
