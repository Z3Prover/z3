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

#include"z3_exception.h"
#include"z3_omp.h"
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
#else
// Linux
#include<csignal>
#include<ctime>
#include<memory.h>
#include"warning.h"
#define CLOCKID CLOCK_PROCESS_CPUTIME_ID
#define SIG     SIGRTMIN
// ---------
#endif 

#include"scoped_timer.h"
#ifdef _CYGWIN
#undef min
#undef max
#endif
#include"util.h"
#include<limits.h>

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
    pthread_cond_t   m_condition_var;
#else
    // Linux
    static void *   g_timer;
    void            (*m_old_handler)(int);
    void *          m_old_timer;
    timer_t         m_timerid;
#endif

#if defined(_WINDOWS) || defined(_CYGWIN)
    static void CALLBACK abort_proc(PVOID param, BOOLEAN timer_or_wait_fired) {
        imp * obj = static_cast<imp*>(param);
        if (obj->m_first) {
            obj->m_first = false;
        }
        else {
            obj->m_eh->operator()();
        }
    }
#elif defined(__APPLE__) && defined(__MACH__)
    // Mac OS X
    static void * thread_func(void * arg) {
        scoped_timer::imp * st = static_cast<scoped_timer::imp*>(arg);  

        pthread_mutex_t  mutex;
        clock_serv_t host_clock;
        struct timespec abstime;
        mach_timespec_t now;
        unsigned long long nano = static_cast<unsigned long long>(st->m_interval) * 1000000ull;

        host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &host_clock);

        if (pthread_mutex_init(&mutex, NULL) != 0)
            throw default_exception("failed to initialize timer mutex");
        if (pthread_cond_init(&st->m_condition_var, NULL) != 0)
            throw default_exception("failed to initialize timer condition variable");

        abstime.tv_sec  = nano / 1000000000ull;
        abstime.tv_nsec = nano % 1000000000ull;

        pthread_mutex_lock(&mutex);
        clock_get_time(host_clock, &now);
        ADD_MACH_TIMESPEC(&abstime, &now);
        int e = pthread_cond_timedwait(&st->m_condition_var, &mutex, &abstime);
        if (e != 0 && e != ETIMEDOUT)
            throw default_exception("failed to start timed wait");
        st->m_eh->operator()();
        pthread_mutex_unlock(&mutex);

        if (pthread_mutex_destroy(&mutex) != 0)
            throw default_exception("failed to destroy pthread mutex");
        if (pthread_cond_destroy(&st->m_condition_var) != 0)
            throw default_exception("failed to destroy pthread condition variable");
        return st;
    }
#else
    static void sig_handler(int) {
       static_cast<imp*>(g_timer)->m_eh->operator()();
    }
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
        m_interval = ms;
        if (pthread_attr_init(&m_attributes) != 0)
            throw default_exception("failed to initialize timer thread attributes");
        if (pthread_create(&m_thread_id, &m_attributes, &thread_func, this) != 0)
            throw default_exception("failed to start timer thread");
#else
	// Linux version
        if (omp_in_parallel()) {
            // It doesn't work in with more than one thread.
            // SIGEV_SIGNAL: the event is handled by the process not by the thread that installed the handler.
            // SIGEV_THREAD: the event is handled by a new thread (Z3 crashes with this configuration).
            // 
            // It seems the way to go is SIGEV_SIGNAL, but I have to find a way to identify the thread the event is meant to.
            return;
        }
	m_old_timer   = g_timer;
	g_timer       = this;
	m_old_handler = signal(SIG, sig_handler);

	struct sigevent sev;
        memset(&sev, 0, sizeof(sigevent));
	sev.sigev_notify = SIGEV_SIGNAL;
	sev.sigev_signo  = SIG;
	sev.sigev_value.sival_ptr = &m_timerid;
	if (timer_create(CLOCKID, &sev, &m_timerid) == -1)
	    throw default_exception("failed to create timer");

	unsigned long long nano = static_cast<unsigned long long>(ms) * 1000000ull;
	struct itimerspec its;
	its.it_value.tv_sec  = nano / 1000000000ull;
	its.it_value.tv_nsec = nano % 1000000000ull;
	its.it_interval.tv_sec  = 0; // timer experies once
	its.it_interval.tv_nsec = 0;
	if (timer_settime(m_timerid, 0, &its, NULL) == -1)
	    throw default_exception("failed to set timer");
#endif
    }

    ~imp() {
#if defined(_WINDOWS) || defined(_CYGWIN)
        DeleteTimerQueueTimer(NULL,
                              m_timer,
                              INVALID_HANDLE_VALUE);
#elif defined(__APPLE__) && defined(__MACH__)
        // Mac OS X
        pthread_cond_signal(&m_condition_var); // this is okay to fail
        if (pthread_join(m_thread_id, NULL) != 0)
            throw default_exception("failed to join thread");
        if (pthread_attr_destroy(&m_attributes) != 0)
            throw default_exception("failed to destroy pthread attributes object");
#else
	// Linux version
        if (omp_in_parallel())
            return; // see comments in the constructor.
	timer_delete(m_timerid);
	if (m_old_handler != SIG_ERR)
	    signal(SIG, m_old_handler);
	g_timer = m_old_timer;
#endif
    }

};

#if defined(_WINDOWS) || defined(_CYGWIN)
#elif defined(__APPLE__) && defined(__MACH__)
// Mac OS X
#else
// Linux
void * scoped_timer::imp::g_timer = 0;
#endif

scoped_timer::scoped_timer(unsigned ms, event_handler * eh) {
    if (ms != UINT_MAX)
        m_imp = alloc(imp, ms, eh);
    else
        m_imp = 0;
}
    
scoped_timer::~scoped_timer() {
    if (m_imp)
        dealloc(m_imp);
}
