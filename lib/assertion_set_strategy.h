/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set_strategy.h

Abstract:

    Abstract strategy for assertion sets, and simple combinators.

Author:

    Leonardo (leonardo) 2011-05-17

Notes:

--*/
#ifndef _AS_STRATEGY_H_
#define _AS_STRATEGY_H_

#include"params.h"
#include"assertion_set.h"
#include"model_converter.h"
#include"statistics.h"
#include"strategy_exception.h"
#include"lbool.h"
#include"assertion_set_util.h"

struct front_end_params;

class progress_callback;

// minimum verbosity level for strategies
#define ST_VERBOSITY_LVL 10

class as_st_report {
    struct imp;
    imp *  m_imp;
public:
    as_st_report(char const * id, assertion_set & s);
    ~as_st_report();
};

void report_st_progress(char const * id, unsigned val);

/**
   \brief Abstract assertion-set strategy. 
*/
class assertion_set_strategy {
    unsigned m_ref_count;
public:
    assertion_set_strategy():m_ref_count(0) {}
    virtual ~assertion_set_strategy() {}
    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }
    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}
    void cancel();
    void reset_cancel();
    virtual void set_cancel(bool f) {}
    virtual void operator()(assertion_set & s, model_converter_ref & mc) = 0;
    virtual void collect_statistics(statistics & st) const {}
    virtual void reset_statistics() {}
    virtual void cleanup() = 0;
    virtual void reset() { cleanup(); }
    // for backward compatibility
    virtual void set_front_end_params(front_end_params & p) {}
    virtual void set_logic(symbol const & l) {}
    virtual void set_progress_callback(progress_callback * callback) {}
};

bool is_equal(assertion_set const & s1, assertion_set const & s2);

// dummy for using ref_vector
struct assertion_set_strategy_context {
    static void inc_ref(assertion_set_strategy * st) { st->inc_ref(); }
    static void dec_ref(assertion_set_strategy * st) { st->dec_ref(); }
};

typedef assertion_set_strategy as_st;
typedef assertion_set_strategy_context as_st_ctx;

typedef ref<as_st> as_st_ref;
typedef ref_vector<as_st, as_st_ctx> as_st_ref_vector;
typedef ref_buffer<as_st, as_st_ctx> as_st_ref_buffer;

as_st * and_then(unsigned num, as_st * const * sts);
as_st * and_then(as_st * st1, as_st * st2);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9);
as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9, as_st * st10);

as_st * or_else(unsigned num, as_st * const * sts);
as_st * or_else(as_st * st1, as_st * st2);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9);
as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9, as_st * st10);

as_st * par(unsigned num, as_st * const * sts);
as_st * par(as_st * st1, as_st * st2);
as_st * par(as_st * st1, as_st * st2, as_st * st3);
as_st * par(as_st * st1, as_st * st2, as_st * st3, as_st * st4);

as_st * round_robin(unsigned num, as_st * const * sts, unsigned start, unsigned end, unsigned delta);
as_st * round_robin(as_st * st1, as_st * st2, unsigned start, unsigned end, unsigned delta);
as_st * round_robin(as_st * st1, as_st * st2, as_st * st3, unsigned start, unsigned end, unsigned delta);
as_st * round_robin(as_st * st1, as_st * st2, as_st * st3, as_st * st4, unsigned start, unsigned end, unsigned delta);

as_st * try_for(as_st * st, unsigned msecs);
as_st * clean(as_st * st);
as_st * using_params(as_st * st, params_ref const & p);
as_st * noop();
as_st * trace_mc(as_st * st);

as_st * filter_is_sat(as_st* st, bool const& unless_condition);
as_st * filter_is_unsat(as_st* st, bool const& unless_condition); 

as_st * mk_report_verbose_st(char const* msg, unsigned lvl);

as_st * repeat(as_st * st, unsigned max = UINT_MAX); 

class wrapper_as_st : public as_st {
protected:
    as_st * m_st;
public:
    wrapper_as_st(as_st * s): m_st(s) { SASSERT(s); s->inc_ref(); }    
    virtual ~wrapper_as_st();
   
    virtual void operator()(assertion_set& s, model_converter_ref& mc) { (*m_st)(s, mc); }
    virtual void cleanup(void) { m_st->cleanup(); }
    virtual void collect_statistics(statistics & st) const { m_st->collect_statistics(st); }
    virtual void reset_statistics() { m_st->reset_statistics(); }    
    virtual void set_front_end_params(front_end_params & p) { m_st->set_front_end_params(p); }
    virtual void updt_params(params_ref const & p) { m_st->updt_params(p); }
    virtual void collect_param_descrs(param_descrs & r) { m_st->collect_param_descrs(r); }
    virtual void reset() { m_st->reset(); }
    virtual void set_logic(symbol const& l) { m_st->set_logic(l); }    
    virtual void set_progress_callback(progress_callback * callback) { m_st->set_progress_callback(callback); }

protected:
    virtual void set_cancel(bool f) { if (m_st) m_st->set_cancel(f); }
};


class as_test { 
    unsigned m_ref_count;
public:
    as_test():m_ref_count(0) {}
    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }
    virtual bool operator()(assertion_set const & s) const = 0; 
};

as_test * check_mem(unsigned l);
as_test * check_as_size(unsigned l);
as_test * check_decided();
as_st * cond(as_test * c, as_st * t, as_st * e);

as_st * mk_smt_solver_core(bool candidate_models = false);
as_st * mk_smt_solver(bool auto_config = true, bool candidate_models = false);

void exec(as_st * st, assertion_set & s, model_converter_ref & mc);
lbool check_sat(as_st * st, assertion_set & s, model_ref & md, proof_ref & pr, std::string & reason_unknown);

class assertion_set_strategy_factory {
public:
    virtual ~assertion_set_strategy_factory() {}
    virtual as_st * operator()(ast_manager & m, params_ref const & p) = 0;
};

typedef assertion_set_strategy_factory as_st_f;

as_st * fail(); 
as_st * fail_if_not_decided(as_st * st);
as_st * fail_if_sat(); 
as_st * fail_if_unsat(); 
as_st * fail_if_not_small(unsigned sz);
as_st * fail_if_not_small_set(unsigned sz);

#define MK_FAIL_IF(NAME, TEST, MSG)                                                                                     \
class NAME ## _st : public assertion_set_strategy {                                                                     \
public:                                                                                                                 \
    virtual void operator()(assertion_set & s, model_converter_ref & mc) { if (TEST) throw strategy_exception(MSG); }  \
    virtual void cleanup() {}                                                                                           \
};                                                                                                                      \
inline as_st * NAME() { return alloc(NAME ## _st); }

as_st * par_or(ast_manager & m, unsigned num, as_st_f * const * stfs);

#define MK_ST_FACTORY(NAME, CODE)                                               \
class NAME : public assertion_set_strategy_factory {                            \
public:                                                                         \
    virtual ~NAME() {}                                                          \
    virtual as_st * operator()(ast_manager & m, params_ref const & p) { CODE }  \
};

#define MK_SIMPLE_ST_FACTORY(NAME, ST)  MK_ST_FACTORY(NAME, return ST;)

MK_SIMPLE_ST_FACTORY(smt_solver_stf, mk_smt_solver());

struct is_qfbv_test : public as_test {
    virtual bool operator()(assertion_set const & s) const {  return is_qfbv(s); }
};

struct is_qflia_test : public as_test {
    virtual bool operator()(assertion_set const & s) const {  return is_qflia(s); }
};

struct is_qflra_test : public as_test {
    virtual bool operator()(assertion_set const & s) const {  return is_qflra(s); }
};

inline as_test * is_qfbv() { return alloc(is_qfbv_test); }
inline as_test * is_qflia() { return alloc(is_qflia_test); }
inline as_test * is_qflra() { return alloc(is_qflra_test); }

#endif
