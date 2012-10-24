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
#include"assertion_set_strategy.h"
#include"assertion_set_util.h"
#include"cooperate.h"
#include"scoped_timer.h"
#include"cancel_eh.h"
#include"front_end_params.h"
#include"progress_callback.h"
#include"params2front_end_params.h"
#include"stopwatch.h"
#include"ast_translation.h"
#include"model_v2_pp.h"
#include<iomanip>
#include"z3_omp.h"

struct as_st_report::imp {
    char const *    m_id;
    assertion_set & m_set;
    stopwatch       m_watch;
    double          m_start_memory;

    imp(char const * id, assertion_set & s):
        m_id(id),
        m_set(s),
        m_start_memory(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024)) {
        m_watch.start();
    }
        
    ~imp() {
        m_watch.stop();
        double end_memory = static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024);
        verbose_stream() << "(" << m_id
                         << " :num-exprs " << m_set.num_exprs()
                         << " :num-asts " << m_set.m().get_num_asts()
                         << " :time " << std::fixed << std::setprecision(2) << m_watch.get_seconds()
                         << " :before-memory " << std::fixed << std::setprecision(2) << m_start_memory
                         << " :after-memory " << std::fixed << std::setprecision(2) << end_memory
                         << ")" << std::endl;
    }
};

as_st_report::as_st_report(char const * id, assertion_set & s) {
    if (get_verbosity_level() >= ST_VERBOSITY_LVL)
        m_imp = alloc(imp, id, s);
    else
        m_imp = 0;
}

void report_st_progress(char const * id, unsigned val) {
    if (val > 0) {
        IF_VERBOSE(ST_VERBOSITY_LVL, verbose_stream() << "(" << id << " " << val << ")" << std::endl;);
    }
}

as_st_report::~as_st_report() {
    if (m_imp)
        dealloc(m_imp);
}

class report_verbose_st : public assertion_set_strategy {
    std::string m_msg;
    unsigned m_lvl;
public:
    report_verbose_st(char const* msg, unsigned lvl) : m_msg(msg), m_lvl(lvl) {}
    
    virtual void cleanup() {}
    virtual void operator()(assertion_set& s, model_converter_ref & mc) {
        IF_VERBOSE(m_lvl, verbose_stream() << m_msg << "\n";);
    }
};

as_st * mk_report_verbose_st(char const* msg, unsigned lvl) {
    return alloc(report_verbose_st, msg, lvl);
}

    
void assertion_set_strategy::cancel() {
    #pragma omp critical (as_st_cancel)
    {
        set_cancel(true);
    }
}

void assertion_set_strategy::reset_cancel() {
    #pragma omp critical (as_st_cancel)
    {
        set_cancel(false);
    }
}

bool is_equal(assertion_set const & s1, assertion_set const & s2) {
    if (s1.size() != s2.size())
        return false;
    unsigned num1 = 0; // num unique ASTs in s1
    unsigned num2 = 0; // num unique ASTs in s2
    expr_fast_mark1 visited1;
    expr_fast_mark2 visited2;
    unsigned sz = s1.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f1 = s1.form(i);
        if (visited1.is_marked(f1))
            continue;
        num1++;
        visited1.mark(f1);
    }
    SASSERT(num1 <= sz);
    SASSERT(0 <= num1);
    for (unsigned i = 0; i < sz; i++) {
        expr * f2 = s2.form(i);
        if (visited2.is_marked(f2))
            continue;
        num2++;
        visited2.mark(f2);
        if (!visited1.is_marked(f2))
            return false;
    }
    SASSERT(num2 <= sz);
    SASSERT(0 <= num2);
    SASSERT(num1 >= num2);
    return num1 == num2;
}

class composite_as_st : public as_st {
protected:
    ptr_vector<as_st> m_sts;
    volatile bool     m_cancel;

    void checkpoint() {
        if (m_cancel)
            throw strategy_exception(STE_CANCELED_MSG);
    }

public:
    composite_as_st(unsigned num, as_st * const * sts):m_cancel(false) {
        for (unsigned i = 0; i < num; i++) {
            m_sts.push_back(sts[i]);
            sts[i]->inc_ref();
        }
        DEBUG_CODE({
            for (unsigned i = 0; i < num; i++) {
                SASSERT(sts[i]);
            }
        });
    }
    
    virtual ~composite_as_st() {
        ptr_buffer<as_st> old_sts;
        unsigned sz = m_sts.size();
        old_sts.append(sz, m_sts.c_ptr());
        #pragma omp critical (as_st_cancel)
        {
            for (unsigned i = 0; i < sz; i++) {
                m_sts[i] = 0;
            }
        }
        for (unsigned i = 0; i < sz; i++) {
            old_sts[i]->dec_ref();
        }
    }
    
    virtual void updt_params(params_ref const & p) {
        TRACE("composite_updt_params", tout << "updt_params: " << p << "\n";);
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->updt_params(p);
    }
    
    virtual void collect_param_descrs(param_descrs & r) {
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->collect_param_descrs(r);
    }
    
    virtual void collect_statistics(statistics & st) const {
        ptr_vector<as_st>::const_iterator it  = m_sts.begin();
        ptr_vector<as_st>::const_iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->collect_statistics(st);
    }

    virtual void reset_statistics() { 
        ptr_vector<as_st>::const_iterator it  = m_sts.begin();
        ptr_vector<as_st>::const_iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->reset_statistics();
    }
        
    virtual void cleanup() {
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->cleanup();
    }
    
    virtual void reset() {
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->reset();
    }

    virtual void set_front_end_params(front_end_params & p) {
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->set_front_end_params(p);
    }

    virtual void set_logic(symbol const & l) {
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->set_logic(l);
    }

    virtual void set_progress_callback(progress_callback * callback) {
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            (*it)->set_progress_callback(callback);
    }

protected:
    /**
       \brief Reset cancel flag of st if this was not canceled.
    */
    void parent_reset_cancel(as_st & st) {
        #pragma omp critical (as_st_cancel)
        {
            if (!m_cancel) {
                st.set_cancel(false);
            }
        }
    }

    virtual void set_cancel(bool f) {
        m_cancel = f;
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it)
            if (*it)
                (*it)->set_cancel(f);
    }
};

class and_then_as_st : public composite_as_st {
public:
    and_then_as_st(unsigned num, as_st * const * sts):composite_as_st(num, sts) {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        if (s.inconsistent())
            return;
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it) {
            checkpoint();
            as_st & st = *(*it);
            model_converter_ref mc1; // force mc1 to be 0 at every iteration... otherwise, it may contain value of the previous iteration.
            try {
                st(s, mc1);
            }
            catch (strategy_exception & ex) {
                mc = 0;
                throw ex;
            }
            mc = concat(mc.get(), mc1.get());
        }
    }
};

as_st * and_then(unsigned num, as_st * const * sts) {
    return alloc(and_then_as_st, num, sts);
}

as_st * and_then(as_st * st1, as_st * st2) {
    as_st * sts[2] = { st1, st2 };
    return and_then(2, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3) {
    as_st * sts[3] = { st1, st2, st3 };
    return and_then(3, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4) {
    as_st * sts[4] = { st1, st2, st3, st4 };
    return and_then(4, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5) {
    as_st * sts[5] = { st1, st2, st3, st4, st5 };
    return and_then(5, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6) {
    as_st * sts[6] = { st1, st2, st3, st4, st5, st6 };
    return and_then(6, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7) {
    as_st * sts[7] = { st1, st2, st3, st4, st5, st6, st7 };
    return and_then(7, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8) {
    as_st * sts[8] = { st1, st2, st3, st4, st5, st6, st7, st8 };
    return and_then(8, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9) {
    as_st * sts[9] = { st1, st2, st3, st4, st5, st6, st7, st8, st9 };
    return and_then(9, sts);
}

as_st * and_then(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9, as_st * st10) {
    as_st * sts[10] = { st1, st2, st3, st4, st5, st6, st7, st8, st9, st10 };
    return and_then(10, sts);

}

class or_else_as_st : public composite_as_st {
public:
    or_else_as_st(unsigned num, as_st * const * sts):composite_as_st(num, sts) {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        if (s.inconsistent())
            return;
        assertion_set orig_s(s.m());
        s.copy(orig_s);
        unsigned sz = m_sts.size();
        unsigned i;
        for (i = 0; i < sz - 1; i++) {
            checkpoint();
            as_st & st = *(m_sts[i]);
            mc = 0;
            try {
                st(s, mc);
                return;
            }
            catch (strategy_exception ex) {
                mc = 0;
                s.reset();
                orig_s.copy(s);
            }
        }
        checkpoint();
        SASSERT(i == sz - 1);
        as_st & st = *(m_sts[i]);
        st(s, mc);
    }
};


as_st * or_else(unsigned num, as_st * const * sts) {
    return alloc(or_else_as_st, num, sts);
}

as_st * or_else(as_st * st1, as_st * st2) {
    as_st * sts[2] = { st1, st2 };
    return or_else(2, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3) {
    as_st * sts[3] = { st1, st2, st3 };
    return or_else(3, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4) {
    as_st * sts[4] = { st1, st2, st3, st4 };
    return or_else(4, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5) {
    as_st * sts[5] = { st1, st2, st3, st4, st5 };
    return or_else(5, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6) {
    as_st * sts[6] = { st1, st2, st3, st4, st5, st6 };
    return or_else(6, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7) {
    as_st * sts[7] = { st1, st2, st3, st4, st5, st6, st7 };
    return or_else(7, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8) {
    as_st * sts[8] = { st1, st2, st3, st4, st5, st6, st7, st8 };
    return or_else(8, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9) {
    as_st * sts[9] = { st1, st2, st3, st4, st5, st6, st7, st8, st9 };
    return or_else(9, sts);
}

as_st * or_else(as_st * st1, as_st * st2, as_st * st3, as_st * st4, as_st * st5, as_st * st6, as_st * st7, as_st * st8, as_st * st9, as_st * st10) {
    as_st * sts[10] = { st1, st2, st3, st4, st5, st6, st7, st8, st9, st10 };
    return or_else(10, sts);
}

class par_as_st : public or_else_as_st {
public:
    par_as_st(unsigned num, as_st * const * sts):or_else_as_st(num, sts) {}
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        if (s.inconsistent()) {
            mc = 0;
            return;
        }

        if (omp_in_parallel()) {
            // execute tasks sequentially
            or_else_as_st::operator()(s, mc);
            return;
        }
        
        ast_manager & m = s.m();

        sbuffer<assertion_set> s_copies;
        ptr_vector<as_st>::iterator it  = m_sts.begin();
        ptr_vector<as_st>::iterator end = m_sts.end();
        for (; it != end; ++it) {
            s_copies.push_back(assertion_set(m));
            assertion_set & s_copy = s_copies.back();
            s.copy(s_copy);
        }

        unsigned finished_id = UINT_MAX;
        char const * ex1_msg = 0;
        std::string  z3_ex1_msg;

        int sz = m_sts.size();
        
        cooperation_section section;
        omp_set_num_threads(sz);
        #pragma omp parallel for
        for (int i = 0; i < sz; i++) {
            init_task task("par_as_st");
            as_st & st = *(m_sts[i]);
            try {
                model_converter_ref tmp_mc;
                assertion_set & s_copy = s_copies[i];
                st(s_copy, tmp_mc);
                bool first = false;
                #pragma omp critical (par_as_st)
                {
                    if (finished_id == UINT_MAX) {
                        finished_id = i;
                        first = true;
                    }
                }
                if (first) {
                    mc = tmp_mc;
                    s_copy.copy(s);
                    for (int j = 0; j < sz; j++) {
                        if (i != j)
                            m_sts[j]->cancel();
                    }
                }
            }
            catch (strategy_exception & ex) {
                if (i == 0)
                    ex1_msg = ex.msg();
            }
            catch (z3_error & ex) {
                throw ex;
            }
            catch (z3_exception & z3_ex) {
                if (i == 0)
                    z3_ex1_msg = z3_ex.msg();
            }
        }

        if (finished_id == UINT_MAX) {
            mc = 0;
            if (ex1_msg != 0)
                throw strategy_exception(ex1_msg);
            else
                throw default_exception(z3_ex1_msg.c_str());
        }
    }
};

as_st * par(unsigned num, as_st * const * sts) {
    return alloc(par_as_st, num, sts);
}

as_st * par(as_st * st1, as_st * st2) {
    as_st * sts[2] = { st1, st2 };
    return par(2, sts);
}

as_st * par(as_st * st1, as_st * st2, as_st * st3) {
    as_st * sts[3] = { st1, st2, st3 };
    return par(3, sts);
}

as_st * par(as_st * st1, as_st * st2, as_st * st3, as_st * st4) {
    as_st * sts[4] = { st1, st2, st3, st4 };
    return par(4, sts);
}

class par_or_as_st : public as_st {
    ptr_vector<as_st_f> m_stfs;
    ptr_vector<as_st>   m_sts;
    std::string         m_exc_msg;
    params_ref          m_params;

    void dec_ref_sts() {
        unsigned sz = m_sts.size();
        for (unsigned i = 0; i < sz; i++) {
            as_st * st = m_sts[i];
            #pragma omp critical (as_st_cancel) 
            {
                m_sts[i] = 0;
            }
            st->dec_ref();
        }
    }

    void exec_seq(assertion_set & s, model_converter_ref & mc) {
        for (unsigned i = 0; i < m_stfs.size(); i++) {
            as_st_f & f = *m_stfs[i];
            as_st * new_st = f(s.m(), m_params);
            new_st->inc_ref();
            #pragma omp critical (as_st_cancel) 
            {
                m_sts[i] = new_st;
            }
        }
        or_else_as_st(m_sts.size(), m_sts.c_ptr())(s, mc);
        dec_ref_sts();
    }
    
public:
    par_or_as_st(unsigned num, as_st_f * const * stfs) {
        m_stfs.append(num, stfs);
        m_sts.resize(num, 0);
    }

    virtual ~par_or_as_st() {
        DEBUG_CODE({
            for (unsigned i = 0; i < m_sts.size(); i++) {
                SASSERT(m_sts[i] == 0);
            }
        });
        std::for_each(m_stfs.begin(), m_stfs.end(), delete_proc<as_st_f>());
    }

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        if (s.inconsistent()) {
            mc = 0;
            return;
        }

        ast_manager & m = s.m();

        if (omp_in_parallel()) {
            exec_seq(s, mc);
            return;
        }
        
        ptr_buffer<ast_manager> managers;

        unsigned num = m_stfs.size();
        for (unsigned i = 0; i < num; i++) {
            SASSERT(!m.is_format_manager());
            managers.push_back(alloc(ast_manager, m.proof_mode()));
            managers.back()->copy_families_plugins(m); // has to be the first operation on the new managers.
            as_st_f & f = *m_stfs[i];
            ast_manager & m_i = *managers.back();            
            as_st * new_st = f(m_i, m_params);
            new_st->inc_ref();
            #pragma omp critical (as_st_cancel)
            {
                m_sts[i] = new_st;
            }
        }

        int sz = m_sts.size();
        unsigned finished_id = UINT_MAX;
        bool got_z3_exc = false;
        m_exc_msg = "";
        bool good_abort = false;

        #pragma omp parallel for
        for (int i = 0; i < sz; i++) {
#ifdef _WINDOWS
            DWORD_PTR am = (0x01 << (omp_get_thread_num() % omp_get_num_procs()));            
            SetThreadAffinityMask(GetCurrentThread(), am);
#endif
            as_st & st = *(m_sts[i]);
            ast_manager & s_m = *managers[i];
            ast_translation input_translator(m, s_m); 
            assertion_set * s_copy = s.translate(input_translator);
            
            try {
                model_converter_ref tmp_mc;
                st(*s_copy, tmp_mc);

                #pragma omp critical (par_or_as_st)
                {                    
                    if (finished_id == UINT_MAX) // ... and we're the first!
                        finished_id = i;
                }

                if (finished_id == static_cast<unsigned>(i)) {
                    good_abort = true;
                    for (int j = 0; j < sz; j++) {
                        if (i != j)
                            m_sts[j]->cancel();
                    }

                    ast_translation output_translator(s_m, m);
                    mc = (tmp_mc) ? tmp_mc->translate(output_translator) : 0;
                    
                    assertion_set * temp_set = s_copy->translate(output_translator);
                    temp_set->copy(s);
                    dealloc(temp_set);
                }
            }
            catch (strategy_exception & ex) {
                if (!good_abort) {
                    #pragma omp critical (par_or_as_st_ex)
                    {
                        m_exc_msg = ex.msg();
                        got_z3_exc = false;
                    }
                }
            }
            catch (z3_error & ex) {
                throw ex;
            }
            catch (z3_exception & z3_ex) {
                if (!good_abort) {
                    #pragma omp critical (par_or_as_st_ex)
                    {
                        m_exc_msg = z3_ex.msg();
                        got_z3_exc = true;
                    }
                }
            }
            catch (...) {
                if (!good_abort) {
                    #pragma omp critical (par_or_as_st_ex)
                    {
                        m_exc_msg = "unidentified exception in parallel region.";
                        got_z3_exc = false;
                    }
                }
            }

            dealloc(s_copy);
        }

        dec_ref_sts();
        
        for (unsigned i = 0; i < num; i++) {
            dealloc(managers[i]);
        }
        
        if (finished_id == UINT_MAX) {
            mc = 0;
            if (got_z3_exc)
                throw default_exception(m_exc_msg.c_str());
            else
                throw strategy_exception(m_exc_msg.c_str());
        }
    }

    virtual void cleanup() {
        // Cleanup is invoked to free memory allocated by the strategy,
        // but it must leave the strategy object in a usable state.
        // par_or does not need a cleanup since it only has factories.
    }
    
    virtual void set_cancel(bool f) {
        for (unsigned i = 0; i < m_sts.size(); i++)
            if (m_sts[i])
                m_sts[i]->set_cancel(f);
    }

    virtual void updt_params(params_ref const & p) {        
        m_params = p;
    }
};

as_st * par_or(ast_manager & m, unsigned num, as_st_f * const * stfs) {
#ifdef _Z3_BUILD_PARALLEL_SMT
    return alloc(par_or_as_st, num, stfs);
#else
    // If Z3 was not compiled using _Z3_BUILD_PARALLEL_SMT, then
    // it is not safe to use par_or (symbol and big_num managers are not protected).
    // We use par instead
    ptr_buffer<as_st> sts;
    params_ref p;
    for (unsigned i = 0; i < num; i++)
        sts.push_back(stfs[i]->operator()(m, p));
    return par(num, sts.c_ptr());
#endif
}

class fail_as_st : public as_st {
public:
    fail_as_st() {}
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        throw strategy_exception("failed");
    }
    void cleanup() {}
};

as_st * fail() {
    return alloc(fail_as_st);
}

as_st * fail_if_not_decided(as_st * st) {
    return and_then(st, cond(check_decided(), noop(), fail()));
}

class fail_if_unsat_st : public as_st {
public:
    fail_if_unsat_st() {}
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        TRACE("fail_if_unsat", s.display(tout););
        if (s.inconsistent())
            throw strategy_exception("failed: not unsat");
    }
    void cleanup() {}
};

class fail_if_sat_st : public as_st {
public:
    fail_if_sat_st() {}
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        TRACE("fail_if_sat", s.display(tout););
        if (s.size() == 0)
            throw strategy_exception("failed: not sat");
    }
    void cleanup() {}
};

as_st * fail_if_unsat() {
    return alloc(fail_if_unsat_st);
}

as_st * fail_if_sat() {
    return alloc(fail_if_sat_st);
}

struct fail_if_not_small_st : public assertion_set_strategy {
    unsigned m_size;
    fail_if_not_small_st(unsigned sz):m_size(sz) {}
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        TRACE("fail_if_not_small", tout << "fail_if_not_small: executing, s.num_exprs(): " << s.num_exprs() << ", threshold: " << m_size << "\n";);
        if (s.num_exprs() >= m_size) {
            TRACE("fail_if_not_small", tout << "fail_if_not_small: failed\n";);
            throw strategy_exception("failed: not small");
        }
    }

    virtual void cleanup() {}
};

as_st * fail_if_not_small(unsigned sz) {
    return alloc(fail_if_not_small_st, sz);
}

struct fail_if_not_small_set_st : public assertion_set_strategy {
    unsigned m_size;
    fail_if_not_small_set_st(unsigned sz):m_size(sz) {}
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        TRACE("fail_if_not_small_set", tout << "fail_if_not_small: executing, s.size(): " << s.size() << ", threshold: " << m_size << "\n";);
        if (s.size() >= m_size) {
            TRACE("fail_if_not_small_set", tout << "fail_if_not_small: failed\n";);
            throw strategy_exception("failed: not small");
        }
    }

    virtual void cleanup() {}
};

as_st * fail_if_not_small_set(unsigned sz) {
    return alloc(fail_if_not_small_set_st, sz);
}

class round_robin_as_st : public composite_as_st {
    unsigned m_start_timeout;
    unsigned m_end_timeout;
    unsigned m_delta_timeout;
public:
    round_robin_as_st(unsigned num, as_st * const * sts, unsigned start, unsigned end, unsigned delta):
        composite_as_st(num, sts),
        m_start_timeout(start),
        m_end_timeout(end),
        m_delta_timeout(delta) {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        if (s.inconsistent())
            return;
        assertion_set orig_s(s.m());
        s.copy(orig_s);
        unsigned timeout = m_start_timeout;
        while (true) {
            unsigned sz = m_sts.size();
            unsigned i;
            for (i = 0; i < sz; i++) {
                checkpoint();
                as_st & st = *(m_sts[i]);
                cancel_eh<as_st> eh(st);
                {
                    scoped_timer timer(timeout, &eh);
                    mc = 0;
                    try {
                        st(s, mc);
                        return;
                    }
                    catch (strategy_exception & ex) {
                        parent_reset_cancel(st);
                        mc = 0;
                        if (i == sz - 1 && timeout + m_delta_timeout > m_end_timeout)
                            throw ex; // last strategy in the last round
                        s.reset();
                        orig_s.copy(s);
                    }
                }
            }
            timeout += m_delta_timeout;
        }
    }
};

as_st * round_robin(unsigned num, as_st * const * sts, unsigned start, unsigned end, unsigned delta) {
    return alloc(round_robin_as_st, num, sts, start, end, delta);
}

as_st * round_robin(as_st * st1, as_st * st2, unsigned start, unsigned end, unsigned delta) {
    as_st * sts[2] = { st1, st2 };
    return round_robin(2, sts, start, end, delta);
}

as_st * round_robin(as_st * st1, as_st * st2, as_st * st3, unsigned start, unsigned end, unsigned delta) {
    as_st * sts[3] = { st1, st2, st3 };
    return round_robin(3, sts, start, end, delta);
}

as_st * round_robin(as_st * st1, as_st * st2, as_st * st3, as_st * st4, unsigned start, unsigned end, unsigned delta) {
    as_st * sts[4] = { st1, st2, st3, st4 };
    return round_robin(4, sts, start, end, delta);
}

wrapper_as_st::~wrapper_as_st() {
    as_st * d = m_st;
    #pragma omp critical (as_st_cancel)
    {
        m_st = 0;
    }
    d->dec_ref();
}

class try_for_as_st : public wrapper_as_st {
    unsigned m_timeout;
public:
    try_for_as_st(as_st * s, unsigned t):wrapper_as_st(s), m_timeout(t) {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        cancel_eh<assertion_set_strategy> eh(*m_st);
        { 
            // Warning: scoped_timer is not thread safe in Linux.
            scoped_timer timer(m_timeout, &eh);
            wrapper_as_st::operator()(s, mc);
        }
    }
};

as_st * try_for(as_st * st, unsigned msecs) {
    return alloc(try_for_as_st, st, msecs);
}

class cleanup_as_st : public wrapper_as_st {
public:
    cleanup_as_st(as_st * s):wrapper_as_st(s) {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        try {
            wrapper_as_st::operator()(s, mc);
            wrapper_as_st::cleanup();
        }
        catch (strategy_exception & ex) {
            wrapper_as_st::cleanup();
            throw ex;
        }
    }
};

as_st * clean(as_st * st) {
    return alloc(cleanup_as_st, st);
}

class using_params_as_st : public wrapper_as_st {
    params_ref m_params;
public:
    using_params_as_st(as_st * s, params_ref const & p):wrapper_as_st(s), m_params(p) {
        s->updt_params(p);
    }

    virtual void updt_params(params_ref const & p) {
        TRACE("using_params", 
              tout << "before p: " << p << "\n";
              tout << "m_params: " << m_params << "\n";
              ;);
        
        params_ref new_p = p;
        new_p.append(m_params);
        wrapper_as_st::updt_params(new_p);
        
        TRACE("using_params", 
              tout << "after p: " << p << "\n";
              tout << "m_params: " << m_params << "\n";
              tout << "new_p: " << new_p << "\n";);
    }
};

as_st * using_params(as_st * st, params_ref const & p) {
    return alloc(using_params_as_st, st, p);
}

/**
   \brief For debugging purposes: display model converter in the trace. 
*/
class trace_mc_as_st : public wrapper_as_st {
public:
    trace_mc_as_st(as_st * s):wrapper_as_st(s) {
    }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        wrapper_as_st::operator()(s, mc);
        TRACE("trace_mc", tout << "trace_mc...\n"; if (mc) mc->display(tout););
    }
};

as_st * trace_mc(as_st * st) {
    return alloc(trace_mc_as_st, st);
}

class repeat_as_st : public wrapper_as_st {
    unsigned      m_max;
    volatile bool m_cancel;

    void checkpoint() {
        if (m_cancel)
            throw strategy_exception(STE_CANCELED_MSG);
    }

public:
    repeat_as_st(as_st * s, unsigned max):wrapper_as_st(s), m_max(max), m_cancel(false) {
    }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        if (s.inconsistent())
            return;
        unsigned counter = 0;
        while (true) {
            checkpoint();
            
            assertion_set orig_s(s.m());
            s.copy(orig_s);
            
            model_converter_ref mc1;
            try {
                (*m_st)(s, mc1);
            }
            catch (strategy_exception & ex) {
                mc = 0;
                throw ex;
            }
            
            mc = concat(mc.get(), mc1.get());
            counter++;
            if (counter >= m_max)
                return;
            if (is_equal(orig_s, s))
                return;
        }
    }

    virtual void set_cancel(bool f) {
        m_cancel = f;
        wrapper_as_st::set_cancel(f);
    }
};

as_st * repeat(as_st * st, unsigned max) {
    return alloc(repeat_as_st, st, max);
}

class noop_as_st : public assertion_set_strategy {
public:
    virtual void set_cancel(bool f) {}
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {}
    virtual void cleanup() {}
};

as_st * noop() {
    return alloc(noop_as_st);
}

MK_ST_EXCEPTION(check_is_sat_exception);
MK_ST_EXCEPTION(check_is_unsat_exception);

class filter_is_sat_st : public wrapper_as_st {
    bool const& m_unless_condition;
public:
    filter_is_sat_st(as_st* st, bool const& unless_condition):
        wrapper_as_st(st), m_unless_condition(unless_condition) {}
    virtual ~filter_is_sat_st() {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        TRACE("filter_is_sat_bug", tout << "cond: " << m_unless_condition << "\n"; s.display(tout); mc->display(tout););
        wrapper_as_st::operator()(s, mc);
        if (!m_unless_condition && (s.size() > 0 || s.inconsistent())) {
            throw check_is_sat_exception("Solver did not establish satisfiability");
        }        
    }
};

as_st * filter_is_sat(as_st* st, bool const& unless_condition) {
    return alloc(filter_is_sat_st, st, unless_condition);
}


class filter_is_unsat_st : public wrapper_as_st {
    bool const& m_unless_condition;
public:
    filter_is_unsat_st(as_st* st, bool const& unless_condition):
        wrapper_as_st(st), m_unless_condition(unless_condition) {}
    virtual ~filter_is_unsat_st() {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        wrapper_as_st::operator()(s, mc);
        if (!m_unless_condition && !s.inconsistent()) {
            throw check_is_unsat_exception("Solver did not establish unsatisfiability");
        }        
    }
};

as_st * filter_is_unsat(as_st* st, bool const& unless_condition) {
    return alloc(filter_is_unsat_st, st, unless_condition);
}



class cond_as_st : public as_st {
protected:
    as_test *     m_cond;
    as_st *       m_then;
    as_st *       m_else;
    volatile bool m_cancel;
public:
    cond_as_st(as_test * c, as_st * t, as_st * e):m_cond(c), m_then(t), m_else(e), m_cancel(false) {
        SASSERT(c); SASSERT(t); SASSERT(e);
        c->inc_ref();
        t->inc_ref();
        e->inc_ref();
    }
    
    virtual ~cond_as_st() {
        as_st * d1  = m_then;
        as_st * d2  = m_else;
        #pragma omp critical (as_st_cancel)
        {
            m_then = 0;
            m_else = 0;
        }
        m_cond->dec_ref();
        d1->dec_ref();
        d2->dec_ref();
    }
    
    virtual void updt_params(params_ref const & p) {
        m_then->updt_params(p);
        m_else->updt_params(p);
    }
    
    virtual void collect_param_descrs(param_descrs & r) {
        m_then->collect_param_descrs(r);
        m_else->collect_param_descrs(r);
    }
    
    virtual void collect_statistics(statistics & s) const {
        m_then->collect_statistics(s);
        m_else->collect_statistics(s);
    }

    virtual void reset_statistics() { 
        m_then->reset_statistics();
        m_else->reset_statistics();
    }

    virtual void cleanup() {
        m_then->cleanup();
        m_else->cleanup();
    }
    
    virtual void reset() {
        m_then->reset();
        m_else->reset();
    }

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        if (s.inconsistent())
            return;
        assertion_set orig_s(s.m());
        s.copy(orig_s);
        bool c = (*m_cond)(s);
        if (m_cancel)
            throw strategy_exception(STE_CANCELED_MSG);
        if (c)
            (*m_then)(s, mc);
        else
            (*m_else)(s, mc);
    }

    virtual void set_front_end_params(front_end_params & p) {
        m_then->set_front_end_params(p);
        m_else->set_front_end_params(p);
    }

    virtual void set_logic(symbol const & l) {
        m_then->set_logic(l);
        m_else->set_logic(l);
    }

    virtual void set_progress_callback(progress_callback * callback) {
        m_then->set_progress_callback(callback);
        m_else->set_progress_callback(callback);
    }

protected:
    virtual void set_cancel(bool f) {
        m_cancel = f;
        if (m_then)
            m_then->set_cancel(f);
        if (m_else)
            m_else->set_cancel(f);
    }
};


as_st * cond(as_test * c, as_st * t, as_st * e) {
    return alloc(cond_as_st, c, t, e);
}

struct check_mem_test : public as_test {
    unsigned m_limit;
    check_mem_test(unsigned l):m_limit(l) {}
    virtual bool operator()(assertion_set const & s) const {
        return memory::get_allocation_size() < m_limit;
    }
};

as_test * check_mem(unsigned l) { return alloc(check_mem_test, l); }

struct check_as_size_test : public as_test {
    unsigned m_limit;
    check_as_size_test(unsigned l):m_limit(l) {}
    virtual bool operator()(assertion_set const & s) const { return s.num_exprs() < m_limit; }
};

as_test * check_as_size(unsigned l) { return alloc(check_as_size_test, l); }

struct check_decided_test : public as_test {    
    check_decided_test() {}
    virtual bool operator()(assertion_set const & s) const { return s.size()==0 || s.inconsistent(); }
};

as_test * check_decided() { return alloc(check_decided_test); }

/**
   \brief Execute strategy st on the given assertion set.
*/
void exec(as_st * st, assertion_set & s, model_converter_ref & mc) {
    st->reset_statistics();
    st->reset_cancel();
    try {
        (*st)(s, mc);
        st->cleanup();
    }
    catch (strategy_exception & ex) {
        IF_VERBOSE(ST_VERBOSITY_LVL, verbose_stream() << "(strategy-exception \"" << escaped(ex.msg()) << "\")" << std::endl;);
        st->cleanup();
        throw ex;
    }
}

/**
   \brief Use strategy st to check wether the assertion set s is satisfiable or not.
   If result == l_true and model generation is enabled, then the model is stored in md.
   If result == l_false and proof generation is enabled, then the proof is stored in pr.
   If result == l_undef, the reason for failure is stored in reason_unknown.
*/
lbool check_sat(as_st * st, assertion_set & s, model_ref & md, proof_ref & pr, std::string & reason_unknown) {
    ast_manager & m = s.m();
    model_converter_ref mc;
    try {
        exec(st, s, mc);
    }
    catch (strategy_exception & ex) {
        reason_unknown = ex.msg();
        return l_undef;
    }
    if (s.size() == 0) {
        if (mc) {
            TRACE("check_sat_model", tout << "model-converter:\n"; mc->display(tout);); 
            md = alloc(model, m);
            (*mc)(md);
            TRACE("check_sat_model", tout << "model:\n"; model_v2_pp(tout, *md););
        }
        return l_true;
    }
    if (s.size() == 1 && m.is_false(s.form(0))) {
        pr = s.pr(0);
        return l_false;
    }
    if (mc) {
        md = alloc(model, m);
        (*mc)(md);
    }
    reason_unknown = "incomplete";
    return l_undef;
}
