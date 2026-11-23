/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactical.h

Abstract:

    Basic combinators

Author:

    Leonardo (leonardo) 2011-10-13

Notes:

--*/
#include "util/scoped_timer.h"
#include "util/cancel_eh.h"
#include "util/scoped_ptr_vector.h"
#include "util/gparams.h"
#include "tactic/tactical.h"
#include "tactic/goal_proof_converter.h"
#ifndef SINGLE_THREAD
#include <thread>
#endif
#include <vector>
#include <cstring>
#include <sstream>

// Display a probe with the parameters params it receives; a comment says why the display
// does not parse, if it does not. With annotate, the comment also lists the
// parameters the probe reads (a parameter probe is displayed as its value).
static std::string display_probe(probe const & p, params_ref const & params, bool annotate, std::string & comment) {
    std::ostringstream out;
    std::string notes, problems;
    p.display_with(out, params, annotate ? &notes : nullptr, problems);
    if (!problems.empty())
        comment = "not parseable: " + problems;
    if (!notes.empty())
        comment += (comment.empty() ? "" : "; ") + ("probe: " + notes);
    return out.str();
}

class binary_tactical : public tactic {
protected:
    tactic_ref      m_t1;
    tactic_ref      m_t2;
    bool            m_clean = true;
    
public:

    binary_tactical(tactic * t1, tactic * t2):
        m_t1(t1),
        m_t2(t2) {
        SASSERT(m_t1);
        SASSERT(m_t2);
    }
    
    void updt_params(params_ref const & p) override {
        m_t1->updt_params(p);
        m_t2->updt_params(p);
    }
    
    void collect_param_descrs(param_descrs & r) override {
        m_t1->collect_param_descrs(r);
        m_t2->collect_param_descrs(r);
    }

    void collect_statistics(statistics & st) const override {
        m_t1->collect_statistics(st);
        m_t2->collect_statistics(st);
    }

    void reset_statistics() override { 
        m_t1->reset_statistics();
        m_t2->reset_statistics();
    }
        
    void cleanup() override {
        if (m_clean)
            return;
        m_t1->cleanup();
        m_t2->cleanup();
        m_clean = true;
    }
    
    void reset() override {
        m_t1->reset();
        m_t2->reset();
    }

    void set_logic(symbol const & l) override {
        m_t1->set_logic(l);
        m_t2->set_logic(l);
    }

    void set_progress_callback(progress_callback * callback) override {
        m_t1->set_progress_callback(callback);
        m_t2->set_progress_callback(callback);
    }

protected:


    template<typename T>
    tactic * translate_core(ast_manager & m) { 
        tactic * new_t1 = m_t1->translate(m);
        tactic * new_t2 = m_t2->translate(m);
        return alloc(T, new_t1, new_t2);
    }
};

struct false_pred {
    bool operator()(goal * g) { return false; }
};



class and_then_tactical : public binary_tactical {
public:
    and_then_tactical(tactic * t1, tactic * t2):binary_tactical(t1, t2) {}

    char const* name() const override { return "and_then"; }

    // tactic_display_ctx::close displays and_then(t1, and_then(t2, t3)) as (then t1 t2 t3).
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        ctx.open(strcmp(name(), "par_then") == 0 ? "(par-then" : "(then");
        m_t1->display_pipeline(p, ctx);
        m_t2->display_pipeline(p, ctx);
        ctx.close();
    }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        m_clean = false;

        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                         
        goal_ref_buffer r1;
        m_t1->operator()(in, r1);
        unsigned r1_size = r1.size();                                                                       
        SASSERT(r1_size > 0);  
        if (r1_size == 1) {                                                                                 
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);
                return;
            }                                                                                               
            goal_ref r1_0 = r1[0];      
            m_t2->operator()(r1_0, result);
        }
        else {
            goal_ref_buffer r2;
            for (unsigned i = 0; i < r1_size; ++i) {                                                        
                goal_ref g = r1[i];                                                                       
                r2.reset();
                if (g->is_decided())
                    r2.push_back(g.get());
                else
                    m_t2->operator()(g, r2);
                if (is_decided(r2)) {
                    SASSERT(r2.size() == 1);
                    if (is_decided_sat(r2)) {                                                          
                        if (in->keep_sat_subgoals()) {
                            result.push_back(r2[0]);
                            continue;
                        }
                        // found solution...                                                           
                        result.reset();
                        result.push_back(r2[0]);
                        return;
                    }                                                                                   
                    else {                                                                                  
                        SASSERT(is_decided_unsat(r2));                                                 
                    }                                                                         
                }                                                                                       
                else {                                                                                      
                    result.append(r2.size(), r2.data());
                }                                                                                           
            }
                        
            if (result.empty()) {                                                                           
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                expr_dependency_ref core(m);
                if (proofs_enabled) {
                    pr = apply(m, in->pc());
                    in->set(static_cast<proof_converter*>(nullptr));
                }
                dependency_converter* dc = in->dc();
                if (cores_enabled && dc) {
                    core = (*dc)();
                }
                in->assert_expr(m.mk_false(), pr, core);
                result.push_back(in.get());
            }
        }
    }

    tactic * translate(ast_manager & m) override {
        return translate_core<and_then_tactical>(m);
    }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        m_t2->register_on_clause(ctx, on_clause);
    }

    void user_propagate_init(
        void* ctx,
        user_propagator::push_eh_t& push_eh,
        user_propagator::pop_eh_t& pop_eh,
        user_propagator::fresh_eh_t& fresh_eh) override {
        m_t2->user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }

    void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) override {
        m_t2->user_propagate_register_fixed(fixed_eh);
    }

    void user_propagate_register_final(user_propagator::final_eh_t& final_eh) override {
        m_t2->user_propagate_register_final(final_eh);
    }

    void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) override {
        m_t2->user_propagate_register_eq(eq_eh);
    }

    void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) override {
        m_t2->user_propagate_register_diseq(diseq_eh);
    }

    void user_propagate_register_on_binding(user_propagator::binding_eh_t& binding_eh) override {
        m_t2->user_propagate_register_on_binding(binding_eh);
    }

    void user_propagate_register_expr(expr* e) override {
        m_t1->user_propagate_register_expr(e);
        m_t2->user_propagate_register_expr(e);
    }

    void user_propagate_clear() override {
        m_t1->user_propagate_clear();
        m_t2->user_propagate_clear();
    }

    void user_propagate_register_created(user_propagator::created_eh_t& created_eh) override {
        m_t2->user_propagate_register_created(created_eh);
    }

    void user_propagate_register_decide(user_propagator::decide_eh_t& decide_eh) override {
        m_t2->user_propagate_register_decide(decide_eh);
    }

    void user_propagate_initialize_value(expr* var, expr* value) override {
        m_t2->user_propagate_initialize_value(var, value);
    }

};

tactic * and_then(tactic * t1, tactic * t2) {
    return alloc(and_then_tactical, t1, t2);
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3) {
    return and_then(t1, and_then(t2, t3));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4) {
    return and_then(t1, and_then(t2, t3, t4));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5) {
    return and_then(t1, and_then(t2, t3, t4, t5));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6) {
    return and_then(t1, and_then(t2, t3, t4, t5, t6));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7) {
    return and_then(t1, and_then(t2, t3, t4, t5, t6, t7));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8) {
    return and_then(t1, and_then(t2, t3, t4, t5, t6, t7, t8));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9) {
    return and_then(t1, and_then(t2, t3, t4, t5, t6, t7, t8, t9));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9, tactic * t10) {
    return and_then(t1, and_then(t2, t3, t4, t5, t6, t7, t8, t9, t10));
}

tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9, tactic * t10, tactic * t11) {
    return and_then(t1, and_then(t2, t3, t4, t5, t6, t7, t8, t9, t10, t11));
}

tactic * and_then(unsigned num, tactic * const * ts) {
    SASSERT(num > 0);
    unsigned i = num - 1;
    tactic * r = ts[i];
    while (i > 0) {
        --i;
        r = and_then(ts[i], r);
    }
    return r;
}

class nary_tactical : public tactic {
protected:
    sref_vector<tactic> m_ts;

public:
    nary_tactical(unsigned num, tactic * const * ts) {
        for (unsigned i = 0; i < num; ++i) {
            SASSERT(ts[i]);
            m_ts.push_back(ts[i]);
        }
    }

    void updt_params(params_ref const & p) override {
        TRACE(nary_tactical_updt_params, tout << "updt_params: " << p << "\n";);
        for (tactic* t : m_ts) t->updt_params(p);
    }
    
    void collect_param_descrs(param_descrs & r) override {
        for (tactic* t : m_ts) t->collect_param_descrs(r);
    }

    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        ctx.open(strcmp(name(), "par") == 0 ? "(par-or" : "(or-else");
        for (tactic* t : m_ts) t->display_pipeline(p, ctx);
        ctx.close();
    }
    
    void collect_statistics(statistics & st) const override {
        for (tactic const* t : m_ts) t->collect_statistics(st);
    }

    void reset_statistics() override { 
        for (tactic* t : m_ts) t->reset_statistics();
    }
        
    void cleanup() override {
        for (tactic* t : m_ts) t->cleanup();
    }
    
    void reset() override {
        for (tactic* t : m_ts) t->reset();
    }

    void set_logic(symbol const & l) override {
        for (tactic* t : m_ts) t->set_logic(l);
    }

    void set_progress_callback(progress_callback * callback) override {
        for (tactic* t : m_ts) t->set_progress_callback(callback);
    }

protected:

    template<typename T>
    tactic * translate_core(ast_manager & m) { 
        sref_vector<tactic> new_ts;
        for (tactic* curr : m_ts) {
            new_ts.push_back(curr->translate(m));
        }
        return alloc(T, new_ts.size(), new_ts.data());
    }

};

class or_else_tactical : public nary_tactical {
public:
    or_else_tactical(unsigned num, tactic * const * ts):nary_tactical(num, ts) { SASSERT(num > 0); }

    char const* name() const override { return "or_else"; }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        goal orig(*(in.get()));
        unsigned sz = m_ts.size();
        unsigned i;
        for (i = 0; i < sz; ++i) {
            tactic * t = m_ts[i];
            SASSERT(sz > 0);
            if (i < sz - 1) {
                try {
                    t->operator()(in, result);
                    return;
                }
                catch (tactic_exception &) {
                    result.reset();
                }
                catch (rewriter_exception&) {
                    result.reset();
                }
                catch (z3_error & ex) {
                    IF_VERBOSE(10, verbose_stream() << "z3 error: " << ex.error_code() << " in or-else\n");
                    throw;
                }
                catch (z3_exception& ex) {
                    IF_VERBOSE(10, verbose_stream() << ex.what() << " in or-else\n");
                    throw;
                }
                catch (const std::exception &ex) {
                    IF_VERBOSE(10, verbose_stream() << ex.what() << " in or-else\n");
                    throw;
                }
                catch (...) {
                    IF_VERBOSE(10, verbose_stream() << " unclassified exception in or-else\n");
                    // std::current_exception returns a std::exception_ptr, which apparently 
                    // needs to be re-thrown to extract type information.
                    // typeid(ex).name() would be nice.
                    throw;
                }
            }
            else {
                t->operator()(in, result);
                return;
            }
            in->reset_all();
            in->copy_from(orig);
        }
    }

    tactic * translate(ast_manager & m) override { return translate_core<or_else_tactical>(m); }

    void user_propagate_initialize_value(expr* var, expr* value) override {
        for (auto t : m_ts)
            t->user_propagate_initialize_value(var, value);
    }

};

tactic * or_else(unsigned num, tactic * const * ts) {
    return alloc(or_else_tactical, num, ts);
}

tactic * or_else(tactic * t1, tactic * t2) {
    tactic * ts[2] = { t1, t2 };
    return or_else(2, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3) {
    tactic * ts[3] = { t1, t2, t3 };
    return or_else(3, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4) {
    tactic * ts[4] = { t1, t2, t3, t4 };
    return or_else(4, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5) {
    tactic * ts[5] = { t1, t2, t3, t4, t5 };
    return or_else(5, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6) {
    tactic * ts[6] = { t1, t2, t3, t4, t5, t6 };
    return or_else(6, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7) {
    tactic * ts[7] = { t1, t2, t3, t4, t5, t6, t7 };
    return or_else(7, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8) {
    tactic * ts[8] = { t1, t2, t3, t4, t5, t6, t7, t8 };
    return or_else(8, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9) {
    tactic * ts[9] = { t1, t2, t3, t4, t5, t6, t7, t8, t9 };
    return or_else(9, ts);
}

tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9, tactic * t10) {
    tactic * ts[10] = { t1, t2, t3, t4, t5, t6, t7, t8, t9, t10 };
    return or_else(10, ts);
}

#ifdef SINGLE_THREAD

tactic* par(unsigned num, tactic* const* ts) {
    return alloc(or_else_tactical, num, ts);
}

#else

enum par_exception_kind {
    TACTIC_EX,
    DEFAULT_EX,
    ERROR_EX
};

class par_tactical : public or_else_tactical {

	std::string        ex_msg;
	unsigned           error_code;

public:
    par_tactical(unsigned num, tactic * const * ts):or_else_tactical(num, ts) {
		error_code = 0;
	}

    char const* name() const override { return "par"; }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        bool use_seq;
        use_seq = false;
        if (use_seq) {
            // execute tasks sequentially
            or_else_tactical::operator()(in, result);
            return;
        }
        
        ast_manager & m = in->m();
        
        if (m.has_trace_stream())
            throw default_exception("threads and trace are incompatible");

        scoped_ptr_vector<ast_manager> managers;
        scoped_limits scl(m.limit());
        goal_ref_vector                in_copies;
        tactic_ref_vector              ts;
        unsigned sz = m_ts.size();
        for (unsigned i = 0; i < sz; ++i) {
            ast_manager * new_m = alloc(ast_manager, m, !m.proof_mode());
            managers.push_back(new_m);
            ast_translation translator(m, *new_m);
            in_copies.push_back(in->translate(translator));
            ts.push_back(m_ts.get(i)->translate(*new_m));
            scl.push_child(&new_m->limit());
        }

        unsigned finished_id       = UINT_MAX;
        par_exception_kind ex_kind = DEFAULT_EX;

        std::mutex         mux;

        auto worker_thread = [&](unsigned i) {
            goal_ref_buffer     _result;                        
            goal_ref in_copy = in_copies[i];
            tactic & t = *(ts.get(i));
            
            try {
                t(in_copy, _result);
                bool first = false;
                {
                    std::lock_guard<std::mutex> lock(mux);
                    if (finished_id == UINT_MAX) {
                        finished_id = i;
                        first = true;
                    }
                }                
                if (first) {
                    for (unsigned j = 0; j < sz; ++j) {
                        if (i != j) {
                            managers[j]->limit().cancel();
                        }
                    }
                    
                    ast_translation translator(*(managers[i]), m, false);
                    for (goal* g : _result) {
                        result.push_back(g->translate(translator));
                    }
                    goal_ref in2(in_copy->translate(translator));
                    in->copy_from(*(in2.get()));
                }
            }
            catch (tactic_exception & ex) {
                if (i == 0) {
                    ex_kind = TACTIC_EX;
                    ex_msg = ex.what();
                }
            }
            catch (z3_error & err) {
                if (i == 0) {
                    ex_kind = ERROR_EX;
                    error_code = err.error_code();
                }
            }
            catch (z3_exception & z3_ex) {
                if (i == 0) {
                    ex_kind = DEFAULT_EX;
                    ex_msg = z3_ex.what();
                }
            }
        };

        vector<std::thread> threads(sz);

        for (unsigned i = 0; i < sz; ++i) {
            threads[i] = std::thread([&, i]() { worker_thread(i); });
        }
        for (unsigned i = 0; i < sz; ++i) {
            threads[i].join();
        }
        
        if (finished_id == UINT_MAX) {
            switch (ex_kind) {
            case ERROR_EX: throw z3_error(error_code);
            case TACTIC_EX: throw tactic_exception(std::move(ex_msg));
            default:
                throw default_exception(std::move(ex_msg));
            }
        }
    }    

    tactic * translate(ast_manager & m) override { return translate_core<par_tactical>(m); }
};

tactic * par(unsigned num, tactic * const * ts) {
    return alloc(par_tactical, num, ts);
}

#endif

tactic * par(tactic * t1, tactic * t2) {
    tactic * ts[2] = { t1, t2 };
    return par(2, ts);
}

tactic * par(tactic * t1, tactic * t2, tactic * t3) {
    tactic * ts[3] = { t1, t2, t3 };
    return par(3, ts);
}

tactic * par(tactic * t1, tactic * t2, tactic * t3, tactic * t4) {
    tactic * ts[4] = { t1, t2, t3, t4 };
    return par(4, ts);
}


#ifdef SINGLE_THREAD

tactic * par_and_then(tactic * t1, tactic * t2) {
    return alloc(and_then_tactical, t1, t2);
}

#else
class par_and_then_tactical : public and_then_tactical {
public:
    par_and_then_tactical(tactic * t1, tactic * t2):and_then_tactical(t1, t2) {}

    char const* name() const override { return "par_then"; }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        bool use_seq;
        use_seq = false;
        if (use_seq) {
            // execute tasks sequentially
            and_then_tactical::operator()(in, result);
            return;
        }

        // enabling proofs is possible, but requires translating subgoals back.
        fail_if_proof_generation("par_and_then", in);
        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                          
        goal_ref_buffer r1;
        m_t1->operator()(in, r1);                
        unsigned r1_size = r1.size();                                                                               
        SASSERT(r1_size > 0);                                                                               
        if (r1_size == 1) {                                                                                 
            // Only one subgoal created... no need for parallelism
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);
                return;
            }                                                                                               
            goal_ref r1_0 = r1[0];                                                                          
            m_t2->operator()(r1_0, result);
        }                                                                                     
        else {                                                                                              

            scoped_ptr_vector<ast_manager> managers;
            scoped_limits scl(m.limit());
            tactic_ref_vector              ts2;
            goal_ref_vector                g_copies;

            for (unsigned i = 0; i < r1_size; ++i) {
                ast_manager * new_m = alloc(ast_manager, m, !m.proof_mode());
                managers.push_back(new_m);
                ast_translation translator(m, *new_m);
                g_copies.push_back(r1[i]->translate(translator));
                ts2.push_back(m_t2->translate(*new_m));
                scl.push_child(&new_m->limit());
            }

            scoped_ptr_vector<expr_dependency_ref> core_buffer;
            scoped_ptr_vector<goal_ref_buffer>     goals_vect;

            core_buffer.resize(r1_size);
            goals_vect.resize(r1_size);

            bool found_solution = false;
            bool failed         = false;
            par_exception_kind ex_kind = DEFAULT_EX;
            unsigned error_code = 0;
            std::string  ex_msg;
            std::mutex mux;

            auto worker_thread = [&](unsigned i) {
                ast_manager & new_m = *(managers[i]);
                goal_ref new_g = g_copies[i];

                goal_ref_buffer r2;
                
                bool curr_failed = false;

                try {
                    if (in->keep_sat_subgoals() && new_g->is_decided())
                        r2.push_back(new_g.get());
                    else
                        ts2[i]->operator()(new_g, r2);
                }
                catch (tactic_exception & ex) {
                    {
                        std::lock_guard<std::mutex> lock(mux);
                        if (!failed && !found_solution) {
                            curr_failed = true;
                            failed      = true;
                            ex_kind     = TACTIC_EX;
                            ex_msg      = ex.what();
                        }
                    }
                }
                catch (z3_error & err) {
                    {
                        std::lock_guard<std::mutex> lock(mux);
                        if (!failed && !found_solution) {
                            curr_failed = true;
                            failed      = true;
                            ex_kind     = ERROR_EX;
                            error_code  = err.error_code();
                        }
                    }                    
                }
                catch (z3_exception & z3_ex) {
                    {
                        std::lock_guard<std::mutex> lock(mux);
                        if (!failed && !found_solution) {
                            curr_failed = true;
                            failed      = true;
                            ex_kind     = DEFAULT_EX;
                            ex_msg      = z3_ex.what();
                        }
                    }
                }

                if (curr_failed) {
                    for (unsigned j = 0; j < r1_size; ++j) {
                        if (static_cast<unsigned>(i) != j) {
                            managers[j]->limit().cancel();
                        }
                    }
                }
                else {
                    if (is_decided(r2)) {
                        SASSERT(r2.size() == 1);
                        if (is_decided_sat(r2) && in->keep_sat_subgoals()) {
                            goal_ref_buffer * new_r2 = alloc(goal_ref_buffer);
                            goals_vect.set(i, new_r2);
                            new_r2->push_back(r2[0]);
                        }
                        else if (is_decided_sat(r2)) {
                            // found solution... 
                            bool first = false;
                            {
                                std::lock_guard<std::mutex> lock(mux);
                                if (!found_solution) {
                                    failed         = false;
                                    found_solution = true;
                                    first          = true;
                                }
                            }
                            if (first) {
                                for (unsigned j = 0; j < r1_size; ++j) {
                                    if (static_cast<unsigned>(i) != j) {
                                        managers[j]->limit().cancel();
                                    }
                                }
                                ast_translation translator(new_m, m, false);
                                SASSERT(r2.size() == 1);
                                result.push_back(r2[0]->translate(translator));                                
                            }       
                        }                                                     
                        else {                                                                                  
                            SASSERT(is_decided_unsat(r2));                                                 
                            
                            if (cores_enabled && r2[0]->dep(0) != nullptr) {
                                expr_dependency_ref * new_dep = alloc(expr_dependency_ref, new_m);
                                *new_dep = r2[0]->dep(0);
                                core_buffer.set(i, new_dep);
                            }
                        }                                                                 
                    }                                                                                       
                    else {                                                                                      
                        goal_ref_buffer * new_r2 = alloc(goal_ref_buffer);
                        goals_vect.set(i, new_r2);
                        new_r2->append(r2.size(), r2.data());
                        dependency_converter* dc = r1[i]->dc();                           
                        if (cores_enabled && dc) {
                            expr_dependency_ref * new_dep = alloc(expr_dependency_ref, new_m);
                            *new_dep = (*dc)();
                            core_buffer.set(i, new_dep);
                        }
                    }                                                                                           
                }
            };

            if (m.has_trace_stream())
                throw default_exception("threads and trace are incompatible");

            vector<std::thread> threads(r1_size);
            for (unsigned i = 0; i < r1_size; ++i) {
                threads[i] = std::thread([&, i]() { worker_thread(i); });
            }
            for (unsigned i = 0; i < r1_size; ++i) {
                threads[i].join();
            }
            
            if (failed) {
                switch (ex_kind) {
                case ERROR_EX: throw z3_error(error_code);
                case TACTIC_EX: throw tactic_exception(std::move(ex_msg));
                default:
                    throw default_exception(std::move(ex_msg));
                }
            }

            if (found_solution)
                return;
            
            expr_dependency_ref core(m);
            for (unsigned i = 0; i < r1_size; ++i) {
                ast_translation translator(*(managers[i]), m, false);
                goal_ref_buffer * r = goals_vect[i];
                unsigned j = result.size();
                if (r != nullptr) {
                    for (unsigned k = 0; k < r->size(); ++k) {
                        result.push_back((*r)[k]->translate(translator));
                    }
                }
                if (proofs_enabled) {
                    // update proof converter of r1[i]
                    r1[i]->set(concat(r1[i]->pc(), result.size() - j, result.data() + j));
                }
                expr_dependency_translation td(translator);
                if (core_buffer[i] != nullptr) {
                    expr_dependency_ref curr_core(m);
                    curr_core = td(*(core_buffer[i]));
                    core = m.mk_join(curr_core, core);
                }
            }
            if (core) {
                in->add(dependency_converter::unit(core));
            }

            if (result.empty()) {
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                if (proofs_enabled) {
                    pr = apply(m, in->pc());
                    in->set(static_cast<proof_converter*>(nullptr));
                }
                dependency_converter* dc = in->dc();
                if (cores_enabled && dc) {
                    core = (*dc)();
                }
                in->assert_expr(m.mk_false(), pr, core);
                result.push_back(in.get());
            }
        }
    }

    tactic * translate(ast_manager & m) override {
        return translate_core<and_then_tactical>(m);
    }

};

// Similar to and_then combinator, but t2 is applied in parallel to all subgoals produced by t1
tactic * par_and_then(tactic * t1, tactic * t2) {
    return alloc(par_and_then_tactical, t1, t2);
}
#endif

tactic * par_and_then(unsigned num, tactic * const * ts) {
    unsigned i = num - 1;
    tactic * r = ts[i];
    while (i > 0) {
        --i;
        r = par_and_then(ts[i], r);
    }
    return r;
}

class unary_tactical : public tactic {
protected:
    tactic_ref m_t;
    bool m_clean = true;


public:
    unary_tactical(tactic * t): 
        m_t(t) {
        SASSERT(t);  
    }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        m_clean = false;
        m_t->operator()(in, result);
    }
   
    void cleanup(void) override { if (!m_clean) m_t->cleanup(); m_clean = true; }
    void collect_statistics(statistics & st) const override { m_t->collect_statistics(st); }
    void reset_statistics() override { m_t->reset_statistics(); }    
    void updt_params(params_ref const & p) override { m_t->updt_params(p); }
    void collect_param_descrs(param_descrs & r) override { m_t->collect_param_descrs(r); }
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        char const * n = language_name();
        if (n)
            ctx.open(std::string("(") + n);
        else
            ctx.open(std::string("(") + name() + (display_tail().empty() ? "" : " " + display_tail()),
                     std::string("not parseable: ") + name());
        m_t->display_pipeline(p, ctx);
        ctx.close(n ? display_tail() : std::string());
    }
    // name of the combinator in the tactic language, nullptr if it has none
    virtual char const * language_name() const { return nullptr; }
    // arguments of the combinator displayed after the tactic it wraps: "5"
    virtual std::string display_tail() const { return std::string(); }
    void reset() override { m_t->reset(); }
    void set_logic(symbol const& l) override { m_t->set_logic(l); }    
    void set_progress_callback(progress_callback * callback) override { m_t->set_progress_callback(callback); }
    void user_propagate_register_expr(expr* e) override { m_t->user_propagate_register_expr(e); }
    void user_propagate_clear() override { m_t->user_propagate_clear(); }
    void user_propagate_initialize_value(expr* var, expr* value) override { m_t->user_propagate_initialize_value(var, value); }

protected:

    template<typename T>
    tactic * translate_core(ast_manager & m) { 
        tactic * new_t = m_t->translate(m);
        return alloc(T, new_t);
    }
};

class repeat_tactical : public unary_tactical {
    unsigned m_max_depth;
    
    void operator()(unsigned depth,
                    goal_ref const & in, 
                    goal_ref_buffer& result) {

        bool models_enabled = in->models_enabled();
        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                          
        goal_ref_buffer      r1;  
        goal_ref g = in;
        unsigned r1_size = 0;
        result.reset();      
    try_goal:
        r1.reset();
        if (depth > m_max_depth || (in->keep_sat_subgoals() && g->is_decided())) {
            result.push_back(g.get());
            return;
        }
        {
            goal orig_in(g->m(), proofs_enabled, models_enabled, cores_enabled);
            orig_in.copy_from(*(g.get()));
            m_t->operator()(g, r1);                                                            
            if (r1.size() == 1 && is_equal(orig_in, *(r1[0]))) {
                result.push_back(r1[0]);
                return;                                                                                     
            }
        }
        r1_size = r1.size();                                                                       
        SASSERT(r1_size > 0);    
        if (r1_size == 1) {                                                                                 
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);  
                return;                                                                                     
            }                          
            g = r1[0];   
            depth++;
            goto try_goal;
        }                      

		goal_ref_buffer            r2;
		for (unsigned i = 0; i < r1_size; ++i) {
			goal_ref g = r1[i];
			r2.reset();
			operator()(depth + 1, g, r2);
			if (is_decided(r2)) {
				SASSERT(r2.size() == 1);
				if (is_decided_sat(r2)) {
					if (!in->keep_sat_subgoals()) {
						result.reset();
						result.push_back(r2[0]);
						return;
					}
					result.push_back(r2[0]);
				}
				else {
					SASSERT(is_decided_unsat(r2));
				}
			}
			else {
				result.append(r2.size(), r2.data());
			}
		}

		if (result.empty()) {
			// all subgoals were shown to be unsat.                                                     
			// create an decided_unsat goal with the proof
			g->reset_all();
			proof_ref pr(m);
			expr_dependency_ref core(m);
			if (proofs_enabled) {
				pr = apply(m, g->pc());
				g->set(static_cast<proof_converter*>(nullptr));
			}
			if (cores_enabled && g->dc()) {
				core = (*g->dc())();
			}
			g->assert_expr(m.mk_false(), pr, core);
			result.push_back(g.get());
		}
    }

public:
    repeat_tactical(tactic * t, unsigned max_depth):
        unary_tactical(t), 
        m_max_depth(max_depth) {
    }

    char const* name() const override { return "repeat"; }

    char const * language_name() const override { return "repeat"; }
    std::string display_tail() const override {
        return m_max_depth == UINT_MAX ? std::string() : std::to_string(m_max_depth);
    }
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        operator()(0, in, result);
    }

    tactic * translate(ast_manager & m) override { 
        tactic * new_t = m_t->translate(m);
        return alloc(repeat_tactical, new_t, m_max_depth);
    }
};

tactic * repeat(tactic * t, unsigned max) {
    return alloc(repeat_tactical, t, max);
}

class fail_if_branching_tactical : public unary_tactical {
    unsigned m_threshold;
public:
    fail_if_branching_tactical(tactic * t, unsigned threshold):unary_tactical(t), m_threshold(threshold) {}

    char const* name() const override { return "fail_if_branching"; }

    char const * language_name() const override { return "fail-if-branching"; }
    std::string display_tail() const override { return std::to_string(m_threshold); }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        m_t->operator()(in, result);
        if (result.size() > m_threshold) {
            result.reset(); // assumes in is not strenthened to one of the branches
            throw tactic_exception("failed-if-branching tactical");
        }
    }    

    tactic * translate(ast_manager & m) override { 
        tactic * new_t = m_t->translate(m);
        return alloc(fail_if_branching_tactical, new_t, m_threshold);
    }
};

tactic * fail_if_branching(tactic * t, unsigned threshold) {
    return alloc(fail_if_branching_tactical, t, threshold);
}

class cleanup_tactical : public unary_tactical {
public:
    cleanup_tactical(tactic * t):unary_tactical(t) {}

    char const* name() const override { return "cleanup"; }

    // cleanup does not change what runs: display the tactic it wraps
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        m_t->display_pipeline(p, ctx);
    }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        m_t->operator()(in, result);
        m_t->cleanup();
    }    

    tactic * translate(ast_manager & m) override { 
        tactic * new_t = m_t->translate(m);
        return alloc(cleanup_tactical, new_t);
    }
};

tactic * clean(tactic * t) {
    return alloc(cleanup_tactical, t);
}

class try_for_tactical : public unary_tactical {
    unsigned m_timeout;
public:
    try_for_tactical(tactic * t, unsigned ts):unary_tactical(t), m_timeout(ts) {}

    char const* name() const override { return "try_for"; }

    char const * language_name() const override { return "try-for"; }
    std::string display_tail() const override { return std::to_string(m_timeout); }
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        cancel_eh<reslimit> eh(in->m().limit());
        { 
            scoped_timer timer(m_timeout, &eh);
            try {
                m_t->operator()(in, result);
            } catch (z3_error &ex) {
                throw ex;
            } catch (tactic_exception &) {
                throw;
            } catch (z3_exception &ex) {
                // convert all Z3 exceptions into tactic exceptions.
                throw tactic_exception(ex.what());
            }
        }
    }

    tactic * translate(ast_manager & m) override { 
        tactic * new_t = m_t->translate(m);
        return alloc(try_for_tactical, new_t, m_timeout);
    }
};

tactic * try_for(tactic * t, unsigned msecs) {
    return alloc(try_for_tactical, t, msecs);
}

// the parser of using-params accepts k for a tactic that declares d
static bool tactic_param_has_syntax(param_descrs const & d, symbol k) {
    switch (d.get_kind_in_module(k)) {
    case CPK_BOOL: case CPK_UINT: case CPK_NUMERAL: case CPK_SYMBOL: case CPK_DOUBLE:
        return true;
    default:
        return false;
    }
}

class using_params_tactical : public unary_tactical {
    params_ref m_params;
public:
    using_params_tactical(tactic * t, params_ref const & p):unary_tactical(t), m_params(p) {
        t->updt_params(p);
    }

    char const* name() const override { return "using_params"; }

    // Display (using-params t :k v ...) and t with the parameters updt_params passes to it.
    //
    // A key is written as syntax if the parser accepts it: the parser of using-params
    // requires that t declares the key in collect_param_descrs. Other keys go in a
    // "not parseable:" comment. A default (flagged) value is written like the others;
    // with ctx.annotate it is also listed in the comment, marked "(default)".
    //
    // A parameter set here is [unused] if no tactic of the pipeline declares it.
    // It is not checked if it is passed on unchanged from p: it is checked where it is set.
    // Checking against the tactics below instead of the whole pipeline would flag
    // the idiom q = p; q.set_*(...); using_params(t, q): q carries every key of the
    // factory parameters p, which are meant for other steps.
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        if (m_params.size() == 0) {
            m_t->display_pipeline(p, ctx);
            return;
        }
        params_ref new_p = p;
        merge(new_p);
        // the child first: the scopes in it declare the keys they route
        // A key is written as syntax if a displayed step declares it: the parser checks
        // it against the tactic the output parses to. If a key is declared only by
        // disabled steps, it is still written, and t is displayed again with its disabled
        // steps as (when 0 t'), which declare it (see below).
        ctx.open("(using-params");
        ctx.push_frame();
        m_t->display_pipeline(new_p, ctx);
        param_descrs shown, child;
        ctx.pop_frame(shown);
        m_t->collect_param_descrs(child);
        // If a key is declared only by disabled steps, displayed as skip, display t again
        // with them as (when 0 t'): writing the key needs a step that declares it, and
        // leaving it out would change what the displayed steps receive (they may read
        // keys they do not declare, as solve-eqs passes its parameters to its rewriter).
        // ctx.keep_disabled applies to every disabled scope in t, also those whose keys
        // are not needed: (when 0 t') is then shown where skip would do. That is correct,
        // only longer.
        if (!ctx.keep_disabled) {
            bool needed = false;
            for (unsigned i = 0; !needed && i < m_params.size(); ++i) {
                symbol k = m_params.get_key(i);
                needed = !declares(ctx.scope_keys, k) && !tactic_param_has_syntax(shown, k) && tactic_param_has_syntax(child, k);
            }
            if (needed) {
                ctx.drop_last();
                ctx.keep_disabled = true;
                ctx.push_frame();
                m_t->display_pipeline(new_p, ctx);
                param_descrs shown2;
                ctx.pop_frame(shown2);
                ctx.keep_disabled = false;
                shown.copy(shown2);
            }
        }
        std::string tail, comment, scoped, skipped;
        for (unsigned i = 0; i < m_params.size(); ++i) {
            symbol k = m_params.get_key(i);
            std::ostringstream v;
            m_params.display(v, k);
            // A default is written with the value it has for t: the value that replaces
            // it, if any. The tactic language has no defaults, so a default written as is
            // would replace that value when the output is run.
            char const * mark = "";
            std::string value = v.str();
            if (m_params.is_default(k)) {
                std::ostringstream w;
                if (!new_p.is_default(k))
                    new_p.display(w, k);
                else {
                    char const * module = child.get_module(k);
                    params_ref g = module ? gparams::get_module(module) : params_ref();
                    if (g.contains(k)) {
                        g.display(w, k);
                        mark = " (global)";
                    }
                    else {
                        new_p.display(w, k);
                        mark = " (default)";
                    }
                }
                value = w.str();
            }
            std::string entry = ":" + std::string(k.str()) + " " + value;
            // A key that a scope routes: the scope writes its effect on the step.
            if (declares(ctx.scope_keys, k)) {
                if (ctx.annotate)
                    scoped += (scoped.empty() ? "scoped: " : ", ") + entry;
                continue;
            }
            bool unused = ctx.pipeline && !declares(*ctx.pipeline, k) && !is_inherited(p, k, v.str());
            if (unused && ctx.unused && !ctx.unused->contains(k))
                ctx.unused->push_back(k);
            std::string note;
            // After the redisplay, disabled scopes declare their keys. This is reached only
            // if t declares k in collect_param_descrs but no displayed step declares it
            // (a tactic whose display does not declare what it collects): the key is left
            // out, since the output would not parse with it.
            if (!tactic_param_has_syntax(shown, k) && tactic_param_has_syntax(child, k)) {
                if (ctx.annotate)
                    skipped += (skipped.empty() ? "for skipped steps: " : ", ") + entry;
                continue;
            }
            if (!tactic_param_has_syntax(shown, k))
                note = entry + (unused ? " [unused]" : "");
            else {
                tail += (tail.empty() ? "" : " ") + entry;
                if (ctx.annotate && m_params.is_default(k) && *mark)
                    note = entry + mark;
            }
            if (!note.empty())
                comment += (comment.empty() ? "not parseable: " : ", ") + note;
        }
        std::string c;
        for (std::string const * x : { &scoped, &skipped, &comment })
            if (!x->empty())
                c += (c.empty() ? "" : "; ") + *x;
        ctx.close(tail, c);
    }

    // Append m_params to new_p. A key that m_params sets unflagged is no longer a value
    // that an enclosing scope took from a global scoped key: clear its mark, so that an
    // inner scope sees it as local (see scope_global_mark).
    void merge(params_ref & new_p) const {
        new_p.append(m_params);
        for (unsigned i = 0; i < m_params.size(); ++i) {
            symbol k = m_params.get_key(i);
            if (m_params.is_default(k))
                continue;
            symbol mark = scope_global_mark(k);
            // new_p holds a mark only if it does not share its entries with m_params:
            // params_ref::reset does not copy on write.
            if (new_p.contains(mark))
                new_p.reset(mark);
        }
    }

    static bool declares(param_descrs const & d, symbol k) {
        return d.get_kind_in_module(k) != CPK_INVALID;
    }

    static bool is_inherited(params_ref const & p, symbol const & k, std::string const & v) {
        if (!p.contains(k))
            return false;
        std::ostringstream w;
        p.display(w, k);
        return w.str() == v;
    }

    void updt_params(params_ref const & p) override {
        TRACE(using_params, 
              tout << "before p: " << p << "\n";
              tout << "m_params: " << m_params << "\n";);
        
        params_ref new_p = p;
        merge(new_p);
        unary_tactical::updt_params(new_p);
        
        TRACE(using_params, 
              tout << "after p: " << p << "\n";
              tout << "m_params: " << m_params << "\n";
              tout << "new_p: " << new_p << "\n";);
    }

    tactic * translate(ast_manager & m) override { 
        tactic * new_t = m_t->translate(m);
        return alloc(using_params_tactical, new_t, m_params);
    }
};

tactic * using_params(tactic * t, params_ref const & p) {
    return alloc(using_params_tactical, t, p);
}

class annotate_tactical : public unary_tactical {
    std::string m_name;
    struct scope {
        const std::string &m_name;
        scope(std::string const& name) : m_name(name) {
            IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(" << m_name << " start)\n";);
        }
        ~scope() {
            IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(" << m_name << " done)\n";);
        }
    };
public:
    annotate_tactical(char const* name, tactic* t):
        unary_tactical(t), m_name(name) {}
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        scope _scope(m_name);
        m_t->operator()(in, result);
    }

    tactic * translate(ast_manager & m) override { 
        tactic * new_t = m_t->translate(m);
        return alloc(annotate_tactical, m_name.c_str(), new_t);
    }

    char const* name() const override { return "annotate"; }

    std::string display_tail() const override { return tactic_display_string(m_name.c_str()); }
    
};

tactic * annotate_tactic(char const* name, tactic * t) {
    return alloc(annotate_tactical, name, t);
}

// See scope_tactic in tactical.h.
class scope_tactical : public unary_tactical {
    std::string m_path;
    bool        m_enabled = true;

    enum class source { none, local, global };

    // true and rest if k is "<path>.<rest>" or "tactic.<path>.<rest>"; prefixed tells which
    bool strip(symbol const & k, std::string & rest, bool & prefixed) const {
        if (k.is_numerical() || k.is_null())
            return false;
        char const * s = k.bare_str();
        std::string const pre = m_path + ".";
        for (char const * mod : { "", "tactic." }) {
            size_t n = strlen(mod);
            if (strncmp(s, mod, n) == 0 && strncmp(s + n, pre.c_str(), pre.size()) == 0 && s[n + pre.size()]) {
                rest = s + n + pre.size();
                prefixed = n > 0;
                return true;
            }
        }
        return false;
    }

    // The parameters the child receives for parameters p, and whether the step is enabled.
    // A local entry <path>.<rest> sets <rest>. A global tactic.<path>.<rest> sets <rest>
    // unless a local value for <rest> is present: an unflagged entry that is not marked as
    // taken from a global scoped key by an enclosing scope.
    // If p has both <path>.<rest> and tactic.<path>.<rest>, the first one wins, whatever
    // their order: it is the name that validation gives a local key.
    // routed, if not null, receives the keys <rest> that were set.
    bool route(params_ref const & p, params_ref & new_p, source & enabled_src, svector<symbol> * routed = nullptr) const {
        new_p.copy(p);
        bool enabled = true;
        enabled_src = source::none;
        std::string rest;
        bool prefixed;
        for (unsigned i = 0; i < p.size(); ++i) {
            symbol k = p.get_key(i);
            if (!strip(k, rest, prefixed))
                continue;
            if (prefixed && p.contains(symbol((m_path + "." + rest).c_str())))
                continue;
            if (rest == "enabled") {
                enabled = p.get_bool(k, true);
                enabled_src = source::local;
                continue;
            }
            symbol r(rest.c_str());
            new_p.set_entry(r, p, k);
            if (routed && !routed->contains(r))
                routed->push_back(r);
            // params_ref::reset does not copy on write: safe because set_entry called
            // init(), so new_p no longer shares its entries with p.
            new_p.reset(scope_global_mark(r));
        }
        params_ref g = gparams::get_module("tactic");
        for (unsigned i = 0; i < g.size(); ++i) {
            symbol k = g.get_key(i);
            if (!strip(k, rest, prefixed))
                continue;
            if (rest == "enabled") {
                if (enabled_src != source::local) {
                    enabled = g.get_bool(k, true);
                    enabled_src = source::global;
                }
                continue;
            }
            symbol r(rest.c_str());
            symbol mark = scope_global_mark(r);
            if (new_p.contains(r) && !new_p.is_default(r) && !new_p.contains(mark))
                continue;
            new_p.set_entry(r, g, k);
            new_p.set_bool(mark, true);
            if (routed && !routed->contains(r))
                routed->push_back(r);
        }
        return enabled;
    }

    // the descriptions of the keys of the tactic module under the path
    void collect_scoped_descrs(param_descrs & r) const {
        param_descrs all;
        gparams::collect_module_param_descrs("tactic", all);
        std::string const pre = m_path + ".";
        for (unsigned i = 0; i < all.size(); ++i) {
            symbol n = all.get_param_name(i);
            if (strncmp(n.bare_str(), pre.c_str(), pre.size()) == 0)
                r.insert(n, all.get_kind(n), all.get_descr(n), all.get_default(n), "tactic");
        }
    }

public:
    scope_tactical(char const * path, tactic * t) : unary_tactical(t), m_path(path) {
        // the global settings until the first updt_params
        params_ref new_p;
        source src;
        m_enabled = route(params_ref(), new_p, src);
    }

    char const * name() const override { return "scope"; }

    void updt_params(params_ref const & p) override {
        params_ref new_p;
        source src;
        m_enabled = route(p, new_p, src);
        m_t->updt_params(new_p);
    }

    void collect_param_descrs(param_descrs & r) override {
        m_t->collect_param_descrs(r);
        collect_scoped_descrs(r);
    }

    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        if (!m_enabled) {
            IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(scope " << m_path << " disabled)\n";);
            result.push_back(in.get());
            return;
        }
        unary_tactical::operator()(in, result);
    }

    // The tactic language has no scopes, and the display must be a tactic that, run
    // without the scoped settings, does what this one does with them. So a scope is
    // displayed as what it does under the current settings:
    // - disabled: skip, or (when 0 t) under ctx.keep_disabled (an enclosing using-params
    //   needs the keys t declares);
    // - otherwise t, wrapped in (using-params t :k v ...) for the keys the scope routes
    //   to it (local or global scoped values) that t declares.
    // With ctx.annotate, a comment names the scope: "scope <path>", the routed values
    // with their "(global)" marks, and "disabled".
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        params_ref new_p;
        source src;
        svector<symbol> routed;
        bool enabled = route(p, new_p, src, &routed);
        param_descrs rows;
        collect_scoped_descrs(rows);
        ctx.declare(rows);
        ctx.scope_keys.copy(rows);
        std::string label = "scope " + m_path;
        if (!enabled) {
            std::string c = ctx.annotate ? label + " disabled" + (src == source::global ? " (global)" : "") : std::string();
            if (!ctx.keep_disabled) {
                ctx.leaf("skip", c);
                return;
            }
            // (when 0 t) never runs t, and t still declares its keys
            ctx.open("(when 0", c);
            m_t->display_pipeline(new_p, ctx);
            ctx.close();
            return;
        }
        // (using-params t) without keys is displayed as t (tactic_display_ctx::close)
        ctx.open("(using-params");
        ctx.push_frame();
        m_t->display_pipeline(new_p, ctx);
        param_descrs shown;
        ctx.pop_frame(shown);
        std::string tail, note;
        for (symbol const & r : routed) {
            if (!tactic_param_has_syntax(shown, r))
                continue;
            std::ostringstream v;
            new_p.display(v, r);
            std::string entry = ":" + std::string(r.str()) + " " + v.str();
            tail += (tail.empty() ? "" : " ") + entry;
            note += " " + entry + (new_p.contains(scope_global_mark(r)) ? " (global)" : "");
        }
        if (tail.empty()) {
            ctx.close();
            if (ctx.annotate)
                ctx.comment_last(label);
            return;
        }
        ctx.close(tail, ctx.annotate ? label + ":" + note : std::string());
    }

    tactic * translate(ast_manager & m) override {
        tactic * new_t = m_t->translate(m);
        scope_tactical * r = alloc(scope_tactical, m_path.c_str(), new_t);
        r->m_enabled = m_enabled;
        return r;
    }
};

tactic * scope_tactic(char const * path, tactic * t) {
    return alloc(scope_tactical, path, t);
}

class cond_tactical : public binary_tactical {
    probe_ref m_p;
public:
    cond_tactical(probe * p, tactic * t1, tactic * t2):
        binary_tactical(t1, t2),
        m_p(p) { 
        SASSERT(m_p);
    }

    char const* name() const override { return "cond"; }

    // cond(p, t, skip) is what (when p t) builds: display it as such.
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        bool is_when = strcmp(m_t2->name(), "skip") == 0;
        std::string comment;
        std::string c = display_probe(*m_p, p, ctx.annotate, comment);
        ctx.open((is_when ? "(when " : "(if ") + c, comment);
        m_t1->display_pipeline(p, ctx);
        if (!is_when)
            m_t2->display_pipeline(p, ctx);
        ctx.close();
    }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        m_clean = false;
        if (m_p->operator()(*(in.get())).is_true()) 
            m_t1->operator()(in, result);
        else
            m_t2->operator()(in, result);
    }

    void updt_params(params_ref const & p) override {
        m_p->updt_params(p);
        binary_tactical::updt_params(p);
    }

    tactic * translate(ast_manager & m) override {
        tactic * new_t1 = m_t1->translate(m);
        tactic * new_t2 = m_t2->translate(m);
        return alloc(cond_tactical, m_p->clone(), new_t1, new_t2);
    }

    void user_propagate_initialize_value(expr* var, expr* value) override {
        m_t1->user_propagate_initialize_value(var, value);
        m_t2->user_propagate_initialize_value(var, value);
    }
};

tactic * cond(probe * p, tactic * t1, tactic * t2) {
    return alloc(cond_tactical, p, t1, t2);
}

tactic * when(probe * p, tactic * t) {
    return cond(p, t, mk_skip_tactic());
}

class fail_if_tactic : public tactic {
    probe_ref m_p;
public:
    fail_if_tactic(probe * p):
        m_p(p) { 
        SASSERT(m_p);
    }

    char const* name() const override { return "fail_if"; }

    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        std::string comment;
        std::string c = display_probe(*m_p, p, ctx.annotate, comment);
        ctx.leaf("(fail-if " + c + ")", comment);
    }

    void cleanup() override {}

    void  operator()(goal_ref const & in, goal_ref_buffer& result) override {
        if (m_p->operator()(*(in.get())).is_true()) {
            throw tactic_exception("fail-if tactic");
        }
        result.push_back(in.get());
    }

    void updt_params(params_ref const & p) override { m_p->updt_params(p); }

    tactic * translate(ast_manager & m) override {
        probe * q = m_p->clone();
        return alloc(fail_if_tactic, q);
    }

    void collect_statistics(statistics& st) const override {
    }
};

tactic * fail_if(probe * p) {
    return alloc(fail_if_tactic, p);
}

tactic * fail_if_not(probe * p) {
    return fail_if(mk_not(p));
}

class if_no_proofs_tactical : public unary_tactical {
public:
    if_no_proofs_tactical(tactic * t):unary_tactical(t) {}

    char const* name() const override { return "if_no_proofs"; }

    char const * language_name() const override { return "if-no-proofs"; }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        if (in->proofs_enabled()) {
            result.push_back(in.get());
        }
        else {
            m_t->operator()(in, result);
        }
    }

    tactic * translate(ast_manager & m) override { return translate_core<if_no_proofs_tactical>(m); }
   
};

class if_no_unsat_cores_tactical : public unary_tactical {
public:
    if_no_unsat_cores_tactical(tactic * t):unary_tactical(t) {}

    char const* name() const override { return "if_no_unsat_cores"; }

    char const * language_name() const override { return "if-no-unsat-cores"; }
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        if (in->unsat_core_enabled()) {
            result.push_back(in.get());
        }
        else {
            m_t->operator()(in, result);
        }
    }

    tactic * translate(ast_manager & m) override { return translate_core<if_no_unsat_cores_tactical>(m); }
};

class if_no_models_tactical : public unary_tactical {
public:
    if_no_models_tactical(tactic * t):unary_tactical(t) {}

    char const* name() const override { return "if_no_models"; }

    char const * language_name() const override { return "if-no-models"; }
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        if (in->models_enabled()) {
            result.push_back(in.get());
        }
        else {
            m_t->operator()(in, result);
        }
    }

    tactic * translate(ast_manager & m) override { 
        return translate_core<if_no_models_tactical>(m); 
    }

};

tactic * if_no_proofs(tactic * t) {
    return alloc(if_no_proofs_tactical, t);
}

tactic * if_no_unsat_cores(tactic * t) {
    return alloc(if_no_unsat_cores_tactical, t);
}

tactic * if_no_models(tactic * t) {
    return alloc(if_no_models_tactical, t);
}

tactic * skip_if_failed(tactic * t) {
    return or_else(t, mk_skip_tactic());
}
