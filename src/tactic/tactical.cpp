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
#include "util/cooperate.h"
#include "util/scoped_ptr_vector.h"
#include "util/z3_omp.h"
#include "tactic/tactical.h"

class binary_tactical : public tactic {
protected:
    tactic_ref      m_t1;
    tactic_ref      m_t2;
    
public:

    binary_tactical(tactic * t1, tactic * t2):
        m_t1(t1),
        m_t2(t2) {
        SASSERT(m_t1);
        SASSERT(m_t2);
    }
    
    ~binary_tactical() override { }
    
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
        m_t1->cleanup();
        m_t2->cleanup();
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
    ~and_then_tactical() override {}

    void operator()(goal_ref const & in, goal_ref_buffer& result) override { 

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
            for (unsigned i = 0; i < r1_size; i++) {                                                        
                goal_ref g = r1[i];                                                                       
                r2.reset();
                m_t2->operator()(g, r2);
                if (is_decided(r2)) {
                    SASSERT(r2.size() == 1);
                    if (is_decided_sat(r2)) {                                                          
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
                    result.append(r2.size(), r2.c_ptr());
                }                                                                                           
            }
                        
            if (result.empty()) {                                                                           
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                expr_dependency_ref core(m);
                if (proofs_enabled) {
                    apply(m, in->pc(), pr);
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
        for (unsigned i = 0; i < num; i++) {
            SASSERT(ts[i]);
            m_ts.push_back(ts[i]);
        }
    }

    ~nary_tactical() override { }

    void updt_params(params_ref const & p) override {
        TRACE("nary_tactical_updt_params", tout << "updt_params: " << p << "\n";);
        for (tactic* t : m_ts) t->updt_params(p);
    }
    
    void collect_param_descrs(param_descrs & r) override {
        for (tactic* t : m_ts) t->collect_param_descrs(r);
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
        return alloc(T, new_ts.size(), new_ts.c_ptr());
    }

};

class or_else_tactical : public nary_tactical {
public:
    or_else_tactical(unsigned num, tactic * const * ts):nary_tactical(num, ts) { SASSERT(num > 0); }

    ~or_else_tactical() override {}

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        goal orig(*(in.get()));
        unsigned sz = m_ts.size();
        unsigned i;
        for (i = 0; i < sz; i++) {
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

enum par_exception_kind {
    TACTIC_EX,
    DEFAULT_EX,
    ERROR_EX
};

class par_tactical : public or_else_tactical {


public:
    par_tactical(unsigned num, tactic * const * ts):or_else_tactical(num, ts) {}
    ~par_tactical() override {}

    

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        bool use_seq;
#ifdef _NO_OMP_
        use_seq = true;
#else
        use_seq = 0 != omp_in_parallel();
#endif
        if (use_seq) {
            // execute tasks sequentially
            or_else_tactical::operator()(in, result);
            return;
        }
        
        ast_manager & m = in->m();
        
        scoped_ptr_vector<ast_manager> managers;
        scoped_limits scl(m.limit());
        goal_ref_vector                in_copies;
        tactic_ref_vector              ts;
        unsigned sz = m_ts.size();
        for (unsigned i = 0; i < sz; i++) {
            ast_manager * new_m = alloc(ast_manager, m, !m.proof_mode());
            managers.push_back(new_m);
            ast_translation translator(m, *new_m);
            in_copies.push_back(in->translate(translator));
            ts.push_back(m_ts.get(i)->translate(*new_m));
            scl.push_child(&new_m->limit());
        }

        unsigned finished_id       = UINT_MAX;
        par_exception_kind ex_kind = DEFAULT_EX;
        std::string        ex_msg;
        unsigned           error_code = 0;
        
        #pragma omp parallel for
        for (int i = 0; i < static_cast<int>(sz); i++) {
            goal_ref_buffer     _result;
            
            goal_ref in_copy = in_copies[i];
            tactic & t = *(ts.get(i));
            
            try {
                t(in_copy, _result);
                bool first = false;
                #pragma omp critical (par_tactical)
                {
                    if (finished_id == UINT_MAX) {
                        finished_id = i;
                        first = true;
                    }
                }                
                if (first) {
                    for (unsigned j = 0; j < sz; j++) {
                        if (static_cast<unsigned>(i) != j) {
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
                    ex_msg = ex.msg();
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
                    ex_msg = z3_ex.msg();
                }
            }
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

class par_and_then_tactical : public and_then_tactical {
public:
    par_and_then_tactical(tactic * t1, tactic * t2):and_then_tactical(t1, t2) {}
    ~par_and_then_tactical() override {}

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        bool use_seq;
#ifdef _NO_OMP_
        use_seq = true;
#else
        use_seq = 0 != omp_in_parallel();
#endif
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
            tactic_ref_vector              ts2;
            goal_ref_vector                g_copies;

            for (unsigned i = 0; i < r1_size; i++) {
                ast_manager * new_m = alloc(ast_manager, m, !m.proof_mode());
                managers.push_back(new_m);
                ast_translation translator(m, *new_m);
                g_copies.push_back(r1[i]->translate(translator));
                ts2.push_back(m_t2->translate(*new_m));
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

            #pragma omp parallel for
            for (int i = 0; i < static_cast<int>(r1_size); i++) { 
                ast_manager & new_m = *(managers[i]);
                goal_ref new_g = g_copies[i];

                goal_ref_buffer r2;
                
                bool curr_failed = false;

                try {
                    ts2[i]->operator()(new_g, r2);                  
                }
                catch (tactic_exception & ex) {
                    #pragma omp critical (par_and_then_tactical)
                    {
                        if (!failed && !found_solution) {
                            curr_failed = true;
                            failed      = true;
                            ex_kind     = TACTIC_EX;
                            ex_msg      = ex.msg();
                        }
                    }
                }
                catch (z3_error & err) {
                    #pragma omp critical (par_and_then_tactical)
                    {
                        if (!failed && !found_solution) {
                            curr_failed = true;
                            failed      = true;
                            ex_kind     = ERROR_EX;
                            error_code  = err.error_code();
                        }
                    }                    
                }
                catch (z3_exception & z3_ex) {
                    #pragma omp critical (par_and_then_tactical)
                    {
                        if (!failed && !found_solution) {
                            curr_failed = true;
                            failed      = true;
                            ex_kind     = DEFAULT_EX;
                            ex_msg      = z3_ex.msg();
                        }
                    }
                }

                if (curr_failed) {
                    for (unsigned j = 0; j < r1_size; j++) {
                        if (static_cast<unsigned>(i) != j) {
                            managers[j]->limit().cancel();
                        }
                    }
                }
                else {
                    if (is_decided(r2)) {
                        SASSERT(r2.size() == 1);
                        if (is_decided_sat(r2)) {                                                          
                            // found solution... 
                            bool first = false;
                            #pragma omp critical (par_and_then_tactical)
                            {
                                if (!found_solution) {
                                    failed         = false;
                                    found_solution = true;
                                    first          = true;
                                }
                            }
                            if (first) {
                                for (unsigned j = 0; j < r1_size; j++) {
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
                        new_r2->append(r2.size(), r2.c_ptr());
                        dependency_converter* dc = r1[i]->dc();                           
                        if (cores_enabled && dc) {
                            expr_dependency_ref * new_dep = alloc(expr_dependency_ref, new_m);
                            *new_dep = (*dc)();
                            core_buffer.set(i, new_dep);
                        }
                    }                                                                                           
                }
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
            for (unsigned i = 0; i < r1_size; i++) {
                ast_translation translator(*(managers[i]), m, false);
                goal_ref_buffer * r = goals_vect[i];
                unsigned j = result.size();
                if (r != nullptr) {
                    for (unsigned k = 0; k < r->size(); k++) {
                        result.push_back((*r)[k]->translate(translator));
                    }
                }
                if (proofs_enabled) {
                    // update proof converter of r1[i]
                    r1[i]->set(concat(r1[i]->pc(), result.size() - j, result.c_ptr() + j));
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
                    apply(m, in->pc(), pr);
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


public:
    unary_tactical(tactic * t): 
        m_t(t) {
        SASSERT(t);  
    }    

    ~unary_tactical() override { }

    void operator()(goal_ref const & in, goal_ref_buffer& result) override { 
        m_t->operator()(in, result);
    }
   
    void cleanup(void) override { m_t->cleanup(); }
    void collect_statistics(statistics & st) const override { m_t->collect_statistics(st); }
    void reset_statistics() override { m_t->reset_statistics(); }    
    void updt_params(params_ref const & p) override { m_t->updt_params(p); }
    void collect_param_descrs(param_descrs & r) override { m_t->collect_param_descrs(r); }
    void reset() override { m_t->reset(); }
    void set_logic(symbol const& l) override { m_t->set_logic(l); }    
    void set_progress_callback(progress_callback * callback) override { m_t->set_progress_callback(callback); }
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
        // TODO: implement a non-recursive version.
        if (depth > m_max_depth) {
            result.push_back(in.get());
            return;
        }

        bool models_enabled = in->models_enabled();
        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                          
        goal_ref_buffer      r1;  
        result.reset();          
        {
            goal orig_in(in->m(), proofs_enabled, models_enabled, cores_enabled);
            orig_in.copy_from(*(in.get()));
            m_t->operator()(in, r1);                                                            
            if (r1.size() == 1 && is_equal(orig_in, *(r1[0]))) {
                result.push_back(r1[0]);
                return;                                                                                     
            }
        }
        unsigned r1_size = r1.size();                                                                       
        SASSERT(r1_size > 0);                                                                               
        if (r1_size == 1) {                                                                                 
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);  
                return;                                                                                     
            }                                                                                               
            goal_ref r1_0 = r1[0];                                                                          
            operator()(depth+1, r1_0, result); 
        }                                                                                                   
        else {
            goal_ref_buffer            r2;                                                                  
            for (unsigned i = 0; i < r1_size; i++) {                                                        
                goal_ref g = r1[i];                                                                         
                r2.reset();                   
                operator()(depth+1, g, r2);                                              
                if (is_decided(r2)) {
                    SASSERT(r2.size() == 1);
                    if (is_decided_sat(r2)) {                                                          
                        // found solution...                                                                
                        result.push_back(r2[0]);
                        return;                                                                             
                    }                                                                                       
                    else {                                                                                  
                        SASSERT(is_decided_unsat(r2));
                    }                                                                                       
                }                                                                                           
                else {                                                                                      
                    result.append(r2.size(), r2.c_ptr());                                                           
                }                                                                                           
            }    
                                                                                           
            if (result.empty()) {                                                                           
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                expr_dependency_ref core(m);
                if (proofs_enabled) {
                    apply(m, in->pc(), pr);                    
                }
                if (cores_enabled && in->dc()) {
                    core = (*in->dc())();
                }
                in->assert_expr(m.mk_false(), pr, core);
                result.push_back(in.get());
            }
        }
    }

public:
    repeat_tactical(tactic * t, unsigned max_depth):
        unary_tactical(t), 
        m_max_depth(max_depth) {
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

    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        m_t->operator()(in, result);
        if (result.size() > m_threshold) {
            result.reset(); // assumes in is not strenthened to one of the branches
            throw tactic_exception("failed-if-branching tactical");
        }
    };    

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
    
    void operator()(goal_ref const & in, goal_ref_buffer& result) override {
        cancel_eh<reslimit> eh(in->m().limit());
        { 
            // Warning: scoped_timer is not thread safe in Linux.
            scoped_timer timer(m_timeout, &eh);
            m_t->operator()(in, result);
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

class using_params_tactical : public unary_tactical {
    params_ref m_params;
public:
    using_params_tactical(tactic * t, params_ref const & p):unary_tactical(t), m_params(p) {
        t->updt_params(p);
    }

    void updt_params(params_ref const & p) override {
        TRACE("using_params", 
              tout << "before p: " << p << "\n";
              tout << "m_params: " << m_params << "\n";);
        
        params_ref new_p = p;
        new_p.append(m_params);
        unary_tactical::updt_params(new_p);
        
        TRACE("using_params", 
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
        std::string m_name;
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
    
};

tactic * annotate_tactic(char const* name, tactic * t) {
    return alloc(annotate_tactical, name, t);
}

class cond_tactical : public binary_tactical {
    probe_ref m_p;
public:
    cond_tactical(probe * p, tactic * t1, tactic * t2):
        binary_tactical(t1, t2),
        m_p(p) { 
        SASSERT(m_p);
    }

    ~cond_tactical() override {}
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        if (m_p->operator()(*(in.get())).is_true()) 
            m_t1->operator()(in, result);
        else
            m_t2->operator()(in, result);
    }

    tactic * translate(ast_manager & m) override {
        tactic * new_t1 = m_t1->translate(m);
        tactic * new_t2 = m_t2->translate(m);
        return alloc(cond_tactical, m_p.get(), new_t1, new_t2);
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
    
    ~fail_if_tactic() override {}

    void cleanup() override {}

    void  operator()(goal_ref const & in, goal_ref_buffer& result) override {
        if (m_p->operator()(*(in.get())).is_true()) {
            throw tactic_exception("fail-if tactic");
        }
        result.push_back(in.get());
    }

    tactic * translate(ast_manager & m) override {
        return this;
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

