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
#include"tactical.h"
#include"scoped_timer.h"
#include"cancel_eh.h"
#include"cooperate.h"
#include"scoped_ptr_vector.h"
#include"z3_omp.h"

class binary_tactical : public tactic {
protected:
    tactic *      m_t1;
    tactic *      m_t2;

    
public:
    binary_tactical(tactic * t1, tactic * t2):
        m_t1(t1),
        m_t2(t2) {
        SASSERT(m_t1);
        SASSERT(m_t2);
        m_t1->inc_ref();
        m_t2->inc_ref();
    }
    
    virtual ~binary_tactical() {
        m_t1->dec_ref();
        m_t2->dec_ref();
    }
    
    virtual void updt_params(params_ref const & p) {
        m_t1->updt_params(p);
        m_t2->updt_params(p);
    }
    
    virtual void collect_param_descrs(param_descrs & r) {
        m_t1->collect_param_descrs(r);
        m_t2->collect_param_descrs(r);
    }
    
    virtual void collect_statistics(statistics & st) const {
        m_t1->collect_statistics(st);
        m_t2->collect_statistics(st);
    }

    virtual void reset_statistics() { 
        m_t1->reset_statistics();
        m_t2->reset_statistics();
    }
        
    virtual void cleanup() {
        m_t1->cleanup();
        m_t2->cleanup();
    }
    
    virtual void reset() {
        m_t1->reset();
        m_t2->reset();
    }

    virtual void set_logic(symbol const & l) {
        m_t1->set_logic(l);
        m_t2->set_logic(l);
    }

    virtual void set_progress_callback(progress_callback * callback) {
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
    virtual ~and_then_tactical() {}

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {

        bool models_enabled = in->models_enabled();
        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                          
        goal_ref_buffer      r1;
        model_converter_ref mc1;                                                                           
        proof_converter_ref pc1;                                                                           
        expr_dependency_ref core1(m);                                                                      
        result.reset();                                                                                     
        mc   = 0;                                                                                
        pc   = 0;        
        core = 0;
        m_t1->operator()(in, r1, mc1, pc1, core1);                                                            
        SASSERT(!is_decided(r1) || (!pc1 && !core1)); // the pc and core of decided goals is 0
        unsigned r1_size = r1.size();                                                                       
        SASSERT(r1_size > 0);                                                                               
        if (r1_size == 1) {                                                                                 
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);    
                if (models_enabled) mc = mc1;
                return;                                                                                     
            }                                                                                               
            goal_ref r1_0 = r1[0];      
            m_t2->operator()(r1_0, result, mc, pc, core);
            if (models_enabled) mc = concat(mc1.get(), mc.get());
            if (proofs_enabled) pc = concat(pc1.get(), pc.get()); 
            if (cores_enabled) core = m.mk_join(core1.get(), core); 
        }
        else {
            if (cores_enabled) core = core1;
            proof_converter_ref_buffer pc_buffer;                                                           
            model_converter_ref_buffer mc_buffer;                                                           
            sbuffer<unsigned>          sz_buffer;                                                           
            goal_ref_buffer            r2;                                                                  
            for (unsigned i = 0; i < r1_size; i++) {                                                        
                goal_ref g = r1[i];                                                                         
                r2.reset();                                                                                 
                model_converter_ref mc2;                                                                   
                proof_converter_ref pc2;                                                                   
                expr_dependency_ref  core2(m);                                                              
                m_t2->operator()(g, r2, mc2, pc2, core2);                                              
                if (is_decided(r2)) {
                    SASSERT(r2.size() == 1);
                    if (is_decided_sat(r2)) {                                                          
                        // found solution...                                                                
                        result.push_back(r2[0]);
                        if (models_enabled) {
                            // mc2 contains the actual model                                                    
                            model_ref md;     
                            md = alloc(model, m);
                            apply(mc2, md, 0);
                            apply(mc1, md, i);
                            mc   = model2model_converter(md.get());                                             
                        }
                        SASSERT(!pc); SASSERT(!core);
                        return;                                                                             
                    }                                                                                   
                    else {                                                                                  
                        SASSERT(is_decided_unsat(r2));                                                 
                        // the proof and unsat core of a decided_unsat goal are stored in the node itself.
                        // pc2 and core2 must be 0.
                        SASSERT(!pc2);
                        SASSERT(!core2);
                        if (models_enabled) mc_buffer.push_back(0);
                        if (proofs_enabled) pc_buffer.push_back(proof2proof_converter(m, r2[0]->pr(0)));
                        if (models_enabled || proofs_enabled) sz_buffer.push_back(0);
                        if (cores_enabled) core = m.mk_join(core.get(), r2[0]->dep(0));
                    }                                                                         
                }                                                                                       
                else {                                                                                      
                    result.append(r2.size(), r2.c_ptr());
                    if (models_enabled) mc_buffer.push_back(mc2.get());
                    if (proofs_enabled) pc_buffer.push_back(pc2.get());
                    if (models_enabled || proofs_enabled) sz_buffer.push_back(r2.size()); 
                    if (cores_enabled) core = m.mk_join(core.get(), core2.get());
                }                                                                                           
            }
            
            if (result.empty()) {                                                                           
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                if (proofs_enabled)
                    apply(m, pc1, pc_buffer, pr);
                SASSERT(cores_enabled || core == 0);
                in->assert_expr(m.mk_false(), pr, core);
                core = 0;
                result.push_back(in.get());
                SASSERT(!mc); SASSERT(!pc); SASSERT(!core);
            }
            else {
                if (models_enabled) mc = concat(mc1.get(), mc_buffer.size(), mc_buffer.c_ptr(), sz_buffer.c_ptr());                 
                if (proofs_enabled) pc = concat(pc1.get(), pc_buffer.size(), pc_buffer.c_ptr(), sz_buffer.c_ptr()); 
                SASSERT(cores_enabled || core == 0);
            }
        }
    }

    virtual tactic * translate(ast_manager & m) {
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
    ptr_vector<tactic> m_ts;

public:
    nary_tactical(unsigned num, tactic * const * ts) {
        for (unsigned i = 0; i < num; i++) {
            SASSERT(ts[i]);
            m_ts.push_back(ts[i]);
            ts[i]->inc_ref();
        }
    }

    virtual ~nary_tactical() {
        unsigned sz = m_ts.size();
        for (unsigned i = 0; i < sz; i++) {
            m_ts[i]->dec_ref();
        }
    }

    virtual void updt_params(params_ref const & p) {
        TRACE("nary_tactical_updt_params", tout << "updt_params: " << p << "\n";);
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->updt_params(p);
    }
    
    virtual void collect_param_descrs(param_descrs & r) {
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->collect_param_descrs(r);
    }
    
    virtual void collect_statistics(statistics & st) const {
        ptr_vector<tactic>::const_iterator it  = m_ts.begin();
        ptr_vector<tactic>::const_iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->collect_statistics(st);
    }

    virtual void reset_statistics() { 
        ptr_vector<tactic>::const_iterator it  = m_ts.begin();
        ptr_vector<tactic>::const_iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->reset_statistics();
    }
        
    virtual void cleanup() {
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->cleanup();
    }
    
    virtual void reset() {
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->reset();
    }

    virtual void set_logic(symbol const & l) {
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->set_logic(l);
    }

    virtual void set_progress_callback(progress_callback * callback) {
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it)
            (*it)->set_progress_callback(callback);
    }

protected:

    template<typename T>
    tactic * translate_core(ast_manager & m) { 
        ptr_buffer<tactic> new_ts;
        ptr_vector<tactic>::iterator it  = m_ts.begin();
        ptr_vector<tactic>::iterator end = m_ts.end();
        for (; it != end; ++it) {
            tactic * curr = *it;
            tactic * new_curr = curr->translate(m);
            new_ts.push_back(new_curr);
        }
        return alloc(T, new_ts.size(), new_ts.c_ptr());
    }

};

class or_else_tactical : public nary_tactical {
public:
    or_else_tactical(unsigned num, tactic * const * ts):nary_tactical(num, ts) { SASSERT(num > 0); }

    virtual ~or_else_tactical() {}

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        goal orig(*(in.get()));
        unsigned sz = m_ts.size();
        unsigned i;
        for (i = 0; i < sz; i++) {
            tactic * t = m_ts[i];
            result.reset();
            mc   = 0;
            pc   = 0;
            core = 0;
            SASSERT(sz > 0);
            if (i < sz - 1) {
                try {
                    t->operator()(in, result, mc, pc, core);
                    return;
                }
                catch (tactic_exception &) {
                }
            }
            else {
                t->operator()(in, result, mc, pc, core);
                return;
            }
            in->reset_all();
            in->copy_from(orig);
        }
    }

    virtual tactic * translate(ast_manager & m) { return translate_core<or_else_tactical>(m); }
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
    virtual ~par_tactical() {}

    

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        bool use_seq;
#ifdef _NO_OMP_
        use_seq = true;
#else
        use_seq = 0 != omp_in_parallel();
#endif
        if (use_seq) {
            // execute tasks sequentially
            or_else_tactical::operator()(in, result, mc, pc, core);
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
            model_converter_ref _mc; 
            proof_converter_ref _pc; 
            expr_dependency_ref _core(*(managers[i]));
            
            goal_ref in_copy = in_copies[i];
            tactic & t = *(ts.get(i));
            
            try {
                t(in_copy, _result, _mc, _pc, _core);
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
                    for (unsigned k = 0; k < _result.size(); k++) {
                        result.push_back(_result[k]->translate(translator));
                    }
                    mc   = _mc ? _mc->translate(translator) : 0;
                    pc   = _pc ? _pc->translate(translator) : 0;
                    expr_dependency_translation td(translator);
                    core = td(_core);
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
            mc = 0;
            switch (ex_kind) {
            case ERROR_EX: throw z3_error(error_code);
            case TACTIC_EX: throw tactic_exception(ex_msg.c_str());
            default:
                throw default_exception(ex_msg.c_str());
            }
        }
    }    

    virtual tactic * translate(ast_manager & m) { return translate_core<par_tactical>(m); }
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
    virtual ~par_and_then_tactical() {}

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        bool use_seq;
#ifdef _NO_OMP_
        use_seq = true;
#else
        use_seq = 0 != omp_in_parallel();
#endif
        if (use_seq) {
            // execute tasks sequentially
            and_then_tactical::operator()(in, result, mc, pc, core);
            return;
        }

        bool models_enabled = in->models_enabled();
        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                          
        goal_ref_buffer      r1;
        model_converter_ref mc1;                                                                           
        proof_converter_ref pc1;                                                                           
        expr_dependency_ref core1(m);                                                                      
        result.reset();                                                                                     
        mc   = 0;                                                                                
        pc   = 0;        
        core = 0;
        m_t1->operator()(in, r1, mc1, pc1, core1);                                                            
        SASSERT(!is_decided(r1) || (!pc1 && !core1)); // the pc and core of decided goals is 0
        unsigned r1_size = r1.size();                                                                       
        SASSERT(r1_size > 0);                                                                               
        if (r1_size == 1) {                                                                                 
            // Only one subgoal created... no need for parallelism
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);                                                                    
                if (models_enabled) mc = mc1;                                                                                 
                SASSERT(!pc); SASSERT(!core);
                return;                                                                                     
            }                                                                                               
            goal_ref r1_0 = r1[0];                                                                          
            m_t2->operator()(r1_0, result, mc, pc, core);                                              
            if (models_enabled) mc = concat(mc1.get(), mc.get());
            if (proofs_enabled) pc = concat(pc1.get(), pc.get());
            if (cores_enabled) core = m.mk_join(core1.get(), core); 
        }                                                                                     
        else {                                                                                              
            if (cores_enabled) core = core1;  

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

            proof_converter_ref_buffer             pc_buffer; 
            model_converter_ref_buffer             mc_buffer; 
            scoped_ptr_vector<expr_dependency_ref> core_buffer;
            scoped_ptr_vector<goal_ref_buffer>     goals_vect;

            pc_buffer.resize(r1_size);
            mc_buffer.resize(r1_size);
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
                model_converter_ref mc2;                                                                   
                proof_converter_ref pc2;                                                                   
                expr_dependency_ref core2(new_m);                                                              
                
                bool curr_failed = false;

                try {
                    ts2[i]->operator()(new_g, r2, mc2, pc2, core2);                                              
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
                                if (models_enabled) {
                                    // mc2 contains the actual model                                                    
                                    mc2  = mc2 ? mc2->translate(translator) : 0;
                                    model_ref md;     
                                    md = alloc(model, m);
                                    apply(mc2, md, 0);
                                    apply(mc1, md, i);
                                    mc   = model2model_converter(md.get());
                                }
                                SASSERT(!pc); SASSERT(!core);
                            }       
                        }                                                     
                        else {                                                                                  
                            SASSERT(is_decided_unsat(r2));                                                 
                            // the proof and unsat core of a decided_unsat goal are stored in the node itself.
                            // pc2 and core2 must be 0.
                            SASSERT(!pc2);
                            SASSERT(!core2);
                            
                            if (models_enabled) mc_buffer.set(i, 0);
                            if (proofs_enabled) {
                                proof * pr = r2[0]->pr(0);
                                pc_buffer.push_back(proof2proof_converter(m, pr));
                            }
                            if (cores_enabled && r2[0]->dep(0) != 0) {
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
                        mc_buffer.set(i, mc2.get());
                        pc_buffer.set(i, pc2.get());
                        if (cores_enabled && core2 != 0) {
                            expr_dependency_ref * new_dep = alloc(expr_dependency_ref, new_m);
                            *new_dep = core2;
                            core_buffer.set(i, new_dep);
                        }
                    }                                                                                           
                }
            }
            
            if (failed) {
                switch (ex_kind) {
                case ERROR_EX: throw z3_error(error_code);
                case TACTIC_EX: throw tactic_exception(ex_msg.c_str());
                default:
                    throw default_exception(ex_msg.c_str());
                }
            }

            if (found_solution)
                return;

            core = 0;
            sbuffer<unsigned> sz_buffer;                                                           
            for (unsigned i = 0; i < r1_size; i++) {
                ast_translation translator(*(managers[i]), m, false);
                goal_ref_buffer * r = goals_vect[i];
                if (r != 0) {
                    for (unsigned k = 0; k < r->size(); k++) {
                        result.push_back((*r)[k]->translate(translator));
                    }
                    sz_buffer.push_back(r->size());
                }
                else {
                    sz_buffer.push_back(0);
                }
                if (mc_buffer[i] != 0)
                    mc_buffer.set(i, mc_buffer[i]->translate(translator));
                if (pc_buffer[i] != 0)
                    pc_buffer.set(i, pc_buffer[i]->translate(translator));
                expr_dependency_translation td(translator);
                if (core_buffer[i] != 0) {
                    expr_dependency_ref curr_core(m);
                    curr_core = td(*(core_buffer[i]));
                    core = m.mk_join(curr_core, core);
                }
            }

            if (result.empty()) {
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                if (proofs_enabled)
                    apply(m, pc1, pc_buffer, pr);
                SASSERT(cores_enabled || core == 0);
                in->assert_expr(m.mk_false(), pr, core);
                core = 0;
                result.push_back(in.get());
                SASSERT(!mc); SASSERT(!pc); SASSERT(!core);
            }
            else {
                if (models_enabled) mc = concat(mc1.get(), mc_buffer.size(), mc_buffer.c_ptr(), sz_buffer.c_ptr());                 
                if (proofs_enabled) pc = concat(pc1.get(), pc_buffer.size(), pc_buffer.c_ptr(), sz_buffer.c_ptr()); 
                SASSERT(cores_enabled || core == 0);
            }
        }
    }

    virtual tactic * translate(ast_manager & m) {
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
    tactic * m_t;


public:
    unary_tactical(tactic * t): 
        m_t(t) {
        SASSERT(t); 
        t->inc_ref(); 
    }    

    virtual ~unary_tactical() { 
        m_t->dec_ref();
    }

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        m_t->operator()(in, result, mc, pc, core);
    }
   
    virtual void cleanup(void) { m_t->cleanup(); }
    virtual void collect_statistics(statistics & st) const { m_t->collect_statistics(st); }
    virtual void reset_statistics() { m_t->reset_statistics(); }    
    virtual void updt_params(params_ref const & p) { m_t->updt_params(p); }
    virtual void collect_param_descrs(param_descrs & r) { m_t->collect_param_descrs(r); }
    virtual void reset() { m_t->reset(); }
    virtual void set_logic(symbol const& l) { m_t->set_logic(l); }    
    virtual void set_progress_callback(progress_callback * callback) { m_t->set_progress_callback(callback); }
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
                    goal_ref_buffer & result, 
                    model_converter_ref & mc, 
                    proof_converter_ref & pc, 
                    expr_dependency_ref & core) {
        // TODO: implement a non-recursive version.
        if (depth > m_max_depth) {
            result.push_back(in.get());
            mc   = 0;
            pc   = 0;
            core = 0;
            return;
        }

        bool models_enabled = in->models_enabled();
        bool proofs_enabled = in->proofs_enabled();
        bool cores_enabled  = in->unsat_core_enabled();

        ast_manager & m = in->m();                                                                          
        goal_ref_buffer      r1;                                                                            
        model_converter_ref mc1;                                                                           
        proof_converter_ref pc1;                                                                           
        expr_dependency_ref core1(m);                                                                      
        result.reset();                                                                                     
        mc   = 0;                                                                                             
        pc   = 0;             
        core = 0;
        {
            goal orig_in(in->m(), proofs_enabled, models_enabled, cores_enabled);
            orig_in.copy_from(*(in.get()));
            m_t->operator()(in, r1, mc1, pc1, core1);                                                            
            if (is_equal(orig_in, *(in.get()))) {
                result.push_back(r1[0]);                                                                    
                if (models_enabled) mc = mc1;
                if (proofs_enabled) pc = pc1;
                if (cores_enabled)  core = core1; 
                return;                                                                                     
            }
        }
        unsigned r1_size = r1.size();                                                                       
        SASSERT(r1_size > 0);                                                                               
        if (r1_size == 1) {                                                                                 
            if (r1[0]->is_decided()) {
                result.push_back(r1[0]);                                                                    
                if (models_enabled) mc = mc1;
                SASSERT(!pc); SASSERT(!core);
                return;                                                                                     
            }                                                                                               
            goal_ref r1_0 = r1[0];                                                                          
            operator()(depth+1, r1_0, result, mc, pc, core); 
            if (models_enabled) mc = concat(mc.get(), mc1.get());
            if (proofs_enabled) pc = concat(pc.get(), pc1.get()); 
            if (cores_enabled)  core = m.mk_join(core1.get(), core); 
        }                                                                                                   
        else {
            if (cores_enabled) core = core1;
            proof_converter_ref_buffer pc_buffer;                                                           
            model_converter_ref_buffer mc_buffer;                                                           
            sbuffer<unsigned>          sz_buffer;                                                           
            goal_ref_buffer            r2;                                                                  
            for (unsigned i = 0; i < r1_size; i++) {                                                        
                goal_ref g = r1[i];                                                                         
                r2.reset();                                                                                 
                model_converter_ref mc2;                                                                   
                proof_converter_ref pc2;                                                                   
                expr_dependency_ref  core2(m);                                                              
                operator()(depth+1, g, r2, mc2, pc2, core2);                                              
                if (is_decided(r2)) {
                    SASSERT(r2.size() == 1);
                    if (is_decided_sat(r2)) {                                                          
                        // found solution...                                                                
                        result.push_back(r2[0]);
                        if (models_enabled) {
                            // mc2 contains the actual model                                                    
                            model_ref md;                                                                      
                            if (mc2) (*mc2)(md, 0);                                                             
                            if (mc1) (*mc1)(md, i);                                                             
                            mc   = model2model_converter(md.get());                                             
                        }
                        SASSERT(!pc); SASSERT(!core);
                        return;                                                                             
                    }                                                                                       
                    else {                                                                                  
                        SASSERT(is_decided_unsat(r2));
                        SASSERT(!pc2); 
                        SASSERT(!core2);
                        if (models_enabled) mc_buffer.push_back(0);
                        if (proofs_enabled) pc_buffer.push_back(proof2proof_converter(m, r2[0]->pr(0)));
                        if (models_enabled || proofs_enabled) sz_buffer.push_back(0);                                                             
                        if (cores_enabled) core = m.mk_join(core.get(), r2[0]->dep(0));
                    }                                                                                       
                }                                                                                           
                else {                                                                                      
                    result.append(r2.size(), r2.c_ptr());                                                   
                    if (models_enabled) mc_buffer.push_back(mc2.get());                                                         
                    if (proofs_enabled) pc_buffer.push_back(pc2.get());                                                         
                    if (models_enabled || proofs_enabled) sz_buffer.push_back(r2.size());                                                         
                    if (cores_enabled) core = m.mk_join(core.get(), core2.get());                                              
                }                                                                                           
            }    
                                                                                           
            if (result.empty()) {                                                                           
                // all subgoals were shown to be unsat.                                                     
                // create an decided_unsat goal with the proof
                in->reset_all();
                proof_ref pr(m);
                if (proofs_enabled)
                    apply(m, pc1, pc_buffer, pr);
                SASSERT(cores_enabled || core == 0);
                in->assert_expr(m.mk_false(), pr, core);
                core = 0;
                result.push_back(in.get());
                SASSERT(!mc); SASSERT(!pc); SASSERT(!core);
            }
            else {
                if (models_enabled) mc = concat(mc1.get(), mc_buffer.size(), mc_buffer.c_ptr(), sz_buffer.c_ptr());                 
                if (proofs_enabled) pc = concat(pc1.get(), pc_buffer.size(), pc_buffer.c_ptr(), sz_buffer.c_ptr());                 
                SASSERT(cores_enabled || core == 0);
            }
        }
    }

public:
    repeat_tactical(tactic * t, unsigned max_depth):
        unary_tactical(t), 
        m_max_depth(max_depth) {
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        operator()(0, in, result, mc, pc, core);
    }

    virtual tactic * translate(ast_manager & m) { 
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

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        m_t->operator()(in, result, mc, pc, core);
        if (result.size() > m_threshold) {
            result.reset();
            mc   = 0;
            pc   = 0;
            core = 0;
            throw tactic_exception("failed-if-branching tactical");
        }
    };    

    virtual tactic * translate(ast_manager & m) { 
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

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        m_t->operator()(in, result, mc, pc, core);
        m_t->cleanup();
    }    

    virtual tactic * translate(ast_manager & m) { 
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
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        cancel_eh<reslimit> eh(in->m().limit());
        { 
            // Warning: scoped_timer is not thread safe in Linux.
            scoped_timer timer(m_timeout, &eh);
            m_t->operator()(in, result, mc, pc, core);
        }
    }

    virtual tactic * translate(ast_manager & m) { 
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

    virtual void updt_params(params_ref const & p) {
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

    virtual tactic * translate(ast_manager & m) { 
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
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {        
        scope _scope(m_name);
        m_t->operator()(in, result, mc, pc, core);
    }

    virtual tactic * translate(ast_manager & m) { 
        tactic * new_t = m_t->translate(m);
        return alloc(annotate_tactical, m_name.c_str(), new_t);
    }
    
};

tactic * annotate_tactic(char const* name, tactic * t) {
    return alloc(annotate_tactical, name, t);
}

class cond_tactical : public binary_tactical {
    probe * m_p;
public:
    cond_tactical(probe * p, tactic * t1, tactic * t2):
        binary_tactical(t1, t2),
        m_p(p) { 
        SASSERT(m_p);
        m_p->inc_ref(); 
    }

    ~cond_tactical() {
        m_p->dec_ref();
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        if (m_p->operator()(*(in.get())).is_true()) 
            m_t1->operator()(in, result, mc, pc, core);
        else
            m_t2->operator()(in, result, mc, pc, core);
    }

    virtual tactic * translate(ast_manager & m) { 
        tactic * new_t1 = m_t1->translate(m);
        tactic * new_t2 = m_t2->translate(m);
        return alloc(cond_tactical, m_p, new_t1, new_t2);
    }
};

tactic * cond(probe * p, tactic * t1, tactic * t2) {
    return alloc(cond_tactical, p, t1, t2);
}

tactic * when(probe * p, tactic * t) {
    return cond(p, t, mk_skip_tactic());
}

class fail_if_tactic : public tactic {
    probe * m_p;
public:
    fail_if_tactic(probe * p):
        m_p(p) { 
        SASSERT(m_p);
        m_p->inc_ref(); 
    }
    
    ~fail_if_tactic() {
        m_p->dec_ref();
    }

    void cleanup() {}

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        mc   = 0;
        pc   = 0;
        core = 0;
        if (m_p->operator()(*(in.get())).is_true()) {
            throw tactic_exception("fail-if tactic");
        }
        result.push_back(in.get());
    }

    virtual tactic * translate(ast_manager & m) { 
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
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        if (in->proofs_enabled()) {
            mc = 0; pc = 0; core = 0;
            result.reset();
            result.push_back(in.get());
        }
        else {
            m_t->operator()(in, result, mc, pc, core);
        }
    }

    virtual tactic * translate(ast_manager & m) { return translate_core<if_no_proofs_tactical>(m); }
};

class if_no_unsat_cores_tactical : public unary_tactical {
public:
    if_no_unsat_cores_tactical(tactic * t):unary_tactical(t) {}
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        if (in->unsat_core_enabled()) {
            mc = 0; pc = 0; core = 0;
            result.reset();
            result.push_back(in.get());
        }
        else {
            m_t->operator()(in, result, mc, pc, core);
        }
    }

    virtual tactic * translate(ast_manager & m) { return translate_core<if_no_unsat_cores_tactical>(m); }
};

class if_no_models_tactical : public unary_tactical {
public:
    if_no_models_tactical(tactic * t):unary_tactical(t) {}
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc, 
                            expr_dependency_ref & core) {
        if (in->models_enabled()) {
            mc = 0; pc = 0; core = 0;
            result.reset();
            result.push_back(in.get());
        }
        else {
            m_t->operator()(in, result, mc, pc, core);
        }
    }

    virtual tactic * translate(ast_manager & m) { return translate_core<if_no_models_tactical>(m); }
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

    
