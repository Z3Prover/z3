/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ufbv_strategy.cpp

Abstract:

    General purpose strategy for UFBV benchmarks.

Author:

    Christoph (cwinter) 2011-07-28

Notes:

--*/
#include"assertion_set_rewriter.h"
#include"nnf.h"
#include"der.h"
#include"distribute_forall.h"
#include"macro_finder.h"
#include"arith_simplifier_plugin.h"
#include"bv_simplifier_plugin.h"
#include"ufbv_rewriter.h"
#include"quasi_macros.h"
#include"reduce_args.h"
#include"ufbv_strategy.h"
#include"shallow_context_simplifier.h"
#include"gaussian_elim.h"
#include"elim_var_model_converter.h"
#include"ast_smt2_pp.h"

// --- TRACE STRATEGY 

#ifdef _TRACE

class trace_as_st : public assertion_set_strategy {
    ast_manager & m;    
    const char * tag;

public:
    trace_as_st(ast_manager & m, const char * tag) : m(m),tag(tag) { }    
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {        
        TRACE(tag, { s.display(tout); });
    }

    virtual void cleanup() {}
};

#endif

as_st * mk_trace_as(ast_manager & m, const char * tag) {
#ifdef _TRACE
    return alloc(trace_as_st, m, tag);
#else
    return noop();
#endif
}

as_st * mk_der_fp(ast_manager & m, params_ref const & p) {
    return repeat(and_then(mk_der(m), mk_simplifier(m, p)));
}


// --- DISTRIBUTE-FORALL STRATEGY

class distribute_forall_st : public assertion_set_strategy {
    ast_manager & m;
    params_ref    m_params;
    bool          m_produce_models;
    bool          m_cancel;

public:
    distribute_forall_st(ast_manager & m, params_ref const & p = params_ref()) : m(m),m_params(p),m_produce_models(false),m_cancel(false) { }
    virtual ~distribute_forall_st() {}

    virtual void updt_params(params_ref const & p) {
        m_produce_models = p.get_bool(":produce-models", false);
    }

    static  void get_param_descrs(param_descrs & r) {
        insert_produce_models(r);
    }

    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        as_st_report report("distribute-forall", s);
        basic_simplifier_plugin bsimp(m);
        bsimp.set_eliminate_and(true);
        distribute_forall apply_dist(m, bsimp);        
            
        for (unsigned i = 0; i < s.size(); i++) {
            if (m_cancel) 
                throw strategy_exception(STE_CANCELED_MSG);

            expr * n = s.form(i);
            expr_ref r(m);
            apply_dist(n, r);
            if (n != r.get()) {
                if (m.proofs_enabled()) {
                    proof * old_pr = s.pr(i);
                    proof_ref new_pr(m);
                    new_pr = m.mk_rewrite_star(n, r, 0, 0);
                    new_pr = m.mk_modus_ponens(old_pr, new_pr);
                    s.update(i, r, new_pr);
                }
                else
                    s.update(i, r, 0);
            }
        }        
        
        mc = 0; // CMW: No model conversion necessary; variables and functions don't change.
        TRACE("distribute_forall", s.display(tout););
    }

    virtual void cleanup() {}
protected:
    virtual void set_cancel(bool f) { m_cancel = f; }
};

as_st * mk_distribute_forall(ast_manager & m, params_ref const & p) {
    return alloc(distribute_forall_st, m, p);
}

model_converter * macro_manager2model_converter(macro_manager const & mm) {
    elim_var_model_converter * mc = alloc(elim_var_model_converter, mm.get_manager());
    unsigned num = mm.get_num_macros();
    for (unsigned i = 0; i < num; i++) {
        expr_ref f_interp(mm.get_manager());
        func_decl * f = mm.get_macro_interpretation(i, f_interp);
        mc->insert(f, f_interp);
    }
    return mc;
}

// --- MACRO FINDER STRATEGY

class macro_finder_st : public assertion_set_strategy {
    ast_manager & m;
    params_ref    m_params;
    bool          m_produce_models;
    bool          m_cancel;
    bool          m_elim_and;

public:
    macro_finder_st(ast_manager & m, params_ref const & p = params_ref(), bool elim_and=false) : m(m),m_params(p),m_produce_models(false),m_cancel(false),m_elim_and(elim_and) { }
    virtual ~macro_finder_st() {}

    virtual void updt_params(params_ref const & p) {
        m_produce_models = p.get_bool(":produce-models", false);
    }

    static  void get_param_descrs(param_descrs & r) {
        insert_produce_models(r);
    }

    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        TRACE("debug_ids", m.display_free_ids(tout); tout << "\n";);
        as_st_report report("macro-finder", s);
        simplifier simp(m);
        basic_simplifier_plugin * bsimp = alloc(basic_simplifier_plugin, m);
        bsimp->set_eliminate_and(m_elim_and);
        simp.register_plugin(bsimp);
        arith_simplifier_params a_params;
        arith_simplifier_plugin * asimp = alloc(arith_simplifier_plugin, m, *bsimp, a_params);
        simp.register_plugin(asimp);
        bv_simplifier_params bv_params;
        bv_simplifier_plugin * bvsimp = alloc(bv_simplifier_plugin, m, *bsimp, bv_params);
        simp.register_plugin(bvsimp);
                
        macro_manager mm(m, simp);
        macro_finder mf(m, mm);
            
        expr_ref_vector forms(m), new_forms(m);
        proof_ref_vector proofs(m), new_proofs(m);

        for (unsigned i = 0; i < s.size(); i++) {
            forms.push_back(s.form(i));
            proofs.push_back(s.pr(i));
        }

        mf(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);
        
        s.reset();
        for (unsigned i = 0; i < new_forms.size(); i++) {
            s.assert_expr(new_forms.get(i), (m.proofs_enabled()) ? new_proofs.get(i) : 0);
        }        

        mc = macro_manager2model_converter(mm);
        TRACE("debug_ids", m.display_free_ids(tout); tout << "\n";);
    }

    virtual void cleanup() {}
protected:
    virtual void set_cancel(bool f) { m_cancel = f; }
};

as_st * mk_macro_finder(ast_manager & m, params_ref const & p, bool elim_and=false) {
    return alloc(macro_finder_st, m, p, elim_and);
}


// --- UFBV-Rewriter (demodulator) STRATEGY

class ufbv_rewriter_st : public assertion_set_strategy {
    ast_manager & m;
    params_ref    m_params;
    bool          m_produce_models;
    bool          m_cancel;

public:
    ufbv_rewriter_st(ast_manager & m, params_ref const & p = params_ref()) : m(m),m_params(p),m_produce_models(false),m_cancel(false) { }
    virtual ~ufbv_rewriter_st() {}

    virtual void updt_params(params_ref const & p) {
        m_produce_models = p.get_bool(":produce-models", false);
    }

    static  void get_param_descrs(param_descrs & r) {
        insert_produce_models(r);
    }

    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        as_st_report report("ufbv-rewriter", s);
        basic_simplifier_plugin bsimp(m);
        bsimp.set_eliminate_and(true);
        ufbv_rewriter dem(m, bsimp);
            
        expr_ref_vector forms(m), new_forms(m);
        proof_ref_vector proofs(m), new_proofs(m);

        for (unsigned i = 0; i < s.size(); i++) {
            forms.push_back(s.form(i));
            proofs.push_back(s.pr(i));
        }

        dem(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);
        
        s.reset();
        for (unsigned i = 0; i < new_forms.size(); i++) {
            s.assert_expr(new_forms.get(i), (m.proofs_enabled()) ? new_proofs.get(i) : 0);
        }        

        mc = 0; // CMW: The demodulator could potentially remove all references to a variable. 
    }

    virtual void cleanup() {}
protected:
    virtual void set_cancel(bool f) { m_cancel = f; }
};

as_st * mk_ufbv_rewriter(ast_manager & m, params_ref const & p) {
    return alloc(ufbv_rewriter_st, m, p);
}


// --- QUASI-MACROS STRATEGY

class quasi_macros_st : public assertion_set_strategy {
    ast_manager & m;
    params_ref    m_params;
    bool          m_produce_models;
    bool          m_cancel;

public:
    quasi_macros_st(ast_manager & m, params_ref const & p = params_ref()) : m(m),m_params(p),m_produce_models(false),m_cancel(false) { }
    virtual ~quasi_macros_st() {}

    virtual void updt_params(params_ref const & p) {
        m_produce_models = p.get_bool(":produce-models", false);
    }

    static  void get_param_descrs(param_descrs & r) {
        insert_produce_models(r);
    }

    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        as_st_report report("quasi-macros", s);
        simplifier simp(m);
        basic_simplifier_plugin * bsimp = alloc(basic_simplifier_plugin, m);
        bsimp->set_eliminate_and(true);
        simp.register_plugin(bsimp);
        arith_simplifier_params a_params;
        arith_simplifier_plugin * asimp = alloc(arith_simplifier_plugin, m, *bsimp, a_params);
        simp.register_plugin(asimp);
        bv_simplifier_params bv_params;
        bv_simplifier_plugin * bvsimp = alloc(bv_simplifier_plugin, m, *bsimp, bv_params);
        simp.register_plugin(bvsimp);
                
        macro_manager mm(m, simp);
        quasi_macros qm(m, mm, *bsimp, simp);
        bool more = true;
        
        expr_ref_vector forms(m), new_forms(m);
        proof_ref_vector proofs(m), new_proofs(m);

        for (unsigned i = 0; i < s.size(); i++) {
            forms.push_back(s.form(i));
            proofs.push_back(s.pr(i));
        }
        
        while (more) { // CMW: This is applied until fixpoint; should we have a fixpoint_as_st for that?            
            if (m_cancel) 
              throw strategy_exception(STE_CANCELED_MSG);

            new_forms.reset();
            new_proofs.reset();
            more = qm(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);            
            forms.swap(new_forms);
            proofs.swap(new_proofs);            
        }

        s.reset();
        for (unsigned i = 0; i < forms.size(); i++) {
            s.assert_expr(forms.get(i), (m.proofs_enabled()) ? proofs.get(i) : 0);
        }

        mc = macro_manager2model_converter(mm);
    }

    virtual void cleanup() {}
protected:
    virtual void set_cancel(bool f) { m_cancel = f; }
};

as_st * mk_quasi_macros(ast_manager & m, params_ref const & p) {
    return alloc(quasi_macros_st, m, p);
}

// --- ELIMINATE AND STRATEGY

as_st * mk_eliminate_and(ast_manager & m, params_ref const & p) {
    params_ref elim_and_p;
    elim_and_p.set_bool(":elim-and", true);
    return using_params(mk_simplifier(m, p), elim_and_p);
}

// --- DISPLAY ASSERTION SET STRATEGY
// CMW: This was a temporary hack. Use cmd_context to print benchmark files. 

//class display_as_st : public assertion_set_strategy {
//    ast_manager & m;
//    params_ref    m_params;
//
//public:
//    display_as_st (ast_manager & m, params_ref const & p = params_ref()) : m(m),m_params(p) { }
//    virtual ~display_as_st() {}
//
//    virtual void updt_params(params_ref const & p) {}
//
//    static  void get_param_descrs(param_descrs & r) {}
//
//    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
//
//    struct find_uf_proc {
//        ast_manager              & m_manager;
//        obj_hashtable<func_decl> & m_fds;
//        
//        find_uf_proc(ast_manager & m, obj_hashtable<func_decl> & fds):
//            m_manager(m),
//            m_fds(fds) {
//        }
//        
//        void operator()(var * n) {}
//        
//        void operator()(quantifier * n) {}
//        
//        void operator()(app * n) {            
//            func_decl * d = n->get_decl();
//            if (d->get_family_id() != null_family_id)
//                return; // ignore interpreted symbols                         
//            m_fds.insert(d);
//        }
//    };
//    
//    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
//        std::cerr << "(set-info :source ||)" << std::endl;
//        std::cerr << "(set-info :status unknown)" << std::endl;
//        std::cerr << "(set-logic UFBV)" << std::endl;
//
//        // Find functions
//        obj_hashtable<func_decl> fds;
//        find_uf_proc proc(m, fds);        
//        unsigned sz = s.size();
//        for (unsigned i = 0; i < sz; i++) {
//            expr_fast_mark1 visited;
//            quick_for_each_expr(proc, visited, s.form(i));
//        }
//
//        // print functions
//        for (obj_hashtable<func_decl>::iterator it = fds.begin(); it != fds.end(); it++) {
//            // How do we print (declare-fun ...) ?
//            std::cerr << mk_ismt2_pp(*it, m) << std::endl;
//        }
//
//        // print assertions
//        for (unsigned i = 0; i < s.size(); i++) {
//            std::cerr << "(assert ";            
//            std::cerr << mk_ismt2_pp(s.form(i), m);
//            std::cerr << ")" << std::endl;
//        }
//        std::cerr << "(check-sat)" << std::endl;
//    }
//
//    virtual void cleanup() {}
//protected:
//    virtual void set_cancel(bool f) {}
//};
//
//as_st * mk_display_as(ast_manager & m, params_ref const & p) {
//    return alloc(display_as_st, m, p);
//}


class debug_ids_st : public assertion_set_strategy {
    ast_manager & m;
    
    struct proc {
        ast_manager & m;
        proc(ast_manager & _m):m(_m) {}
        void operator()(var * n)        { TRACE_CODE(tout << n->get_id() << " ";); }
        void operator()(app * n)        { TRACE_CODE(tout << n->get_id() << " ";); }
        void operator()(quantifier * n) { TRACE_CODE(tout << n->get_id() << " ";); }
    };

public:
    debug_ids_st(ast_manager & _m):m(_m) {}

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        TRACE("debug_ids", 
              tout << "free ids:\n"; m.display_free_ids(tout); tout << "\n";
              proc p(m);
              tout << "assertion_set ids:\n";
              for_each_expr_as(p, s);
              tout << "\n";);
    }
    virtual void cleanup() {}
};


// --- UFBV STRATEGY

as_st * mk_preprocessor(ast_manager & m, params_ref const & p) {

    return and_then(mk_trace_as(m, "ufbv_pre"),
            and_then( mk_simplifier(m, p),
                      mk_constant_propagation(m, p),
                      and_then(mk_macro_finder(m, p, false), mk_simplifier(m, p)),
                      and_then(mk_snf(p), mk_simplifier(m, p)),
                      mk_eliminate_and(m, p),
                      mk_eq_solver(m, p),
                      and_then(mk_der_fp(m, p), mk_simplifier(m, p)),
                      and_then(mk_distribute_forall(m, p), mk_simplifier(m, p))
                      ),
            and_then( and_then(mk_reduce_args(m, p), mk_simplifier(m, p)),
                      and_then(mk_macro_finder(m, p, true), mk_simplifier(m, p)),
                      and_then(mk_ufbv_rewriter(m, p), mk_simplifier(m, p)),
                      and_then(mk_quasi_macros(m, p), mk_simplifier(m, p)),
                      and_then(mk_der_fp(m, p), mk_simplifier(m, p)),
                      mk_simplifier(m, p)),
                    mk_trace_as(m, "ufbv_post"));    
}

as_st * mk_ufbv_strategy(ast_manager & m, params_ref const & p) {
    params_ref main_p(p);    
    main_p.set_bool(":mbqi", true);
    main_p.set_uint(":mbqi-max-iterations", -1);
    main_p.set_bool(":elim-and", true);
    main_p.set_bool(":solver", true);

    // this prints the skolemized version of a benchmark
    // as_st * st = and_then(mk_skolemizer(m, main_p), mk_display_as(m, main_p));

    as_st * st = and_then(repeat(mk_preprocessor(m, main_p), 2),            
                          alloc(debug_ids_st, m),
                          using_params(mk_smt_solver(false), main_p));
    
    st->updt_params(p);

    return st;
}
