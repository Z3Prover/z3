/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    reduce_args.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-06.

Revision History:

--*/
#include"reduce_args.h"
#include"cooperate.h"
#include"ast_smt2_pp.h"
#include"map.h"
#include"rewriter_def.h"
#include"elim_var_model_converter.h"
#include"filter_model_converter.h"

struct reduce_args::imp {
    ast_manager &            m_manager;
    bool                     m_produce_models;
    volatile bool            m_cancel;

    ast_manager & m() const { return m_manager; }
    
    imp(ast_manager & m, params_ref const & p):
        m_manager(m) {
        updt_params(p);
        m_cancel = false;
    }

    void updt_params(params_ref const & p) {
        m_produce_models = p.get_bool(":produce-models", false);
    }

    void set_cancel(bool f) {
        m_cancel = f;
    }

    void checkpoint() { 
        if (m_cancel)
            throw reduce_args_exception(STE_CANCELED_MSG);
        cooperate("reduce-args");
    }
    
    struct find_non_candidates_proc {
        ast_manager &              m_manager;
        obj_hashtable<func_decl> & m_non_cadidates;
        
        find_non_candidates_proc(ast_manager & m, obj_hashtable<func_decl> & non_cadidates):
            m_manager(m),
            m_non_cadidates(non_cadidates) {
        }
        
        void operator()(var * n) {}
        
        void operator()(quantifier * n) {}
        
        void operator()(app * n) {
            if (n->get_num_args() == 0)
                return; // ignore constants
            func_decl * d = n->get_decl();
            if (d->get_family_id() != null_family_id)
                return; // ignore interpreted symbols
            if (m_non_cadidates.contains(d))
                return; // it is already in the set.
            unsigned j    = n->get_num_args();        
            while (j > 0) {
                --j;
                if (m_manager.is_value(n->get_arg(j)))
                    return;
            }  
            m_non_cadidates.insert(d);
        }
    };

    /**
       \brief Populate the table non_cadidates with function declarations \c f
       such that there is a function application (f t1 ... tn) where t1 ... tn are not values.
    */
    void find_non_candidates(assertion_set const & s, obj_hashtable<func_decl> & non_candidates) {
        non_candidates.reset();
        find_non_candidates_proc proc(m_manager, non_candidates);
        expr_fast_mark1 visited;
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, s.form(i));
        }
        
        TRACE("reduce_args", tout << "non_candidates:\n";
              obj_hashtable<func_decl>::iterator it  = non_candidates.begin();
              obj_hashtable<func_decl>::iterator end = non_candidates.end();
              for (; it != end; ++it) {
                  func_decl * d = *it;
                  tout << d->get_name() << "\n";
              });
    }

    struct populate_decl2args_proc {
        ast_manager &                     m_manager;
        obj_hashtable<func_decl> &        m_non_cadidates;
        obj_map<func_decl, bit_vector> &  m_decl2args;    
        
        populate_decl2args_proc(ast_manager & m, obj_hashtable<func_decl> & nc, obj_map<func_decl, bit_vector> & d):
            m_manager(m), m_non_cadidates(nc), m_decl2args(d) {}
        
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app * n) {
            if (n->get_num_args() == 0)
                return; // ignore constants
            func_decl * d = n->get_decl();
            if (d->get_family_id() != null_family_id)
                return; // ignore interpreted symbols
            if (m_non_cadidates.contains(d))
                return; // declaration is not a candidate
            unsigned j = n->get_num_args();
            obj_map<func_decl, bit_vector>::iterator it = m_decl2args.find_iterator(d);
            if (it == m_decl2args.end()) {
                m_decl2args.insert(d, bit_vector());
                it = m_decl2args.find_iterator(d);
                SASSERT(it != m_decl2args.end());
                it->m_value.reserve(j);
                while (j > 0) {
                    --j;
                    it->m_value.set(j, m_manager.is_value(n->get_arg(j)));
                }
            } else {
                SASSERT(j == it->m_value.size());                        
                while (j > 0) {
                    --j;
                    it->m_value.set(j, it->m_value.get(j) && m_manager.is_value(n->get_arg(j)));
                }
            }
        }
    };

    void populate_decl2args(assertion_set const & s, 
                            obj_hashtable<func_decl> & non_candidates, 
                            obj_map<func_decl, bit_vector> & decl2args) {
        expr_fast_mark1 visited;
        decl2args.reset();
        populate_decl2args_proc proc(m_manager, non_candidates, decl2args);
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, s.form(i));
        }
        
        // Remove all cases where the simplification is not applicable.
        ptr_buffer<func_decl> bad_decls;
        obj_map<func_decl, bit_vector>::iterator it  = decl2args.begin();
        obj_map<func_decl, bit_vector>::iterator end = decl2args.end();
        for (; it != end; it++) {
            bool is_zero = true;
            for (unsigned i = 0; i < it->m_value.size() && is_zero ; i++) {
                if (it->m_value.get(i)) 
                    is_zero = false;
            }
            if (is_zero) 
                bad_decls.push_back(it->m_key);
        }
    
        ptr_buffer<func_decl>::iterator it2  = bad_decls.begin();
        ptr_buffer<func_decl>::iterator end2 = bad_decls.end();
        for (; it2 != end2; ++it2)
            decl2args.erase(*it2);

        TRACE("reduce_args", tout << "decl2args:" << std::endl;
              for (obj_map<func_decl, bit_vector>::iterator it = decl2args.begin() ; it != decl2args.end() ; it++) {
                  tout << it->m_key->get_name() << ": ";
                  for (unsigned i = 0 ; i < it->m_value.size() ; i++)
                      tout << (it->m_value.get(i) ? "1" : "0");                            
                  tout << std::endl;
              });
    }

    struct arg2func_hash_proc {
        bit_vector const & m_bv;
        
        arg2func_hash_proc(bit_vector const & bv):m_bv(bv) {}
        unsigned operator()(app const * n) const {
            // compute the hash-code using only the arguments where m_bv is true.
            unsigned a = 0x9e3779b9;
            unsigned num_args = n->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                if (!m_bv.get(i)) 
                    continue; // ignore argument
                a = hash_u_u(a, n->get_arg(i)->get_id());
            }
            return a;
        }
    };
     
    struct arg2func_eq_proc {
        bit_vector const & m_bv;
     
        arg2func_eq_proc(bit_vector const & bv):m_bv(bv) {}
        bool operator()(app const * n1, app const * n2) const {
            // compare only the arguments where m_bv is true
            SASSERT(n1->get_num_args() == n2->get_num_args());
            unsigned num_args = n1->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                if (!m_bv.get(i)) 
                    continue; // ignore argument
                if (n1->get_arg(i) != n2->get_arg(i))
                    return false;
            }
            return true;
        }
    };

    typedef map<app *, func_decl *, arg2func_hash_proc, arg2func_eq_proc> arg2func;
    typedef obj_map<func_decl, arg2func *> decl2arg2func_map;

    struct reduce_args_ctx { 
        ast_manager &           m_manager;
        decl2arg2func_map       m_decl2arg2funcs;

        reduce_args_ctx(ast_manager & m): m_manager(m) {
        }
        
        ~reduce_args_ctx() {
            obj_map<func_decl, arg2func *>::iterator it  = m_decl2arg2funcs.begin();
            obj_map<func_decl, arg2func *>::iterator end = m_decl2arg2funcs.end();
            for (; it != end; ++it) {
                arg2func * map = it->m_value;
                arg2func::iterator it2  = map->begin();
                arg2func::iterator end2 = map->end();
                for (; it2 != end2; ++it2) {
                    m_manager.dec_ref(it2->m_key);
                    m_manager.dec_ref(it2->m_value);
                }
                dealloc(map);
            }
        }
    };

    struct populate_decl2arg_set_proc {
        ast_manager &                          m_manager;
        obj_map<func_decl, bit_vector> &       m_decl2args;
        decl2arg2func_map &                    m_decl2arg2funcs;
    
        populate_decl2arg_set_proc(ast_manager & m, 
                                   obj_map<func_decl, bit_vector> & d,
                                   decl2arg2func_map & ds):
            m_manager(m), m_decl2args(d), m_decl2arg2funcs(ds) {}

        void operator()(var * n) {}
        void operator()(quantifier * n) {}

        void operator()(app * n) {
            if (n->get_num_args() == 0)
                return; // ignore constants
            func_decl * d = n->get_decl();
            if (d->get_family_id() != null_family_id)
                return; // ignore interpreted symbols
            obj_map<func_decl, bit_vector>::iterator it = m_decl2args.find_iterator(d);
            if (it == m_decl2args.end())
                return; // not reducing the arguments of this declaration
            bit_vector & bv = it->m_value;
            arg2func * map = 0;
            decl2arg2func_map::iterator it2 = m_decl2arg2funcs.find_iterator(d);
            if (it2 == m_decl2arg2funcs.end()) {
                map = alloc(arg2func, arg2func_hash_proc(bv), arg2func_eq_proc(bv));
                m_decl2arg2funcs.insert(d, map);
            }
            else {
                map = it2->m_value;
            }
            if (!map->contains(n)) {
                // create fresh symbol...
                ptr_buffer<sort> domain;
                unsigned arity = d->get_arity();
                for (unsigned i = 0; i < arity; i++) {
                    if (!bv.get(i))
                        domain.push_back(d->get_domain(i));
                }
                func_decl * new_d = m_manager.mk_fresh_func_decl(d->get_name(), symbol::null, domain.size(), domain.c_ptr(), d->get_range());
                map->insert(n, new_d);
                m_manager.inc_ref(n);
                m_manager.inc_ref(new_d);
            }
        }    
    };
    
    void populate_decl2arg_set(assertion_set const & s, 
                               obj_map<func_decl, bit_vector> & decl2args,
                               decl2arg2func_map & decl2arg2funcs) {
        expr_fast_mark1 visited;
    
        populate_decl2arg_set_proc proc(m_manager, decl2args, decl2arg2funcs);
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, s.form(i));
        }
    }
    
    struct reduce_args_rw_cfg : public default_rewriter_cfg {
        ast_manager &                    m;
        imp &                            m_owner;
        obj_map<func_decl, bit_vector> & m_decl2args;
        decl2arg2func_map &              m_decl2arg2funcs;
        
        reduce_args_rw_cfg(imp & owner, obj_map<func_decl, bit_vector> & decl2args, decl2arg2func_map & decl2arg2funcs):
            m(owner.m_manager),
            m_owner(owner),
            m_decl2args(decl2args),
            m_decl2arg2funcs(decl2arg2funcs) {
        }

        bool max_steps_exceeded(unsigned num_steps) const { 
            m_owner.checkpoint();
            return false;
        }
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
            if (f->get_arity() == 0)
                return BR_FAILED; // ignore constants
            if (f->get_family_id() != null_family_id)
                return BR_FAILED; // ignore interpreted symbols
            decl2arg2func_map::iterator it  = m_decl2arg2funcs.find_iterator(f);
            if (it == m_decl2arg2funcs.end())
                return BR_FAILED;
            SASSERT(m_decl2args.contains(f));
            bit_vector & bv = m_decl2args.find(f);
            arg2func * map  = it->m_value;
            app_ref tmp(m);
            tmp = m.mk_app(f, num, args);
            CTRACE("reduce_args", !map->contains(tmp),
                   tout << "map does not contain tmp f: " << f->get_name() << "\n";
                   tout << mk_ismt2_pp(tmp, m) << "\n";
                   arg2func::iterator it  = map->begin();
                   arg2func::iterator end = map->end();
                   for (; it != end; ++it) {
                       tout << mk_ismt2_pp(it->m_key, m) << "\n---> " << it->m_value->get_name() << "\n";
                   });
            SASSERT(map->contains(tmp));
            func_decl * new_f = map->find(tmp);
            ptr_buffer<expr> new_args;
            for (unsigned i = 0; i < num; i++) {
                if (!bv.get(i))
                    new_args.push_back(args[i]);
            }
            result = m.mk_app(new_f, new_args.size(), new_args.c_ptr());
            return BR_DONE;
        }
    };

    struct reduce_args_rw : rewriter_tpl<reduce_args_rw_cfg> {
        reduce_args_rw_cfg m_cfg;
    public:
        reduce_args_rw(imp & owner, obj_map<func_decl, bit_vector> & decl2args, decl2arg2func_map & decl2arg2funcs):
            rewriter_tpl<reduce_args_rw_cfg>(owner.m_manager, false, m_cfg),
            m_cfg(owner, decl2args, decl2arg2funcs) {
        }
    };

    model_converter * mk_mc(obj_map<func_decl, bit_vector> & decl2args, decl2arg2func_map & decl2arg2funcs) {
        ptr_buffer<expr> new_args;
        var_ref_vector   new_vars(m_manager);
        ptr_buffer<expr> new_eqs;
        elim_var_model_converter * e_mc = alloc(elim_var_model_converter, m_manager);
        filter_model_converter * f_mc   = alloc(filter_model_converter, m_manager);
        decl2arg2func_map::iterator it  = decl2arg2funcs.begin();
        decl2arg2func_map::iterator end = decl2arg2funcs.end();
        for (; it != end; ++it) {
            func_decl * f  = it->m_key;
            arg2func * map = it->m_value;
            expr * def     = 0;
            SASSERT(decl2args.contains(f));
            bit_vector & bv = decl2args.find(f);
            new_vars.reset();
            new_args.reset();
            for (unsigned i = 0; i < f->get_arity(); i++) {
                new_vars.push_back(m_manager.mk_var(i, f->get_domain(i)));
                if (!bv.get(i))
                    new_args.push_back(new_vars.back());
            }
            arg2func::iterator it2  = map->begin();
            arg2func::iterator end2 = map->end();
            for (; it2 != end2; ++it2) {
                app * t = it2->m_key;
                func_decl * new_def = it2->m_value;
                f_mc->insert(new_def);
                SASSERT(new_def->get_arity() == new_args.size());
                app * new_t = m_manager.mk_app(new_def, new_args.size(), new_args.c_ptr());
                if (def == 0) {
                    def = new_t;
                }
                else {
                    new_eqs.reset();
                    for (unsigned i = 0; i < f->get_arity(); i++) {
                        if (bv.get(i))
                            new_eqs.push_back(m_manager.mk_eq(new_vars.get(i), t->get_arg(i)));
                    }
                    SASSERT(new_eqs.size() > 0);
                    expr * cond;
                    if (new_eqs.size() == 1)
                        cond = new_eqs[0];
                    else
                        cond = m_manager.mk_and(new_eqs.size(), new_eqs.c_ptr());
                    def = m_manager.mk_ite(cond, new_t, def);
                }
            }
            SASSERT(def);
            e_mc->insert(f, def);
        }
        return concat(f_mc, e_mc);
    }
    
    void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        if (s.inconsistent())
            return;
        if (m().proofs_enabled())
            throw reduce_args_exception("reduce-args does not support proofs");
        as_st_report report("reduce-args", s);
        TRACE("reduce_args", s.display(tout););

        obj_hashtable<func_decl> non_candidates;
        obj_map<func_decl, bit_vector> decl2args;
        find_non_candidates(s, non_candidates);
        populate_decl2args(s, non_candidates, decl2args);
        
        if (decl2args.empty())
            return;
        
        ptr_vector<arg2func> arg2funcs;
        reduce_args_ctx ctx(m_manager);
        populate_decl2arg_set(s, decl2args, ctx.m_decl2arg2funcs);
    
        reduce_args_rw rw(*this, decl2args, ctx.m_decl2arg2funcs);
        
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            if (s.inconsistent())
                break;
            expr * f = s.form(i);
            expr_ref new_f(m_manager);
            rw(f, new_f);
            s.update(i, new_f);
        }

        report_st_progress(":reduced-funcs", decl2args.size());

        if (m_produce_models)
            mc = mk_mc(decl2args, ctx.m_decl2arg2funcs);

        TRACE("reduce_args", s.display(tout); if (mc) mc->display(tout););
    }
};

reduce_args::reduce_args(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

reduce_args::~reduce_args() {
    dealloc(m_imp);
}

ast_manager & reduce_args::m() const {
    return m_imp->m();
}

void reduce_args::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void reduce_args::get_param_descrs(param_descrs & r) {
    insert_produce_models(r);                                        
}

void reduce_args::operator()(assertion_set & s, model_converter_ref & mc) {
    m_imp->operator()(s, mc);
}

void reduce_args::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}

void reduce_args::cleanup() {
    ast_manager & m   = m_imp->m();
    imp * d = m_imp;
    #pragma omp critical (as_st_cancel)
    {
        m_imp = 0;
    }
    dealloc(d);
    d = alloc(imp, m, m_params);
    #pragma omp critical (as_st_cancel)
    {
        m_imp = d;
    }
}

void reduce_args::collect_statistics(statistics & st) const {
}

void reduce_args::reset_statistics() {
}

as_st * mk_reduce_args(ast_manager & m, params_ref const & p) {
    return clean(alloc(reduce_args, m, p));
}


