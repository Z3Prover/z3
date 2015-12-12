/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    reduce_args_tactic.cpp

Abstract:

    Reduce the number of arguments in function applications.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"ast_smt2_pp.h"
#include"map.h"
#include"rewriter_def.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"

/**
   \brief Reduce the number of arguments in function applications.

   Example, suppose we have a function f with 2 arguments. 
   There are 1000 applications of this function, but the first argument is always "a", "b" or "c".
   Thus, we replace the f(t1, t2)
   with 
      f_a(t2)   if   t1 = a
      f_b(t2)   if   t2 = b
      f_c(t2)   if   t2 = c

   Since f_a, f_b, f_c are new symbols, satisfiability is preserved.
   
   This transformation is very similar in spirit to the Ackermman's reduction. 

   This transformation should work in the following way:

   1- Create a mapping decl2arg_map from declarations to tuples of booleans, an entry [f -> (true, false, true)]
       means that f is a declaration with 3 arguments where the first and third arguments are always values.
   2- Traverse the formula and populate the mapping. 
        For each function application f(t1, ..., tn) do
          a) Create a boolean tuple (is_value(t1), ..., is_value(tn)) and do
             the logical-and with the tuple that is already in the mapping. If there is no such tuple
             in the mapping, we just add a new entry.

   If all entries are false-tuples, then there is nothing to be done. The transformation is not applicable.

   Now, we create a mapping decl2new_decl from (decl, val_1, ..., val_n) to decls. Note that, n may be different for each entry,
   but it is the same for the same declaration.
   For example, suppose we have [f -> (true, false, true)] in decl2arg_map, and applications f(1, a, 2), f(1, b, 2), f(1, b, 3), f(2, b, 3), f(2, c, 3) in the formula.
   Then, decl2arg_map would contain
        (f, 1, 2) -> f_1_2
        (f, 1, 3) -> f_1_3
        (f, 2, 3) -> f_2_3
   where f_1_2, f_1_3 and f_2_3 are new function symbols.
   Using the new map, we can replace the occurrences of f.
*/
class reduce_args_tactic : public tactic {
    struct     imp;
    imp *      m_imp;
public:
    reduce_args_tactic(ast_manager & m);

    virtual tactic * translate(ast_manager & m) {
        return alloc(reduce_args_tactic, m);
    }

    virtual ~reduce_args_tactic();
    
    virtual void operator()(goal_ref const & g, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core);
    virtual void cleanup();
};

tactic * mk_reduce_args_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(reduce_args_tactic, m));
}

struct reduce_args_tactic::imp {
    ast_manager &            m_manager;
    bool                     m_produce_models;

    ast_manager & m() const { return m_manager; }
    
    imp(ast_manager & m):
        m_manager(m) {
    }


    void checkpoint() { 
        if (m_manager.canceled())
            throw tactic_exception(m_manager.limit().get_cancel_msg());
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
                if (m_manager.is_unique_value(n->get_arg(j)))
                    return;
            }  
            m_non_cadidates.insert(d);
        }
    };

    /**
       \brief Populate the table non_cadidates with function declarations \c f
       such that there is a function application (f t1 ... tn) where t1 ... tn are not values.
    */
    void find_non_candidates(goal const & g, obj_hashtable<func_decl> & non_candidates) {
        non_candidates.reset();
        find_non_candidates_proc proc(m_manager, non_candidates);
        expr_fast_mark1 visited;
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, g.form(i));
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
                    it->m_value.set(j, m_manager.is_unique_value(n->get_arg(j)));
                }
            } else {
                SASSERT(j == it->m_value.size());                        
                while (j > 0) {
                    --j;
                    it->m_value.set(j, it->m_value.get(j) && m_manager.is_unique_value(n->get_arg(j)));
                }
            }
        }
    };

    void populate_decl2args(goal const & g, 
                            obj_hashtable<func_decl> & non_candidates, 
                            obj_map<func_decl, bit_vector> & decl2args) {
        expr_fast_mark1 visited;
        decl2args.reset();
        populate_decl2args_proc proc(m_manager, non_candidates, decl2args);
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, g.form(i));
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
    
    void populate_decl2arg_set(goal const & g, 
                               obj_map<func_decl, bit_vector> & decl2args,
                               decl2arg2func_map & decl2arg2funcs) {
        expr_fast_mark1 visited;
    
        populate_decl2arg_set_proc proc(m_manager, decl2args, decl2arg2funcs);
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, g.form(i));
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
        extension_model_converter * e_mc = alloc(extension_model_converter, m_manager);
        filter_model_converter * f_mc    = alloc(filter_model_converter, m_manager);
        decl2arg2func_map::iterator it   = decl2arg2funcs.begin();
        decl2arg2func_map::iterator end  = decl2arg2funcs.end();
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

    void operator()(goal & g, model_converter_ref & mc) {
        if (g.inconsistent())
            return;
        m_produce_models = g.models_enabled();
        TRACE("reduce_args", g.display(tout););
        tactic_report report("reduce-args", g);
        obj_hashtable<func_decl> non_candidates;
        obj_map<func_decl, bit_vector> decl2args;
        find_non_candidates(g, non_candidates);
        populate_decl2args(g, non_candidates, decl2args);
        
        if (decl2args.empty())
            return;
        
        ptr_vector<arg2func> arg2funcs;
        reduce_args_ctx ctx(m_manager);
        populate_decl2arg_set(g, decl2args, ctx.m_decl2arg2funcs);
    
        reduce_args_rw rw(*this, decl2args, ctx.m_decl2arg2funcs);
        
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            if (g.inconsistent())
                break;
            expr * f = g.form(i);
            expr_ref new_f(m_manager);
            rw(f, new_f);
            g.update(i, new_f);
        }

        report_tactic_progress(":reduced-funcs", decl2args.size());

        if (m_produce_models)
            mc = mk_mc(decl2args, ctx.m_decl2arg2funcs);

        TRACE("reduce_args", g.display(tout); if (mc) mc->display(tout););
    }
};

reduce_args_tactic::reduce_args_tactic(ast_manager & m) {
    m_imp = alloc(imp, m);
}

reduce_args_tactic::~reduce_args_tactic() {
    dealloc(m_imp);
}

void reduce_args_tactic::operator()(goal_ref const & g, 
                                    goal_ref_buffer & result, 
                                    model_converter_ref & mc, 
                                    proof_converter_ref & pc,
                                    expr_dependency_ref & core) {
    SASSERT(g->is_well_sorted());
    fail_if_proof_generation("reduce-args", g);
    fail_if_unsat_core_generation("reduce-args", g);
    mc = 0; pc = 0; core = 0; result.reset();
    m_imp->operator()(*(g.get()), mc);
    g->inc_depth();
    result.push_back(g.get());
    SASSERT(g->is_well_sorted());
}

void reduce_args_tactic::cleanup() {
    ast_manager & m   = m_imp->m();    
    imp * d = alloc(imp, m);
    std::swap(d, m_imp);    
    dealloc(d);
}

