 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackr_helper.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef ACKR_HELPER_H_
#define ACKR_HELPER_H_

#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"

class ackr_helper {
public:
    struct app_occ {
        obj_hashtable<app> const_args;
        obj_hashtable<app> var_args;
    };
    typedef app_occ  app_set;
    typedef obj_map<func_decl, app_set*> fun2terms_map;
    typedef obj_map<app, app_set*>       sel2terms_map;
    
    ackr_helper(ast_manager& m) : m_bvutil(m), m_autil(m) {}
    
    /**
       \brief  Determines if a given function should be Ackermannized.
       
       This includes all uninterpreted functions but also "special" functions, e.g. OP_BSMOD0,
       which are not marked as uninterpreted but effectively are.
    */
    inline bool is_uninterp_fn(app const * a) const {
        if (is_uninterp(a))
            return true;
        else {
            decl_plugin * p = m_bvutil.get_manager().get_plugin(a->get_family_id());
            return p->is_considered_uninterpreted(a->get_decl());
        }
    }

    /**
       \brief determines if a term is a candidate select for Ackerman reduction
    */
    inline bool is_select(app* a) {
        return m_autil.is_select(a) && is_uninterp_const(a->get_arg(0));
    }

    void mark_non_select(app* a, expr_mark& non_select) {
        if (m_autil.is_select(a)) {
            bool first = true;
            for (expr* arg : *a) {
                if (first) 
                    first = false; 
                else 
                    non_select.mark(arg, true);
            }
        }
        else {
            for (expr* arg : *a) {
                non_select.mark(arg, true);
            }
        }
    }

    void prune_non_select(obj_map<app, app_set*> & sels, expr_mark& non_select) {
        ptr_vector<app> nons;
        for (auto& kv : sels) {
            if (non_select.is_marked(kv.m_key)) {
                nons.push_back(kv.m_key);
                dealloc(kv.m_value);
            }
        }
        for (app* s : nons) {
            sels.erase(s);
        }
    }
    
    inline bv_util& bvutil() { return m_bvutil; }
    
    /**
       \brief Calculates an upper bound for congruence lemmas given a map of function of occurrences.
    */
    static double calculate_lemma_bound(fun2terms_map const& occs1, sel2terms_map const& occs2);
    
    /** \brief Calculate n choose 2. **/
    inline static unsigned n_choose_2(unsigned n) { return (n & 1) ? (n * (n >> 1)) : (n >> 1) * (n - 1); }
    
    /** \brief Calculate n choose 2 guarded for overflow. Returns infinity if unsafe. **/
    inline static double n_choose_2_chk(unsigned n) {
        SASSERT(std::numeric_limits<unsigned>().max() & 32);
        return n & (1 << 16) ? std::numeric_limits<double>().infinity() : n_choose_2(n);
    }

    void insert(fun2terms_map& f2t, sel2terms_map& s2t, app* a) {
        if (a->get_num_args() == 0) return;
        ast_manager& m = m_bvutil.get_manager();
        app_set* ts = nullptr;
        bool is_const_args = true;
        if (is_select(a)) {
            app* sel = to_app(a->get_arg(0));
            if (!s2t.find(sel, ts)) {
                ts = alloc(app_set);
                s2t.insert(sel, ts);
            }
        }
        else if (is_uninterp_fn(a)) {
            func_decl* const fd = a->get_decl();
            if (!f2t.find(fd, ts)) {
                ts = alloc(app_set);
                f2t.insert(fd, ts);
            }
            is_const_args = m.is_value(a->get_arg(0));
        }
        else {
            return;
        }
        for (unsigned i = 1; is_const_args && i < a->get_num_args(); ++i) {
            is_const_args &= m.is_value(a->get_arg(i));
        }
        
        if (is_const_args) {
            ts->const_args.insert(a);
        }
        else {
            ts->var_args.insert(a);
        }
    }
    
private:
    bv_util                              m_bvutil;
    array_util                           m_autil;
};
#endif /* ACKR_HELPER_H_ */
