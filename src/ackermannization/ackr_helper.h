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
    typedef obj_hashtable<app>           app_set;
    typedef obj_map<func_decl, app_set*> fun2terms_map;
    typedef obj_map<app, app_set*>      sel2terms_map;
    
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
    inline static unsigned n_choose_2(unsigned n) { return n & 1 ? (n * (n >> 1)) : (n >> 1) * (n - 1); }
    
    /** \brief Calculate n choose 2 guarded for overflow. Returns infinity if unsafe. **/
    inline static double n_choose_2_chk(unsigned n) {
        SASSERT(std::numeric_limits<unsigned>().max() & 32);
        return n & (1 << 16) ? std::numeric_limits<double>().infinity() : n_choose_2(n);
    }
    
private:
    bv_util                              m_bvutil;
    array_util                           m_autil;
};
#endif /* ACKR_HELPER_H_ */
