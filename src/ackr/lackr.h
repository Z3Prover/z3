 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef LACKR_H_15079
#define LACKR_H_15079
///////////////
#include"ackr_info.h"
#include"ackr_params.hpp"
#include"th_rewriter.h"
#include"cooperate.h"
#include"bv_decl_plugin.h"
#include"lbool.h"
#include"model.h"
#include"solver.h"
#include"util.h"
#include"tactic_exception.h"

struct lackr_stats {
    lackr_stats() : m_it(0), m_ackrs_sz(0) {}
    void reset() { m_it = m_ackrs_sz = 0; }
    unsigned    m_it;       // number of lazy iterations
    unsigned    m_ackrs_sz; // number of congruence constraints
};

class lackr {
    public:
        lackr(ast_manager& m, params_ref p, lackr_stats& st, expr_ref _f);
        ~lackr();
        void updt_params(params_ref const & _p) {
            ackr_params p(_p);
            m_eager = p.eager();
            m_use_sat = p.sat_backend();
        }
        lbool operator() ();

        //
        // getters
        //
        inline ackr_info_ref get_info() { return m_info; }
        inline model_ref get_model() { return m_model; }

        //
        //  timeout mechanism
        //
        void checkpoint() {
            if (m_m.canceled()) {            
                throw tactic_exception(TACTIC_CANCELED_MSG);
            }
            cooperate("lackr");
        }
    private:
        typedef obj_hashtable<app>           app_set;
        typedef obj_map<func_decl, app_set*> fun2terms_map;
        ast_manager&                         m_m;
        params_ref                           m_p;
        expr_ref                             m_fla;
        expr_ref                             m_abstr;
        fun2terms_map                        m_fun2terms;
        ackr_info_ref                        m_info;
        scoped_ptr<solver>                   m_sat;
        bv_util                              m_bvutil;
        th_rewriter                          m_simp;
        expr_ref_vector                      m_ackrs;
        model_ref                            m_model;
        bool                                 m_eager;
        bool                                 m_use_sat;
        lackr_stats&                         m_st;

        void init();
        void setup_sat();
        lbool eager();
        lbool lazy();

        //
        // Introduce congruence ackermann lemma for the two given terms.
        //
        bool ackr(app * const t1, app * const t2);

        //
        // Introduce the ackermann lemma for each pair of terms.
        //
        void eager_enc();

        void abstract();

        void add_term(app* a);

        //
        // Collect all uninterpreted terms, skipping 0-arity.
        //
        void collect_terms();
};
#endif /* LACKR_H_15079 */
