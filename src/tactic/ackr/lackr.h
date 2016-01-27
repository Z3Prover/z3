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
#include"goal.h"

struct lackr_stats {
    lackr_stats() : m_it(0), m_ackrs_sz(0) {}
    void reset() { m_it = m_ackrs_sz = 0; }
    unsigned    m_it;       // number of lazy iterations
    unsigned    m_ackrs_sz; // number of congruence constraints
};

/** \brief
   A class to encode or directly solve problems with uninterpreted functions via ackermannization.
   Currently, solving is supported only for QF_UFBV.
**/
class lackr {
    public:
        lackr(ast_manager& m, params_ref p, lackr_stats& st, expr_ref_vector& formulas);
        ~lackr();
        void updt_params(params_ref const & _p) {
            ackr_params p(_p);
            m_eager = p.eager();
            m_use_sat = p.sat_backend();
        }

        /** \brief
         * Solve the formula that the class was initialized with.
         **/
        lbool operator() ();


        /** \brief
        * Converts function occurrences to constants and encodes all congruence ackermann lemmas.
        * This guarantees a equisatisfiability with the input formula. It has a worst-case quadratic blowup.
        **/
        void mk_ackermann(/*out*/goal_ref& g);


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
        expr_ref_vector                      m_formulas;
        expr_ref_vector                      m_abstr;
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
        bool                                 m_is_init;

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

        void push_abstraction();

        void add_term(app* a);

        //
        // Collect all uninterpreted terms, skipping 0-arity.
        //
        void collect_terms();

        inline bool should_ackermannize(app const * a) const;
};

inline bool lackr::should_ackermannize(app const * a) const {
    if (a->get_family_id() == m_bvutil.get_family_id()) {
        switch (a->get_decl_kind()) {
        case OP_BSDIV0:
        case OP_BUDIV0:
        case OP_BSREM0:
        case OP_BUREM0:
        case OP_BSMOD0:
            return true;
        default:
            return is_uninterp(a);
        }
    }
    return (is_uninterp(a));
}

#endif /* LACKR_H_15079 */
