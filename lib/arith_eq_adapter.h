/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_eq_adapter.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-25.

Revision History:

--*/
#ifndef _ARITH_EQ_ADAPTER_H_
#define _ARITH_EQ_ADAPTER_H_

#include"smt_theory.h"
#include"obj_pair_hashtable.h"
#include"arith_decl_plugin.h"
#include"statistics.h"
#include"arith_simplifier_plugin.h"

namespace smt {

    struct arith_eq_adapter_stats {
        unsigned m_num_eq_axioms;
        void reset() { m_num_eq_axioms = 0; }
        arith_eq_adapter_stats() { reset(); }
    };

    /**
       \brief Auxiliary class used to convert (dis) equalities
       propagated from the core into arith equalities/inequalities
       atoms. This class is used by the arithmetic theories to 
       handle the (dis) equalities propagated from the logical context.
      
       - config 1:
         recreate axioms at restart

       - config 2:
         lazy diseq split
    */
    class arith_eq_adapter {
    public:
        arith_eq_adapter_stats           m_stats;

    private:
        struct data {
            expr * m_t1_eq_t2;
            expr * m_le;
            expr * m_ge;
            data():m_t1_eq_t2(0), m_le(0), m_ge(0) {}
            data(expr * t1_eq_t2, expr * le, expr * ge):m_t1_eq_t2(t1_eq_t2), m_le(le), m_ge(ge) {}
        };

    public:
        typedef obj_pair_map<enode, enode, data> already_processed; 
        
    private:
        theory &                         m_owner;
        theory_arith_params &            m_params;
        arith_util &                     m_util;
        arith_simplifier_plugin *        m_as;

        already_processed                m_already_processed;
        svector<enode_pair>              m_restart_pairs;
        svector<parameter>               m_proof_hint;

        context & get_context() const { return m_owner.get_context(); }
        ast_manager & get_manager() const { return m_owner.get_manager(); }
        enode * get_enode(theory_var v) const { return m_owner.get_enode(v); }

        arith_simplifier_plugin * get_simplifier();

    public:
        arith_eq_adapter(theory & owner, theory_arith_params & params, arith_util & u):m_owner(owner), m_params(params), m_util(u), m_as(0) {}
        void new_eq_eh(theory_var v1, theory_var v2);
        void new_diseq_eh(theory_var v1, theory_var v2);
        void reset_eh();
        void init_search_eh();
        void restart_eh();
        /**
           \brief Add the eq axioms for n1 and n2. 
        */
        void mk_axioms(enode * n1, enode * n2);
        void collect_statistics(::statistics & st) const;
        void display_already_processed(std::ostream & out) const;
    };
};

#endif /* _ARITH_EQ_ADAPTER_H_ */

