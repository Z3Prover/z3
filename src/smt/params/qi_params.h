/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    qi_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-15.

Revision History:

--*/
#ifndef QI_PARAMS_H_
#define QI_PARAMS_H_

#include "util/util.h"
#include "util/params.h"

enum quick_checker_mode {
    MC_NO,     // do not use (cheap) model checking based instantiation
    MC_UNSAT,  // instantiate unsatisfied instances
    MC_NO_SAT  // instantiate unsatisfied and not-satisfied instances
};

struct qi_params {
    std::string        m_qi_cost;
    std::string        m_qi_new_gen;
    double             m_qi_eager_threshold;
    double             m_qi_lazy_threshold;
    unsigned           m_qi_max_eager_multipatterns;
    unsigned           m_qi_max_lazy_multipattern_matching;
    bool               m_qi_profile;
    unsigned           m_qi_profile_freq;
    quick_checker_mode m_qi_quick_checker;
    bool               m_qi_lazy_quick_checker;
    bool               m_qi_promote_unsat;
    unsigned           m_qi_max_instances;
    bool               m_qi_lazy_instantiation;
    bool               m_qi_conservative_final_check;

    bool               m_mbqi;
    unsigned           m_mbqi_max_cexs;
    unsigned           m_mbqi_max_cexs_incr;
    unsigned           m_mbqi_max_iterations;
    bool               m_mbqi_trace;
    unsigned           m_mbqi_force_template;
    const char *       m_mbqi_id;

    qi_params(params_ref const & p = params_ref()):
        /*
          The "weight 0" performance bug
          ------------------------------
          
          The parameters m_qi_cost and m_qi_new_gen influence quantifier instantiation.
          - m_qi_cost: specify the cost of a quantifier instantiation. Z3 will block instantiations using m_qi_eager_threshold and m_qi_lazy_threshold.
          - m_qi_new_gen: specify how the "generation" tag of an enode created by quantifier instantiation is set.
          
          Enodes in the input problem have generation 0.
          
          Some combinations of m_qi_cost and m_qi_new_gen will prevent Z3 from breaking matching loops.
          For example, the "Weight 0" performance bug was triggered by the following combination:
              - m_qi_cost:     (+ weight generation)
              - m_qi_new_gen:  cost
          If a quantifier has weight 0, then the cost of instantiating it with a term in the input problem has cost 0.
          The new enodes created during the instantiation will be tagged with generation = const = 0. So, every enode
          will have generation 0, and consequently every quantifier instantiation will have cost 0.
          
          Although dangerous, this feature was requested by the Boogie team. In their case, the patterns are carefully constructed,
          and there are no matching loops. Moreover, the tag some quantifiers with weight 0 to instruct Z3 to never block their instances.
          An example is the select-store axiom. They need this feature to be able to analyze code that contains very long execution paths.

          So, unless requested by the user, the default weight must be > 0. Otherwise, Z3 will execute without any 
          matching loop detection.
        */
        m_qi_cost("(+ weight generation)"),
        m_qi_new_gen("cost"), 
        m_qi_eager_threshold(10.0),
        m_qi_lazy_threshold(20.0), // reduced to give a chance to MBQI
        m_qi_max_eager_multipatterns(0),
        m_qi_max_lazy_multipattern_matching(2),
        m_qi_profile(false),
        m_qi_profile_freq(UINT_MAX),
        m_qi_quick_checker(MC_NO),
        m_qi_lazy_quick_checker(true),
        m_qi_promote_unsat(true),
        m_qi_max_instances(UINT_MAX),
        m_qi_lazy_instantiation(false),
        m_qi_conservative_final_check(false),
        m_mbqi(true), // enabled by default
        m_mbqi_max_cexs(1),
        m_mbqi_max_cexs_incr(1),
        m_mbqi_max_iterations(1000),
        m_mbqi_trace(false),
        m_mbqi_force_template(10),
        m_mbqi_id(nullptr)
    {
        updt_params(p);
    }

    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};

#endif /* QI_PARAMS_H_ */

