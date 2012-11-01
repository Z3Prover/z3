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
#ifndef _QI_PARAMS_H_
#define _QI_PARAMS_H_

#include"ini_file.h"

enum quick_checker_mode {
    MC_NO,     // do not use (cheap) model checking based instantiation
    MC_UNSAT,  // instantiate unsatisfied instances
    MC_NO_SAT  // instantiate unsatisfied and not-satisfied instances
};

struct qi_params {
    bool               m_qi_ematching;
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

    bool               m_instgen;

    qi_params():
        /*
          The "weight 0" performance bug
          ------------------------------
          
          The parameters m_qi_cost and m_qi_new_gen influence quantifier instantiation.
          - m_qi_cost: specify the cost of a quantifier instantiation. Z3 will block instantiations using m_qi_eager_threshold and m_qi_lazy_threshold.
          - m_qi_new_gen: specify how the "generation" tag of an enode created by quantifier instantiation is set.
          
          Enodes in the input problem have generation 0.
          
          Some combinations of m_qi_cost and m_qi_new_gen will prevent Z3 from breaking matching loops.
          For example, the "Weight 0" peformace bug was triggered by the following combination:
              - m_qi_cost:     (+ weight generation)
              - m_qi_new_gen:  cost
          If a quantifier has weight 0, then the cost of instantiating it with a term in the input problem has cost 0.
          The new enodes created during the instantiation will be tagged with generation = const = 0. So, every enode
          will have generation 0, and consequently every quantifier instantiation will have cost 0.
          
          Although dangerous, this feature was requested by the Boogie team. In their case, the patterns are carefully constructred,
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
#ifdef _EXTERNAL_RELEASE
        m_mbqi(true), // enabled by default
#else
        m_mbqi(false), // to avoid Rustan whining that the models are not partial anymore.
#endif
        m_mbqi_max_cexs(1),
        m_mbqi_max_cexs_incr(1),
        m_mbqi_max_iterations(1000),
        m_mbqi_trace(false),
        m_mbqi_force_template(10),
        m_instgen(false) {
    }
    
    void register_params(ini_params & p) {
        p.register_unsigned_param("QI_MAX_EAGER_MULTI_PATTERNS", m_qi_max_eager_multipatterns,
                                  "Specify the number of extra multi patterns that are processed eagerly. By default, the prover use at most one multi-pattern eagerly when there is no unary pattern. This value should be smaller than or equal to PI_MAX_MULTI_PATTERNS");
        p.register_unsigned_param("QI_MAX_LAZY_MULTI_PATTERN_MATCHING", m_qi_max_lazy_multipattern_matching, "Maximum number of rounds of matching in a branch for delayed multipatterns. A multipattern is delayed based on the value of QI_MAX_EAGER_MULTI_PATTERNS");
        p.register_string_param("QI_COST", m_qi_cost, "The cost function for quantifier instantiation");
        p.register_string_param("QI_NEW_GEN", m_qi_new_gen, "The function for calculating the generation of newly constructed terms");
        p.register_double_param("QI_EAGER_THRESHOLD", m_qi_eager_threshold, "Threshold for eager quantifier instantiation");
        p.register_double_param("QI_LAZY_THRESHOLD", m_qi_lazy_threshold, "Threshold for lazy quantifier instantiation");
        p.register_bool_param("QI_PROFILE", m_qi_profile);
        p.register_unsigned_param("QI_PROFILE_FREQ", m_qi_profile_freq);
        p.register_int_param("QI_QUICK_CHECKER", 0, 2, reinterpret_cast<int&>(m_qi_quick_checker), "0 - do not use (cheap) model checker, 1 - instantiate instances unsatisfied by current model, 2 - 1 + instantiate instances not satisfied by current model");
        p.register_bool_param("QI_LAZY_QUICK_CHECKER", m_qi_lazy_quick_checker);
        p.register_bool_param("QI_PROMOTE_UNSAT", m_qi_promote_unsat);
        p.register_unsigned_param("QI_MAX_INSTANCES", m_qi_max_instances);
        p.register_bool_param("QI_LAZY_INSTANTIATION", m_qi_lazy_instantiation);
        p.register_bool_param("QI_CONSERVATIVE_FINAL_CHECK", m_qi_conservative_final_check);


        p.register_bool_param("MBQI", m_mbqi, "Model Based Quantifier Instantiation (MBQI)");
        p.register_unsigned_param("MBQI_MAX_CEXS", m_mbqi_max_cexs, "Initial maximal number of counterexamples used in MBQI, each counterexample generates a quantifier instantiation", true);
        p.register_unsigned_param("MBQI_MAX_CEXS_INCR", m_mbqi_max_cexs_incr, "Increment for MBQI_MAX_CEXS, the increment is performed after each round of MBQI", true);
        p.register_unsigned_param("MBQI_MAX_ITERATIONS", m_mbqi_max_iterations, "Maximum number of rounds of MBQI", true);
        p.register_bool_param("MBQI_TRACE", m_mbqi_trace, "Generate tracing messages for Model Based Quantifier Instantiation (MBQI). It will display a message before every round of MBQI, and the quantifiers that were not satisfied.", true);
        p.register_unsigned_param("MBQI_FORCE_TEMPLATE", m_mbqi_force_template, "Some quantifiers can be used as templates for building interpretations for functions. Z3 uses heuristics to decide whether a quantifier will be used as a template or not. Quantifiers with weight >= MBQI_FORCE_TEMPLATE are forced to be used as a template", true);

        p.register_bool_param("INST_GEN", m_instgen, "Enable Instantiation Generation solver (disables other quantifier reasoning)", false);
    }
};

#endif /* _QI_PARAMS_H_ */

