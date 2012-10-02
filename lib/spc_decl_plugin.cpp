/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-12.

Revision History:

--*/
#include"spc_decl_plugin.h"

std::ostream & operator<<(std::ostream & out, spc_op_kind k) {
    switch (k) {
    case PR_DEMODULATION:              out << "demod"; break;
    case PR_SPC_REWRITE:               out << "rewrite"; break;
    case PR_SPC_RESOLUTION:            out << "res"; break;
    case PR_SUPERPOSITION:             out << "sup"; break;
    case PR_EQUALITY_RESOLUTION:       out << "eq_res"; break;
    case PR_FACTORING:                 out << "fact"; break;
    case PR_SPC_DER:                   out << "der"; break;
    case PR_SPC_ASSERTED:              out << "asserted"; break;
    default:                           out << "unknown"; break;
    }
    return out;
}

spc_decl_plugin::spc_decl_plugin() :
    m_demodulation("demod"),
    m_spc_rewrite("sp-rw"),
    m_spc_resolution("sp-res"),
    m_superposition("sp"),
    m_equality_resolution("eq-res"),
    m_factoring("fact"),
    m_spc_der("spc-der") {
}
    
spc_decl_plugin::~spc_decl_plugin() {
}

sort * spc_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    UNREACHABLE();
    return 0;
}

func_decl * spc_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                          unsigned arity, sort * const * domain, sort * range) {
    
#define MK_PROOF(SYM) m_manager->mk_func_decl(SYM, arity, domain, m_manager->mk_proof_sort(), func_decl_info(m_family_id, k))
    
    SASSERT(num_parameters == 0);
    switch (k) {
        /*
          #1: (forall (x) (= t[x] s[x]))
          [demod #1] (= t[a] s[a])
        */
    case PR_DEMODULATION:           return MK_PROOF(m_demodulation);
        /*
          Justifies a rewriting (simplification step) in the superposition engine.
          It has n+1 antecedents. The first antecedent is the clause being simplified.
          The other antecedents are demodulators.
          The consequent is the simplied clause.
        */
    case PR_SPC_REWRITE:            return MK_PROOF(m_spc_rewrite);
        /*
          Resolution proof:

          #1: (or C l)
          #2: (or D (not l'))
          [sp-res #1 #2]: sigma(or C D)

          where sigma is the mgu of l and l'

        */
    case PR_SPC_RESOLUTION:         return MK_PROOF(m_spc_resolution);
        /*
          Superposition proof:

          #1: (or (= s t) R)
          #2: D[u]
          [sp #1 #2]: sigma(or R D[t])

          where sigma is the mgu(u, s)
        */
    case PR_SUPERPOSITION:          return MK_PROOF(m_superposition);
        /*
          Equality resolution proof:

          #1: (or (not (= s t)) R)
          [eq-res #1]: sigma R

          where sigma is the mgu of s and t.
        */
    case PR_EQUALITY_RESOLUTION:    return MK_PROOF(m_equality_resolution);
        /*
          Proof object for factoring and equality-factoring:

          #1: (or P[t] P[s] R)
          [fact #1]: sigma(or P[t] R)

          where sigma is the mgu(t,s)

          #1: (or (= s t) (= u v) R)
          [fact #1]: sigma(or (not (= t v)) (= u v) R)

          where sigma = mgu(s, u)
        */
    case PR_FACTORING:              return MK_PROOF(m_factoring);
        /*
          Proof object for destructive equality resolution:

          #1: (or (not (= x t)) C[x])
          [spc-der #1]: C[t]

          t does not contain x.
          
          Several variables may be eliminated simultaneously.
        */
    case PR_SPC_DER:                return MK_PROOF(m_spc_der);
    default:
        UNREACHABLE();
        return 0;
    }

}


