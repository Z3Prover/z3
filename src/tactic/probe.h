/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    probe.h

Abstract:

    Evaluates/Probes a goal.

    A probe is used to build tactics (aka strategies) that
    makes decisions based on the structure of a goal.

    The current implementation is very simple.

Author:

    Leonardo de Moura (leonardo) 2011-10-13.

Revision History:

--*/
#pragma once

#include "tactic/goal.h"

class probe {
public:
    class result {
        double m_value;
    public:
        result(double v = 0.0):m_value(v) {}
        result(unsigned v):m_value(static_cast<double>(v)) {}
        result(int v):m_value(static_cast<double>(v)) {}
        result(bool b):m_value(b ? 1.0 : 0.0) {}

        bool is_true() const { return m_value != 0.0; }
        double get_value() const { return m_value; }
    };

private:
    unsigned m_ref_count;

public:
    probe():m_ref_count(0) {}
    virtual ~probe() {}

    void inc_ref() { ++m_ref_count; }
    void dec_ref() { SASSERT(m_ref_count > 0); --m_ref_count; if (m_ref_count == 0) dealloc(this); }

    virtual result operator()(goal const & g) = 0;
};

typedef ref<probe> probe_ref;

probe * mk_const_probe(double val);

probe * mk_memory_probe();
probe * mk_depth_probe();
probe * mk_size_probe();

/*
  ADD_PROBE("memory", "amount of used memory in megabytes.", "mk_memory_probe()")
  ADD_PROBE("depth", "depth of the input goal.", "mk_depth_probe()")
  ADD_PROBE("size", "number of assertions in the given goal.", "mk_size_probe()")
*/

probe * mk_num_exprs_probe();
probe * mk_num_consts_probe();
probe * mk_num_bool_consts_probe();
probe * mk_num_arith_consts_probe();
probe * mk_num_bv_consts_probe();

/*
  ADD_PROBE("num-exprs", "number of expressions/terms in the given goal.", "mk_num_exprs_probe()")
  ADD_PROBE("num-consts", "number of non Boolean constants in the given goal.", "mk_num_consts_probe()")
  ADD_PROBE("num-bool-consts", "number of Boolean constants in the given goal.", "mk_num_bool_consts_probe()")
  ADD_PROBE("num-arith-consts", "number of arithmetic constants in the given goal.", "mk_num_arith_consts_probe()")
  ADD_PROBE("num-bv-consts", "number of bit-vector constants in the given goal.", "mk_num_bv_consts_probe()")
*/

probe * mk_produce_proofs_probe();
probe * mk_produce_models_probe();
probe * mk_produce_unsat_cores_probe();

/*
  ADD_PROBE("produce-proofs", "true if proof generation is enabled for the given goal.", "mk_produce_proofs_probe()")
  ADD_PROBE("produce-model", "true if model generation is enabled for the given goal.", "mk_produce_models_probe()")
  ADD_PROBE("produce-unsat-cores", "true if unsat-core generation is enabled for the given goal.", "mk_produce_unsat_cores_probe()")
*/

probe * mk_has_quantifier_probe();
probe * mk_has_pattern_probe();

/*
  ADD_PROBE("has-quantifiers", "true if the goal contains quantifiers.", "mk_has_quantifier_probe()")
  ADD_PROBE("has-patterns", "true if the goal contains quantifiers with patterns.", "mk_has_pattern_probe()")
*/

// Some basic combinators for probes
probe * mk_not(probe * p1);
probe * mk_and(probe * p1, probe * p2);
probe * mk_or(probe * p1, probe * p2);
probe * mk_implies(probe * p1, probe * p2);
probe * mk_eq(probe * p1, probe * p2);
probe * mk_neq(probe * p1, probe * p2);
probe * mk_le(probe * p1, probe * p2);
probe * mk_lt(probe * p1, probe * p2);
probe * mk_ge(probe * p1, probe * p2);
probe * mk_gt(probe * p1, probe * p2);
probe * mk_add(probe * p1, probe * p2);
probe * mk_sub(probe * p1, probe * p2);
probe * mk_mul(probe * p1, probe * p2);
probe * mk_div(probe * p1, probe * p2);

probe * mk_is_propositional_probe();
probe * mk_is_qfbv_probe();
probe * mk_is_qfaufbv_probe();
probe * mk_is_qfufbv_probe();

/*
  ADD_PROBE("is-propositional", "true if the goal is in propositional logic.", "mk_is_propositional_probe()")
  ADD_PROBE("is-qfbv", "true if the goal is in QF_BV.", "mk_is_qfbv_probe()")
  ADD_PROBE("is-qfaufbv", "true if the goal is in QF_AUFBV.", "mk_is_qfaufbv_probe()")
*/

