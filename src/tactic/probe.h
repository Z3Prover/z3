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
    unsigned m_ref_count = 0;

public:
    virtual ~probe() = default;

    void inc_ref() { ++m_ref_count; }
    void dec_ref() { SASSERT(m_ref_count > 0); --m_ref_count; if (m_ref_count == 0) dealloc(this); }

    virtual result operator()(goal const & g) = 0;
};

typedef ref<probe> probe_ref;

/**
   \brief Self-registration for built-in probes -- the probe analogue of tactic_registration
   (see tactic/tactic.h for the full rationale). Unlike tactics, a probe factory takes no
   arguments and is invoked once per tactic_manager (i.e. once per Z3 context) from
   install_tactics(), constructing a fresh probe object each time -- matching how the old
   ADD_PROBE('name', 'descr', 'code') scraper spliced `code` directly into install_tactics()'s
   body, evaluated fresh on every call.
*/
struct probe_registration {
    typedef probe* (*factory_t)();
    char const * name;
    char const * descr;
    factory_t factory;
    probe_registration * next;
    static inline probe_registration * g_head = nullptr;
    probe_registration(char const * name, char const * descr, factory_t factory):
        name(name), descr(descr), factory(factory), next(g_head) {
        g_head = this;
    }
};

#define Z3_ADD_PROBE(TAG, NAME, DESCR, CODE) \
  inline probe_registration g_z3_probe_registration_##TAG(NAME, DESCR, []() -> probe* { return CODE; })

probe * mk_const_probe(double val);

probe * mk_memory_probe();
probe * mk_depth_probe();
probe * mk_size_probe();

Z3_ADD_PROBE(memory, "memory", "amount of used memory in megabytes.", mk_memory_probe());
Z3_ADD_PROBE(depth, "depth", "depth of the input goal.", mk_depth_probe());
Z3_ADD_PROBE(size, "size", "number of assertions in the given goal.", mk_size_probe());

probe * mk_num_exprs_probe();
probe * mk_num_consts_probe();
probe * mk_num_bool_consts_probe();
probe * mk_num_arith_consts_probe();
probe * mk_num_bv_consts_probe();

Z3_ADD_PROBE(num_exprs, "num-exprs", "number of expressions/terms in the given goal.", mk_num_exprs_probe());
Z3_ADD_PROBE(num_consts, "num-consts", "number of non Boolean constants in the given goal.", mk_num_consts_probe());
Z3_ADD_PROBE(num_bool_consts, "num-bool-consts", "number of Boolean constants in the given goal.", mk_num_bool_consts_probe());
Z3_ADD_PROBE(num_arith_consts, "num-arith-consts", "number of arithmetic constants in the given goal.", mk_num_arith_consts_probe());
Z3_ADD_PROBE(num_bv_consts, "num-bv-consts", "number of bit-vector constants in the given goal.", mk_num_bv_consts_probe());

probe * mk_produce_proofs_probe();
probe * mk_produce_models_probe();
probe * mk_produce_unsat_cores_probe();

Z3_ADD_PROBE(produce_proofs, "produce-proofs", "true if proof generation is enabled for the given goal.", mk_produce_proofs_probe());
Z3_ADD_PROBE(produce_model, "produce-model", "true if model generation is enabled for the given goal.", mk_produce_models_probe());
Z3_ADD_PROBE(produce_unsat_cores, "produce-unsat-cores", "true if unsat-core generation is enabled for the given goal.", mk_produce_unsat_cores_probe());

probe * mk_has_quantifier_probe();
probe * mk_has_pattern_probe();

Z3_ADD_PROBE(has_quantifiers, "has-quantifiers", "true if the goal contains quantifiers.", mk_has_quantifier_probe());
Z3_ADD_PROBE(has_patterns, "has-patterns", "true if the goal contains quantifiers with patterns.", mk_has_pattern_probe());

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

Z3_ADD_PROBE(is_propositional, "is-propositional", "true if the goal is in propositional logic.", mk_is_propositional_probe());
Z3_ADD_PROBE(is_qfbv, "is-qfbv", "true if the goal is in QF_BV.", mk_is_qfbv_probe());
Z3_ADD_PROBE(is_qfaufbv, "is-qfaufbv", "true if the goal is in QF_AUFBV.", mk_is_qfaufbv_probe());

