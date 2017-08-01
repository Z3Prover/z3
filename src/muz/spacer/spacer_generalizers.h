/*++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_generalizers.h

Abstract:

    Generalizer plugins.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-22.
    Arie Gurfinkel
Revision History:

--*/

#ifndef _SPACER_GENERALIZERS_H_
#define _SPACER_GENERALIZERS_H_

#include "muz/spacer/spacer_context.h"
#include "ast/arith_decl_plugin.h"

namespace spacer {

// can be used to check whether produced core is really implied by
// frame and therefore valid TODO: or negation?
class lemma_sanity_checker : public lemma_generalizer {
public:
    lemma_sanity_checker(context& ctx) : lemma_generalizer(ctx) {}
    virtual ~lemma_sanity_checker() {}
    virtual void operator()(lemma_ref &lemma);
};

/**
 * Boolean inductive generalization by dropping literals
 */
class lemma_bool_inductive_generalizer : public lemma_generalizer {

    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() {reset();}
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    unsigned m_failure_limit;
    stats m_st;

public:
    lemma_bool_inductive_generalizer(context& ctx, unsigned failure_limit) :
        lemma_generalizer(ctx), m_failure_limit(failure_limit) {}
    virtual ~lemma_bool_inductive_generalizer() {}
    virtual void operator()(lemma_ref &lemma);

    virtual void collect_statistics(statistics& st) const;
    virtual void reset_statistics() {m_st.reset();}
};

class unsat_core_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    stats m_st;
public:
    unsat_core_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    virtual ~unsat_core_generalizer() {}
    virtual void operator()(lemma_ref &lemma);

    virtual void collect_statistics(statistics &st) const;
    virtual void reset_statistics() {m_st.reset();}
};

class lemma_array_eq_generalizer : public lemma_generalizer {
public:
    lemma_array_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    virtual ~lemma_array_eq_generalizer() {}
    virtual void operator()(lemma_ref &lemma);

};

class lemma_eq_generalizer : public lemma_generalizer {
public:
    lemma_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    virtual ~lemma_eq_generalizer() {}
    virtual void operator()(lemma_ref &lemma);
};


};
#endif
