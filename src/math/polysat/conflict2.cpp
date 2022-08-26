/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

--*/

#include "math/polysat/conflict2.h"
#include "math/polysat/solver.h"
#include "math/polysat/inference_logger.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/explain.h"
#include "math/polysat/eq_explain.h"
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/saturation.h"
#include "math/polysat/variable_elimination.h"
#include <algorithm>
#include <fstream>

namespace polysat {

    conflict2::conflict2(solver& s) : s(s) {
        // TODO: m_log_conflicts is always false even if "polysat.log_conflicts=true" is given on the command line
        if (true || s.get_config().m_log_conflicts)
            m_logger = alloc(file_inference_logger, s);
        else
            m_logger = alloc(dummy_inference_logger);
    }

    inference_logger& conflict2::logger() {
        return *m_logger;
    }

    bool conflict2::empty() const {
        return m_literals.empty() && m_vars.empty() && m_lemmas.empty();
    }

    void conflict2::reset() {
        m_literals.reset();
        m_vars.reset();
        m_var_occurrences.reset();
        m_lemmas.reset();
        SASSERT(empty());
    }

    void conflict2::init(signed_constraint c) {
        SASSERT(empty());
        if (c.bvalue(s) == l_false) {
            // boolean conflict
            NOT_IMPLEMENTED_YET();
        } else {
            // conflict due to assignment
            SASSERT(c.bvalue(s) == l_true);
            SASSERT(c.is_currently_false(s));
            insert(c);
            insert_vars(c);
        }
        SASSERT(!empty());
    }

    void conflict2::init(pvar v, bool by_viable_fallback) {
        // NOTE: do forbidden interval projection in this method (rather than keeping a separate state like we did before)
        // Option 1: forbidden interval projection
        // Option 2: add all constraints from m_viable + dependent variables

        if (by_viable_fallback) {
            // Conflict detected by viable fallback:
            // initial conflict is the unsat core of the univariate solver
            signed_constraints unsat_core = s.m_viable_fallback.unsat_core(v);
            for (auto c : unsat_core)
                insert(c);
            return;
        }

        // TODO:
        // VERIFY(s.m_viable.resolve(v, *this));
        // log_inference(inf_fi_lemma(v));
    }

    bool conflict2::contains(sat::literal lit) const {
        SASSERT(lit != sat::null_literal);
        return m_literals.contains(lit.index());
    }

    void conflict2::insert(signed_constraint c) {
        if (contains(c))
            return;
        if (c.is_always_true())
            return;
        LOG("Inserting: " << c);
        SASSERT(!c.is_always_false());  // if we add c, the core would be a tautology
        SASSERT(!c->vars().empty());
        m_literals.insert(c.blit().index());
        for (pvar v : c->vars()) {
            if (v >= m_var_occurrences.size())
                m_var_occurrences.resize(v + 1, 0);
            m_var_occurrences[v]++;
        }
    }

    void conflict2::remove(signed_constraint c) {
        SASSERT(contains(c));
        m_literals.remove(c.blit().index());
        for (pvar v : c->vars())
            m_var_occurrences[v]--;
    }

    void conflict2::insert_vars(signed_constraint c) {
        for (pvar v : c->vars())
            if (s.is_assigned(v))
                m_vars.insert(v);
    }

    std::ostream& conflict2::display(std::ostream& out) const {
        out << "TODO\n";
    }
}
