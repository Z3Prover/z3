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

    struct inf_resolve_bool : public inference {
        sat::literal m_lit;
        clause const& m_clause;
        inf_resolve_bool(sat::literal lit, clause const& cl) : m_lit(lit), m_clause(cl) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Resolve upon " << m_lit << " with " << m_clause;
        }
    };

    struct inf_resolve_with_assignment : public inference {
        solver& s;
        sat::literal lit;
        signed_constraint c;
        inf_resolve_with_assignment(solver& s, sat::literal lit, signed_constraint c) : s(s), lit(lit), c(c) {}
        std::ostream& display(std::ostream& out) const override {
            out << "Resolve upon " << lit << " with assignment:";
            for (pvar v : c->vars())
                if (s.is_assigned(v))
                    out << " " << assignment_pp(s, v, s.get_value(v), true);
            return out;
        }
    };

    struct inf_resolve_value : public inference {
        solver& s;
        pvar v;
        inf_resolve_value(solver& s, pvar v) : s(s), v(v) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Value resolution with " << assignment_pp(s, v, s.get_value(v), true);
        }
    };

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
        m_kind = conflict2_kind_t::ok;
        SASSERT(empty());
    }

    void conflict2::set_bailout() {
        SASSERT(m_kind == conflict2_kind_t::ok);
        m_kind = conflict2_kind_t::bailout;
        s.m_stats.m_num_bailouts++;
    }

    void conflict2::set_backjump() {
        SASSERT(m_kind == conflict2_kind_t::ok);
        m_kind = conflict2_kind_t::backjump;
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
        logger().begin_conflict();
    }

    void conflict2::init(pvar v, bool by_viable_fallback) {
        if (by_viable_fallback) {
            // Conflict detected by viable fallback:
            // initial conflict is the unsat core of the univariate solver
            signed_constraints unsat_core = s.m_viable_fallback.unsat_core(v);
            for (auto c : unsat_core)
                insert(c);
            logger().begin_conflict("unsat core from viable fallback");
            // TODO: apply conflict resolution plugins here too?
        } else {
            VERIFY(s.m_viable.resolve(v, *this));
            // TODO: in general the forbidden interval lemma is not asserting.
            //       but each branch exclude the current assignment.
            //       in those cases we will (additionally?) need an abstraction that is asserting to make sure viable is updated properly.
            set_backjump();
            logger().begin_conflict("forbidden interval lemma");
        }
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
        SASSERT(!c.is_always_false());  // if we added c, the core would be a tautology
        SASSERT(!c->vars().empty());
        m_literals.insert(c.blit().index());
        for (pvar v : c->vars()) {
            if (v >= m_var_occurrences.size())
                m_var_occurrences.resize(v + 1, 0);
            m_var_occurrences[v]++;
        }
    }

    void conflict2::insert_eval(signed_constraint c) {
        switch (c.bvalue(s)) {
        case l_undef:
            s.assign_eval(c.blit());
            break;
        case l_true:
            break;
        case l_false:
            break;
        }
        insert(c);
    }

    void conflict2::insert_vars(signed_constraint c) {
        for (pvar v : c->vars())
            if (s.is_assigned(v))
                m_vars.insert(v);
    }

    void conflict2::remove(signed_constraint c) {
        SASSERT(contains(c));
        m_literals.remove(c.blit().index());
        for (pvar v : c->vars())
            m_var_occurrences[v]--;
    }

    void conflict2::resolve_bool(sat::literal lit, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

        SASSERT(contains(lit));
        SASSERT(std::count(cl.begin(), cl.end(), lit) > 0);
        SASSERT(!contains(~lit));
        SASSERT(std::count(cl.begin(), cl.end(), ~lit) == 0);

        remove(s.lit2cnstr(lit));
        for (sat::literal other : cl)
            if (other != lit)
                insert(s.lit2cnstr(~other));

        logger().log(inf_resolve_bool(lit, cl));
    }

    void conflict2::resolve_with_assignment(sat::literal lit) {
        // The reason for lit is conceptually:
        //    x1 = v1 /\ ... /\ xn = vn ==> lit

        SASSERT(contains(lit));
        SASSERT(!contains(~lit));

        if (is_backjumping())
            return;

        unsigned const lvl = s.m_bvars.level(lit);
        signed_constraint c = s.lit2cnstr(lit);

        // If evaluation depends on a decision,
        // then we rather keep the more general constraint c instead of inserting "x = v"
        bool has_decision = false;
        for (pvar v : c->vars())
            if (s.is_assigned(v) && s.m_justification[v].is_decision())
                m_bail_vars.insert(v), has_decision = true;

        if (!has_decision) {
            remove(c);
            for (pvar v : c->vars())
                if (s.is_assigned(v) && s.get_level(v) <= lvl)
                    m_vars.insert(v);
        }

        logger().log(inf_resolve_with_assignment(s, lit, c));
    }

    bool conflict2::resolve_value(pvar v) {
        SASSERT(contains_pvar(v));

        if (is_backjumping()) {
            for (auto const& c : s.m_viable.get_constraints(v))
                for (pvar v : c->vars())
                    logger().log_var(v);
            return false;
        }

        if (is_bailout())
            return false;

        auto const& j = s.m_justification[v];

        if (j.is_decision() && m_bail_vars.contains(v))   // TODO: what if also m_vars.contains(v)? might have a chance at elimination
            return false;

        s.inc_activity(v);
        m_vars.remove(v);

        if (j.is_propagation()) {
            for (auto const& c : s.m_viable.get_constraints(v))
                insert_eval(c);
            for (auto const& i : s.m_viable.units(v)) {
                insert_eval(s.eq(i.lo(), i.lo_val()));
                insert_eval(s.eq(i.hi(), i.hi_val()));
            }
        }
        logger().log(inf_resolve_value(s, v));

        // TODO: call conflict resolution plugins here; "return true" if successful

        // No conflict resolution plugin succeeded => give up and bail out
        set_bailout();
        // Need to keep the variable in case of decision
        if (s.is_assigned(v) && j.is_decision())
            m_vars.insert(v);
        logger().log("bailout");
        return false;
    }

    std::ostream& conflict2::display(std::ostream& out) const {
        out << "TODO\n";
        return out;
    }
}
