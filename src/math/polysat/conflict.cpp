/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

TODO:
- update notes/example above

- question: if a side lemma justifies a constraint, then we resolve over one of the premises of the lemma; do we want to update the lemma or not?

- conflict resolution plugins
    - may generate lemma
        - post-processing/simplification on lemma (e.g., literal subsumption; can be done in solver)
    - may force backjumping without further conflict resolution (e.g., if applicable lemma was found by global analysis of search state)
    - bailout lemma if no method applies (log these cases in particular because it indicates where we are missing something)
    - force a restart if we get a bailout lemma or non-asserting conflict?

- store the side lemmas as well (but only those that justify a constraint in the final lemma, recursively)

- consider case if v is both in vars and bail_vars (do we need to keep it in bail_vars even if we can eliminate it from vars?)

- Find a way to use resolve_value with forbidden interval lemmas.
  Then get rid of conflict_kind_t::backtrack and m_relevant_vars.
  Maybe:
    x := a, y := b, z has no viable value
    - assume y was propagated
    - FI-Lemma C1 \/ ... \/ Cn without z.
    - for each i, we should have x := a /\ Ci ==> y != b
    - can we choose one of the Ci to cover the domain of y and extract an FI-Lemma D1 \/ ... \/ Dk without y,z?
    - or try to find an L(x,y) such that C1 -> L, ..., Cn -> L, and L -> y != b  (under x := a); worst case y != b can work as L

- fix minimize_vars:
    - it is not sound to do minimization for each constraint separately, if there are multiple constraints.
    - condition `c.is_currently_false(s, a)` is too weak (need also `c.bvalue(s) == l_true`?)

--*/

#include "math/polysat/conflict.h"
#include "math/polysat/clause_builder.h"
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

namespace polysat {

    class conflict_resolver {
        inf_saturate m_saturate;

    public:
        conflict_resolver(solver& s)
            : m_saturate(s)
        {}

        bool try_resolve_value(pvar v, conflict& core) {
            if (m_saturate.perform(v, core))
                return true;
            return false;
        }
    };

    class header_with_var : public displayable {
        char const* m_text;
        pvar m_var;
    public:
        header_with_var(char const* text, pvar var) : m_text(text), m_var(var) { SASSERT(text); }
        std::ostream& display(std::ostream& out) const override { return out << m_text << m_var; }
    };

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

    conflict::conflict(solver& s) : s(s) {
        // TODO: m_log_conflicts is always false even if "polysat.log_conflicts=true" is given on the command line
        if (true || s.get_config().m_log_conflicts)
            m_logger = alloc(file_inference_logger, s);
        else
            m_logger = alloc(dummy_inference_logger);
        m_resolver = alloc(conflict_resolver, s);
    }

    conflict::~conflict() {}

    inference_logger& conflict::logger() {
        return *m_logger;
    }

    conflict::const_iterator conflict::begin() const {
        return conflict_iterator::begin(s.m_constraints, m_literals);
    }

    conflict::const_iterator conflict::end() const {
        return conflict_iterator::end(s.m_constraints, m_literals);
    }

    bool conflict::empty() const {
        bool const is_empty = (m_level == UINT_MAX);
        if (is_empty) {
            SASSERT(m_literals.empty());
            SASSERT(m_vars.empty());
            SASSERT(m_bail_vars.empty());
            SASSERT(m_lemmas.empty());
        }
        return is_empty;
    }

    void conflict::reset() {
        m_literals.reset();
        m_vars.reset();
        m_bail_vars.reset();
        m_relevant_vars.reset();
        m_var_occurrences.reset();
        m_lemmas.reset();
        m_kind = conflict_kind_t::ok;
        m_level = UINT_MAX;
        SASSERT(empty());
    }

    void conflict::set_bailout() {
        SASSERT(m_kind == conflict_kind_t::ok);
        m_kind = conflict_kind_t::bailout;
        s.m_stats.m_num_bailouts++;
    }

    void conflict::set_backtrack() {
        SASSERT(m_kind == conflict_kind_t::ok);
        SASSERT(m_relevant_vars.empty());
        m_kind = conflict_kind_t::backtrack;

    }
    void conflict::set_backjump() {
        SASSERT(m_kind == conflict_kind_t::ok);
        m_kind = conflict_kind_t::backjump;
    }

    bool conflict::is_relevant_pvar(pvar v) const {
        switch (m_kind) {
        case conflict_kind_t::ok:
            return contains_pvar(v);
        case conflict_kind_t::bailout:
            return true;
        case conflict_kind_t::backtrack:
            return pvar_occurs_in_constraints(v) || m_relevant_vars.contains(v);
        case conflict_kind_t::backjump:
            UNREACHABLE();  // we don't follow the regular loop when backjumping
            return false;
        }
        UNREACHABLE();
        return false;
    }

    bool conflict::is_relevant(sat::literal lit) const {
        return contains(lit) || contains(~lit);
    }

    void conflict::init_at_base_level() {
        SASSERT(empty());
        SASSERT(s.at_base_level());
        m_level = s.m_level;
        SASSERT(!empty());
    }

    void conflict::init(signed_constraint c) {
        SASSERT(empty());
        m_level = s.m_level;
        set_impl(c);
        logger().begin_conflict();
    }

    void conflict::set(signed_constraint c) {
        reset();
        set_impl(c);
    }

    void conflict::set_impl(signed_constraint c) {
        if (c.bvalue(s) == l_false) {
            // boolean conflict
            // This case should not happen:
            // - opposite input literals are handled separately
            // - other boolean conflicts will discover violated clause during boolean propagation
            VERIFY(false);  // fail here to force check when we encounter this case
        } else {
            // conflict due to assignment
            SASSERT(c.bvalue(s) == l_true);
            SASSERT(c.is_currently_false(s));
            insert(c);
            insert_vars(c);
        }
        SASSERT(!empty());
    }

    void conflict::init(clause const& cl) {
        SASSERT(empty());
        m_level = s.m_level;
        for (auto lit : cl) {
            auto c = s.lit2cnstr(lit);
            SASSERT(c.bvalue(s) == l_false);
            insert(~c);
        }
        SASSERT(!empty());
        logger().begin_conflict();
    }

    void conflict::init(pvar v, bool by_viable_fallback) {
        SASSERT(empty());
        m_level = s.m_level;
        if (by_viable_fallback) {
            logger().begin_conflict(header_with_var("unsat core from viable fallback for v", v));
            // Conflict detected by viable fallback:
            // initial conflict is the unsat core of the univariate solver,
            // and the assignment (under which the constraints are univariate in v)
            // TODO:
            // - currently we add variables directly, which is sound:
            //      e.g.:   v^2 + w^2 == 0;   w := 1
            // - but we could use side constraints on the coefficients instead (coefficients when viewed as polynomial over v):
            //      e.g.:   v^2 + w^2 == 0;   w^2 == 1
            signed_constraints unsat_core = s.m_viable_fallback.unsat_core(v);
            for (auto c : unsat_core) {
                insert(c);
                insert_vars(c);
            }
            SASSERT(!m_vars.contains(v));
            // TODO: apply conflict resolution plugins here too?
        } else {
            logger().begin_conflict(header_with_var("forbidden interval lemma for v", v));
            set_backtrack();
            VERIFY(s.m_viable.resolve(v, *this));
            // TODO: in general the forbidden interval lemma is not asserting.
            //       but each branch exclude the current assignment.
            //       in those cases we will (additionally?) need an abstraction that is asserting to make sure viable is updated properly.
        }
        SASSERT(!empty());
    }

    bool conflict::contains(sat::literal lit) const {
        SASSERT(lit != sat::null_literal);
        return m_literals.contains(lit.index());
    }

    void conflict::insert(signed_constraint c) {
        if (contains(c))
            return;
        if (c.is_always_true())
            return;
        LOG("Inserting " << lit_pp(s, c));
        SASSERT_EQ(c.bvalue(s), l_true);
        SASSERT(!c.is_always_false());  // if we added c, the core would be a tautology
        SASSERT(!c->vars().empty());
        m_literals.insert(c.blit().index());
        for (pvar v : c->vars()) {
            if (v >= m_var_occurrences.size())
                m_var_occurrences.resize(v + 1, 0);
            m_var_occurrences[v]++;
        }
    }

    void conflict::insert_eval(signed_constraint c) {
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

    void conflict::insert_vars(signed_constraint c) {
        for (pvar v : c->vars())
            if (s.is_assigned(v))
                m_vars.insert(v);
    }

    void conflict::remove(signed_constraint c) {
        SASSERT(contains(c));
        m_literals.remove(c.blit().index());
        for (pvar v : c->vars())
            m_var_occurrences[v]--;
    }

    void conflict::insert(signed_constraint c, clause_ref lemma) {
        unsigned const idx = c.blit().to_uint();
        SASSERT(!contains(c));  // not required, but this case should be checked
        SASSERT(!m_lemmas.contains(idx));  // not required, but this case should be checked
        insert(c);
        m_lemmas.insert(idx, lemma);
    }

    clause* conflict::side_lemma(sat::literal lit) const {
        unsigned const idx = lit.to_uint();
        return m_lemmas.get(idx, {}).get();
    }

    void conflict::resolve_bool(sat::literal lit, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

        SASSERT(contains(lit));
        SASSERT(count(cl, lit) > 0);
        SASSERT(!contains(~lit));
        SASSERT(count(cl, ~lit) == 0);

        remove(s.lit2cnstr(lit));
        for (sat::literal other : cl)
            if (other != lit)
                insert(s.lit2cnstr(~other));

        logger().log(inf_resolve_bool(lit, cl));
    }

    void conflict::resolve_with_assignment(sat::literal lit) {
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

    bool conflict::resolve_value(pvar v) {

        if (is_bailout())
            return false;

        if (is_backtracking()) {
            for (auto const& c : s.m_viable.get_constraints(v))
                for (pvar v : c->vars()) {
                    m_relevant_vars.insert(v);
                    logger().log_var(v);
                }
            return false;
        }

        SASSERT(contains_pvar(v));
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

        if (m_resolver->try_resolve_value(v, *this))
            return true;

        // No conflict resolution plugin succeeded => give up and bail out
        set_bailout();
        // Need to keep the variable in case of decision
        if (s.is_assigned(v) && j.is_decision())
            m_vars.insert(v);
        logger().log("Bailout");
        return false;
    }

    clause_ref conflict::build_lemma() {
        LOG_H3("Build lemma from core");
        LOG("core: " << *this);
        clause_builder lemma(s);

#if 0
        if (m_literals.size() == 1) {
            auto c = *begin();
            minimize_vars(c);
        }
#endif

        for (auto c : *this)
            lemma.push(~c);

        for (unsigned v : m_vars) {
            auto eq = s.eq(s.var(v), s.get_value(v));
            if (eq.bvalue(s) == l_undef)
                s.assign_eval(eq.blit());
            lemma.push(~eq);
        }
        s.decay_activity();

        logger().log_lemma(lemma);
        logger().end_conflict();

        // TODO: additional lemmas

        return lemma.build();
    }

    bool conflict::minimize_vars(signed_constraint c) {
        if (m_vars.empty())
            return false;
        if (!c.is_currently_false(s))
            return false;

        assignment_t a;
        for (auto v : m_vars)
            a.push_back(std::make_pair(v, s.get_value(v)));
        for (unsigned i = 0; i < a.size(); ++i) {
            std::pair<pvar, rational> save = a[i];
            std::pair<pvar, rational> last = a.back();
            a[i] = last;
            a.pop_back();
            if (c.is_currently_false(s, a))
                --i;
            else {
                a.push_back(last);
                a[i] = save;
            }
        }
        if (a.size() == m_vars.num_elems())
            return false;
        m_vars.reset();
        for (auto const& [v, val] : a)
            m_vars.insert(v);
        logger().log("minimize vars");
        LOG("reduced " << m_vars);
        return true;
    }

    std::ostream& conflict::display(std::ostream& out) const {
        char const* sep = "";
        for (auto c : *this)
            out << sep << c->bvar2string() << " " << c, sep = " ; ";
        if (!m_vars.empty())
            out << " vars";
        for (auto v : m_vars)
            out << " v" << v;
        if (!m_bail_vars.empty())
            out << " bail vars";
        for (auto v : m_bail_vars)
            out << " v" << v;
        return out;
    }
}
