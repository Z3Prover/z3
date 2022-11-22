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

- Find a way to use resolve_value with forbidden interval lemmas.
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

- we are missing a stopping criterion like "first UIP" in  SAT solving. Currently we always resolve backwards until the decision.

--*/

#include "math/polysat/conflict.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/solver.h"
#include "math/polysat/inference_logger.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/superposition.h"
#include "math/polysat/eq_explain.h"
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/saturation.h"
#include "math/polysat/variable_elimination.h"
#include <algorithm>

namespace polysat {

    class conflict_resolver {
        inf_saturate m_saturate;
        ex_polynomial_superposition m_poly_sup;
        free_variable_elimination m_free_variable_elimination;

    public:
        conflict_resolver(solver& s)
            : m_saturate(s)
            , m_poly_sup(s)
            , m_free_variable_elimination(s)
        {}

        bool try_resolve_value(pvar v, conflict& core) {
            if (m_poly_sup.perform(v, core))
                return true;
            if (m_saturate.perform(v, core))
                return true;
            return false;
        }

        // Analyse current conflict core to extract additional lemmas
        void find_extra_lemmas(conflict& core) {
            m_free_variable_elimination.find_lemma(core);
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
            SASSERT(m_vars_occurring.empty());
            SASSERT(m_lemmas.empty());
            SASSERT(m_narrow_queue.empty());
            SASSERT_EQ(m_max_jump_level, UINT_MAX);
        }
        return is_empty;
    }

    void conflict::reset() {
        m_literals.reset();
        m_vars.reset();
        m_var_occurrences.reset();
        m_vars_occurring.reset();
        m_lemmas.reset();
        m_narrow_queue.reset();
        m_level = UINT_MAX;
        m_max_jump_level = UINT_MAX;
        SASSERT(empty());
    }

    bool conflict::is_relevant_pvar(pvar v) const {
        return contains_pvar(v);
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
        m_narrow_queue.push_back(c.blit());  // if the conflict is only due to a missed propagation of c
        set_impl(c);
        logger().begin_conflict();
    }

    void conflict::set(signed_constraint c) {
        SASSERT(!empty());
        remove_all();
        set_impl(c);
    }

    void conflict::set_impl(signed_constraint c) {
        if (c.bvalue(s) == l_false) {
            // boolean conflict
            // This case should not happen:
            // - opposite input literals are handled separately
            // - other boolean conflicts will discover violated clause during boolean propagation
            VERIFY(false);  // fail here to force check when we encounter this case
        }
        else {
            // Constraint c conflicts with the variable assignment
            SASSERT_EQ(c.bvalue(s), l_true);
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
            SASSERT_EQ(c.bvalue(s), l_false);
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
        }
        else {
            logger().begin_conflict(header_with_var("forbidden interval lemma for v", v));
            VERIFY(s.m_viable.resolve(v, *this));
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
            if (!m_var_occurrences[v])
                m_vars_occurring.insert(v);
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

    void conflict::add_lemma(std::initializer_list<signed_constraint> cs) {
        add_lemma(std::data(cs), cs.size());
    }

    void conflict::add_lemma(signed_constraint const* cs, size_t cs_len) {
        clause_builder cb(s);
        for (size_t i = 0; i < cs_len; ++i)
            cb.insert(cs[i]);
        add_lemma(cb.build());
    }

    void conflict::add_lemma(clause_ref lemma) {
        SASSERT(lemma);
        lemma->set_redundant(true);
        LOG_H3("Side lemma: " << *lemma);
        for (sat::literal lit : *lemma) {
            LOG(lit_pp(s, lit));
            SASSERT(s.m_bvars.value(lit) != l_true);
        }
        // TODO: call clause simplifier here?
        //       maybe it reduces the level we have to consider.

        // Two kinds of side lemmas:
        // 1. If all constraints are false, then the side lemma is an alternative conflict lemma.
        //      => we should at least jump back to the second-highest level in the lemma (could be lower, if so justified by another lemma)
        // 2. If there is an undef constraint, then it is is a justification for this new constraint.
        //    (Can there be more than one undef constraint? Should not happen for these lemmas.)
        //      => TODO: (unclear) jump at least to the max level in the lemma and hope the propagation helps there? or ignore it for jump level computation?
        unsigned max_level = 0;  // highest level in lemma
        unsigned jump_level = 0;  // second-highest level in lemma
        bool has_unassigned = false;
        for (sat::literal lit : *lemma) {
            if (!s.m_bvars.is_assigned(lit)) {
                has_unassigned = true;
                continue;
            }
            unsigned const lit_level = s.m_bvars.level(lit);
            if (lit_level > max_level) {
                jump_level = max_level;
                max_level = lit_level;
            } else if (max_level > lit_level && lit_level > jump_level) {
                jump_level = lit_level;
            }
        }
        if (has_unassigned)
            jump_level = max_level;
        LOG("Jump level: " << jump_level);
        m_max_jump_level = std::min(m_max_jump_level, jump_level);
        m_lemmas.push_back(std::move(lemma));
        // If possible, we should set the new constraint to l_true;
        // and re-enable the assertions marked with "tag:true_by_side_lemma".
        // Or we adjust the conflict invariant:
        // - l_true constraints is the default case as before,
        // - l_undef constraints are new and justified by some side lemma, but
        //   should be treated by the conflict resolution methods like l_true
        //   constraints,
        // - l_false constraints are disallowed in the conflict (as before).
    }

    void conflict::remove(signed_constraint c) {
        SASSERT(contains(c));
        m_literals.remove(c.blit().index());
        for (pvar v : c->vars()) {
            m_var_occurrences[v]--;
            if (!m_var_occurrences[v])
                m_vars_occurring.remove(v);
        }
    }

    void conflict::remove_all() {
        SASSERT(!empty());
        m_literals.reset();
        m_vars.reset();
        m_var_occurrences.reset();
        m_vars_occurring.reset();
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

        SASSERT(s.m_bvars.is_evaluation(lit));
        SASSERT(contains(lit));
        SASSERT(!contains(~lit));

        unsigned const lvl = s.m_bvars.level(lit);
        signed_constraint c = s.lit2cnstr(lit);

        // If evaluation depends on a decision,
        // then we rather keep the more general constraint c instead of inserting "x = v"
        // TODO: the old implementation based on bail_vars is broken because it may skip relevant decisions.
        //       is there a way to keep the same effect by adding a side lemma at this point?
        bool has_decision = false;
#if 0
        for (pvar v : c->vars())
            if (s.is_assigned(v) && s.m_justification[v].is_decision())
                m_bail_vars.insert(v), has_decision = true;
#endif

        if (!has_decision) {
            remove(c);
            for (pvar v : c->vars())
                if (s.is_assigned(v) && s.get_level(v) <= lvl)
                    m_vars.insert(v);
        }

        SASSERT(!contains(lit));
        SASSERT(!contains(~lit));

        logger().log(inf_resolve_with_assignment(s, lit, c));
    }

    bool conflict::resolve_value(pvar v) {
        SASSERT(contains_pvar(v));
        SASSERT(s.m_justification[v].is_propagation());

        s.inc_activity(v);

        m_vars.remove(v);
        for (auto const& c : s.m_viable.get_constraints(v))
            insert(c);
        for (auto const& i : s.m_viable.units(v)) {
            insert(s.eq(i.lo(), i.lo_val()));
            insert(s.eq(i.hi(), i.hi_val()));
        }
        logger().log(inf_resolve_value(s, v));

        if (m_resolver->try_resolve_value(v, *this))
            return true;

        return false;
    }

    clause_ref conflict::build_lemma() {
        LOG_H3("Build lemma from core");
        LOG("core: " << *this);

        // TODO: do this after each step?
        m_resolver->find_extra_lemmas(*this);

        clause_builder lemma(s);

        for (auto c : *this)
            lemma.insert(~c);

        for (unsigned v : m_vars) {
            auto eq = s.eq(s.var(v), s.get_value(v));
            lemma.insert_eval(~eq);
        }
        s.decay_activity();

        logger().log_lemma(lemma);
        logger().end_conflict();

        return lemma.build();
    }

    clause_ref_vector conflict::take_side_lemmas() {
#ifndef NDEBUG
        on_scope_exit check_empty([this]() {
            SASSERT(m_lemmas.empty());
        });
#endif
        return std::move(m_lemmas);
    }

    sat::literal_vector conflict::take_narrow_queue() {
#ifndef NDEBUG
        on_scope_exit check_empty([this]() {
            SASSERT(m_narrow_queue.empty());
        });
#endif
        return std::move(m_narrow_queue);
    }

#if 0
    // TODO: convert minimize_vars into a clause simplifier
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
#endif

    std::ostream& conflict::display(std::ostream& out) const {
        char const* sep = "";
        for (auto c : *this)
            out << sep << c->bvar2string() << " " << c, sep = " ; ";
        if (!m_vars.empty())
            out << " vars";
        for (auto v : m_vars)
            out << " v" << v;
        if (!m_lemmas.empty())
            out << " side lemmas";
        for (clause const* lemma : m_lemmas)
            out << " " << show_deref(lemma);
        return out;
    }
}
