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
        saturation m_saturation;
        ex_polynomial_superposition m_poly_sup;
        free_variable_elimination m_free_variable_elimination;

    public:
        conflict_resolver(solver& s)
            : m_saturation(s)
            , m_poly_sup(s)
            , m_free_variable_elimination(s)
        {}

        void infer_lemmas_for_value(pvar v, conflict& core) {
            (void)m_poly_sup.perform(v, core);
            m_saturation.perform(v, core);
        }

        void infer_lemmas_for_value(pvar v, signed_constraint const& c, conflict& core) {
            (void)m_saturation.perform(v, c, core);
        }

        // Analyse current conflict core to extract additional lemmas
        void find_extra_lemmas(conflict& core) {
            m_saturation.try_div_monotonicity(core);
#if 1
            // Don't do variable elimination for now
#else
            m_free_variable_elimination.find_lemma(core);
#endif
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

    struct inf_resolve_evaluated : public inference {
        solver& s;
        sat::literal lit;
        signed_constraint c;
        inf_resolve_evaluated(solver& s, sat::literal lit, signed_constraint c) : s(s), lit(lit), c(c) {}
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
        m_resolver = alloc(conflict_resolver, s);
    }

    conflict::~conflict() {}

    inference_logger& conflict::logger() {
        if (!m_logger) {
            if (s.config().m_log_conflicts)
                m_logger = alloc(file_inference_logger, s);
            else
                m_logger = alloc(dummy_inference_logger);
        }
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
            SASSERT(m_dep.is_null());
        }
        return is_empty;
    }

    void conflict::reset() {
        LOG("Reset conflict");
        m_literals.reset();
        m_vars.reset();
        m_var_occurrences.reset();
        m_vars_occurring.reset();
        m_lemmas.reset();
        m_narrow_queue.reset();
        m_level = UINT_MAX;
        m_dep = null_dependency;
        SASSERT(empty());
    }

    bool conflict::is_relevant_pvar(pvar v) const {
        return contains_pvar(v);
    }

    bool conflict::is_relevant(sat::literal lit) const {
        return contains(lit) || contains(~lit);
    }

    unsigned conflict::effective_level() const {
        SASSERT(!empty());
        // If m_dep is set, the corresponding constraint was asserted at m_level and is not valid earlier.
        if (!m_dep.is_null())
            return m_level;
        // In other cases, m_level just tracks the level at which the conflict appeared.
        // Find the minimal level at which the conflict is still valid.
        unsigned lvl = 0;
        for (unsigned lit_idx : m_literals) {
            sat::literal const lit = sat::to_literal(lit_idx);
            lvl = std::max(lvl, s.m_bvars.level(lit));
        }
        for (pvar v : m_vars)
            lvl = std::max(lvl, s.get_level(v));
        return lvl;
    }

    bool conflict::is_valid() const {
        SASSERT(!empty());
        // If m_dep is set, the corresponding constraint was asserted at m_level and is not valid earlier.
        if (!m_dep.is_null() && m_level > s.m_level)
            return false;
        // All conflict constraints must be bool-assigned.
        for (unsigned lit_idx : m_literals)
            if (!s.m_bvars.is_assigned(sat::to_literal(lit_idx)))
                return false;
        // All conflict variables must be assigned.
        for (pvar v : m_vars)
            if (!s.is_assigned(v))
                return false;
        return true;
    }

    void conflict::init_at_base_level(dependency dep) {
        SASSERT(empty());
        SASSERT(s.at_base_level());
        m_level = s.m_level;
        m_dep = dep;
        SASSERT(!empty());
        // TODO: logger().begin_conflict???
        // TODO: check uses of logger().begin_conflict(). sometimes we call it before adding constraints, sometimes after...
        logger().begin_conflict("base level");
    }

    void conflict::init(dependency dep, signed_constraint c) {
        SASSERT(empty());
        m_level = s.m_level;
        m_dep = dep;
        SASSERT(!empty());
        insert_vars(c);
        logger().begin_conflict();
    }


    void conflict::init(signed_constraint c) {
        LOG("Conflict: constraint " << lit_pp(s, c));
        SASSERT(empty());
        m_level = s.m_level;
        m_narrow_queue.push_back(c.blit());  // if the conflict is only due to a missed propagation of c
        VERIFY_EQ(c.bvalue(s), l_true);
        SASSERT(c.is_currently_false(s));
        insert(c);
        insert_vars(c);
        SASSERT(!empty());
        logger().begin_conflict();
    }

    void conflict::init(clause& cl) {
        LOG("Conflict: clause " << cl);
        for (sat::literal lit : cl)
            LOG("    " << lit_pp(s, lit));
        SASSERT(empty());
        m_level = s.m_level;
        for (auto lit : cl) {
            auto c = s.lit2cnstr(lit);
            VERIFY_EQ(c.bvalue(s), l_false);
            insert(~c);
        }

        // NOTE: usually in SAT solving, the conflict clause has at least two false literals at the max level.
        //       (otherwise, the last literal would have been propagated at an earlier level.)
        //       This is not true if we add clauses on demand;
        //       after backtracking we may have the case that the conflict clause has
        //       exactly one undefined literal that must be propagated explicitly.
        m_lemmas.push_back(&cl);

        SASSERT(!empty());
        logger().begin_conflict(cl.name());
    }

    void conflict::init_by_viable_interval(pvar v) {
        LOG("Conflict: viable_interval v" << v);
        SASSERT(empty());
        SASSERT(!s.is_assigned(v));
        m_level = s.m_level;
        logger().begin_conflict(header_with_var("viable_interval v", v));
        if (s.m_viable.resolve_interval(v, *this)) {
            revert_pvar(v);  // at this point, v is not assigned
        }
        SASSERT(!empty());
    }

    void conflict::init_viable_fallback_begin(pvar v) {
        LOG("Conflict: viable_fallback v" << v);
        SASSERT(empty());
        SASSERT(!s.is_assigned(v));
        m_level = s.m_level;
        logger().begin_conflict(header_with_var("viable_fallback v", v));
    }

    void conflict::init_viable_fallback_end(pvar v) {
        SASSERT(!empty());
        revert_pvar(v);  // at this point, v is not assigned
    }

    bool conflict::contains(sat::literal lit) const {
        SASSERT(lit != sat::null_literal);
        return m_literals.contains(lit.index());
    }

    void conflict::insert(signed_constraint c) {
        if (contains(c))
            return;
        if (c.is_always_true())  // TODO: caller should avoid this?
            return;
        LOG("Inserting " << lit_pp(s, c));
        SASSERT_EQ(c.bvalue(s), l_true);
        VERIFY_EQ(c.bvalue(s), l_true);
        SASSERT(!c.is_always_true());   // such constraints would be removed earlier
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

    bool conflict::insert_or_replace(signed_constraint c) {
        // TODO: what if we have already passed c in the trail in resolve_conflict? should check that. (probably restart the resolve_conflict loop with the new conflict?)
        switch (c.bvalue(s)) {
        case l_true:
            // regular case
            insert(c);
            return false;
        case l_undef:
            VERIFY_EQ(c.eval(s), l_true);
            s.assign_eval(c.blit());
            insert(c);
            return false;
        case l_false:
            VERIFY_EQ(c.eval(s), l_true);
            break;
        }
        // TODO: could keep lemmas? but whatever, this case seems very rare
        reset();
        init(~c);
        return true;
    }

    void conflict::insert_vars(signed_constraint c) {
        for (pvar v : c->vars())
            if (s.is_assigned(v))
                m_vars.insert(v);
    }

    void conflict::add_lemma(char const* name, std::initializer_list<signed_constraint> cs) {
        add_lemma(name, std::data(cs), cs.size());
    }

    void conflict::add_lemma(char const* name, signed_constraint const* cs, size_t cs_len) {
        clause_builder cb(s, name);
        for (size_t i = 0; i < cs_len; ++i)
            cb.insert_eval(cs[i]);
        add_lemma(cb.build());
    }

    void conflict::add_lemma(clause_ref lemma) {
        LOG_H3("Lemma: " << ": " << show_deref(lemma));
        VERIFY(lemma);

        IF_VERBOSE(1, {
            for (auto lit : *lemma)
                if (s.m_bvars.is_true(lit)) {
                    verbose_stream() << "REDUNDANT lemma " << lit << " : " << show_deref(lemma) << "\n";
                    for (sat::literal lit : *lemma)
                        verbose_stream() << "    " << lit_pp(s, lit) << "\n";
                }
        });

        s.m_simplify_clause.apply(*lemma);
        lemma->set_redundant(true);
        for (sat::literal lit : *lemma) {
            LOG(lit_pp(s, lit));
            // NOTE: it can happen that the literal's bvalue is l_true at this point.
            //       E.g., lit has been assigned to true on the search stack but not yet propagated.
            //       A propagation before lit will cause a conflict, and by chance the viable conflict will contain lit.
            //       (in that case, the evaluation of lit in the current assignment must be false, and it would have caused a conflict by itself when propagated.)
            SASSERT(s.m_bvars.value(lit) != l_true || !s.lit2cnstr(lit).is_currently_true(s));
        }
        m_lemmas.push_back(std::move(lemma));
        // TODO: pass to inference_logger (with name)
   }

    void conflict::restore_lemma(clause_ref lemma) {
        SASSERT(!empty());
        LOG_H3("Restore Lemma: " << ": " << show_deref(lemma));
        m_lemmas.push_back(std::move(lemma));
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

    void conflict::resolve_evaluated(sat::literal lit) {
        // The reason for lit is conceptually:
        //    x1 = v1 /\ ... /\ xn = vn ==> lit

        SASSERT(s.m_bvars.is_evaluation(lit));
        SASSERT(contains(lit));
        SASSERT(!contains(~lit));

        signed_constraint c = s.lit2cnstr(lit);

        unsigned const eval_idx = s.m_search.get_bool_index(lit);
        for (pvar v : c->vars()) {
            if (s.is_assigned(v) && s.m_search.get_pvar_index(v) <= eval_idx) {
                m_vars.insert(v);
// TODO - figure out what to do with constraints from conflict lemma that disappear here.
//                    if (s.m_bvars.is_false(lit))
//                        m_resolver->infer_lemmas_for_value(v, ~c, *this);
            }
        }
        remove(c);

        SASSERT(!contains(lit));
        SASSERT(!contains(~lit));

        logger().log(inf_resolve_evaluated(s, lit, c));
    }

    void conflict::revert_pvar(pvar v) {
        m_resolver->infer_lemmas_for_value(v, *this);
    }

    void conflict::resolve_value_by_viable(pvar v) {
        SASSERT(contains_pvar(v));
        SASSERT(s.m_justification[v].is_propagation_by_viable());

        s.inc_activity(v);

        m_vars.remove(v);
        for (signed_constraint const c : s.m_viable.get_constraints(v))
            if (insert_or_replace(c))
                return;
        for (auto const& i : s.m_viable.units(v)) {
            if (insert_or_replace(s.eq(i.lo(), i.lo_val())))
                return;
            if (insert_or_replace(s.eq(i.hi(), i.hi_val())))
                return;
        }
        logger().log(inf_resolve_value(s, v));

        revert_pvar(v);
    }

    void conflict::resolve_value_by_slicing(pvar v) {
        SASSERT(contains_pvar(v));
        SASSERT(s.m_justification[v].is_propagation_by_slicing());

        s.inc_activity(v);

        m_vars.remove(v);
        s.m_slicing.explain_value(v,
            [this](sat::literal lit) {
                insert_or_replace(s.lit2cnstr(lit));
            },
            [this](pvar w) {
                SASSERT(s.is_assigned(w));
                m_vars.insert(w);
            });
        logger().log("value was propagated by slicing");  // TODO: add information about v

        revert_pvar(v);
    }

    clause_ref conflict::build_lemma() {
        LOG_H3("Build lemma from core");
        LOG("core: " << *this);

        // TODO: do this after each step?
        m_resolver->find_extra_lemmas(*this);

        clause_builder lemma(s);

        for (signed_constraint c : *this)
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

    clause_ref_vector conflict::take_lemmas() {
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

    void conflict::find_deps(dependency_vector& out_deps) const {
        sat::literal_vector todo_lits;
        sat::bool_var_set done_lits;
        unsigned_vector todo_vars;
        uint_set done_vars;
        indexed_uint_set deps;

        LOG_V(11, "State:\n" << s);
        LOG_V(11, "Conflict: " << *this);
        // LOG_V(11, "Viable:\n" << s.m_viable);
        // for (pvar v : m_vars) {
        //     s.m_viable.log(v);
        // }
        SASSERT(s.at_base_level());

        auto const enqueue_lit = [&](sat::literal lit) {
            if (done_lits.contains(lit.var()))
                return;
            if (!s.m_bvars.is_assigned(lit))
                return;
            IF_VERBOSE(11, verbose_stream() << "    enqueue " << lit_pp(s, lit) << "\n";);
            todo_lits.push_back(lit);
            done_lits.insert(lit.var());
        };

        auto const enqueue_constraint = [&](signed_constraint c) {
            enqueue_lit(c.blit());
        };

        auto const enqueue_var = [&](pvar v) {
            if (done_vars.contains(v))
                return;
            IF_VERBOSE(11, {
                verbose_stream() << "    enqueue v" << v << "\n";
                if (signed_constraint c = s.m_constraints.find_op_by_result_var(v))
                    verbose_stream() << "      defined by op_constraint: " << lit_pp(s, c) << "\n";
            });
            SASSERT(s.is_assigned(v));
            todo_vars.push_back(v);
            done_vars.insert(v);
        };

        // Starting at literals/variables in the conflict, chase propagations backwards and accumulate dependencies.
        for (signed_constraint c : *this)
            enqueue_constraint(c);
        for (pvar v : m_vars)
            enqueue_var(v);

        while (!todo_vars.empty() || !todo_lits.empty()) {
            while (!todo_vars.empty()) {
                pvar const v = todo_vars.back();
                todo_vars.pop_back();
                IF_VERBOSE(11, verbose_stream() << "Handling v" << v << "\n";);

                auto const& j = s.m_justification[v];
                if (j.is_propagation_by_viable()) {
                    for (signed_constraint c : s.m_viable.get_constraints(v))
                        enqueue_constraint(c);
                    for (auto const& i : s.m_viable.units(v)) {
                        enqueue_constraint(s.eq(i.lo(), i.lo_val()));
                        enqueue_constraint(s.eq(i.hi(), i.hi_val()));
                    }
                }
                else if (j.is_propagation_by_slicing()) {
                    s.m_slicing.explain_value(v, enqueue_lit, enqueue_var);
                }
                else {
                    // no decisions at base level
                    UNREACHABLE();
                }
            }
            while (!todo_lits.empty()) {
                sat::literal const lit = todo_lits.back();
                todo_lits.pop_back();
                IF_VERBOSE(11, verbose_stream() << "Handling " << lit_pp(s, lit) << "\n";);

                if (s.m_bvars.is_assumption(lit)) {
                    // only assumptions have external dependencies
                    dependency const d = s.m_bvars.dep(lit);
                    if (!d.is_null()) 
                        deps.insert(d.val());                    
                }
                else if (s.m_bvars.is_bool_propagation(lit)) {
                    IF_VERBOSE(11, verbose_stream() << "    reason " << *s.m_bvars.reason(lit) << "\n";);
                    for (sat::literal other : *s.m_bvars.reason(lit))
                        enqueue_lit(other);
                }
                else if (s.m_bvars.is_evaluation(lit)) {
                    unsigned const eval_idx = s.m_search.get_bool_index(lit);
                    for (pvar v : s.lit2cnstr(lit).vars()) {
                        if (!s.is_assigned(v))
                            continue;
                        if (s.m_search.get_pvar_index(v) > eval_idx)
                            continue;
                        enqueue_var(v);
                    }
                }
                else {
                    // no decisions at base level
                    UNREACHABLE();
                }
            }
        }
        
        for (unsigned d : deps)
            out_deps.push_back(dependency(d));
        if (!m_dep.is_null() && !deps.contains(m_dep.val()))
            out_deps.push_back(m_dep);
    }

    std::ostream& conflict::display(std::ostream& out) const {
        out << "lvl " << m_level;
        if (!m_dep.is_null())
            out << " dep " << m_dep;
        char const* sep = " ";
        for (auto c : *this)
            out << sep << c->bvar2string() << " " << c, sep = " ; ";
        if (!m_vars.empty())
            out << " vars";
        for (auto v : m_vars)
            out << " v" << v;
        if (!m_lemmas.empty())
            out << " lemmas";
        for (clause const* lemma : m_lemmas)
            out << " " << show_deref(lemma);
        return out;
    }
}
