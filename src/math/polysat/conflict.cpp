/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

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
    }

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
        return m_literals.empty()
            && m_vars.empty()
            && m_bail_vars.empty()
            && m_lemmas.empty();
    }

    void conflict::reset() {
        m_literals.reset();
        m_vars.reset();
        m_bail_vars.reset();
        m_relevant_vars.reset();
        m_var_occurrences.reset();
        m_lemmas.reset();
        m_kind = conflict_kind_t::ok;
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
            // return m_relevant_vars.contains(v);
        case conflict_kind_t::backjump:
            UNREACHABLE();  // we don't follow the regular loop when backjumping
            return false;
        }
    }

    bool conflict::is_relevant(sat::literal lit) const {
        return contains(lit) || contains(~lit);
    }

    void conflict::init(signed_constraint c) {
        SASSERT(empty());
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
            SASSERT(false);  // fail here to force check when we encounter this case
            // TODO: if we set() and then log() it will be confusing if this branch is hit.
            //       ideally the boolean resolution would be done separately afterwards
            auto* cl = s.m_bvars.reason(c.blit());
#if 0
            if (cl)
                set(*cl);  // why the whole clause? or do we want the boolean resolution?
            else
                insert(c);
#else
            insert(c);
            if (cl)
                resolve_bool(c.blit(), *cl);
#endif
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
        // if (!empty())
        //     return;
        // LOG("Conflict: " << cl);
        SASSERT(empty());
        for (auto lit : cl) {
            auto c = s.lit2cnstr(lit);
            SASSERT(c.bvalue(s) == l_false);
            insert(~c);
        }
        SASSERT(!empty());
        logger().begin_conflict();
    }

    void conflict::init(pvar v, bool by_viable_fallback) {
        if (by_viable_fallback) {
            logger().begin_conflict(header_with_var("unsat core from viable fallback for v", v));
            // Conflict detected by viable fallback:
            // initial conflict is the unsat core of the univariate solver
            signed_constraints unsat_core = s.m_viable_fallback.unsat_core(v);
            for (auto c : unsat_core)
                insert(c);
            // TODO: apply conflict resolution plugins here too?
        } else {
            logger().begin_conflict(header_with_var("forbidden interval lemma for v", v));
            set_backtrack();
            VERIFY(s.m_viable.resolve(v, *this));
            // TODO: in general the forbidden interval lemma is not asserting.
            //       but each branch exclude the current assignment.
            //       in those cases we will (additionally?) need an abstraction that is asserting to make sure viable is updated properly.
        }
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
        SASSERT(std::count(cl.begin(), cl.end(), lit) > 0);
        SASSERT(!contains(~lit));
        SASSERT(std::count(cl.begin(), cl.end(), ~lit) == 0);

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

        // TODO: call conflict resolution plugins here; "return true" if successful

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

        // TODO: is this sound, doing it for each constraint separately?
        for (auto c : *this)
            minimize_vars(c);

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
