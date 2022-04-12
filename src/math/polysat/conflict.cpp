/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

 TODO: try a final core reduction step or other core minimization

 TODO: revert(pvar v) is too weak. 
       It should apply saturation rules currently only available for propagated values.

 TODO: dependency tracking for constraints evaluating to false should be minimized.

--*/

#include "math/polysat/conflict.h"
#include "math/polysat/solver.h"
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

    class inference_logger {
        uint_set m_used_constraints;
        uint_set m_used_vars;
        scoped_ptr<std::ostream> m_out = nullptr;
        unsigned m_conflicts = 0;

        std::ostream& out() {
            SASSERT(m_out);
            return *m_out;
        }

        std::ostream& out_indent() { return out() << "    "; }

        std::string hline() const { return std::string(70, '-'); }

    public:
        void begin_conflict() {
            m_used_constraints.reset();
            m_used_vars.reset();
            if (!m_out)
                m_out = alloc(std::ofstream, "conflicts.txt");
            else
                out() << "\n\n\n\n\n" << hline() << "\n" << hline() << "\n" << hline() << "\n\n\n\n\n";
            out() << "CONFLICT #" << ++m_conflicts << "\n";
        }

        void log_inference(conflict const& core, inference const* inf) {
            out() << hline() << "\n";
            if (inf)
                out() << *inf << "\n";
            if (core.conflict_var() != null_var) {
                out_indent() << "Conflict var: " << core.conflict_var() << "\n";
                m_used_vars.insert(core.conflict_var());
            }
            for (auto const& c : core) {
                out_indent() << c.blit() << ": " << c << '\n';
                m_used_constraints.insert(c.blit().index());
            }
            for (auto v : core.vars()) {
                out_indent() << "v" << v << "\n";
                m_used_vars.insert(v);
            }
            for (auto v : core.bail_vars()) {
                out_indent() << "v" << v << " (bail)\n";
                m_used_vars.insert(v);
            }
            out().flush();
        }

        void log_lemma(clause_builder const& cb) {
            out() << hline() << "\nLemma:";
            for (auto const& lit : cb)
                out() << " " << lit;
            out() << "\n";
            out().flush();
        }

        void log_gamma(search_state const& m_search) {
            out() << "\n" << hline() << "\n\n";
            out() << "Search state (part):\n";
            for (auto const& item : m_search)
                if (is_relevant(item))
                    out_indent() << search_item_pp(m_search, item, true) << "\n";
            // TODO: log viable
            out().flush();
        }

        bool is_relevant(search_item const& item) const {
            switch (item.kind()) {
            case search_item_k::assignment:
                return m_used_vars.contains(item.var());
            case search_item_k::boolean:
                return m_used_constraints.contains(item.lit().index());
            }
            UNREACHABLE();
            return false;
        }
    };

    conflict::conflict(solver& s): s(s) {
        ex_engines.push_back(alloc(ex_polynomial_superposition, s));
        ex_engines.push_back(alloc(eq_explain, s));
        ve_engines.push_back(alloc(ve_reduction));
        inf_engines.push_back(alloc(inf_saturate, s));
        // TODO: how to set this on the CLI? "polysat.log_conflicts=true" doesn't seem to work although z3 accepts it
        if (true || s.get_config().m_log_conflicts)
            m_logger = alloc(inference_logger);
    }

    conflict::~conflict() {}

    void conflict::begin_conflict() {
        if (m_logger) {
            m_logger->begin_conflict();
            // log initial conflict state
            m_logger->log_inference(*this, nullptr);
        }
    }

    void conflict::log_inference(inference const& inf) {
        if (m_logger)
            m_logger->log_inference(*this, &inf);
    }

    void conflict::log_gamma() {
        if (m_logger)
            m_logger->log_gamma(s.m_search);
    }

    constraint_manager& conflict::cm() const { return s.m_constraints; }

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

    bool conflict::empty() const {
        return m_literals.empty()
            && m_vars.empty()
            && m_bail_vars.empty()
            && m_conflict_var == null_var;
    }

    void conflict::reset() {
        for (auto c : *this)
            unset_mark(c);
        m_literals.reset();
        m_vars.reset();
        m_bail_vars.reset();
        m_conflict_var = null_var;
        m_bailout = false;
        SASSERT(empty());        
    }

    /**
    * The constraint is false under the current assignment of variables.
    * The core is then the conjuction of this constraint and assigned variables.
    */
    void conflict::set(signed_constraint c) {
        LOG("Conflict: " << c << " " << c.bvalue(s));
        SASSERT(empty());
        if (c.bvalue(s) == l_false) {
            auto* cl = s.m_bvars.reason(c.blit().var());
            if (cl)
                set(*cl);
            else
                insert(c);
        }
        else {
            SASSERT(c.is_currently_false(s));
            // TBD: fails with test_subst       SASSERT(c.bvalue(s) == l_true);
            insert_vars(c);
            insert(c);
        }
        SASSERT(!empty());
    }

    /**
    * The variable v cannot be assigned.
    * The conflict is the set of justifications accumulated for the viable values for v.
    * These constraints are (in the current form) not added to the core, but passed directly 
    * to the forbidden interval module.
    * A consistent approach could be to add these constraints to the core and then also include the
    * variable assignments.
    */
    void conflict::set(pvar v) {
        LOG("Conflict: v" << v);
        SASSERT(empty());
        m_conflict_var = v;
        SASSERT(!empty());
    }

    /**
     * The clause is conflicting in the current search state.
     */
    void conflict::set(clause const& cl) {
        if (!empty())
            return;
        LOG("Conflict: " << cl);
        SASSERT(empty());
        for (auto lit : cl) {
            auto c = s.lit2cnstr(lit);
            SASSERT(c.bvalue(s) == l_false);
            insert(~c);            
        }
        SASSERT(!empty());
    }

    /**
     * Insert constraint into conflict state
     * Skip trivial constraints
     *  - e.g., constant ones such as "4 > 1"... only true ones 
     *   should appear, otherwise the lemma would be a tautology
     */
    void conflict::insert(signed_constraint c) {
        if (c.is_always_true())
            return;        
        if (is_marked(c))
            return;
        LOG("inserting: " << c);
        SASSERT(!c->vars().empty());
        set_mark(c);
        m_literals.insert(c.blit().index());
    }

    void conflict::propagate(signed_constraint c) {
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

    /**
     * Premises can either be justified by a Clause or by a value assignment.
     * Premises that are justified by value assignments are not assigned (the bvalue is l_undef)
     * The justification for those premises are based on the free assigned variables.
     *
     * NOTE: maybe we should skip intermediate steps and just collect the leaf premises for c?
     * Ensure that c is assigned and justified
     */
    // TODO: rename this; it pushes onto \Gamma and doesn't insert into the core
    void conflict::insert(signed_constraint c, vector<signed_constraint> const& premises) {
        // keep(c);
        clause_builder c_lemma(s);
        for (auto premise : premises) {
            LOG_H3("premise: " << premise);
            // keep(premise);
            SASSERT(premise.bvalue(s) != l_false);         
            c_lemma.push(~premise.blit());
        }
        c_lemma.push(c.blit());
        clause_ref lemma = c_lemma.build();
        SASSERT(lemma);
        cm().store(lemma.get(), s, false);
        if (c.bvalue(s) == l_undef)
            s.assign_propagate(c.blit(), *lemma);
    }

    void conflict::remove(signed_constraint c) {
        unset_mark(c);       
        m_literals.remove(c.blit().index());
    }

    void conflict::replace(signed_constraint c_old, signed_constraint c_new, vector<signed_constraint> const& c_new_premises) {
        remove(c_old);
        insert(c_new, c_new_premises);
    }

    bool conflict::contains(signed_constraint c) const {
        return m_literals.contains(c.blit().index());
    }

    bool conflict::contains(sat::literal lit) const {
        return m_literals.contains(lit.index());
    }

    void conflict::set_bailout() {
        SASSERT(!is_bailout());
        m_bailout = true;
        s.m_stats.m_num_bailouts++;
    }

    struct inference_resolve : public inference {
        sat::literal m_lit;
        clause const& m_clause;
        inference_resolve(sat::literal lit, clause const& cl) : m_lit(lit), m_clause(cl) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Resolve upon " << m_lit << " with " << m_clause;
        }
    };

    void conflict::resolve(sat::literal lit, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

        SASSERT(lit != sat::null_literal);
        SASSERT(~lit != sat::null_literal);
        SASSERT(contains(lit));
        SASSERT(std::count(cl.begin(), cl.end(), lit) > 0);
        SASSERT(!contains(~lit));
        SASSERT(std::count(cl.begin(), cl.end(), ~lit) == 0);
        
        remove(s.lit2cnstr(lit));
        for (sat::literal lit2 : cl)
            if (lit2 != lit)
                insert(s.lit2cnstr(~lit2));
        log_inference(inference_resolve(lit, cl));
    }

    struct inference_resolve_with_assignment : public inference {
        solver& s;
        sat::literal lit;
        signed_constraint c;
        inference_resolve_with_assignment(solver& s, sat::literal lit, signed_constraint c) : s(s), lit(lit), c(c) {}
        std::ostream& display(std::ostream& out) const override {
            out << "Resolve upon " << lit << " with assignment:";
            for (pvar v : c->vars())
                out << " " << assignment_pp(s, v, s.get_value(v), true);
            return out;
        }
    };

    void conflict::resolve_with_assignment(sat::literal lit, unsigned lvl) {
        // The reason for lit is conceptually:
        //    x1 = v1 /\ ... /\ xn = vn ==> lit

        SASSERT(lit != sat::null_literal);
        SASSERT(~lit != sat::null_literal);
        SASSERT(contains(lit));
        SASSERT(!contains(~lit));

        signed_constraint c = s.lit2cnstr(lit);
        bool has_decision = false;
        for (pvar v : c->vars()) 
            if (s.is_assigned(v) && s.m_justification[v].is_decision()) 
                m_bail_vars.insert(v), has_decision = true;

        if (!has_decision) {
            remove(c);
            for (pvar v : c->vars()) 
                if (s.is_assigned(v)) {
                    // TODO: 'lit' was propagated at level 'lvl'; can we here ignore variables above that?
                    SASSERT(s.get_level(v) <= lvl);
                    m_vars.insert(v);            
                }
        }
        log_inference(inference_resolve_with_assignment(s, lit, c));
    }

    clause_builder conflict::build_lemma() {
        LOG_H3("Build lemma from core");
        LOG("core: " << *this);
        clause_builder lemma(s);

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

        if (m_logger)
            m_logger->log_lemma(lemma);

        return lemma;
    }

    void conflict::minimize_vars(signed_constraint c) {
        if (m_vars.empty())
            return;
        if (!c.is_currently_false(s))
            return;
        
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
            return;
        m_vars.reset();
        for (auto const& [v, val] : a)
            m_vars.insert(v);
        log_inference("minimize vars");
        LOG("reduced " << m_vars);
    }


    struct inference_resolve_value : public inference {
        solver& s;
        pvar v;
        inference_resolve_value(solver& s, pvar v) : s(s), v(v) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Value resolution with " << assignment_pp(s, v, s.get_value(v), true);
        }
    };

    bool conflict::resolve_value(pvar v) {
        // NOTE:
        // In the "standard" case where "v = val" is on the stack:
        // forbidden interval projection is performed at top level

        SASSERT(v != conflict_var());

        auto const& j = s.m_justification[v];

        if (j.is_decision() && m_bail_vars.contains(v))
            return false;
        
        s.inc_activity(v);    
        m_vars.remove(v);

        if (is_bailout())
            goto bailout;
        
        if (j.is_propagation()) 
            for (auto const& c : s.m_viable.get_constraints(v)) 
                propagate(c);

        LOG("try-explain v" << v);
        if (try_explain(v))
            return true;

        // No value resolution method was successful => fall back to saturation and variable elimination
        while (s.inc()) {
            LOG("try-eliminate v" << v);
            // TODO: as a last resort, substitute v by m_value[v]?
            if (try_eliminate(v))
                return true;
            if (!try_saturate(v))
                break;
        }
        LOG("bailout v" << v);
        set_bailout();
    bailout:
        if (s.is_assigned(v) && j.is_decision())
            m_vars.insert(v);
        log_inference(inference_resolve_value(s, v));
        return false;
    }

    bool conflict::try_eliminate(pvar v) {    
        LOG("try v" << v << " contains " << m_vars.contains(v));
        if (m_vars.contains(v))
            return false;
        bool has_v = false;
        for (auto c : *this)
            has_v |= c->contains_var(v);
        if (!has_v)
            return true;
        for (auto* engine : ve_engines)
            if (engine->perform(s, v, *this)) 
                return true;            
        return false;
    }

    bool conflict::try_saturate(pvar v) {
        for (auto* engine : inf_engines)
            if (engine->perform(v, *this))
                return true;
        return false;
    }

    bool conflict::try_explain(pvar v) {
        for (auto* engine : ex_engines)
            if (engine->try_explain(v, *this))
                return true;
        return false;
    }

    void conflict::set_mark(signed_constraint c) {
        sat::bool_var b = c->bvar();
        if (b >= m_bvar2mark.size())
            m_bvar2mark.resize(b + 1);
        SASSERT(!m_bvar2mark[b]);
        m_bvar2mark[b] = true;
    }

    /**
     * unset marking on the constraint, but keep variable dependencies.
     */
    void conflict::unset_mark(signed_constraint c) {
        sat::bool_var b = c->bvar();
        SASSERT(m_bvar2mark[b]);
        m_bvar2mark[b] = false;
    }

    bool conflict::is_marked(signed_constraint c) const {
        return is_marked(c->bvar());
    }

    bool conflict::is_marked(sat::bool_var b) const {
        return m_bvar2mark.get(b, false);
    }
}
