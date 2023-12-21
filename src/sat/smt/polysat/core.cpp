/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat_core.cpp

Abstract:

    PolySAT core functionality

Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26
    Jakob Rath 2021-04-06

Notes:

polysat::solver
- adds assignments
- calls propagation and check

polysat::core
- propagates literals 
- crates case splits by value assignment (equalities)
- detects conflicts based on Literal assignmets
- adds lemmas based on projections

--*/

#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/saturation.h"

namespace polysat {

    class core::mk_assign_var : public trail {
        pvar m_var;
        core& c;
    public:
        mk_assign_var(pvar v, core& c) : m_var(v), c(c) {}
        void undo() {
            c.m_justification[m_var] = constraint_id::null();
            c.m_assignment.pop();
        }
    };

    class core::mk_dqueue_var : public trail {
        pvar m_var;
        core& c;
    public:
        mk_dqueue_var(pvar v, core& c) : m_var(v), c(c) {}
        void undo() {
            c.m_var_queue.unassign_var_eh(m_var);
        }
    };

    class core::mk_add_var : public trail {
        core& c;
    public:
        mk_add_var(core& c) : c(c) {}
        void undo() override {
            c.del_var();
        }
    };

    class core::mk_add_watch : public trail {
        core& c;
    public:
        mk_add_watch(core& c) : c(c) {}
        void undo() override {
            auto& [sc, lit, val] = c.m_constraint_index.back();
            auto& vars = sc.vars();
            auto idx = c.m_constraint_index.size() - 1;
            IF_VERBOSE(10,
                verbose_stream() << "undo add watch " << sc << " ";
            if (vars.size() > 0) verbose_stream() << "(" << idx << ": " << c.m_watch[vars[0]] << ") ";
            if (vars.size() > 1) verbose_stream() << "(" << idx << ": " << c.m_watch[vars[1]] << ") ";
            verbose_stream() << "\n");
            unsigned n = sc.num_watch();
            SASSERT(n <= vars.size());
            auto del_watch = [&](unsigned i) {
                auto& w = c.m_watch[vars[i]];
                for (unsigned j = w.size(); j-- > 0;) {
                    if (w[j] == idx) {
                        std::swap(w[w.size() - 1], w[j]);
                        w.pop_back();
                        return;
                    }
                }
                UNREACHABLE();
                };
            if (n > 0)
                del_watch(0);
            if (n > 1)
                del_watch(1);
            c.m_constraint_index.pop_back();
        }
    };

    core::core(solver_interface& s) :
        s(s),
        m_viable(*this),
        m_constraints(*this),
        m_assignment(*this),
        m_var_queue(m_activity)
    {}

    pdd core::value(rational const& v, unsigned sz) {
        return sz2pdd(sz).mk_val(v);
    }

    dd::pdd_manager& core::sz2pdd(unsigned sz) const {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz])
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000, dd::pdd_manager::semantics::mod2N_e, sz));
        return *m_pdd[sz];
    }

    dd::pdd_manager& core::var2pdd(pvar v) const {
        return sz2pdd(size(v));
    }

    pvar core::add_var(unsigned sz) {
        unsigned v = m_vars.size();
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_activity.push_back({ sz, 0 });
        m_justification.push_back(constraint_id::null());
        m_watch.push_back({});
        m_var_queue.mk_var_eh(v);
        m_viable.ensure_var(v);
        m_values.push_back(rational::zero());
        s.trail().push(mk_add_var(*this));
        return v;
    }

    void core::del_var() {
        unsigned v = m_vars.size() - 1;
        m_vars.pop_back();
        m_activity.pop_back();
        m_justification.pop_back();
        m_watch.pop_back();
        m_values.pop_back();
        m_var_queue.del_var_eh(v);
    }

    constraint_id core::register_constraint(signed_constraint& sc, dependency d) {
        unsigned idx = m_constraint_index.size();
        m_constraint_index.push_back({ sc, d, l_undef });
        auto& vars = sc.vars();
        unsigned i = 0, j = 0, sz = vars.size();
        for (; i < sz && j < 2; ++i)
            if (!is_assigned(vars[i]))
                std::swap(vars[i], vars[j++]);
        sc.set_num_watch(j);
        if (j > 0)
            add_watch(idx, vars[0]);
        if (j > 1)
            add_watch(idx, vars[1]);
        IF_VERBOSE(10, verbose_stream() << "add watch " << sc << " " << vars << "  ";
        if (j > 0) verbose_stream() << "( " << idx << " : " << m_watch[vars[0]] << ") ";
        if (j > 1) verbose_stream() << "( " << idx << " : " << m_watch[vars[1]] << ") ";
        verbose_stream() << "\n");
        s.trail().push(mk_add_watch(*this));
        return { idx };
    }

    // case split on unassigned variables until all are assigned values.
    // create equality literal for unassigned variable.
    // return new_eq if there is a new literal.

    sat::check_result core::check() {
        if (m_var_queue.empty())
            return final_check();
        m_var = m_var_queue.next_var();
        s.trail().push(mk_dqueue_var(m_var, *this));
        switch (m_viable.find_viable(m_var, m_value)) {
        case find_t::empty:
            s.set_lemma(m_viable.get_core(), get_dependencies(m_viable.explain()));
            // propagate_unsat_core();        
            return sat::check_result::CR_CONTINUE;
        case find_t::singleton:
            s.propagate(m_constraints.eq(var2pdd(m_var), m_value), get_dependencies(m_viable.explain()));
            return sat::check_result::CR_CONTINUE;
        case find_t::multiple:
            s.add_eq_literal(m_var, m_value);
            return sat::check_result::CR_CONTINUE;
        case find_t::resource_out:
            m_var_queue.unassign_var_eh(m_var);
            return sat::check_result::CR_GIVEUP;
        }
        UNREACHABLE();
        return sat::check_result::CR_GIVEUP;
    }

    sat::check_result core::final_check() {
        constraint_id conflict_idx = find_conflicting_constraint();

        // If all constraints evaluate to true, we are done.
        if (conflict_idx.is_null())
            return sat::check_result::CR_DONE;
        
        // Extract variables that are of level or above of conflicting constraint and contradict the constraint
        auto vars = find_conflict_variables(conflict_idx);
        saturation sat(*this);
        for (auto v: vars)
         if (sat.propagate(v, conflict_idx))
                return sat::check_result::CR_CONTINUE;

        // If no saturation propagation was possible, explain the conflict using the variable assignment.
        m_unsat_core = explain_eval(get_constraint(conflict_idx));
        m_unsat_core.push_back(conflict_idx);
        propagate_unsat_core();
        return sat::check_result::CR_CONTINUE;
    }

    /**
    * Identify a conflicting constraint, if any, that evaluates to false under 
    * the current assignment.
    */
    constraint_id core::find_conflicting_constraint() {
        unsigned conflict_level = UINT_MAX;
        constraint_id conflict_idx = { UINT_MAX };
        for (auto idx : m_prop_queue) {
            auto [sc, d, value] = m_constraint_index[idx.id];
            SASSERT(value != l_undef);
            lbool eval_value = eval(sc);
            SASSERT(eval_value != l_undef);
            if (eval_value == value)
                continue;
            auto explain = explain_eval(sc);
            unsigned new_conflict_level = d.level();
            for (auto idx2 : explain)
                new_conflict_level = std::max(new_conflict_level, m_constraint_index[idx2.id].d.level());

            if (new_conflict_level >= conflict_level)
                continue;
            conflict_idx = idx;
            conflict_level = new_conflict_level;
        }
        return conflict_idx;
    }

    /**
    * Find variables at the maximal scope level that are used in the conflicting literal.
    */
    svector<pvar> core::find_conflict_variables(constraint_id idx) {
        svector<pvar> result;
        auto [sc, d, value] = m_constraint_index[idx.id];
        unsigned lvl = d.level();
        for (auto v : sc.vars()) {
            if (!is_assigned(v))
                continue;
            auto new_level = m_constraint_index[m_justification[v].id].d.level();
            if (new_level < lvl)
                continue;
            if (new_level > lvl)
                result.reset();
            result.push_back(v);
            lvl = new_level;
        }
        return result;
    }

    // First propagate Boolean assignment, then propagate value assignment
    bool core::propagate() { 
        if (m_qhead == m_prop_queue.size())
            return false;
        s.trail().push(value_trail(m_qhead));
        for (; m_qhead < m_prop_queue.size() && !s.inconsistent(); ++m_qhead)
            propagate_assignment(m_prop_queue[m_qhead]);               
        return true;
    }

    void core::propagate_assignment(constraint_id idx) { 

        auto [sc, dep, value] = m_constraint_index[idx.id];
        SASSERT(value != l_undef);
        if (value == l_false)
            sc = ~sc;
        if (sc.is_eq(m_var, m_value))
            propagate_assignment(m_var, m_value, idx);
        else 
            sc.activate(*this, dep);        
    }

    void core::add_watch(unsigned idx, unsigned var) {
        m_watch[var].push_back(idx);
    }

    void core::propagate_assignment(pvar v, rational const& value, constraint_id dep) {
        if (is_assigned(v))
            return;
        if (m_var_queue.contains(v)) {
            m_var_queue.del_var_eh(v);
            s.trail().push(mk_dqueue_var(v, *this));
        }
        m_values[v] = value;
        m_justification[v] = dep;   
        m_assignment.push(v , value);
        s.trail().push(mk_assign_var(v, *this));

        // update the watch lists for pvars
        // remove constraints from m_watch[v] that have more than 2 free variables.
        // for entries where there is only one free variable left add to viable set 
        unsigned j = 0, sz = m_watch[v].size();
        for (unsigned k = 0; k < sz; ++k) {
            auto idx = m_watch[v][k];
            auto [sc, dep, value] = m_constraint_index[idx];
            auto& vars = sc.vars();
            if (vars[0] != v)
                std::swap(vars[0], vars[1]);
            SASSERT(vars[0] == v);
            bool swapped = false;
            for (unsigned i = vars.size(); i-- > 2; ) {
                if (!is_assigned(vars[i])) {
                    add_watch(idx, vars[i]);
                    std::swap(vars[i], vars[0]);
                    swapped = true;
                    break;
                }
            }

            // this can create fresh literals and update m_watch, but
            // will not update m_watch[v] (other than copy constructor for m_watch)
            // because v has been assigned a value.
            propagate_eval({ idx });
            if (s.inconsistent())
                return;
           
            SASSERT(!swapped || vars.size() <= 1 || (!is_assigned(vars[0]) && !is_assigned(vars[1])));
            if (swapped)
                continue;
            m_watch[v][j++] = idx;
            if (vars.size() <= 1)
                continue;
            auto v1 = vars[1];
            if (is_assigned(v1))
                continue;
            SASSERT(is_assigned(vars[0]) && vars.size() >= 2);
            // detect unitary, add to viable, detect conflict?
            m_viable.add_unitary(v1, idx);            
        }
        SASSERT(m_watch[v].size() == sz && "size of watch list was not changed");
        m_watch[v].shrink(j);
    }

    /*
    * T-propagation.
    * Propagate literals that haven't been assigned a truth value if they evaluate to true or false.
    */
    void core::propagate_eval(constraint_id idx) {
        auto [sc, d, value] = m_constraint_index[idx.id];
        if (value != l_undef)
            return;
        switch (eval(sc)) {
        case l_false:
            s.propagate(d, true, get_dependencies(explain_eval(sc)));
            break;
        case l_true:
            s.propagate(d, false, get_dependencies(explain_eval(sc)));
            break;
        default:
            break;
        }
    }

    dependency core::get_dependency(constraint_id idx) const {
        auto [sc, d, value] = m_constraint_index[idx.id];
        SASSERT(value != l_undef);
        return value == l_false ? ~d : d;
    }

    dependency_vector core::get_dependencies(constraint_id_vector const& cc) {
        dependency_vector result;
        for (auto idx : cc) 
            result.push_back(get_dependency(idx));        
        return result;
    }

    dependency_vector core::get_dependencies(std::initializer_list<constraint_id> const& cc) {
        dependency_vector result;
        for (auto idx : cc)
            result.push_back(get_dependency(idx));
        return result;
    }

    void core::propagate(constraint_id id, signed_constraint& sc, lbool value, dependency const& d) {
        lbool eval_value = eval(sc);
        if (eval_value == l_undef)
            sc.propagate(*this, value, d);
        else if (value == l_undef)
            s.propagate(d, eval_value != l_true, get_dependencies(explain_eval(sc)));
        else if (value != eval_value) {
            m_unsat_core = explain_eval(sc);
            m_unsat_core.push_back(id);
            propagate_unsat_core();
        }                   
    }

    void core::get_bitvector_suffixes(pvar v, pvar_vector& out) {
        s.get_bitvector_suffixes(v, out);
    }

    void core::get_fixed_bits(pvar v, svector<justified_fixed_bits>& fixed_bits) {
        s.get_fixed_bits(v, fixed_bits);
    }

    bool core::inconsistent() const {
        return s.inconsistent();
    }

    void core::propagate_unsat_core() { 
        // default is to use unsat core:
        // if core is based on viable, use s.set_lemma();

        s.set_conflict(get_dependencies(m_unsat_core));       
    }

    void core::assign_eh(constraint_id index, bool sign, unsigned level) { 
        struct unassign : public trail {
            core& c;
            unsigned m_index;
            unassign(core& c, unsigned index): c(c), m_index(index) {}
            void undo() override {
                c.m_constraint_index[m_index].value = l_undef;
                c.m_prop_queue.pop_back();
            }
        };
        m_prop_queue.push_back(index);
        m_constraint_index[index.id].value = to_lbool(!sign);
        m_constraint_index[index.id].d.set_level(level);
        s.trail().push(unassign(*this, index.id));
    }

    constraint_id_vector core::explain_eval(signed_constraint const& sc) { 
        constraint_id_vector deps;
        for (auto v : sc.vars()) 
            if (is_assigned(v))
                deps.push_back(m_justification[v]);
        return deps;
    }

    lbool core::eval(signed_constraint const& sc) { 
        return sc.eval(m_assignment);
    }

    pdd core::subst(pdd const& p) { 
        return m_assignment.apply_to(p);
    }

    trail_stack& core::trail() {
        return s.trail();
    }

    std::ostream& core::display(std::ostream& out) const {
        if (m_constraint_index.empty() && m_vars.empty())
            return out;
        out << "polysat:\n";
        for (auto const& [sc, d, value] : m_constraint_index) 
            out << sc << " " << d << " := " << value << "\n";        
        for (unsigned i = 0; i < m_vars.size(); ++i) 
            out << m_vars[i] << " := " << m_values[i] << " " << m_constraint_index[m_justification[i].id].d << "\n";
        m_var_queue.display(out << "vars ") << "\n";
        return out;
    }

    bool core::try_eval(pdd const& p, rational& r) {
        auto q = subst(p);
        if (!q.is_val())
            return false;
        r = q.val();
        return true;
    }

    void core::collect_statistics(statistics& st) const {

    }

    void core::add_axiom(signed_constraint sc) {
        auto idx = register_constraint(sc, dependency::axiom());
        assign_eh(idx, false, 0);
    }

    bool core::add_clause(char const* name, core_vector const& cs, bool is_redundant) {
        for (auto e : cs) 
            if (std::holds_alternative<signed_constraint>(e) && eval(*std::get_if<signed_constraint>(&e)) == l_true)
                return false;
        
        return s.add_polysat_clause(name, cs, is_redundant);
    }

    signed_constraint core::get_constraint(constraint_id idx) {
        auto [sc, d, value] = m_constraint_index[idx.id];
        SASSERT(value != l_undef);
        if (value == l_false)
            sc = ~sc;
        return sc;
    }

    lbool core::eval(constraint_id id) {
        return get_constraint(id).eval(m_assignment);
    }

}
