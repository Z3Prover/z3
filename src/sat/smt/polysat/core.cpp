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

namespace polysat {

    class core::mk_assign_var : public trail {
        pvar m_var;
        core& c;
    public:
        mk_assign_var(pvar v, core& c) : m_var(v), c(c) {}
        void undo() {
            c.m_justification[m_var] = null_dependency;
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
            IF_VERBOSE(10, 
            verbose_stream() << "undo add watch " << sc << " ";
            if (vars.size() > 0) verbose_stream() << "(" << c.m_constraint_index.size() -1 << ": " << c.m_watch[vars[0]] << ") ";
            if (vars.size() > 1) verbose_stream() << "(" << c.m_constraint_index.size() -1 << ": " << c.m_watch[vars[1]] << ") ";
            verbose_stream() << "\n");
            unsigned n = sc.num_watch();
            SASSERT(n <= vars.size());
            SASSERT(n <= 0 || c.m_watch[vars[0]].back() == c.m_constraint_index.size() - 1);
            SASSERT(n <= 1 || c.m_watch[vars[1]].back() == c.m_constraint_index.size() - 1);
            if (n > 0)
                c.m_watch[vars[0]].pop_back();
            if (n > 1)
                c.m_watch[vars[1]].pop_back();
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
        m_justification.push_back(null_dependency);
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

    unsigned core::register_constraint(signed_constraint& sc, dependency d) {
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
        return idx;
    }

    // case split on unassigned variables until all are assigned values.
    // create equality literal for unassigned variable.
    // return new_eq if there is a new literal.
    
    sat::check_result core::check() { 
        if (m_var_queue.empty())
            return sat::check_result::CR_DONE;
        m_var = m_var_queue.next_var();       
        s.trail().push(mk_dqueue_var(m_var, *this));
        switch (m_viable.find_viable(m_var, m_value)) {
        case find_t::empty: 
            s.set_lemma(m_viable.get_core(), m_viable.explain());
            // propagate_unsat_core();        
            return sat::check_result::CR_CONTINUE;
        case find_t::singleton: {
            s.propagate(m_constraints.eq(var2pdd(m_var), m_value), m_viable.explain());
            return sat::check_result::CR_CONTINUE;
        }
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

    // First propagate Boolean assignment, then propagate value assignment
    bool core::propagate() { 
        if (m_qhead == m_prop_queue.size() && m_vqhead == m_prop_queue.size())
            return false;
        s.trail().push(value_trail(m_qhead));
        for (; m_qhead < m_prop_queue.size() && !s.inconsistent(); ++m_qhead)
            propagate_assignment(m_prop_queue[m_qhead]);        
        s.trail().push(value_trail(m_vqhead));
        for (; m_vqhead < m_prop_queue.size() && !s.inconsistent(); ++m_vqhead) 
            propagate_value(m_prop_queue[m_vqhead]);        
        return true;
    }

    signed_constraint core::get_constraint(unsigned idx, bool sign) {
        auto sc = m_constraint_index[idx].sc;
        if (sign)
            sc = ~sc;
        return sc;
    }

    void core::propagate_assignment(prop_item& dc) { 
        auto [idx, sign, dep] = dc;
        auto sc = get_constraint(idx, sign);
        if (sc.is_eq(m_var, m_value))
            propagate_assignment(m_var, m_value, dep);
        else 
            sc.activate(*this, dep);        
    }

    void core::add_watch(unsigned idx, unsigned var) {
        m_watch[var].push_back(idx);
    }

    void core::propagate_assignment(pvar v, rational const& value, dependency dep) {
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
                    verbose_stream() << "watch instead " << vars[i] << " instead of " << vars[0] << " for " << idx << "\n";
                    add_watch(idx, vars[i]);
                    std::swap(vars[i], vars[0]);
                    swapped = true;
                    break;
                }
            }

            // this can create fresh literals and update m_watch, but
            // will not update m_watch[v] (other than copy constructor for m_watch)
            // because v has been assigned a value.
            sc.propagate(*this, value, dep);
           
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
        verbose_stream() << "new watch " << v << ": " << m_watch[v] << "\n";
    }

    void core::propagate_value(prop_item const& dc) {
        auto [idx, sign, dep] = dc;
        auto sc = get_constraint(idx, sign);
        // check if sc evaluates to false
        switch (eval(sc)) {
        case l_true:
            break;
        case l_false:
            m_unsat_core = explain_eval(sc);
            m_unsat_core.push_back(dep);
            propagate_unsat_core();
            return;
        default:
            break;
        }
        // propagate current assignment for sc
        sc.propagate(*this, to_lbool(!sign), dep);
        if (s.inconsistent())
            return;

        // if sc is v == value, then check the watch list for v to propagate truth assignments
        if (sc.is_eq(m_var, m_value)) {
            for (auto idx1 : m_watch[m_var]) {
                if (idx == idx1)
                    continue;
                auto [sc, d, value] = m_constraint_index[idx1];
                switch (eval(sc)) {
                case l_false:
                    s.propagate(d, true, explain_eval(sc));
                    break;
                case l_true:
                    s.propagate(d, false, explain_eval(sc));
                    break;
                default:
                    break;
                }
            }
        }       
    }

    void core::get_bitvector_prefixes(pvar v, pvar_vector& out) {
        s.get_bitvector_prefixes(v, out);
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

        s.set_conflict(m_unsat_core);       
    }

    void core::assign_eh(unsigned index, bool sign, dependency const& dep) { 
        struct unassign : public trail {
            core& c;
            unsigned m_index;
            unassign(core& c, unsigned index): c(c), m_index(index) {}
            void undo() override {
                c.m_constraint_index[m_index].value = l_undef;
                c.m_prop_queue.pop_back();
            }
        };
        m_prop_queue.push_back({ index, sign, dep });
        m_constraint_index[index].value = to_lbool(!sign);
        s.trail().push(unassign(*this, index));
    }

    dependency_vector core::explain_eval(signed_constraint const& sc) { 
        dependency_vector deps;
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
            out << m_vars[i] << " := " << m_values[i] << " " << m_justification[i] << "\n";
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
        assign_eh(idx, false, dependency::axiom());
    }

    void core::add_clause(char const* name, core_vector const& cs, bool is_redundant) {
        s.add_polysat_clause(name, cs, is_redundant);
    }

}
