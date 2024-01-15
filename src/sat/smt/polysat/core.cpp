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
            c.m_justification[m_var] = null_dependency;
            c.m_assignment.pop();
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
        m_monomials(*this),
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
        s.trail().push(mk_add_watch(*this));
        return { idx };
    }

    // case split on unassigned variables until all are assigned values.
    // create equality literal for unassigned variable.
    // return new_eq if there is a new literal.

    lbool core::assign_variable() {
        if (m_var_queue.empty())
            return l_true;

        for (auto v : m_var_queue) {
            switch (assign_variable(v)) {
            case l_false:
                return l_false;
            case l_true:
                return l_true;
            default:
                break;
            }
        }
        return l_undef;
    }

    lbool core::assign_variable(pvar v) {
        m_var = v;
        CTRACE("bv", is_assigned(m_var), display(tout << "v" << m_var << " is assigned\n"););
        SASSERT(!is_assigned(m_var));

        auto& var_value = m_values[m_var];
        switch (m_viable.find_viable(m_var, var_value)) {
        case find_t::empty:
            viable_conflict(m_var);
            return l_false;
        case find_t::singleton: {
            viable_propagate(m_var, var_value);
            return l_false;
        }
        case find_t::multiple: {
            dependency d = null_dependency;
            lbool value = s.add_eq_literal(m_var, var_value, d);
            TRACE("bv", tout << "check-multiple v" << m_var << " := " << var_value << " " << value << "\n");
            switch (value) {
            case l_true:
                propagate_assignment(m_var, var_value, d);
                break;
            case l_false:
                // disequality is forced into propagation queue.
                var_value = mod(var_value + 1, rational::power_of_two(size(m_var)));
                propagate();
                break;
            default:
                // let core assign equality.                    
                break;
            }
            return l_false;
        }
        case find_t::resource_out:
            TRACE("bv", tout << "check-resource out v" << m_var << "\n");
            return l_undef;
        }
        UNREACHABLE();
        return l_undef;
    }

    sat::check_result core::check() {
        lbool r = l_true;

        if (propagate())
            return sat::check_result::CR_CONTINUE;

        switch (assign_variable()) {
        case l_true:
            break;
        case l_false:
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            // verbose_stream() << "giveup assign\n";
            // return sat::check_result::CR_GIVEUP;
            // or:
            r = l_undef;
            break;
        }

        saturation saturate(*this);
        switch (saturate()) {
        case l_true:
            break;
        case l_false:
            TRACE("bv", tout << "saturate\n");
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            verbose_stream() << "giveup saturate\n";
            r = l_undef;
            break;
        }

        switch (m_monomials.refine()) {
        case l_true:
            break;
        case l_false:
            TRACE("bv", tout << "refine\n");
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            verbose_stream() << "giveup refine\n";
            r = l_undef;
            break;
        }

        switch (m_monomials.bit_blast()) {
        case l_true:
            break;
        case l_false:
            TRACE("bv", tout << "blast\n");
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            verbose_stream() << "giveup blast\n";
            r = l_undef;
            break;
        }

        if (r == l_true)
            return sat::check_result::CR_DONE;

        return sat::check_result::CR_GIVEUP;

#if 0        
        // If no saturation propagation was possible, explain the conflict using the variable assignment.
        m_unsat_core = explain_strong_eval(get_constraint(conflict_idx));
        m_unsat_core.push_back(get_dependency(conflict_idx));
        s.set_conflict(m_unsat_core, "polysat-bail-out-conflict");
        decay_activity();
        return sat::check_result::CR_CONTINUE;
#endif
    }

    /**
    * Find variables at the maximal scope level that are used in the conflicting literal.
    */
    svector<pvar> core::find_conflict_variables(constraint_id idx) {
        svector<pvar> result;
        auto [sc, d, value] = m_constraint_index[idx.id];
        unsigned lvl = s.level(d);
        for (auto v : sc.unfold_vars()) {
            if (!is_assigned(v))
                continue;
            auto new_level = s.level(m_justification[v]);
            if (new_level < lvl)
                continue;
            if (new_level > lvl)
                result.reset();
            result.push_back(v);
            lvl = new_level;
        }
        return result;
    }

    bool core::propagate() { 
        if (m_qhead == m_prop_queue.size())
            return false;
        s.trail().push(value_trail(m_qhead));
        for (; m_qhead < m_prop_queue.size() && !s.inconsistent(); ++m_qhead)
            propagate_assignment(m_prop_queue[m_qhead]);               
        return true;
    }

    void core::viable_conflict(pvar v) {
        TRACE("bv", tout << "viable-conflict v" << v << "\n");
        s.set_conflict(m_viable.explain(), "viable-conflict");
        decay_activity();
    }

    void core::viable_propagate(pvar v, rational const& var_value) {
        auto p = var2pdd(v).mk_var(v);
        auto sc = m_constraints.eq(p, var_value);
        TRACE("bv", tout << "check-propagate v" << v << " := " << var_value << " " << sc << "\n");
        auto d = s.propagate(sc, m_viable.explain(), "viable-propagate");
        propagate_assignment(v, var_value, d);
    }

    void core::propagate_assignment(constraint_id idx) { 

        auto [sc, dep, value] = m_constraint_index[idx.id];
        SASSERT(value != l_undef);
        if (value == l_false)
            sc = ~sc;
        TRACE("bv", tout << "propagate " << sc << " using " << dep << " := " << value << "\n");
        if (sc.is_always_false()) {
            s.set_conflict({dep}, "infeasible constraint");
            return;
        }
        rational var_value;
        if (sc.is_eq(m_var, var_value) && !is_assigned(m_var))
            propagate_assignment(m_var, var_value, dep);
        else
            propagate_activation(idx, sc, dep);
    }

    void core::add_watch(unsigned idx, unsigned var) {
        m_watch[var].push_back(idx);
    }

    void core::propagate_activation(constraint_id idx, signed_constraint& sc, dependency dep) {
        sc.activate(*this, dep);
        pvar v = null_var;
        for (auto w : sc.vars()) {
            if (is_assigned(w))
                continue;
            if (v != null_var)
                return;
            v = w;
        }
        if (v != null_var) {
            switch (m_viable.add_unitary(v, idx, m_values[v])) {
            case find_t::empty:
                viable_conflict(v);
                break;
            case find_t::singleton:
                viable_propagate(v, m_values[v]);
                break;
            default:
                break;
            }
        }           
        else if (v == null_var && weak_eval(sc) == l_false) {
            auto ex = explain_weak_eval(sc);
            ex.push_back(dep);
            s.set_conflict(ex, "infeasible propagation");
        }
    }

    void core::propagate_assignment(pvar v, rational const& value, dependency dep) {
        TRACE("bv", tout << "propagate assignment v" << v << " := " << value << "\n");
        SASSERT(!is_assigned(v));
        if (!m_viable.assign(v, value)) {
            auto deps = m_viable.explain();
            deps.push_back(dep);
            s.set_conflict(deps, "non-viable assignment");
            return;
        }
        s.propagate_eq(v, value, dep);
        if (s.inconsistent())
            return;
        m_values[v] = value;
        m_justification[v] = dep;   
        m_assignment.push(v , value);
        s.trail().push(mk_assign_var(v, *this));
        m_var_queue.del_var_eh(v);

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

           
            SASSERT(!swapped || vars.size() <= 1 || (!is_assigned(vars[0]) && !is_assigned(vars[1])));
            if (!swapped)
                m_watch[v][j++] = idx;
            if (s.inconsistent()) {
                ++k;
                for (; k < sz; ++k)
                    m_watch[v][j++] = m_watch[v][k];
                m_watch[v].shrink(j);
                return;
            }
            if (vars.size() <= 1)
                continue;
            auto v0 = vars[0];
            auto v1 = vars[1];
            if (!is_assigned(v0) || is_assigned(v1))
                continue;
            if (value != l_undef) {
                switch (m_viable.add_unitary(v1, { idx }, m_values[v1])) {
                case find_t::empty:
                    viable_conflict(v1);
                    break;
                case find_t::singleton:
                    viable_propagate(v1, m_values[v1]);
                    break;
                default:
                    break;
                }
            }                
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
        switch (weak_eval(sc)) {
        case l_false:
            if (value != l_false)
                s.propagate(d, true, explain_weak_eval(sc), "eval-propagate");
            break;
        case l_true:
            if (value != l_true)
                s.propagate(d, false, explain_weak_eval(sc), "eval-propagate");
            break;
        default:
            break;
        }
    }

    dependency core::get_dependency(constraint_id idx) const {
        if (idx.is_null())
            return null_dependency;
        auto [sc, d, value] = m_constraint_index[idx.id];
        return d;
    }

    void core::propagate(constraint_id id, signed_constraint& sc, lbool value, dependency const& d) {
        lbool eval_value = weak_eval(sc);
        if (eval_value == l_undef)
            sc.propagate(*this, value, d);
        else if (value == l_undef)
            s.propagate(d, eval_value != l_true, explain_weak_eval(sc), "constraint-propagate");
        else if (value != eval_value) {
            m_unsat_core = explain_weak_eval(sc);
            m_unsat_core.push_back(m_constraint_index[id.id].d);
            s.set_conflict(m_unsat_core, "polysat-constraint-core");
            decay_activity();
        }                   
    }

    void core::get_bitvector_suffixes(pvar v, offset_slices& out) {
        s.get_bitvector_suffixes(v, out);
    }

    void core::get_fixed_bits(pvar v, fixed_bits_vector& fixed_bits) {
        s.get_fixed_bits(v, fixed_bits);
    }

    void core::get_subslices(pvar v, offset_slices& out) {
        s.get_bitvector_sub_slices(v, out);
    }

    pdd core::mk_zero_extend(unsigned sz, pdd const& p) { 
        if (p.is_val()) 
            return value(p.val(), p.manager().power_of_2() + sz);        
        throw default_exception("nyi zero_extend"); 
    }

    pdd core::mk_extract(unsigned hi, unsigned lo, pdd const& p) {
        if (p.is_val()) 
            return value(p.val(), hi - lo + 1);        
        throw default_exception("nyi extract");
    }

    bool core::inconsistent() const {
        return s.inconsistent();
    }

    void core::assign_eh(constraint_id index, bool sign) { 
        struct unassign : public trail {
            core& c;
            unsigned m_index;
            unassign(core& c, unsigned index): c(c), m_index(index) {}
            void undo() override {
                c.m_constraint_index[m_index].value = l_undef;
                c.m_prop_queue.pop_back();
            }
        };

        auto& value = m_constraint_index[index.id].value;
        TRACE("bv", tout << "assignment " << index.id << " " << m_constraint_index[index.id].sc << " := " << value << " sign: " << sign << "\n");

        if (value != l_undef &&
            ((value == l_false && !sign) || (value == l_true && sign))) {
            TRACE("bv", display(tout << "index " << m_constraint_index[index.id].d << " " << m_constraint_index[index.id].sc << "\n"));
        }
        
        SASSERT(value == l_undef || (value == l_false && sign) || (value == l_true && !sign));

        if (value != l_undef)
            return;
        m_prop_queue.push_back(index);
        value = to_lbool(!sign);
        s.trail().push(unassign(*this, index.id));
    }

    dependency_vector core::explain_weak_eval(unsigned_vector const& vars) {
        dependency_vector deps;
        for (auto v : vars) {
            if (is_assigned(v)) {
                inc_activity(v);
                deps.push_back(m_justification[v]);
            }
        }
        return deps;
    }

    dependency_vector core::explain_weak_eval(signed_constraint const& sc) {
        return explain_weak_eval(sc.vars());
    }

    dependency_vector core::explain_strong_eval(signed_constraint const& sc) {
        return explain_weak_eval(sc.unfold_vars());
    }

    lbool core::weak_eval(signed_constraint const& sc) { 
        return sc.weak_eval(m_assignment);
    }

    lbool core::strong_eval(signed_constraint const& sc) {
        return sc.strong_eval(m_assignment);
    }

    pdd core::subst(pdd const& p) { 
        return m_assignment.apply_to(p);
    }

    trail_stack& core::trail() {
        return s.trail();
    }

    bool core::add_axiom(char const* name, constraint_or_dependency_list const& cs, bool is_redundant) {
        return s.add_axiom(name, cs.begin(), cs.end(), is_redundant);
    }

    bool core::add_axiom(char const* name, constraint_or_dependency const* begin, constraint_or_dependency const* end, bool is_redundant) {
        return s.add_axiom(name, begin, end, is_redundant);
    }

    bool core::add_axiom(char const* name, constraint_or_dependency_vector const& cs, bool is_redundant) {
        return s.add_axiom(name, cs.begin(), cs.end(), is_redundant);
    }

    std::ostream& core::display(std::ostream& out) const {
        if (m_constraint_index.empty() && m_vars.empty())
            return out;
        out << "polysat:\n";
        for (auto const& [sc, d, value] : m_constraint_index) 
            out << sc << " " << d << " := " << value << "\n";        
        for (unsigned i = 0; i < m_vars.size(); ++i) 
            out << m_vars[i] << " := " << m_values[i] << " " << m_justification[i] << "\n";        
        m_var_queue.display(out << "var queue: ") << "\n";
        m_viable.display(out);
        m_monomials.display(out);
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

    void core::add_opdef(signed_constraint sc) {
        auto idx = register_constraint(sc, dependency::axiom());
        assign_eh(idx, false);
    }

    signed_constraint core::get_constraint(constraint_id idx) {
        auto [sc, d, value] = m_constraint_index[idx.id];
        SASSERT(value != l_undef);
        if (value == l_false)
            sc = ~sc;
        return sc;
    }

    lbool core::weak_eval(constraint_id id) {
        return get_constraint(id).weak_eval(m_assignment);
    }

    lbool core::strong_eval(constraint_id id) {
        return get_constraint(id).strong_eval(m_assignment);
    }

    void core::inc_activity(pvar v) {
        unsigned& act = m_activity[v].second;
        act += m_activity_inc;
        m_var_queue.activity_increased_eh(v);
        if (act > (1 << 24))
            rescale_activity();        
    }

    void core::rescale_activity() {
        for (auto& act : m_activity) 
            act.second >>= 14;        
        m_activity_inc >>= 14;
    }

    void core::decay_activity() {
        m_activity_inc *= 110;
        m_activity_inc /= 100;
    }

}
