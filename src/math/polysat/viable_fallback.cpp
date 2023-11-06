/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    viable fallback to univariate solvers

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

TODO: improve management of the fallback univariate solvers:
      - use a solver pool and recycle the least recently used solver
      - incrementally add/remove constraints
      - set resource limit of univariate solver

--*/


#include "util/debug.h"
#include "math/polysat/viable_fallback.h"
#include "math/polysat/solver.h"
#include "math/polysat/univariate/univariate_solver.h"

namespace polysat {

    viable_fallback::viable_fallback(solver& s):
        s(s) {
        m_usolver_factory = mk_univariate_bitblast_factory();
    }

    void viable_fallback::push_var(unsigned bit_width) {
        m_constraints.push_back({});
    }

    void viable_fallback::pop_var() {
        m_constraints.pop_back();
    }

    void viable_fallback::push_constraint(pvar v, signed_constraint const& c) {
        // v is the only unassigned variable in c.
        SASSERT(c->vars().size() == 1 || !s.is_assigned(v));
        DEBUG_CODE(for (pvar w : c->vars()) { if (v != w) SASSERT(s.is_assigned(w)); });
        m_constraints[v].push_back(c);
        m_constraints_trail.push_back(v);
        s.m_trail.push_back(trail_instr_t::viable_constraint_i);
    }

    void viable_fallback::pop_constraint() {
        pvar v = m_constraints_trail.back();
        m_constraints_trail.pop_back();
        m_constraints[v].pop_back();
    }

    signed_constraint viable_fallback::find_violated_constraint(assignment const& a, pvar v) {
        for (signed_constraint const c : m_constraints[v]) {
            // for this check, all variables need to be assigned
            DEBUG_CODE(for (pvar w : c->vars()) { SASSERT(a.contains(w)); });
            if (c.is_currently_false(a)) {
                LOG(assignment_pp(s, v, a.value(v)) << " violates constraint " << lit_pp(s, c));
                return c;
            }
            SASSERT(c.is_currently_true(a));
        }
        return {};
    }

    univariate_solver* viable_fallback::usolver(unsigned bit_width) {
        univariate_solver* us;

        auto it = m_usolver.find_iterator(bit_width);
        if (it != m_usolver.end()) {
            us = it->m_value.get();
            us->pop(1);
        }
        else {
            auto& mk_solver = *m_usolver_factory;
            m_usolver.insert(bit_width, mk_solver(bit_width));
            us = m_usolver[bit_width].get();
        }
        SASSERT_EQ(us->scope_level(), 0);

        // push once on the empty solver so we can reset it before the next use
        us->push();

        return us;
    }

    find_t viable_fallback::find_viable(pvar v, rational& out_val) {
        unsigned const bit_width = s.m_size[v];
        univariate_solver* us = usolver(bit_width);

        auto const& cs = m_constraints[v];
        for (unsigned i = cs.size(); i-- > 0; ) {
            signed_constraint const c = cs[i];
            LOG("Univariate constraint: " << c);
            c.add_to_univariate_solver(v, s, *us, c.blit().to_uint());
        }

        switch (us->check()) {
        case l_true:
            out_val = us->model();
            // we don't know whether the SMT instance has a unique solution
            return find_t::multiple;
        case l_false:
            s.set_conflict_by_viable_fallback(v, *us);
            return find_t::empty;
        default:
            return find_t::resource_out;
        }
    }

    std::ostream& operator<<(std::ostream& out, find_t x) {
        switch (x) {
        case find_t::empty:
            return out << "empty";
        case find_t::singleton:
            return out << "singleton";
        case find_t::multiple:
            return out << "multiple";
        case find_t::resource_out:
            return out << "resource_out";
        }
        UNREACHABLE();
        return out;
    }

}

