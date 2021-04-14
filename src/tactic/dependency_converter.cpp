/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dependency_converter.cpp

Abstract:

    Utility for converting dependencies across subgoals.

Author:

    Nikolaj Bjorner (nbjorner) 2017-11-19

Notes:


--*/

#include "tactic/dependency_converter.h"
#include "tactic/goal.h"

class unit_dependency_converter : public dependency_converter {
    expr_dependency_ref m_dep;
public:
    
    unit_dependency_converter(expr_dependency_ref& d) : m_dep(d) {}

    expr_dependency_ref operator()() override { return m_dep; }
    
    dependency_converter * translate(ast_translation & translator) override {
        expr_dependency_translation tr(translator);
        expr_dependency_ref d(tr(m_dep), translator.to());
        return alloc(unit_dependency_converter, d);
    }

    void display(std::ostream& out) override {
        out << m_dep.get() << "\n";
    }
};

class concat_dependency_converter : public dependency_converter {
    dependency_converter_ref m_dc1;
    dependency_converter_ref m_dc2;
public:
    
    concat_dependency_converter(dependency_converter* c1, dependency_converter* c2) : m_dc1(c1), m_dc2(c2) {}

    expr_dependency_ref operator()() override {
        expr_dependency_ref d1 = (*m_dc1)();
        expr_dependency_ref d2 = (*m_dc2)();
        ast_manager& m = d1.get_manager();
        return expr_dependency_ref(m.mk_join(d1, d2), m);
    }
    
    dependency_converter * translate(ast_translation & translator) override {
        return alloc(concat_dependency_converter, m_dc1->translate(translator), m_dc2->translate(translator));
    }

    void display(std::ostream& out) override {
        m_dc1->display(out);
        m_dc2->display(out);
    }
};

class goal_dependency_converter : public dependency_converter {
    ast_manager&    m;
    goal_ref_buffer m_goals;
public:
    goal_dependency_converter(unsigned n, goal * const* goals) :
        m(goals[0]->m()) {
        for (unsigned i = 0; i < n; ++i) m_goals.push_back(goals[i]);
    }

    expr_dependency_ref operator()() override {
        expr_dependency_ref result(m.mk_empty_dependencies(), m);
        for (goal_ref g : m_goals) {
            dependency_converter_ref dc = g->dc();
            if (dc) result = m.mk_join(result, (*dc)());
        }
        return result;
    }    
    dependency_converter * translate(ast_translation & translator) override {
        goal_ref_buffer goals;
        for (goal_ref g : m_goals) goals.push_back(g->translate(translator));
        return alloc(goal_dependency_converter, goals.size(), goals.data());
    }

    void display(std::ostream& out) override { out << "goal-dep\n"; }

};

dependency_converter * dependency_converter::concat(dependency_converter * mc1, dependency_converter * mc2) {
    if (!mc1) return mc2;
    if (!mc2) return mc1;
    return alloc(concat_dependency_converter, mc1, mc2);
}

dependency_converter* dependency_converter::unit(expr_dependency_ref& d) {
    return alloc(unit_dependency_converter, d);
}

dependency_converter * dependency_converter::concat(unsigned n, goal * const* goals) {
    if (n == 0) return nullptr;
    return alloc(goal_dependency_converter, n, goals);
}
