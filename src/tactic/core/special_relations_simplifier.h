/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    special_relations_simplifier.h

Abstract:

    Detect special relations in an axiomatization,
    rewrite goal using special relations.

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-28

Notes:

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/special_relations_decl_plugin.h"
#include "ast/pattern/expr_pattern_match.h"
#include "ast/rewriter/func_decl_replace.h"
#include "ast/ast_util.h"

class special_relations_simplifier : public dependent_expr_simplifier {
    expr_pattern_match      m_pm;
    svector<sr_property>    m_properties;

    struct sp_axioms {
        unsigned_vector m_formula_indices;
        sr_property     m_sp_features;
        sp_axioms() : m_sp_features(sr_none) {}
    };

    obj_map<func_decl, sp_axioms> m_detected_relations;

    void initialize() {
        if (!m_properties.empty()) return;
        sort_ref A(m.mk_uninterpreted_sort(symbol("A")), m);
        func_decl_ref R(m.mk_func_decl(symbol("?R"), A, A, m.mk_bool_sort()), m);
        var_ref x(m.mk_var(0, A), m);
        var_ref y(m.mk_var(1, A), m);
        var_ref z(m.mk_var(2, A), m);
        expr* _x = x, *_y = y, *_z = z;

        expr_ref Rxy(m.mk_app(R, _x, _y), m);
        expr_ref Ryz(m.mk_app(R, _y, _z), m);
        expr_ref Rxz(m.mk_app(R, _x, _z), m);
        expr_ref Rxx(m.mk_app(R, _x, _x), m);
        expr_ref Ryx(m.mk_app(R, _y, _x), m);
        expr_ref Rzy(m.mk_app(R, _z, _y), m);
        expr_ref Rzx(m.mk_app(R, _z, _x), m);
        expr_ref nRxy(m.mk_not(Rxy), m);
        expr_ref nRyx(m.mk_not(Ryx), m);
        expr_ref nRzx(m.mk_not(Rzx), m);
        expr_ref nRxz(m.mk_not(Rxz), m);

        sort* As[3] = { A, A, A };
        symbol xyz[3] = { symbol("x"), symbol("y"), symbol("z") };
        expr_ref fml(m);
        quantifier_ref q(m);
        expr_ref pat(m.mk_pattern(to_app(Rxy)), m);
        expr_ref pat0(m.mk_pattern(to_app(Rxx)), m);
        expr* pats[1]  = { pat };
        expr* pats0[1] = { pat0 };

        fml = m.mk_or(m.mk_not(Rxy), m.mk_not(Ryz), Rxz);
        q = m.mk_forall(3, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_transitive);
        fml = m.mk_or(mk_not(Rxy & Ryz), Rxz);
        q = m.mk_forall(3, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_transitive);

        fml = Rxx;
        q = m.mk_forall(1, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats0);
        register_pattern(m_pm.initialize(q), sr_reflexive);

        fml = m.mk_or(nRxy, nRyx, m.mk_eq(x, y));
        q = m.mk_forall(2, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_antisymmetric);
        fml = m.mk_or(mk_not(Rxy & Ryx), m.mk_eq(x, y));
        q = m.mk_forall(2, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_antisymmetric);

        fml = m.mk_or(nRyx, nRzx, Ryz, Rzy);
        q = m.mk_forall(3, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_lefttree);
        fml = m.mk_or(mk_not(Ryx & Rzx), Ryz, Rzy);
        q = m.mk_forall(3, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_lefttree);

        fml = m.mk_or(nRxy, nRxz, Ryz, Rzy);
        q = m.mk_forall(3, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_righttree);
        fml = m.mk_or(mk_not(Rxy & Rxz), Ryz, Rzy);
        q = m.mk_forall(3, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_righttree);

        fml = m.mk_or(Rxy, Ryx);
        q = m.mk_forall(2, As, xyz, fml, 0, symbol::null, symbol::null, 1, pats);
        register_pattern(m_pm.initialize(q), sr_total);

        TRACE(special_relations, m_pm.display(tout););
    }

    void register_pattern(unsigned index, sr_property p) {
        SASSERT(index == m_properties.size());
        m_properties.push_back(p);
    }

    void insert(func_decl* f, unsigned idx, sr_property p) {
        sp_axioms ax;
        m_detected_relations.find(f, ax);
        ax.m_formula_indices.push_back(idx);
        ax.m_sp_features = (sr_property)(p | ax.m_sp_features);
        m_detected_relations.insert(f, ax);
    }

    void collect_feature(unsigned idx, expr* f) {
        if (!is_quantifier(f)) return;
        unsigned index = 0;
        app_ref_vector patterns(m);
        bool is_match = m_pm.match_quantifier_index(to_quantifier(f), patterns, index);
        TRACE(special_relations, tout << "check " << is_match << " " << mk_pp(f, m) << "\n";
              if (is_match) tout << patterns << " " << index << "\n";);
        if (is_match) {
            func_decl* p = to_app(patterns.get(0)->get_arg(0))->get_decl();
            insert(p, idx, m_properties[index]);
        }
    }

public:
    special_relations_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
        : dependent_expr_simplifier(m, s), m_pm(m) {}

    char const* name() const override { return "special-relations"; }

    void reduce() override {
        initialize();
        m_detected_relations.reset();

        // Phase 1: scan all formulas to detect special relation axioms
        for (unsigned idx : indices())
            collect_feature(idx, m_fmls[idx].fml());

        if (m_detected_relations.empty())
            return;

        // Phase 2: for each detected relation, create a special relation declaration
        special_relations_util u(m);
        func_decl_replace replace(m);
        unsigned_vector to_delete;

        for (auto const& kv : m_detected_relations) {
            sr_property feature = kv.m_value.m_sp_features;
            switch (feature) {
            case sr_po:
                replace.insert(kv.m_key, u.mk_po_decl(kv.m_key));
                to_delete.append(kv.m_value.m_formula_indices);
                break;
            case sr_to:
                replace.insert(kv.m_key, u.mk_to_decl(kv.m_key));
                to_delete.append(kv.m_value.m_formula_indices);
                break;
            case sr_plo:
                replace.insert(kv.m_key, u.mk_plo_decl(kv.m_key));
                to_delete.append(kv.m_value.m_formula_indices);
                break;
            case sr_lo:
                replace.insert(kv.m_key, u.mk_lo_decl(kv.m_key));
                to_delete.append(kv.m_value.m_formula_indices);
                break;
            default:
                TRACE(special_relations, tout << "unprocessed feature " << feature << "\n";);
                break;
            }
        }

        if (replace.empty())
            return;

        // Phase 3: replace function declarations across all formulas
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            if (to_delete.contains(idx)) {
                m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr, d.dep()));
            }
            else {
                expr_ref new_fml = replace(d.fml());
                if (new_fml != d.fml())
                    m_fmls.update(idx, dependent_expr(m, new_fml, nullptr, d.dep()));
            }
        }
    }
};
