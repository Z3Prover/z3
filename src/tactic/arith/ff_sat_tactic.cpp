#include "tactic/arith/ff_solve_tactic.h"
#include "tactic/tactical.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "ast/ff_decl_plugin.h"
#include "ast/converters/model_converter.h"
#include "model/model_evaluator.h"
#include "sat/sat_solver.h"
#include <unordered_map>

namespace {
    // A bounded lazy SAT/algebra combination. The complete ff2bv backend remains
    // available when algebra or Boolean search reaches its budget. Conflict clauses
    // use input dependency cores; v2 additionally needs checkable algebraic witnesses.
    class ff_sat_tactic : public tactic {
        ast_manager &m;
        params_ref p;
        statistics m_stats;

    public:
        ff_sat_tactic(ast_manager &m, params_ref const &p) : m(m), p(p) {}
        char const *name() const override {
            return "ff-sat";
        }
        tactic *translate(ast_manager &target) override {
            return alloc(ff_sat_tactic, target, p);
        }
        void cleanup() override {}
        void collect_statistics(statistics &st) const override {
            st.copy(m_stats);
        }
        void reset_statistics() override {
            m_stats.reset();
        }
        void updt_params(params_ref const &q) override {
            p.append(q);
        }
        void collect_param_descrs(param_descrs &ds) override {
            ds.insert("ff.max_branches", CPK_UINT, "maximum lazy SAT/algebra assignments before exact fallback", "128");
            tactic_ref t = mk_ff_solve_tactic(m, p);
            t->collect_param_descrs(ds);
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            if (g->proofs_enabled())
                throw tactic_exception("QF_FF certificates are not supported in v1");
            ff_util ff(m);
            params_ref sp;
            sat::solver sat(sp, m.limit());
            std::unordered_map<expr *, sat::literal> lits;
            expr_ref_vector pins(m), atoms(m), booleans(m);
            expr_dependency_ref deps(m);
            auto clause = [&](sat::literal_vector const &ls) { sat.mk_clause(ls); };
            auto conjunction = [&](sat::literal r, sat::literal_vector const &args, bool is_and) {
                sat::literal_vector big;
                big.push_back(is_and ? r : ~r);
                for (auto a : args) {
                    sat.mk_clause(is_and ? ~r : r, is_and ? a : ~a);
                    big.push_back(is_and ? ~a : a);
                }
                clause(big);
            };
            unsigned depth = 0;
            std::function<sat::literal(expr *)> encode = [&](expr *e) -> sat::literal {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                if (depth > 512)
                    throw tactic_exception("ff-sat Boolean nesting budget exceeded");
                flet<unsigned> nesting(depth, depth + 1);
                if (auto it = lits.find(e); it != lits.end())
                    return it->second;
                if (!is_app(e) || !m.is_bool(e))
                    throw tactic_exception("ff-sat requires quantifier-free Boolean structure");
                pins.push_back(e);
                sat::literal r(sat.mk_var(true), false);
                lits.emplace(e, r);
                app *a = to_app(e);
                if (m.is_true(e) || m.is_false(e)) {
                    sat::literal_vector unit;
                    unit.push_back(m.is_true(e) ? r : ~r);
                    clause(unit);
                }
                else if (m.is_eq(e) && ff.is_ff(a->get_arg(0)))
                    atoms.push_back(e);
                else if (is_uninterp_const(e))
                    booleans.push_back(e);
                else if (m.is_distinct(e) && a->get_num_args() && ff.is_ff(a->get_arg(0))) {
                    sat::literal_vector ls;
                    for (unsigned i = 0; i < a->get_num_args(); ++i)
                        for (unsigned j = 0; j < i; ++j) {
                            expr_ref eq(m.mk_eq(a->get_arg(i), a->get_arg(j)), m);
                            ls.push_back(~encode(eq));
                        }
                    conjunction(r, ls, true);
                }
                else {
                    sat::literal_vector ls;
                    for (expr *arg : *a)
                        ls.push_back(encode(arg));
                    if (m.is_not(e)) {
                        sat.mk_clause(~r, ~ls[0]);
                        sat.mk_clause(r, ls[0]);
                    }
                    else if (m.is_and(e) || m.is_or(e))
                        conjunction(r, ls, m.is_and(e));
                    else if (m.is_implies(e)) {
                        ls[0] = ~ls[0];
                        conjunction(r, ls, false);
                    }
                    else if ((m.is_eq(e) || m.is_xor(e) || m.is_distinct(e)) && ls.size() == 2) {
                        auto x = ls[0], y = ls[1];
                        auto q = m.is_eq(e) ? r : ~r;
                        sat.mk_clause(~q, ~x, y);
                        sat.mk_clause(~q, x, ~y);
                        sat.mk_clause(q, x, y);
                        sat.mk_clause(q, ~x, ~y);
                    }
                    else if (m.is_ite(e)) {
                        auto c = ls[0], x = ls[1], y = ls[2];
                        sat.mk_clause(~c, ~r, x);
                        sat.mk_clause(~c, r, ~x);
                        sat.mk_clause(c, ~r, y);
                        sat.mk_clause(c, r, ~y);
                    }
                    else
                        throw tactic_exception("ff-sat: unsupported Boolean operator");
                }
                return r;
            };
            for (unsigned i = 0; i < g->size(); ++i) {
                deps = m.mk_join(deps, g->dep(i));
                sat::literal_vector unit;
                unit.push_back(encode(g->form(i)));
                clause(unit);
            }
            tactic_ref algebra = mk_ff_solve_tactic(m, p);
            on_scope_exit collect([&]() { algebra->collect_statistics(m_stats); });
            for (unsigned round = 0; round < p.get_uint("ff.max_branches", 128); ++round) {
                m_stats.update("ff sat branches", 1u);
                lbool status = sat.check();
                goal_ref out = alloc(goal, *g, true);
                if (status == l_false) {
                    out->assert_expr(m.mk_false(), nullptr, deps);
                    g->reset_all();
                    g->copy_from(*out);
                    g->inc_depth();
                    result.push_back(g.get());
                    return;
                }
                if (status != l_true)
                    throw tactic_exception("ff-sat Boolean search incomplete");
                auto const &assignment = sat.get_model();
                auto truth = [&](expr *e) {
                    auto l = lits.at(e);
                    return (assignment[l.var()] == l_true) != l.sign();
                };
                goal_ref branch = alloc(goal, m, false, true, true);
                sat::literal_vector block;
                for (expr *atom : atoms) {
                    bool value = truth(atom);
                    expr_ref signed_atom(value ? atom : m.mk_not(atom), m);
                    branch->assert_expr(signed_atom, nullptr, m.mk_leaf(signed_atom));
                    block.push_back(value ? ~lits.at(atom) : lits.at(atom));
                }
                // Save Boolean values: the next SAT check may change its model.
                std::vector<bool> bool_values;
                for (expr *b : booleans)
                    bool_values.push_back(truth(b));
                goal_ref_buffer solved;
                (*algebra)(branch, solved);
                if (solved.size() != 1)
                    throw tactic_exception("ff-sat unexpected algebra result");
                if (solved[0]->inconsistent()) {
                    m_stats.update("ff sat conflicts", 1u);
                    ptr_vector<expr> core;
                    m.linearize(solved[0]->dep(0), core);
                    sat::literal_vector learned;
                    for (expr *e : core) {
                        if (m.is_not(e))
                            learned.push_back(lits.at(to_app(e)->get_arg(0)));
                        else
                            learned.push_back(~lits.at(e));
                    }
                    block = learned;
                    sat.pop_to_base_level();
                    clause(block);
                    continue;
                }
                if (!solved[0]->is_decided_sat())
                    throw tactic_exception("ff-sat algebra incomplete");
                model_ref mdl;
                model_converter2model(m, solved[0]->mc(), mdl);
                if (!mdl)
                    mdl = alloc(model, m);
                for (unsigned i = 0; i < booleans.size(); ++i)
                    mdl->register_decl(to_app(booleans.get(i))->get_decl(), m.mk_bool_val(bool_values[i]));
                model_evaluator eval(*mdl);
                for (unsigned i = 0; i < g->size(); ++i) {
                    expr_ref value(m);
                    eval(g->form(i), value);
                    if (!m.is_true(value))
                        throw tactic_exception("ff-sat could not validate original model");
                }
                if (g->models_enabled())
                    out->add(model2model_converter(mdl.get()));
                g->reset_all();
                g->copy_from(*out);
                g->inc_depth();
                result.push_back(g.get());
                return;
            }
            throw tactic_exception("ff-sat branch budget exhausted");
        }
    };
}  // namespace
tactic *mk_ff_sat_tactic(ast_manager &m, params_ref const &p) {
    return and_then(mk_elim_term_ite_tactic(m, p), alloc(ff_sat_tactic, m, p));
}
