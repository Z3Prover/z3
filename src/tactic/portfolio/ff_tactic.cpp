#include "tactic/portfolio/ff_tactic.h"
#include "tactic/probe.h"
#include "tactic/tactical.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "ast/for_each_expr.h"
#include "ast/ff_decl_plugin.h"

// SMT fallback for field goals. Over large fields, relevancy propagation
// costs 20-40 % on the goals that reach this stage and gives nothing back.
// Over small fields the goal is mostly bit-blasted and search behaves better
// with relevancy, so the default is kept there.
namespace {
    class ff_small_field_probe : public probe {
    public:
        result operator()(goal const &g) override {
            ast_manager &m = g.m();
            ff_util ff(m);
            bool small = false;
            auto visit = [&](expr *e) {
                if (ff.is_ff(e) && ff.modulus(e->get_sort()) < rational(1 << 16))
                    small = true;
            };
            for (unsigned i = 0; i < g.size() && !small; ++i)
                for_each_expr(visit, g.form(i));
            return result(small);
        }
    };
}

tactic *mk_ff_smt_tactic(ast_manager &m, params_ref const &p) {
    params_ref q;
    q.set_uint("relevancy", 0);
    return cond(alloc(ff_small_field_probe), mk_smt_tactic(m, p), using_params(mk_smt_tactic(m, p), q));
}


bool has_ff_terms(ast_manager &m, expr *e) {
    auto *plugin = static_cast<ff_decl_plugin *>(m.get_plugin(m.get_family_id("ff")));
    if (!plugin || !plugin->has_sorts()) return false;
    ff_util ff(m);
    bool found = false;
    auto visit = [&](expr *e) { found |= ff.is_ff(e); };
    for_each_expr(visit, e);
    return found;
}
