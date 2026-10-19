/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#include "ast/simplifiers/elim_monotone.h"
#include "ast/expr_substitution.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include <algorithm>

namespace {
    struct variable {
        unsigned positive = 0, negative = 0;
        bool blocked = false;
        unsigned_vector atoms;
    };

    struct inequality {
        expr* atom;
        unsigned polarity;
        unsigned_vector vars;
        vector<rational> coeffs;
        rational constant;
        bool removed = false;
    };

    struct state {
        ast_manager& m;
        arith_util& a;
        dependent_expr_state& fmls;
        obj_map<expr, unsigned> var_ids;
        ptr_vector<expr> vars;
        vector<variable> info;
        vector<inequality> atoms;
        expr_mark blocked;

        state(ast_manager& m, arith_util& a, dependent_expr_state& fmls) : m(m), a(a), fmls(fmls) {}

        unsigned var_id(expr* e) {
            unsigned id;
            if (var_ids.find(e, id))
                return id;
            id = vars.size();
            var_ids.insert(e, id);
            vars.push_back(e);
            info.push_back(variable());
            info.back().blocked = fmls.frozen(e);
            return id;
        }

        void block(expr* e) {
            auto visit = [&](expr* t) {
                if (is_uninterp_const(t) && a.is_real(t))
                    info[var_id(t)].blocked = true;
            };
            for_each_expr(visit, blocked, e);
        }

        bool parse(expr* atom, unsigned polarity) {
            expr *lhs, *rhs;
            if (a.is_le(atom, lhs, rhs) || a.is_lt(atom, lhs, rhs)) {}
            else if (a.is_ge(atom, rhs, lhs) || a.is_gt(atom, rhs, lhs)) {}
            else
                return false;
            if (!a.is_real(lhs) || polarity == 3)
                return false;
            obj_map<expr, rational> coeffs;
            rational constant, r;
            vector<std::pair<expr*, rational>> todo;
            todo.push_back({lhs, rational(1)});
            todo.push_back({rhs, rational(-1)});
            unsigned steps = 0;
            while (!todo.empty()) {
                if (++steps > 10000)
                    return false;
                if ((steps & 63) == 0 && !m.inc())
                    return false;
                auto [t, c] = todo.back();
                todo.pop_back();
                if (c.is_zero())
                    continue;
                if (a.is_numeral(t, r) || (a.is_to_real(t) && a.is_extended_numeral(t, r)))
                    constant += c * r;
                else if (is_uninterp_const(t) && a.is_real(t))
                    coeffs.insert_if_not_there(t, rational(0)) += c;
                else if (a.is_add(t)) {
                    for (expr* arg : *to_app(t))
                        todo.push_back({arg, c});
                }
                else if (a.is_sub(t)) {
                    app* f = to_app(t);
                    for (unsigned j = 0; j < f->get_num_args(); ++j)
                        todo.push_back({f->get_arg(j), j == 0 ? c : -c});
                }
                else if (a.is_uminus(t))
                    todo.push_back({to_app(t)->get_arg(0), -c});
                else if (a.is_mul(t) && to_app(t)->get_num_args() == 2) {
                    auto* f = to_app(t);
                    if (a.is_extended_numeral(f->get_arg(0), r))
                        todo.push_back({f->get_arg(1), c * r});
                    else if (a.is_extended_numeral(f->get_arg(1), r))
                        todo.push_back({f->get_arg(0), c * r});
                    else
                        return false;
                }
                else if (a.is_div(t) && a.is_extended_numeral(to_app(t)->get_arg(1), r) && !r.is_zero())
                    todo.push_back({to_app(t)->get_arg(0), c / r});
                else
                    return false;
            }
            inequality row;
            row.atom = atom;
            row.polarity = polarity;
            row.constant = constant;
            ptr_vector<expr> ordered;
            for (auto const& kv : coeffs)
                if (!kv.m_value.is_zero())
                    ordered.push_back(kv.m_key);
            std::sort(ordered.begin(), ordered.end(), [](expr* x, expr* y) { return x->get_id() < y->get_id(); });
            for (expr* x : ordered) {
                unsigned id = var_id(x);
                rational c = coeffs[x];
                row.vars.push_back(id);
                row.coeffs.push_back(c);
                info[id].atoms.push_back(atoms.size());
                if (c.is_pos() == (polarity == 1))
                    ++info[id].positive;
                else
                    ++info[id].negative;
            }
            atoms.push_back(std::move(row));
            return true;
        }

        bool collect() {
            obj_map<expr, unsigned> seen;
            vector<std::pair<expr*, unsigned>> todo;
            ptr_vector<expr> leaves;
            for (unsigned i = fmls.qhead(); i < fmls.qtail(); ++i)
                todo.push_back({fmls[i].fml(), 1});
            while (!todo.empty()) {
                if (!m.inc())
                    return false;
                auto [e, polarity] = todo.back();
                todo.pop_back();
                unsigned& mask = seen.insert_if_not_there(e, 0);
                unsigned fresh = polarity & ~mask;
                if (!fresh)
                    continue;
                mask |= fresh;
                expr *x, *y, *z;
                unsigned flipped = ((fresh & 1) << 1) | ((fresh & 2) >> 1);
                if (m.is_not(e, x))
                    todo.push_back({x, flipped});
                else if (m.is_and(e) || m.is_or(e)) {
                    for (expr* arg : *to_app(e))
                        todo.push_back({arg, fresh});
                }
                else if (m.is_implies(e, x, y)) {
                    todo.push_back({x, flipped});
                    todo.push_back({y, fresh});
                }
                else if (m.is_ite(e, x, y, z)) {
                    todo.push_back({x, 3});
                    todo.push_back({y, fresh});
                    todo.push_back({z, fresh});
                }
                else if (mask == fresh)
                    leaves.push_back(e);
            }
            for (expr* e : leaves) {
                if (!m.inc())
                    return false;
                if (!parse(e, seen[e]))
                    block(e);
            }
            return true;
        }

        bool pure(unsigned id) const {
            auto const& v = info[id];
            return !v.blocked && ((v.positive == 0) != (v.negative == 0));
        }

        expr_ref bound(inequality const& row, unsigned id) {
            rational c;
            for (unsigned k = 0; k < row.vars.size(); ++k)
                if (row.vars[k] == id)
                    c = row.coeffs[k];
            SASSERT(!c.is_zero());
            expr_ref_vector terms(m);
            terms.push_back(a.mk_numeral(-row.constant / c, false));
            for (unsigned k = 0; k < row.vars.size(); ++k) {
                if (row.vars[k] == id)
                    continue;
                expr_ref coefficient(a.mk_numeral(-row.coeffs[k] / c, false), m);
                terms.push_back(a.mk_mul(coefficient, vars[row.vars[k]]));
            }
            return expr_ref(a.mk_add(terms.size(), terms.data()), m);
        }
    };
}

bool elim_monotone::eliminate() {
    state s(m, a, m_fmls);
    if (!s.collect())
        return false;
    unsigned_vector todo;
    for (unsigned id = 0; id < s.vars.size(); ++id)
        if (s.pure(id))
            todo.push_back(id);
    expr_safe_replace replace(m);
    expr_ref_vector eliminated_vars(m), definitions(m);
    unsigned eliminated = 0;
    for (unsigned head = 0; head < todo.size(); ++head) {
        if (!m.inc())
            return false;
        unsigned id = todo[head];
        if (!s.pure(id))
            continue;
        bool increase = s.info[id].positive == 0;
        expr_ref limit(m);
        for (unsigned index : s.info[id].atoms) {
            auto& row = s.atoms[index];
            if (row.removed)
                continue;
            expr_ref b = s.bound(row, id);
            if (!limit)
                limit = b;
            else {
                expr_ref cmp(a.mk_le(limit, b), m);
                limit = m.mk_ite(cmp, increase ? b.get() : limit.get(), increase ? limit.get() : b.get());
            }
            row.removed = true;
            replace.insert(row.atom, row.polarity == 1 ? m.mk_true() : m.mk_false());
            for (unsigned k = 0; k < row.vars.size(); ++k) {
                unsigned v = row.vars[k];
                if (row.coeffs[k].is_pos() == (row.polarity == 1))
                    --s.info[v].positive;
                else
                    --s.info[v].negative;
                if (s.pure(v))
                    todo.push_back(v);
            }
        }
        // One unit of slack satisfies both strict and non-strict real bounds.
        expr_ref slack(a.mk_numeral(rational(increase ? 1 : -1), false), m);
        definitions.push_back(a.mk_add(limit, slack));
        eliminated_vars.push_back(s.vars[id]);
        ++eliminated;
    }
    if (eliminated) {
        scoped_ptr<expr_substitution> sub = alloc(expr_substitution, m);
        expr_safe_replace normalize(m);
        for (unsigned i = definitions.size(); i-- > 0; ) {
            expr_ref def(definitions.get(i), m);
            normalize(def);
            sub->insert(eliminated_vars.get(i), def);
            normalize.insert(eliminated_vars.get(i), def);
        }
        th_rewriter rw(m);
        unsigned_vector changed;
        vector<dependent_expr> old_fmls, new_fmls;
        for (unsigned i = qhead(); i < qtail(); ++i) {
            if (!m.inc())
                return false;
            auto d = m_fmls[i];
            expr_ref f(d.fml(), m);
            replace(f);
            rw(f);
            if (f == d.fml())
                continue;
            changed.push_back(i);
            old_fmls.push_back(d);
            new_fmls.push_back(dependent_expr(m, f, nullptr, d.dep()));
        }
        for (unsigned i = 0; i < changed.size(); ++i)
            m_fmls.update(changed[i], new_fmls[i]);
        // These assignments are witnesses, not equivalent definitions.
        m_fmls.model_trail().push(sub.detach(), old_fmls, true);
        m_eliminated += eliminated;
    }
    return eliminated != 0;
}

void elim_monotone::reduce() {
    if (proofs_enabled())
        return;
    m_fmls.freeze_suffix();
    // Boolean pruning can expose further one-sided variables.
    while (!m_fmls.inconsistent() && eliminate()) {}
}
