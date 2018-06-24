/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

  sine_filter.cpp

Abstract:

  Tactic that performs Sine Qua Non premise selection

Author:

  Doug Woos

Revision History:
--*/

#include "tactic/sine_filter.h"
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_util.h"
#include "util/obj_pair_hashtable.h"
#include "ast/ast_pp.h"

class sine_tactic : public tactic {

    ast_manager&  m;
    params_ref    m_params;

public:

    sine_tactic(ast_manager& m, params_ref const& p):
        m(m), m_params(p) {}

    tactic * translate(ast_manager & m) override {
        return alloc(sine_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
    }

    void collect_param_descrs(param_descrs & r) override {
    }

    void operator()(goal_ref const & g, goal_ref_buffer& result) override {
        TRACE("sine", g->display(tout););
        TRACE("sine", tout << g->size(););
        ptr_vector<expr> new_forms;
        filter_expressions(g, new_forms);
        TRACE("sine", tout << new_forms.size(););
        g->reset();
        for (unsigned i = 0; i < new_forms.size(); i++) {
            g->assert_expr(new_forms.get(i), 0, 0);
        }
        g->inc_depth();
        g->updt_prec(goal::OVER);
        result.push_back(g.get());
        TRACE("sine", result[0]->display(tout););
        SASSERT(g->is_well_sorted());
    }

    void cleanup() override {
    }

private:

    typedef std::pair<expr*,expr*> t_work_item;

    t_work_item work_item(expr * e, expr * root) {
        return std::pair<expr*, expr*>(e, root);
    }

    void find_constants(expr * e, obj_hashtable<func_decl> &consts) {
        ptr_vector<expr> stack;
        stack.push_back(e);
        expr * curr;
        while (!stack.empty()) {
            curr = stack.back();
            stack.pop_back();
            if (is_app(curr) && is_uninterp(curr)) {
                app *a = to_app(curr);
                func_decl *f = a->get_decl();
                consts.insert_if_not_there(f);
            }
        }
    }

    bool quantifier_matches(quantifier * q,
                            obj_hashtable<func_decl> const & consts,
                            ptr_vector<func_decl> & next_consts) {
        TRACE("sine",
              tout << "size of consts is "; tout << consts.size(); tout << "\n";
              for (func_decl* f : consts) tout << f->get_name() << "\n";);

        bool matched = false;
        for (unsigned i = 0; i < q->get_num_patterns(); i++) {
            bool p_matched = true;
            ptr_vector<expr> stack;
            expr * curr;

            // patterns are wrapped with "pattern"
            if (!m.is_pattern(q->get_pattern(i), stack))
                continue;

            while (!stack.empty()) {
                curr = stack.back();
                stack.pop_back();

                if (is_app(curr)) {
                    app * a = to_app(curr);
                    func_decl * f = a->get_decl();
                    if (!consts.contains(f)) {
                        TRACE("sine", tout << mk_pp(f, m) << "\n";);
                        p_matched = false;
                        next_consts.push_back(f);
                        break;
                    }
                    for (unsigned j = 0; j < a->get_num_args(); j++)
                        stack.push_back(a->get_arg(j));
                }
            }

            if (p_matched) {
                matched = true;
                break;
            }
        }

        return matched;
    }

    void filter_expressions(goal_ref const & g, ptr_vector<expr> & new_exprs) {
        obj_map<func_decl, obj_hashtable<expr> > const2exp;
        obj_map<expr, obj_hashtable<func_decl> > exp2const;
        obj_map<func_decl, obj_pair_hashtable<expr, expr> > const2quantifier;
        obj_hashtable<func_decl> consts;
        vector<t_work_item> stack;
        t_work_item curr;

        for (unsigned i = 0; i < g->size(); i++)
            stack.push_back(work_item(g->form(i), g->form(i)));

        while (!stack.empty()) {
            curr = stack.back();
            stack.pop_back();
            if (is_app(curr.first) && is_uninterp(curr.first)) {
                app * a = to_app(curr.first);
                func_decl * f = a->get_decl();
                if (!consts.contains(f)) {
                    consts.insert(f);
                    if (const2quantifier.contains(f)) {
                        for (auto const& p : const2quantifier[f]) 
                            stack.push_back(p);
                        const2quantifier.remove(f);
                    }
                }
                if (!const2exp.contains(f)) {
                    const2exp.insert(f, obj_hashtable<expr>());
                }
                if (!const2exp[f].contains(curr.second)) {
                    const2exp[f].insert(curr.second);
                }
                if (!exp2const.contains(curr.second)) {
                    exp2const.insert(curr.second, obj_hashtable<func_decl>());
                }
                if (!exp2const[curr.second].contains(f)) {
                    exp2const[curr.second].insert(f);
                }

                for (unsigned i = 0; i < a->get_num_args(); i++) {
                    stack.push_back(work_item(a->get_arg(i), curr.second));
                }
            }
            else if (is_quantifier(curr.first)) {
                quantifier *q = to_quantifier(curr.first);
                if (is_forall(q)) {
                    if (q->has_patterns()) {
                        ptr_vector<func_decl> next_consts;
                        if (quantifier_matches(q, consts, next_consts)) {
                            stack.push_back(work_item(q->get_expr(), curr.second));
                        }
                        else {
                            for (unsigned i = 0; i < next_consts.size(); i++) {
                                func_decl *c = next_consts.get(i);
                                if (!const2quantifier.contains(c)) {
                                    const2quantifier.insert(c, obj_pair_hashtable<expr, expr>());
                                }
                                if (!const2quantifier[c].contains(curr)) {
                                    const2quantifier[c].insert(curr);
                                }
                            }
                        }
                    }
                    else {
                        stack.push_back(work_item(q->get_expr(), curr.second));
                    }
                }
                else if (is_exists(q)) {
                    stack.push_back(work_item(q->get_expr(), curr.second));
                }
            }
        }

        // ok, now we just need to find the connected component of the last term
        obj_hashtable<expr> visited;
        ptr_vector<expr> to_visit;
        to_visit.push_back(g->form(g->size() - 1));
        expr * visiting;

        while (!to_visit.empty()) {
            visiting = to_visit.back();
            to_visit.pop_back();
            visited.insert(visiting);
            for (func_decl* f : exp2const[visiting]) 
                for (expr* e : const2exp[f]) {
                    if (!visited.contains(e))
                        to_visit.push_back(e);
                }
        }

        for (unsigned i = 0; i < g->size(); i++) {
            if (visited.contains(g->form(i)))
                new_exprs.push_back(g->form(i));
        }
    }
};

tactic * mk_sine_tactic(ast_manager & m, params_ref const & p) {
    return alloc(sine_tactic, m, p);
}
