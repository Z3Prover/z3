/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_antiunify.cpp

Abstract:

  Antiunification utilities

Author:

    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#include"muz/spacer/spacer_antiunify.h"
#include"ast/ast.h"
#include"ast/rewriter/rewriter.h"
#include"ast/rewriter/rewriter_def.h"
#include"ast/arith_decl_plugin.h"
#include"ast/ast_util.h"
#include"ast/expr_abstract.h"

namespace spacer {

// Abstracts numeric values by variables
struct var_abs_rewriter : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_util;
    ast_mark m_seen;
    ast_mark m_has_num;
    unsigned m_var_index;
    expr_ref_vector m_pinned;
    obj_map<expr, expr*>& m_substitution;
    ptr_vector<expr> m_stack;

    var_abs_rewriter (ast_manager &manager, obj_map<expr, expr*>& substitution,
                      unsigned k = 0) :
        m(manager), m_util(m), m_var_index(k),
        m_pinned(m), m_substitution(substitution) {}

    void reset(unsigned k = 0) {
        m_pinned.reset();
        m_var_index = k;
    }

    bool pre_visit(expr * t) {
        bool r = (!m_seen.is_marked(t) || m_has_num.is_marked(t));
        // only unify if convex closure will not contain non-linear multiplication
        if (m_util.is_mul(t))
        {
            bool contains_const_child = false;
            app* a = to_app(t);
            for (unsigned i=0, sz = a->get_num_args(); i < sz; ++i) {
                if (m_util.is_numeral(a->get_arg(i))) {
                    contains_const_child = true;
                }
            }
            if (!contains_const_child) {r = false;}
        }
        if (r) {m_stack.push_back (t);}
        return r;
    }


    br_status reduce_app (func_decl * f, unsigned num, expr * const * args,
                          expr_ref & result, proof_ref & result_pr) {
        expr *s;
        s = m_stack.back();
        m_stack.pop_back();
        if (is_app(s)) {
            app *a = to_app(s);
            for (unsigned i=0, sz = a->get_num_args(); i < sz; ++i) {
                if (m_has_num.is_marked(a->get_arg(i))) {
                    m_has_num.mark(a,true);
                    return BR_FAILED;
                }
            }
        }
        return BR_FAILED;
    }

    bool cache_all_results() const { return false; }
    bool cache_results() const { return false; }

    bool get_subst(expr * s, expr * & t, proof * & t_pr) {
        if (m_util.is_numeral(s)) {
            t = m.mk_var(m_var_index++, m.get_sort(s));
            m_substitution.insert(t, s);
            m_pinned.push_back(t);
            m_has_num.mark(s, true);
            m_seen.mark(t, true);
            return true;
        }
        return false;
    }

};

/*
* construct m_g, which is a generalization of t, where every constant
* is replaced by a variable for any variable in m_g, remember the
* substitution to get back t and save it in m_substitutions
*/
anti_unifier::anti_unifier(expr* t, ast_manager& man) : m(man), m_pinned(m), m_g(m)
{
    m_pinned.push_back(t);

    obj_map<expr, expr*> substitution;

    var_abs_rewriter var_abs_cfg(m, substitution);
    rewriter_tpl<var_abs_rewriter> var_abs_rw (m, false, var_abs_cfg);
    var_abs_rw (t, m_g);

    m_substitutions.push_back(substitution); //TODO: refactor into vector, remove k
}

/* traverses m_g and t in parallel. if they only differ in constants
 * (i.e. m_g contains a variable, where t contains a constant), then
 * add the substitutions, which need to be applied to m_g to get t, to
 * m_substitutions.
*/
bool anti_unifier::add_term(expr* t) {
    m_pinned.push_back(t);

    ptr_vector<expr> todo;
    ptr_vector<expr> todo2;
    todo.push_back(m_g);
    todo2.push_back(t);

    ast_mark visited;

    arith_util util(m);

    obj_map<expr, expr*> substitution;

    while (!todo.empty()) {
        expr* current = todo.back();
        todo.pop_back();
        expr* current2 = todo2.back();
        todo2.pop_back();

        if (!visited.is_marked(current)) {
            visited.mark(current, true);

            if (is_var(current)) {
                // TODO: for now we don't allow variables in the terms we want to antiunify
                SASSERT(m_substitutions[0].contains(current));
                if (util.is_numeral(current2)) {
                    substitution.insert(current, current2);
                }
                else {return false;}
            }
            else {
                SASSERT(is_app(current));

                if (is_app(current2) &&
                    to_app(current)->get_decl() == to_app(current2)->get_decl() &&
                    to_app(current)->get_num_args() == to_app(current2)->get_num_args()) {
                    // TODO: what to do for numerals here? E.g. if we
                    // have 1 and 2, do they have the same decl or are
                    // the decls already different?
                    SASSERT (!util.is_numeral(current) || current == current2);
                    for (unsigned i = 0, num_args = to_app(current)->get_num_args();
                         i < num_args; ++i) {
                        todo.push_back(to_app(current)->get_arg(i));
                        todo2.push_back(to_app(current2)->get_arg(i));
                    }
                }
                else {
                    return false;
                }
            }
        }
    }

    // we now know that the terms can be anti-unified, so add the cached substitution
    m_substitutions.push_back(substitution);
    return true;
}

/*
* returns m_g, where additionally any variable, which has only equal
* substitutions, is substituted with that substitution
*/
void anti_unifier::finalize() {
    ptr_vector<expr> todo;
    todo.push_back(m_g);

    ast_mark visited;

    obj_map<expr, expr*> generalization;

    arith_util util(m);

    // post-order traversel which ignores constants and handles them
    // directly when the enclosing term of the constant is handled
    while (!todo.empty()) {
        expr* current = todo.back();
        SASSERT(is_app(current));

        // if we haven't already visited current
        if (!visited.is_marked(current)) {
            bool existsUnvisitedParent = false;

            for (unsigned i = 0, sz = to_app(current)->get_num_args(); i < sz; ++i) {
                expr* argument = to_app(current)->get_arg(i);

                if (!is_var(argument)) {
                    SASSERT(is_app(argument));
                    // if we haven't visited the current parent yet
                    if(!visited.is_marked(argument)) {
                        // add it to the stack
                        todo.push_back(argument);
                        existsUnvisitedParent = true;
                    }
                }
            }

            // if we already visited all parents, we can visit current too
            if (!existsUnvisitedParent) {
                visited.mark(current, true);
                todo.pop_back();

                ptr_buffer<expr> arg_list;
                for (unsigned i = 0, num_args = to_app(current)->get_num_args();
                     i < num_args; ++i) {
                    expr* argument = to_app(current)->get_arg(i);

                    if (is_var(argument)) {
                        // compute whether there are different
                        // substitutions for argument
                        bool containsDifferentSubstitutions = false;

                        for (unsigned i=0, sz = m_substitutions.size(); i+1 < sz; ++i) {
                            SASSERT(m_substitutions[i].contains(argument));
                            SASSERT(m_substitutions[i+1].contains(argument));

                            // TODO: how to check equality?
                            if (m_substitutions[i][argument] !=
                                m_substitutions[i+1][argument])
                            {
                                containsDifferentSubstitutions = true;
                                break;
                            }
                        }

                        // if yes, use the variable
                        if (containsDifferentSubstitutions) {
                            arg_list.push_back(argument);
                        }
                        // otherwise use the concrete value instead
                        // and remove the substitutions
                        else
                        {
                            arg_list.push_back(m_substitutions[0][argument]);

                            for (unsigned i=0, sz = m_substitutions.size(); i < sz; ++i) {
                                SASSERT(m_substitutions[i].contains(argument));
                                m_substitutions[i].remove(argument);
                            }
                        }
                    }
                    else {
                        SASSERT(generalization.contains(argument));
                        arg_list.push_back(generalization[argument]);
                    }
                }

                SASSERT(to_app(current)->get_num_args() == arg_list.size());
                expr_ref application(m.mk_app(to_app(current)->get_decl(),
                                              to_app(current)->get_num_args(),
                                              arg_list.c_ptr()), m);
                m_pinned.push_back(application);
                generalization.insert(current, application);
            }
        }
        else {
            todo.pop_back();
        }
    }

    m_g = generalization[m_g];
}


class ncc_less_than_key
{
public:
    ncc_less_than_key(arith_util& util) : m_util(util) {}

    bool operator() (const expr*& e1, const expr*& e2) {
        rational val1;
        rational val2;

        if (m_util.is_numeral(e1, val1) && m_util.is_numeral(e2, val2))
        {
            return val1 < val2;
        }
        else
        {
            SASSERT(false);
            return false;
        }
    }
    arith_util m_util;
};

/*
 * if there is a single interval which exactly captures each of the
 * substitutions, return the corresponding closure, otherwise do
 * nothing
 */
bool naive_convex_closure::compute_closure(anti_unifier& au, ast_manager& m,
                                           expr_ref& result) {
    arith_util util(m);

    SASSERT(au.get_num_substitutions() > 0);
    if (au.get_substitution(0).size() == 0) {
        result = au.get_generalization();
        return true;
    }

    // check that all substitutions have the same size
    for (unsigned i=0, sz = au.get_num_substitutions(); i+1 < sz; ++i) {
        if (au.get_substitution(i).size() != au.get_substitution(i+1).size()) {
            return false;
        }
    }

    // for each substitution entry
    bool is_first_key = true;
    unsigned lower_bound = 0;
    unsigned upper_bound = 0;
    for (const auto& pair : au.get_substitution(0)) {
        // construct vector
        expr* key = &pair.get_key();
        vector<unsigned> entries;

        rational val;
        for (unsigned i=0, sz = au.get_num_substitutions(); i < sz; ++i)
        {
            if (util.is_numeral(au.get_substitution(i)[key], val) &&
                val.is_unsigned()) {
                entries.push_back(val.get_unsigned());
            }
            else {
                return false;
            }
        }

        // check whether vector represents interval
        unsigned current_lower_bound = 0;
        unsigned current_upper_bound = 0;

        // if vector represents interval
        if (get_range(entries, current_lower_bound, current_upper_bound)) {
            // if interval is the same as previous interval
            if (is_first_key) {
                is_first_key = false;
                lower_bound = current_lower_bound;
                upper_bound = current_upper_bound;
            }
            else {
                if (current_lower_bound != lower_bound ||
                    current_upper_bound != upper_bound) {
                    return false;
                }
            }
        }
        // otherwise we don't do a convex closure
        else {
            return false;
        }
    }

    // we finally know that we can express the substitutions using a
    // single interval, so build the expression 1. construct const
    expr_ref const_ref(m.mk_const(symbol("scti!0"), util.mk_int()), m);

    // 2. construct body with const
    expr_ref lit1(util.mk_le(util.mk_int(lower_bound), const_ref), m);
    expr_ref lit2(util.mk_le(const_ref, util.mk_int(upper_bound)), m);
    expr_ref lit3(m);
    substitute_vars_by_const(m, au.get_generalization(), const_ref, lit3);

    expr_ref_vector args(m);
    args.push_back(lit1);
    args.push_back(lit2);
    args.push_back(lit3);
    expr_ref body_with_consts = mk_and(args);

    // 3. replace const by var
    ptr_vector<expr> vars;
    vars.push_back(const_ref);

    expr_ref body(m);
    expr_abstract(m, 0, vars.size(), (expr*const*)vars.c_ptr(), body_with_consts, body);

    // 4. introduce quantifier
    ptr_vector<sort> sorts;
    sorts.push_back(util.mk_int());
    svector<symbol> names;
    names.push_back(symbol("scti!0"));

    result = expr_ref(m.mk_exists(vars.size(), sorts.c_ptr(), names.c_ptr(), body),m);

    return true;
}

bool naive_convex_closure::get_range(vector<unsigned int>& v,
                                     unsigned int& lower_bound, unsigned int& upper_bound)
{
    // sort substitutions
    std::sort(v.begin(), v.end());

    // check that numbers are consecutive
    for (unsigned i=0; i+1 < v.size(); ++i) {
        if (v[i] + 1 != v[i+1]) {
            return false;
        }
    }

    SASSERT(v.size() > 0);
    lower_bound = v[0];
    upper_bound = v.back();

    return true;
}

struct subs_rewriter_cfg : public default_rewriter_cfg {
    ast_manager &m;
    expr_ref m_c;

    subs_rewriter_cfg (ast_manager &manager, expr* c) : m(manager), m_c(c, m) {}

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
        result = m_c;
        result_pr = nullptr;
        return true;
    }
};

void naive_convex_closure::substitute_vars_by_const(ast_manager& m, expr* t,
                                                    expr* c, expr_ref& res) {
    subs_rewriter_cfg subs_cfg(m, c);
    rewriter_tpl<subs_rewriter_cfg> subs_rw (m, false, subs_cfg);
    subs_rw (t, res);
}

}

template class rewriter_tpl<spacer::var_abs_rewriter>;
template class rewriter_tpl<spacer::subs_rewriter_cfg>;
