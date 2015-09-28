/*++
Module Name:

    theory_str.cpp

Abstract:

    String Theory Plugin

Author:

    Murphy Berzish (mtrberzi) 2015-09-03

Revision History:

--*/
#include"ast_smt2_pp.h"
#include"smt_context.h"
#include"theory_str.h"
#include"smt_model_generator.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

namespace smt {

theory_str::theory_str(ast_manager & m):
        theory(m.mk_family_id("str")),
        search_started(false),
        m_autil(m),
        m_strutil(m)
{
}

theory_str::~theory_str() {
}

void theory_str::assert_axiom(ast * a) {
    expr * e = to_expr(a);
    if (get_manager().is_true(e)) return;
    TRACE("t_str_detail", tout << "asserting " << mk_ismt2_pp(a, get_manager()) << "\n";);
    context & ctx = get_context();
    ctx.internalize(e, false);
    literal lit(ctx.get_literal(e));
    ctx.mark_as_relevant(lit);
    ctx.mk_th_axiom(get_id(), 1, &lit);
    TRACE("t_str_detail", tout << "done asserting " << mk_ismt2_pp(a, get_manager()) << "\n";);
}

bool theory_str::internalize_atom(app * atom, bool gate_ctx) {
    // TODO I have no idea if this is correct.
    TRACE("t_str", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << std::endl;);
    SASSERT(atom->get_family_id() == get_family_id());

    ast_manager & m = get_manager();
    context & ctx = get_context();

    if (ctx.b_internalized(atom))
        return true;

    unsigned num_args = atom->get_num_args();
    for (unsigned i = 0; i < num_args; i++)
        ctx.internalize(atom->get_arg(i), false);

    literal l(ctx.mk_bool_var(atom));
    ctx.set_var_theory(l.var(), get_id());

    return true;
}

bool theory_str::internalize_term(app * term) {
    // TODO I have no idea if this is correct either.
    ast_manager & m = get_manager();
    context & ctx = get_context();
    TRACE("t_str", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << std::endl;);
    SASSERT(term->get_family_id() == get_family_id());
    SASSERT(!ctx.e_internalized(term));

    unsigned num_args = term->get_num_args();
    for (unsigned i = 0; i < num_args; i++)
        ctx.internalize(term->get_arg(i), false);

    enode * e = (ctx.e_internalized(term)) ? ctx.get_enode(term) :
                                             ctx.mk_enode(term, false, false, true);

    if (is_attached_to_var(e))
        return false;

    attach_new_th_var(e);

    /*
    if (is_concat(term)) {
        instantiate_concat_axiom(e);
    }
    */

    return true;
}

app * theory_str::mk_strlen(app * e) {
    /*if (m_strutil.is_string(e)) {*/ if (false) {
        const char * strval = 0;
        m_strutil.is_string(e, &strval);
        int len = strlen(strval);
        return m_autil.mk_numeral(rational(len), true);
    } else {
        expr * args[1] = {e};
        return get_manager().mk_app(get_id(), OP_STRLEN, 0, 0, 1, args);
    }
}

bool theory_str::can_propagate() {
    return !m_basicstr_axiom_todo.empty() || !m_str_eq_todo.empty();
}

void theory_str::propagate() {
    while (can_propagate()) {
        TRACE("t_str_detail", tout << "propagating..." << std::endl;);
        for (unsigned i = 0; i < m_basicstr_axiom_todo.size(); ++i) {
            instantiate_basic_string_axioms(m_basicstr_axiom_todo[i]);
        }
        m_basicstr_axiom_todo.reset();

        for (unsigned i = 0; i < m_str_eq_todo.size(); ++i) {
            std::pair<enode*,enode*> pair = m_str_eq_todo[i];
            enode * lhs = pair.first;
            enode * rhs = pair.second;
            handle_equality(lhs->get_owner(), rhs->get_owner());
        }
        m_str_eq_todo.reset();
    }
    TRACE("t_str_detail", tout << "done propagating" << std::endl;);
}

/*
 * Instantiate an axiom of the following form:
 * Length(Concat(x, y)) = Length(x) + Length(y)
 */
// TODO this isn't used yet
void theory_str::instantiate_concat_axiom(enode * cat) {
    SASSERT(is_concat(cat));
    app * a_cat = cat->get_owner();

    context & ctx = get_context();
    ast_manager & m = get_manager();

    // build LHS
    expr_ref len_xy(m);
    // TODO re-use ASTs for length subexpressions, like in old Z3-str?
    // TODO should we use str_util for these and other expressions?
    len_xy = mk_strlen(a_cat);
    SASSERT(len_xy);

    // build RHS: start by extracting x and y from Concat(x, y)
    unsigned nArgs = a_cat->get_num_args();
    SASSERT(nArgs == 2);
    app * a_x = to_app(a_cat->get_arg(0));
    app * a_y = to_app(a_cat->get_arg(1));

    expr_ref len_x(m);
    len_x = mk_strlen(a_x);
    SASSERT(len_x);

    expr_ref len_y(m);
    len_y = mk_strlen(a_y);
    SASSERT(len_y);

    // now build len_x + len_y
    expr_ref len_x_plus_len_y(m);
    len_x_plus_len_y = m_autil.mk_add(len_x, len_y);
    SASSERT(len_x_plus_len_y);

    // finally assert equality between the two subexpressions
    app * eq = m.mk_eq(len_xy, len_x_plus_len_y);
    SASSERT(eq);
    TRACE("t_str", tout << mk_bounded_pp(eq, m) << std::endl;);
    assert_axiom(eq);
}

/*
 * Add axioms that are true for any string variable:
 * 1. Length(x) >= 0
 * 2. Length(x) == 0 <=> x == ""
 * If the term is a string constant, we can assert something stronger:
 *    Length(x) == strlen(x)
 */
void theory_str::instantiate_basic_string_axioms(enode * str) {
    // TODO keep track of which enodes we have added axioms for, so we don't add the same ones twice?

    context & ctx = get_context();
    ast_manager & m = get_manager();

    // generate a stronger axiom for constant strings
    app * a_str = str->get_owner();
    if (m_strutil.is_string(str->get_owner())) {
        expr_ref len_str(m);
        len_str = mk_strlen(a_str);
        SASSERT(len_str);

        const char * strconst = 0;
        m_strutil.is_string(str->get_owner(), & strconst);
        TRACE("t_str_detail", tout << "instantiating constant string axioms for \"" << strconst << "\"" << std::endl;);
        int l = strlen(strconst);
        expr_ref len(m_autil.mk_numeral(rational(l), true), m);

        literal lit(mk_eq(len_str, len, false));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    } else {
        // build axiom 1: Length(a_str) >= 0
        {
            // build LHS
            expr_ref len_str(m);
            len_str = mk_strlen(a_str);
            SASSERT(len_str);
            // build RHS
            expr_ref zero(m);
            zero = m_autil.mk_numeral(rational(0), true);
            SASSERT(zero);
            // build LHS >= RHS and assert
            app * lhs_ge_rhs = m_autil.mk_ge(len_str, zero);
            SASSERT(lhs_ge_rhs);
            // TODO verify that this works
            TRACE("t_str_detail", tout << "string axiom 1: " << mk_bounded_pp(lhs_ge_rhs, m) << std::endl;);
            assert_axiom(lhs_ge_rhs);
        }

        // build axiom 2: Length(a_str) == 0 <=> a_str == ""
        {
            // build LHS of iff
            expr_ref len_str(m);
            len_str = mk_strlen(a_str);
            SASSERT(len_str);
            expr_ref zero(m);
            zero = m_autil.mk_numeral(rational(0), true);
            SASSERT(zero);
            expr_ref lhs(m);
            lhs = ctx.mk_eq_atom(len_str, zero);
            SASSERT(lhs);
            // build RHS of iff
            expr_ref empty_str(m);
            empty_str = m_strutil.mk_string("");
            SASSERT(empty_str);
            expr_ref rhs(m);
            rhs = ctx.mk_eq_atom(a_str, empty_str);
            SASSERT(rhs);
            // build LHS <=> RHS and assert
            TRACE("t_str_detail", tout << "string axiom 2: " << mk_bounded_pp(lhs, m) << " <=> " << mk_bounded_pp(rhs, m) << std::endl;);
            literal l(mk_eq(lhs, rhs, true));
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), 1, &l);
        }

    }
}

/*
 * Add an axiom of the form:
 * (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
 */
void theory_str::instantiate_str_eq_length_axiom(enode * lhs, enode * rhs) {
    context & ctx = get_context();
    ast_manager & m = get_manager();

    app * a_lhs = lhs->get_owner();
    app * a_rhs = rhs->get_owner();

    // build premise: (lhs == rhs)
    expr_ref premise(ctx.mk_eq_atom(a_lhs, a_rhs), m);

    // build conclusion: ( Length(lhs) == Length(rhs) )
    expr_ref len_lhs(mk_strlen(a_lhs), m);
    SASSERT(len_lhs);
    expr_ref len_rhs(mk_strlen(a_rhs), m);
    SASSERT(len_rhs);
    expr_ref conclusion(ctx.mk_eq_atom(len_lhs, len_rhs), m);

    // build (premise -> conclusion) and assert
    expr_ref axiom(m.mk_implies(premise, conclusion), m);
    TRACE("t_str_detail", tout << "string-eq length-eq axiom: " << mk_bounded_pp(axiom, m) << std::endl;);
    assert_axiom(axiom);
}

void theory_str::attach_new_th_var(enode * n) {
    context & ctx = get_context();
    theory_var v = mk_var(n);
    ctx.attach_th_var(n, this, v);
    TRACE("t_str_detail", tout << "new theory var: " << mk_ismt2_pp(n->get_owner(), get_manager()) << " := v#" << v << std::endl;);
}

void theory_str::reset_eh() {
    TRACE("t_str", tout << "resetting" << std::endl;);
    m_basicstr_axiom_todo.reset();
    m_str_eq_todo.reset();
    pop_scope_eh(0);
}

/*
 * Check equality among equivalence class members of LHS and RHS
 * to discover an incorrect LHS == RHS.
 * For example, if we have y2 == "str3"
 * and the equivalence classes are
 * { y2, (Concat ce m2) }
 * { "str3", (Concat abc x2) }
 * then y2 can't be equal to "str3".
 * Then add an assertion: (y2 == (Concat ce m2)) AND ("str3" == (Concat abc x2)) -> (y2 != "str3")
 */
bool theory_str::new_eq_check(expr * lhs, expr * rhs) {
    // TODO this involves messing around with enodes and equivalence classes
    return true;
}

void theory_str::group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts) {
    ast_manager & m = get_manager();
    context & ctx = get_context();
    enode * nNode = ctx.get_enode(n);
    enode * eqcNode = nNode;
    do {
        app * ast = eqcNode->get_owner();
        if (is_concat(eqcNode)) {
            // TODO simplify_concat
            /*
              Z3_ast simConcat = simplifyConcat(t, eqcNode);
              if (simConcat != eqcNode) {
                if (isConcatFunc(t, simConcat)) {
                  concats.insert(simConcat);
                } else {
                  if (isConstStr(t, simConcat)) {
                    constStrs.insert(simConcat);
                  } else {
                    vars.insert(simConcat);
                  }
                }
              } else {
                concats.insert(simConcat);
              }
             */
            concats.insert(ast);
        } else if (is_string(eqcNode)) {
            consts.insert(ast);
        } else {
            vars.insert(ast);
        }
        eqcNode = eqcNode->get_next();
    } while (eqcNode != nNode);
}

void theory_str::simplify_concat_equality(expr * lhs, expr * rhs) {
    // TODO strArgmt::simplifyConcatEq()
}

/*
 * strArgmt::solve_concat_eq_str()
 * Solve concatenations of the form:
 *   const == Concat(const, X)
 *   const == Concat(X, const)
 */
void theory_str::solve_concat_eq_str(expr * concat, expr * str) {
    ast_manager & m = get_manager();
    context & ctx = get_context();

    TRACE("t_str_detail", tout << mk_ismt2_pp(concat, m) << " == " << mk_ismt2_pp(str, m) << std::endl;);

    if (is_concat(to_app(concat)) && is_string(to_app(str))) {
        const char * tmp = 0;
        m_strutil.is_string(str, & tmp);
        std::string const_str(tmp);
        app * a_concat = to_app(concat);
        SASSERT(a_concat->get_num_args() == 2);
        expr * a1 = a_concat->get_arg(0);
        expr * a2 = a_concat->get_arg(1);

        if (const_str == "") {
            TRACE("t_str", tout << "quick path: concat == \"\"" << std::endl;);
            // assert the following axiom:
            // ( (Concat a1 a2) == "" ) -> ( (a1 == "") AND (a2 == "") )
            expr_ref empty_str(m_strutil.mk_string(""), m);
            expr_ref premise(ctx.mk_eq_atom(concat, empty_str), m);
            expr_ref c1(ctx.mk_eq_atom(a1, empty_str), m);
            expr_ref c2(ctx.mk_eq_atom(a2, empty_str), m);
            expr_ref conclusion(m.mk_and(c1, c2), m);
            expr_ref axiom(m.mk_implies(premise, conclusion), m);
            TRACE("t_str_detail", tout << "learn " << mk_ismt2_pp(axiom, m) << std::endl;);
            assert_axiom(axiom);
            return;
        }
        // TODO the rest...
    }
}

void theory_str::handle_equality(expr * lhs, expr * rhs) {
    ast_manager & m = get_manager();
    context & ctx = get_context();
    // both terms must be of sort String
    sort * lhs_sort = m.get_sort(lhs);
    sort * rhs_sort = m.get_sort(rhs);
    sort * str_sort = m.mk_sort(get_family_id(), STRING_SORT);

    if (lhs_sort != str_sort || rhs_sort != str_sort) {
        TRACE("t_str_detail", tout << "skip equality: not String sort" << std::endl;);
        return;
    }

    // TODO freeVarAttempt()?

    // TODO simplify concat?

    // newEqCheck() -- check consistency wrt. existing equivalence classes
    if (!new_eq_check(lhs, rhs)) {
        return;
    }

    // BEGIN new_eq_handler() in strTheory

    // TODO there's some setup with getLenValue() that I don't think is necessary
    // because we should already be generating the string length axioms for all string terms

    instantiate_str_eq_length_axiom(ctx.get_enode(lhs), ctx.get_enode(rhs));

    // group terms by equivalence class (groupNodeInEqc())
    std::set<expr*> eqc_lhs_concat;
    std::set<expr*> eqc_lhs_var;
    std::set<expr*> eqc_lhs_const;
    group_terms_by_eqc(lhs, eqc_lhs_concat, eqc_lhs_var, eqc_lhs_const);

    TRACE("t_str_detail",
        tout << "eqc[lhs]:" << std::endl;
        tout << "Concats:" << std::endl;
        for (std::set<expr*>::iterator it = eqc_lhs_concat.begin(); it != eqc_lhs_concat.end(); ++it) {
            expr * ex = *it;
            tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
        }
        tout << "Variables:" << std::endl;
        for (std::set<expr*>::iterator it = eqc_lhs_var.begin(); it != eqc_lhs_var.end(); ++it) {
            expr * ex = *it;
            tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
        }
        tout << "Constants:" << std::endl;
        for (std::set<expr*>::iterator it = eqc_lhs_const.begin(); it != eqc_lhs_const.end(); ++it) {
            expr * ex = *it;
            tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
        }
        );

    std::set<expr*> eqc_rhs_concat;
    std::set<expr*> eqc_rhs_var;
    std::set<expr*> eqc_rhs_const;
    group_terms_by_eqc(rhs, eqc_rhs_concat, eqc_rhs_var, eqc_rhs_const);

    TRACE("t_str_detail",
        tout << "eqc[rhs]:" << std::endl;
        tout << "Concats:" << std::endl;
        for (std::set<expr*>::iterator it = eqc_rhs_concat.begin(); it != eqc_rhs_concat.end(); ++it) {
            expr * ex = *it;
            tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
        }
        tout << "Variables:" << std::endl;
        for (std::set<expr*>::iterator it = eqc_rhs_var.begin(); it != eqc_rhs_var.end(); ++it) {
            expr * ex = *it;
            tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
        }
        tout << "Constants:" << std::endl;
        for (std::set<expr*>::iterator it = eqc_rhs_const.begin(); it != eqc_rhs_const.end(); ++it) {
            expr * ex = *it;
            tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
        }
        );

    // step 1: Concat == Concat
    bool hasCommon = false;
    if (eqc_lhs_concat.size() != 0 && eqc_rhs_concat.size() != 0) {
        std::set<expr*>::iterator itor1 = eqc_lhs_concat.begin();
        std::set<expr*>::iterator itor2 = eqc_rhs_concat.begin();
        for (; itor1 != eqc_lhs_concat.end(); ++itor1) {
            if (eqc_rhs_concat.find(*itor1) != eqc_rhs_concat.end()) {
                hasCommon = true;
                break;
            }
        }
        for (; !hasCommon && itor2 != eqc_rhs_concat.end(); ++itor2) {
            if (eqc_lhs_concat.find(*itor2) != eqc_lhs_concat.end()) {
                hasCommon = true;
                break;
            }
        }
        if (!hasCommon) {
            simplify_concat_equality(*(eqc_lhs_concat.begin()), *(eqc_rhs_concat.begin()));
        }
    }

    // step 2: Concat == Constant
    if (eqc_lhs_const.size() != 0) {
        expr * conStr = *(eqc_lhs_const.begin());
        std::set<expr*>::iterator itor2 = eqc_rhs_concat.begin();
        for (; itor2 != eqc_rhs_concat.end(); ++itor2) {
            solve_concat_eq_str(*itor2, conStr);
        }
    } else if (eqc_rhs_const.size() != 0) {
        expr * conStr = *(eqc_rhs_const.begin());
        std::set<expr*>::iterator itor1 = eqc_lhs_concat.begin();
        for (; itor1 != eqc_lhs_concat.end(); ++itor1) {
            solve_concat_eq_str(*itor1, conStr);
        }
    }

    // TODO regex unroll? (much later)
}

void theory_str::set_up_axioms(expr * ex) {
    // TODO check to make sure we don't set up axioms on the same term twice
    TRACE("t_str_detail", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) << std::endl;);

    ast_manager & m = get_manager();
    context & ctx = get_context();

    sort * ex_sort = m.get_sort(ex);
    sort * str_sort = m.mk_sort(get_family_id(), STRING_SORT);

    if (ex_sort == str_sort) {
        TRACE("t_str_detail", tout << "expr is of sort String" << std::endl;);
        // set up basic string axioms
        enode * n = ctx.get_enode(ex);
        SASSERT(n);
        m_basicstr_axiom_todo.push_back(n);
    } else {
        TRACE("t_str_detail", tout << "expr is of wrong sort, ignoring" << std::endl;);
    }

    // if expr is an application, recursively inspect all arguments
    if (is_app(ex)) {
        app * term = (app*)ex;
        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            set_up_axioms(term->get_arg(i));
        }
    }
}

void theory_str::init_search_eh() {
    ast_manager & m = get_manager();
    context & ctx = get_context();

    TRACE("t_str_detail",
        tout << "dumping all asserted formulas:" << std::endl;
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr * ex = ctx.get_asserted_formula(i);
            tout << mk_ismt2_pp(ex, m) << std::endl;
        }
    );
    /*
     * Recursive descent through all asserted formulas to set up axioms.
     * Note that this is just the input structure and not necessarily things
     * that we know to be true or false. We're just doing this to see
     * which terms are explicitly mentioned.
     */
    unsigned nFormulas = ctx.get_num_asserted_formulas();
    for (unsigned i = 0; i < nFormulas; ++i) {
        expr * ex = ctx.get_asserted_formula(i);
        set_up_axioms(ex);
    }

    /*
     * Similar recursive descent, except over all initially assigned terms.
     * This is done to find equalities between terms, etc. that we otherwise
     * wouldn't get a chance to see.
     */
    expr_ref_vector assignments(m);
    ctx.get_assignments(assignments);
    for (expr_ref_vector::iterator i = assignments.begin(); i != assignments.end(); ++i) {
        expr * ex = *i;
        TRACE("t_str_detail", tout << "processing assignment " << mk_ismt2_pp(ex, m) << std::endl;);
        if (m.is_eq(ex)) {
            TRACE("t_str_detail", tout << "expr is equality" << std::endl;);
            app * eq = (app*)ex;
            SASSERT(eq->get_num_args() == 2);
            expr * lhs = eq->get_arg(0);
            expr * rhs = eq->get_arg(1);

            enode * e_lhs = ctx.get_enode(lhs);
            enode * e_rhs = ctx.get_enode(rhs);
            std::pair<enode*,enode*> eq_pair(e_lhs, e_rhs);
            m_str_eq_todo.push_back(eq_pair);
        } else {
            TRACE("t_str_detail", tout << "expr ignored" << std::endl;);
        }
    }

    TRACE("t_str", tout << "search started" << std::endl;);
    search_started = true;
}

void theory_str::new_eq_eh(theory_var x, theory_var y) {
    TRACE("t_str", tout << "new eq: v#" << x << " = v#" << y << std::endl;);
    TRACE("t_str_detail", tout << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    handle_equality(get_enode(x)->get_owner(), get_enode(y)->get_owner());
}

void theory_str::new_diseq_eh(theory_var x, theory_var y) {
    TRACE("t_str", tout << "new diseq: v#" << x << " != v#" << y << std::endl;);
    TRACE("t_str_detail", tout << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " != " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
}

void theory_str::relevant_eh(app * n) {
    TRACE("t_str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << "\n";);
}

void theory_str::assign_eh(bool_var v, bool is_true) {
    context & ctx = get_context();
    TRACE("t_str", tout << "assert: v" << v << " #" << ctx.bool_var2expr(v)->get_id() << " is_true: " << is_true << std::endl;);
}

void theory_str::push_scope_eh() {
    TRACE("t_str", tout << "push" << std::endl;);
}

final_check_status theory_str::final_check_eh() {
    ast_manager & m = get_manager();
    context & ctx = get_context();
    // TODO
    TRACE("t_str", tout << "final check" << std::endl;);

    TRACE("t_str_detail",
        tout << "dumping all assignments:" << std::endl;
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        for (expr_ref_vector::iterator i = assignments.begin(); i != assignments.end(); ++i) {
            expr * ex = *i;
            tout << mk_ismt2_pp(ex, m) << std::endl;
        }
    );

    return FC_DONE;
}

void theory_str::init_model(model_generator & mg) {
    TRACE("t_str", tout << "initializing model" << std::endl; display(tout););
    m_factory = alloc(str_value_factory, get_manager(), get_family_id());
    mg.register_factory(m_factory);
}

model_value_proc * theory_str::mk_value(enode * n, model_generator & mg) {
    TRACE("t_str", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) <<
                                " (sort " << mk_ismt2_pp(get_manager().get_sort(n->get_owner()), get_manager()) << ")\n";);
    ast_manager & m = get_manager();
    context & ctx = get_context();
    app_ref owner(m);
    owner = n->get_owner();

    // If the owner is not internalized, it doesn't have an enode associated.
    SASSERT(ctx.e_internalized(owner));

    if (m_strutil.is_string(owner)) {
        return alloc(expr_wrapper_proc, owner);
    }
    NOT_IMPLEMENTED_YET(); // TODO
}

void theory_str::finalize_model(model_generator & mg) {}

}; /* namespace smt */
