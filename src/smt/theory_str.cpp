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
        m_strutil(m),
        tmpStringVarCount(0),
		tmpXorVarCount(0),
		avoidLoopCut(true),
		loopDetected(false)
{
}

theory_str::~theory_str() {
}

void theory_str::assert_axiom(expr * e) {
    if (get_manager().is_true(e)) return;
    TRACE("t_str_detail", tout << "asserting " << mk_ismt2_pp(e, get_manager()) << std::endl;);
    context & ctx = get_context();
    if (!ctx.b_internalized(e)) {
        ctx.internalize(e, true);
    }
    literal lit(ctx.get_literal(e));
    ctx.mark_as_relevant(lit);
    ctx.mk_th_axiom(get_id(), 1, &lit);
    TRACE("t_str_detail", tout << "done asserting " << mk_ismt2_pp(e, get_manager()) << std::endl;);
}

void theory_str::assert_implication(expr * premise, expr * conclusion) {
    ast_manager & m = get_manager();
    TRACE("t_str_detail", tout << "asserting implication " << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
    expr_ref axiom(m.mk_or(m.mk_not(premise), conclusion), m);
    assert_axiom(axiom);
}

bool theory_str::internalize_atom(app * atom, bool gate_ctx) {
    TRACE("t_str", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << std::endl;);
    SASSERT(atom->get_family_id() == get_family_id());

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

static void cut_vars_map_copy(std::map<expr*, int> & dest, std::map<expr*, int> & src) {
    std::map<expr*, int>::iterator itor = src.begin();
    for (; itor != src.end(); itor++) {
        dest[itor->first] = 1;
    }
}

/*
bool hasSelfCut(Z3_ast n1, Z3_ast n2) {
  if (cut_VARMap.find(n1) == cut_VARMap.end())
    return false;

  if (cut_VARMap.find(n2) == cut_VARMap.end())
    return false;

  if (cut_VARMap[n1].empty() || cut_VARMap[n2].empty())
    return false;

  std::map<Z3_ast, int>::iterator itor = cut_VARMap[n1].top()->vars.begin();
  for (; itor != cut_VARMap[n1].top()->vars.end(); itor++) {
    if (cut_VARMap[n2].top()->vars.find(itor->first) != cut_VARMap[n2].top()->vars.end())
      return true;
  }
  return false;
}
*/

bool theory_str::has_self_cut(expr * n1, expr * n2) {
    if (cut_var_map.find(n1) == cut_var_map.end()) {
        return false;
    }
    if (cut_var_map.find(n2) == cut_var_map.end()) {
        return false;
    }
    if (cut_var_map[n1].empty() || cut_var_map[n2].empty()) {
        return false;
    }

    std::map<expr*, int>::iterator itor = cut_var_map[n1].top()->vars.begin();
    for (; itor != cut_var_map[n1].top()->vars.end(); ++itor) {
        if (cut_var_map[n2].top()->vars.find(itor->first) != cut_var_map[n2].top()->vars.end()) {
            return true;
        }
    }
    return false;
}

void theory_str::add_cut_info_one_node(expr * baseNode, int slevel, expr * node) {
    if (cut_var_map.find(baseNode) == cut_var_map.end()) {
        T_cut * varInfo = alloc(T_cut);
        varInfo->level = slevel;
        varInfo->vars[node] = 1;
        cut_var_map[baseNode].push(varInfo);
    } else {
        if (cut_var_map[baseNode].empty()) {
            T_cut * varInfo = alloc(T_cut);
            varInfo->level = slevel;
            varInfo->vars[node] = 1;
            cut_var_map[baseNode].push(varInfo);
        } else {
            if (cut_var_map[baseNode].top()->level < slevel) {
                T_cut * varInfo = alloc(T_cut);
                varInfo->level = slevel;
                cut_vars_map_copy(varInfo->vars, cut_var_map[baseNode].top()->vars);
                varInfo->vars[node] = 1;
                cut_var_map[baseNode].push(varInfo);
            } else if (cut_var_map[baseNode].top()->level == slevel) {
                cut_var_map[baseNode].top()->vars[node] = 1;
            } else {
                get_manager().raise_exception("entered illegal state during add_cut_info_one_node()");
            }
        }
    }
}

void theory_str::add_cut_info_merge(expr * destNode, int slevel, expr * srcNode) {
    if (cut_var_map.find(srcNode) == cut_var_map.end()) {
        get_manager().raise_exception("illegal state in add_cut_info_merge(): cut_var_map doesn't contain srcNode");
    }

    if (cut_var_map[srcNode].empty()) {
        get_manager().raise_exception("illegal state in add_cut_info_merge(): cut_var_map[srcNode] is empty");
    }

    if (cut_var_map.find(destNode) == cut_var_map.end()) {
        T_cut * varInfo = alloc(T_cut);
        varInfo->level = slevel;
        cut_vars_map_copy(varInfo->vars, cut_var_map[srcNode].top()->vars);
        cut_var_map[destNode].push(varInfo);
    } else {
        if (cut_var_map[destNode].empty() || cut_var_map[destNode].top()->level < slevel) {
            T_cut * varInfo = alloc(T_cut);
            varInfo->level = slevel;
            cut_vars_map_copy(varInfo->vars, cut_var_map[destNode].top()->vars);
            cut_vars_map_copy(varInfo->vars, cut_var_map[srcNode].top()->vars);
            cut_var_map[destNode].push(varInfo);
        } else if (cut_var_map[destNode].top()->level == slevel) {
            cut_vars_map_copy(cut_var_map[destNode].top()->vars, cut_var_map[srcNode].top()->vars);
        } else {
            get_manager().raise_exception("illegal state in add_cut_info_merge(): inconsistent slevels");
        }
    }
}

void theory_str::check_and_init_cut_var(expr * node) {
    if (cut_var_map.find(node) != cut_var_map.end()) {
        return;
    } else if (!m_strutil.is_string(node)) {
        add_cut_info_one_node(node, -1, node);
    }
}

app * theory_str::mk_int(int n) {
    return m_autil.mk_numeral(rational(n), true);
}

app * theory_str::mk_internal_xor_var() {
	context & ctx = get_context();
	ast_manager & m = get_manager();
	std::stringstream ss;
	ss << tmpXorVarCount;
	tmpXorVarCount++;
	std::string name = "$$_xor_" + ss.str();
	// Z3_sort r = of_sort(mk_c(c)->m().mk_sort(mk_c(c)->get_arith_fid(), INT_SORT));
	sort * int_sort = m.mk_sort(m_autil.get_family_id(), INT_SORT);
	char * new_buffer = alloc_svect(char, name.length() + 1);
    strcpy(new_buffer, name.c_str());
	symbol sym(new_buffer);

	app* a = m.mk_const(m.mk_const_decl(sym, int_sort));
	// TODO ctx.save_ast_trail(a)?
	return a;
}

/*
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);
  std::stringstream ss;
  ss << tmpStringVarCount;
  tmpStringVarCount++;
  std::string name = "$$_str" + ss.str();
  Z3_ast varAst = mk_var(ctx, name.c_str(), td->String);
  nonEmptyStrVarAxiom(t, varAst, __LINE__);
  return varAst;
*/

app * theory_str::mk_nonempty_str_var() {
    context & ctx = get_context();
    ast_manager & m = get_manager();
    std::stringstream ss;
    ss << tmpStringVarCount;
    tmpStringVarCount++;
    std::string name = "$$_str" + ss.str();
    sort * string_sort = m.mk_sort(m_strutil.get_family_id(), STRING_SORT);
    char * new_buffer = alloc_svect(char, name.length() + 1);
    strcpy(new_buffer, name.c_str());
    symbol sym(new_buffer);

    app* a = m.mk_const(m.mk_const_decl(sym, string_sort));
    // assert a variation of the basic string axioms that ensures this string is nonempty
    {
        // build LHS
        expr_ref len_str(m);
        len_str = mk_strlen(a);
        SASSERT(len_str);
        // build RHS
        expr_ref zero(m);
        zero = m_autil.mk_numeral(rational(0), true);
        SASSERT(zero);
        // build LHS > RHS and assert
        app * lhs_gt_rhs = m_autil.mk_gt(len_str, zero);
        SASSERT(lhs_gt_rhs);
        assert_axiom(lhs_gt_rhs);
    }
    return a;
}

app * theory_str::mk_strlen(expr * e) {
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

/*
 * Returns the simplified concatenation of two expressions,
 * where either both expressions are constant strings
 * or one expression is the empty string.
 * If this precondition does not hold, the function returns NULL.
 * (note: this function was strTheory::Concat())
 */
expr * theory_str::mk_concat_const_str(expr * n1, expr * n2) {
    bool n1HasEqcValue = false;
    bool n2HasEqcValue = false;
    expr * v1 = get_eqc_value(n1, n1HasEqcValue);
    expr * v2 = get_eqc_value(n2, n2HasEqcValue);
    if (n1HasEqcValue && n2HasEqcValue) {
        const char * n1_str_tmp;
        m_strutil.is_string(v1, & n1_str_tmp);
        std::string n1_str(n1_str_tmp);
        const char * n2_str_tmp;
        m_strutil.is_string(v2, & n2_str_tmp);
        std::string n2_str(n2_str_tmp);
        std::string result = n1_str + n2_str;
        return m_strutil.mk_string(result);
    } else if (n1HasEqcValue && !n2HasEqcValue) {
        const char * n1_str_tmp;
        m_strutil.is_string(v1, & n1_str_tmp);
        if (strcmp(n1_str_tmp, "") == 0) {
            return n2;
        }
    } else if (!n1HasEqcValue && n2HasEqcValue) {
        const char * n2_str_tmp;
        m_strutil.is_string(v2, & n2_str_tmp);
        if (strcmp(n2_str_tmp, "") == 0) {
            return n1;
        }
    }
    return NULL;
}

expr * theory_str::mk_concat(expr * n1, expr * n2) {
	ast_manager & m = get_manager();
	if (n1 == NULL || n2 == NULL) {
		m.raise_exception("strings to be concatenated cannot be NULL");
	}
	bool n1HasEqcValue = false;
	bool n2HasEqcValue = false;
	n1 = get_eqc_value(n1, n1HasEqcValue);
	n2 = get_eqc_value(n2, n2HasEqcValue);
	if (n1HasEqcValue && n2HasEqcValue) {
	    return mk_concat_const_str(n1, n2);
	} else {
        // TODO there's a *TON* of missing code here from strTheory::mk_concat()
        // if all else fails, just build the application AST
        expr * args[2] = {n1, n2};
        return get_manager().mk_app(get_id(), OP_STRCAT, 0, 0, 2, args);
	}
}

bool theory_str::can_propagate() {
    return !m_basicstr_axiom_todo.empty() || !m_str_eq_todo.empty() || !m_concat_axiom_todo.empty();
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

        for (unsigned i = 0; i < m_concat_axiom_todo.empty(); ++i) {
            instantiate_concat_axiom(m_concat_axiom_todo[i]);
        }
        m_concat_axiom_todo.reset();
    }
}

/*
 * Instantiate an axiom of the following form:
 * Length(Concat(x, y)) = Length(x) + Length(y)
 */
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
    TRACE("t_str", tout << mk_ismt2_pp(eq, m) << std::endl;);
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
            TRACE("t_str_detail", tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);
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
            TRACE("t_str_detail", tout << "string axiom 2: " << mk_ismt2_pp(lhs, m) << " <=> " << mk_ismt2_pp(rhs, m) << std::endl;);
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

    TRACE("t_str_detail", tout << "string-eq length-eq axiom: "
            << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
    assert_implication(premise, conclusion);
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
    m_concat_axiom_todo.reset();
    pop_scope_eh(get_context().get_scope_level());
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

void theory_str::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
    app * a_node = to_app(node);
    if (!is_concat(a_node)) {
        nodeList.push_back(node);
        return;
    } else {
        SASSERT(a_node->get_num_args() == 2);
        expr * leftArg = a_node->get_arg(0);
        expr * rightArg = a_node->get_arg(1);
        get_nodes_in_concat(leftArg, nodeList);
        get_nodes_in_concat(rightArg, nodeList);
    }
}

/*
 * The inputs:
 *    ~ nn: non const node
 *    ~ eq_str: the equivalent constant string of nn
 *  Iterate the parent of all eqc nodes of nn, looking for:
 *    ~ concat node
 *  to see whether some concat nodes can be simplified.
 */

void theory_str::simplify_parent(expr * nn, expr * eq_str) {
    // TODO strTheory::simplifyParent()
}

expr * theory_str::simplify_concat(expr * node) {
    ast_manager & m = get_manager();
    context & ctx = get_context();
    std::map<expr*, expr*> resolvedMap;
    ptr_vector<expr> argVec;
    get_nodes_in_concat(node, argVec);

    for (unsigned i = 0; i < argVec.size(); ++i) {
        bool vArgHasEqcValue = false;
        expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
        if (vArg != argVec[i]) {
            resolvedMap[argVec[i]] = vArg;
        }
    }

    if (resolvedMap.size() == 0) {
        // no simplification possible
        return node;
    } else {
        expr * resultAst = m_strutil.mk_string("");
        for (unsigned i = 0; i < argVec.size(); ++i) {
            bool vArgHasEqcValue = false;
            expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
            resultAst = mk_concat(resultAst, vArg);
        }
        TRACE("t_str_detail", tout << mk_ismt2_pp(node, m) << " is simplified to " << mk_ismt2_pp(resultAst, m) << std::endl;);

        if (in_same_eqc(node, resultAst)) {
            TRACE("t_str_detail", tout << "SKIP: both concats are already in the same equivalence class" << std::endl;);
        } else {
            expr ** items = alloc_svect(expr*, resolvedMap.size());
            int pos = 0;
            std::map<expr*, expr*>::iterator itor = resolvedMap.begin();
            for (; itor != resolvedMap.end(); ++itor) {
                items[pos++] = ctx.mk_eq_atom(itor->first, itor->second);
            }
            expr_ref premise(m);
            if (pos == 1) {
                premise = items[0];
            } else {
                premise = m.mk_and(pos, items);
            }
            expr_ref conclusion(ctx.mk_eq_atom(node, resultAst), m);
            assert_implication(premise, conclusion);
        }
        return resultAst;
    }

}

/*
 * Handle two equivalent Concats.
 */
void theory_str::simplify_concat_equality(expr * nn1, expr * nn2) {
    ast_manager & m = get_manager();
    context & ctx = get_context();

    app * a_nn1 = to_app(nn1);
    SASSERT(a_nn1->get_num_args() == 2);
    app * a_nn2 = to_app(nn2);
    SASSERT(a_nn2->get_num_args() == 2);

    expr * a1_arg0 = a_nn1->get_arg(0);
    expr * a1_arg1 = a_nn1->get_arg(1);
    expr * a2_arg0 = a_nn2->get_arg(0);
    expr * a2_arg1 = a_nn2->get_arg(1);

    // TODO
    /*
      int a1_arg0_len = getLenValue(t, a1_arg0);
      int a1_arg1_len = getLenValue(t, a1_arg1);
      int a2_arg0_len = getLenValue(t, a2_arg0);
      int a2_arg1_len = getLenValue(t, a2_arg1);
     */
    int a1_arg0_len = -1;
    int a1_arg1_len = -1;
    int a2_arg0_len = -1;
    int a2_arg1_len = -1;

    TRACE("t_str", tout << "nn1 = " << mk_ismt2_pp(nn1, m) << std::endl
            << "nn2 = " << mk_ismt2_pp(nn2, m) << std::endl;);

    // TODO inferLenConcatEq(nn1, nn2);

    if (a1_arg0 == a2_arg0) {
        if (!in_same_eqc(a1_arg1, a2_arg1)) {
            expr_ref premise(ctx.mk_eq_atom(nn1, nn2), m);
            expr_ref eq1(ctx.mk_eq_atom(a1_arg1, a2_arg1), m);
            expr_ref eq2(ctx.mk_eq_atom(mk_strlen(a1_arg1), mk_strlen(a2_arg1)), m);
            expr_ref conclusion(m.mk_and(eq1, eq2), m);
            assert_implication(premise, conclusion);
        }
        TRACE("t_str_detail", tout << "SKIP: a1_arg0 == a2_arg0" << std::endl;);
        return;
    }

    if (a1_arg1 == a2_arg1) {
        if (!in_same_eqc(a1_arg0, a2_arg0)) {
            expr_ref premise(ctx.mk_eq_atom(nn1, nn2), m);
            expr_ref eq1(ctx.mk_eq_atom(a1_arg0, a2_arg0), m);
            expr_ref eq2(ctx.mk_eq_atom(mk_strlen(a1_arg0), mk_strlen(a2_arg0)), m);
            expr_ref conclusion(m.mk_and(eq1, eq2), m);
            assert_implication(premise, conclusion);
        }
        TRACE("t_str_detail", tout << "SKIP: a1_arg1 == a2_arg1" << std::endl;);
        return;
    }

    // quick path

    if (in_same_eqc(a1_arg0, a2_arg0)) {
        if (in_same_eqc(a1_arg1, a2_arg1)) {
            TRACE("t_str_detail", tout << "SKIP: a1_arg0 =~ a2_arg0 and a1_arg1 =~ a2_arg1" << std::endl;);
            return;
        } else {
            TRACE("t_str_detail", tout << "quick path 1-1: a1_arg0 =~ a2_arg0" << std::endl;);
            expr_ref premise(m.mk_and(ctx.mk_eq_atom(nn1, nn2), ctx.mk_eq_atom(a1_arg0, a2_arg0)), m);
            expr_ref conclusion(m.mk_and(ctx.mk_eq_atom(a1_arg1, a2_arg1), ctx.mk_eq_atom(mk_strlen(a1_arg1), mk_strlen(a2_arg1))), m);
            assert_implication(premise, conclusion);
            return;
        }
    } else {
        if (in_same_eqc(a1_arg1, a2_arg1)) {
            TRACE("t_str_detail", tout << "quick path 1-2: a1_arg1 =~ a2_arg1" << std::endl;);
            expr_ref premise(m.mk_and(ctx.mk_eq_atom(nn1, nn2), ctx.mk_eq_atom(a1_arg1, a2_arg1)), m);
            expr_ref conclusion(m.mk_and(ctx.mk_eq_atom(a1_arg0, a2_arg0), ctx.mk_eq_atom(mk_strlen(a1_arg0), mk_strlen(a2_arg0))), m);
            assert_implication(premise, conclusion);
            return;
        }
    }

    // TODO quick path 1-2
    /*
  if(a1_arg0_len != -1 && a2_arg0_len != -1 && a1_arg0_len == a2_arg0_len){
    if (! inSameEqc(t, a1_arg0, a2_arg0)) {
      __debugPrint(logFile, ">> [simplifyConcatEq] Quick Path 2-1: len(nn1.arg0) == len(nn2.arg0)\n");
      Z3_ast ax_l1 = Z3_mk_eq(ctx, nn1, nn2);
      Z3_ast ax_l2 = Z3_mk_eq(ctx, mk_length(t, a1_arg0), mk_length(t, a2_arg0));
      Z3_ast ax_r1 = Z3_mk_eq(ctx, a1_arg0, a2_arg0);
      Z3_ast ax_r2 = Z3_mk_eq(ctx, a1_arg1, a2_arg1);
      Z3_ast toAdd = Z3_mk_implies(ctx, mk_2_and(t, ax_l1, ax_l2), mk_2_and(t, ax_r1, ax_r2));
      addAxiom(t, toAdd, __LINE__);
      return;
    }
  }

  if (a1_arg1_len != -1 && a2_arg1_len != -1 && a1_arg1_len == a2_arg1_len)
  {
    if (!inSameEqc(t, a1_arg1, a2_arg1)) {
      __debugPrint(logFile, ">> [simplifyConcatEq] Quick Path 2-2: len(nn1.arg1) == len(nn2.arg1)\n");
      Z3_ast ax_l1 = Z3_mk_eq(ctx, nn1, nn2);
      Z3_ast ax_l2 = Z3_mk_eq(ctx, mk_length(t, a1_arg1), mk_length(t, a2_arg1));
      Z3_ast ax_r1 = Z3_mk_eq(ctx, a1_arg0, a2_arg0);
      Z3_ast ax_r2 = Z3_mk_eq(ctx, a1_arg1, a2_arg1);
      Z3_ast toAdd = Z3_mk_implies(ctx, mk_2_and(t, ax_l1, ax_l2), mk_2_and(t, ax_r1, ax_r2));
      addAxiom(t, toAdd, __LINE__);
      return;
    }
  }
  */

    expr * new_nn1 = simplify_concat(nn1);
    expr * new_nn2 = simplify_concat(nn2);
    app * a_new_nn1 = to_app(new_nn1);
    app * a_new_nn2 = to_app(new_nn2);
    expr * v1_arg0 = a_new_nn1->get_arg(0);
    expr * v1_arg1 = a_new_nn1->get_arg(1);
    expr * v2_arg0 = a_new_nn2->get_arg(0);
    expr * v2_arg1 = a_new_nn2->get_arg(1);

    TRACE("t_str_detail", tout << "new_nn1 = " << mk_ismt2_pp(new_nn1, m) << std::endl
            << "new_nn2 = " << mk_ismt2_pp(new_nn2, m) << std::endl;);

    if (new_nn1 == new_nn2) {
        TRACE("t_str_detail", tout << "equal concats, return" << std::endl;);
        return;
    }

    if (!can_two_nodes_eq(new_nn1, new_nn2)) {
        expr_ref detected(m.mk_not(ctx.mk_eq_atom(new_nn1, new_nn2)), m);
        TRACE("t_str_detail", tout << "inconsistency detected: " << mk_ismt2_pp(detected, m) << std::endl;);
        assert_axiom(detected);
        return;
    }

    // check whether new_nn1 and new_nn2 are still concats

    bool n1IsConcat = is_concat(a_new_nn1);
    bool n2IsConcat = is_concat(a_new_nn2);
    if (!n1IsConcat && n2IsConcat) {
        TRACE("t_str_detail", tout << "nn1_new is not a concat" << std::endl;);
        if (is_string(a_new_nn1)) {
            simplify_parent(new_nn2, new_nn1);
        }
        return;
    } else if (n1IsConcat && !n2IsConcat) {
        TRACE("t_str_detail", tout << "nn2_new is not a concat" << std::endl;);
        if (is_string(a_new_nn2)) {
            simplify_parent(new_nn1, new_nn2);
        }
        return;
    }

    if (!in_same_eqc(new_nn1, new_nn2) && (nn1 != new_nn1 || nn2 != new_nn2)) {
        int ii4 = 0;
        expr* item[3];
        if (nn1 != new_nn1) {
            item[ii4++] = ctx.mk_eq_atom(nn1, new_nn1);
        }
        if (nn2 != new_nn2) {
            item[ii4++] = ctx.mk_eq_atom(nn2, new_nn2);
        }
        item[ii4++] = ctx.mk_eq_atom(nn1, nn2);
        expr_ref premise(m.mk_and(ii4, item), m);
        expr_ref conclusion(ctx.mk_eq_atom(new_nn1, new_nn2), m);
        assert_implication(premise, conclusion);
    }

    // start to split both concats
    check_and_init_cut_var(v1_arg0);
    check_and_init_cut_var(v1_arg1);
    check_and_init_cut_var(v2_arg0);
    check_and_init_cut_var(v2_arg1);

    //*************************************************************
    // case 1: concat(x, y) = concat(m, n)
    //*************************************************************
    if (is_concat_eq_type1(new_nn1, new_nn2)) {
        process_concat_eq_type1(new_nn1, new_nn2);
        return;
    }

    //*************************************************************
    // case 2: concat(x, y) = concat(m, "str")
    //*************************************************************
    if (is_concat_eq_type2(new_nn1, new_nn2)) {
        process_concat_eq_type2(new_nn1, new_nn2);
        return;
    }

    //*************************************************************
    // case 3: concat(x, y) = concat("str", n)
    //*************************************************************
    if (is_concat_eq_type3(new_nn1, new_nn2)) {
        process_concat_eq_type3(new_nn1, new_nn2);
        return;
    }

    //*************************************************************
    //  case 4: concat("str1", y) = concat("str2", n)
    //*************************************************************
    if (is_concat_eq_type4(new_nn1, new_nn2)) {
        process_concat_eq_type4(new_nn1, new_nn2);
        return;
    }

    //*************************************************************
    //  case 5: concat(x, "str1") = concat(m, "str2")
    //*************************************************************
    if (is_concat_eq_type5(new_nn1, new_nn2)) {
        process_concat_eq_type5(new_nn1, new_nn2);
        return;
    }
    //*************************************************************
    //  case 6: concat("str1", y) = concat(m, "str2")
    //*************************************************************
    if (is_concat_eq_type6(new_nn1, new_nn2)) {
        process_concat_eq_type6(new_nn1, new_nn2);
        return;
    }

}

bool theory_str::is_concat_eq_type1(expr * concatAst1, expr * concatAst2) {
    expr * x = to_app(concatAst1)->get_arg(0);
    expr * y = to_app(concatAst1)->get_arg(1);
    expr * m = to_app(concatAst2)->get_arg(0);
    expr * n = to_app(concatAst2)->get_arg(1);

    if (!m_strutil.is_string(x) && !m_strutil.is_string(y) && !m_strutil.is_string(m) && !m_strutil.is_string(n)) {
        return true;
    } else {
        return false;
    }
}

void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {
    ast_manager & mgr = get_manager();
    context & ctx = get_context();
    TRACE("t_str_detail", tout << "process_concat_eq TYPE 1" << std::endl
            << "concatAst1 = " << mk_ismt2_pp(concatAst1, m) << std::endl
            << "concatAst2 = " << mk_ismt2_pp(concatAst2, m) << std::endl;
    );

    if (!is_concat(to_app(concatAst1))) {
        TRACE("t_str_detail", tout << "concatAst1 is not a concat function" << std::endl;);
        return;
    }
    if (!is_concat(to_app(concatAst2))) {
        TRACE("t_str_detail", tout << "concatAst2 is not a concat function" << std::endl;);
        return;
    }
    expr * x = to_app(concatAst1)->get_arg(0);
    expr * y = to_app(concatAst1)->get_arg(1);
    expr * m = to_app(concatAst2)->get_arg(0);
    expr * n = to_app(concatAst2)->get_arg(1);

    /* TODO query the integer theory:
  int x_len = getLenValue(t, x);
  int y_len = getLenValue(t, y);
  int m_len = getLenValue(t, m);
  int n_len = getLenValue(t, n);
     */
    int x_len = -1;
    int y_len = -1;
    int m_len = -1;
    int n_len = -1;

    int splitType = -1;
    if (x_len != -1 && m_len != -1) {
        if (x_len < m_len)
            splitType = 0;
        else if (x_len == m_len)
            splitType = 1;
        else
            splitType = 2;
    }

    if (splitType == -1 && y_len != -1 && n_len != -1) {
        if (y_len > n_len)
            splitType = 0;
        else if (y_len == n_len)
            splitType = 1;
        else
            splitType = 2;
    }

    TRACE("t_str_detail", tout << "split type " << splitType << std::endl;);

    expr * t1 = NULL;
    expr * t2 = NULL;
    expr * xorFlag = NULL;

    std::pair<expr*, expr*> key1(concatAst1, concatAst2);
    std::pair<expr*, expr*> key2(concatAst2, concatAst1);

    if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
        t1 = mk_nonempty_str_var();
        t2 = mk_nonempty_str_var();
        xorFlag = mk_internal_xor_var();
        check_and_init_cut_var(t1);
        check_and_init_cut_var(t2);
        varForBreakConcat[key1][0] = t1;
        varForBreakConcat[key1][1] = t2;
        varForBreakConcat[key1][2] = xorFlag;
    } else {
        // match found
        if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
            t1 = varForBreakConcat[key1][0];
            t2 = varForBreakConcat[key1][1];
            xorFlag = varForBreakConcat[key1][2];
        } else {
            t1 = varForBreakConcat[key2][0];
            t2 = varForBreakConcat[key2][1];
            xorFlag = varForBreakConcat[key2][2];
        }
    }

    // For split types 0 through 2, we can get away with providing
    // fewer split options since more length information is available.
    if (splitType == 0) {
        NOT_IMPLEMENTED_YET(); // TODO
    } else if (splitType == 1) {
        NOT_IMPLEMENTED_YET(); // TODO
    } else if (splitType == 2) {
        NOT_IMPLEMENTED_YET(); // TODO
    } else if (splitType == -1) {
        // Here we don't really have a choice. We have no length information at all...
        expr ** or_item = alloc_svect(expr*, 3);
        expr ** and_item = alloc_svect(expr*, 20);
        int option = 0;
        int pos = 1;

        // break option 1: m cuts y
        // len(x) < len(m) || len(y) > len(n)
        if (!avoidLoopCut || !has_self_cut(m, y)) {
            // break down option 1-1
            expr * x_t1 = mk_concat(x, t1);
            expr * t1_n = mk_concat(t1, n);
            or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(m, x_t1));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(y, t1_n));

            expr_ref x_plus_t1(m_autil.mk_add(mk_strlen(x), mk_strlen(t1)), mgr);
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(m), x_plus_t1));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], m_autil.mk_gt(mk_strlen(m), mk_strlen(x)));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], m_autil.mk_gt(mk_strlen(y), mk_strlen(n)));

            option++;

            add_cut_info_merge(t1, ctx.get_scope_level(), m);
            add_cut_info_merge(t1, ctx.get_scope_level(), y);
        } else {
            loopDetected = true;
            TRACE("t_str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
            // TODO printCutVar(m, y);
        }

        // break option 2:
        // x = m || y = n
        if (!avoidLoopCut || !has_self_cut(x, n)) {
            // break down option 1-2
            expr * m_t2 = mk_concat(m, t2);
            expr * t2_y = mk_concat(t2, y);
            or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(x, m_t2));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(n, t2_y));


            expr_ref m_plus_t2(m_autil.mk_add(mk_strlen(m), mk_strlen(t2)), mgr);

            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(x), m_plus_t2));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(x), mk_strlen(m)));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(n), mk_strlen(y)));


            option++;

            add_cut_info_merge(t2, sLevel, x);
            add_cut_info_merge(t2, sLevel, n);
        } else {
            loopDetected = true;
            TRACE("t_str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
            // TODO printCutVar(x, n);
        }

        if (can_two_nodes_eq(x, m) && can_two_nodes_eq(y, n)) {
            or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(x, m));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(y, n));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(x), mk_strlen(m)));
            and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(y), mk_strlen(n)));
            ++option;
        }

        if (option > 0) {
            if (option == 1) {
                and_item[0] = or_item[0];
            } else {
                and_item[0] = mgr.mk_or(option, or_item);
            }
            expr_ref premise(ctx.mk_eq_atom(concatAst1, concatAst2), m);
            expr_ref conclusion(mgr.mk_and(pos, and_item), m);
            assert_implication(premise, conclusion);
        } else {
            TRACE("t_str", tout << "STOP: no split option found for two EQ concats." << std::endl;);
        }
    } // (splitType == -1)
}

bool theory_str::is_concat_eq_type2(expr * concatAst1, expr * concatAst2) {
    // TODO
    return false;
}

void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {

}

bool theory_str::is_concat_eq_type3(expr * concatAst1, expr * concatAst2) {
    // TODO
    return false;
}

void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {

}

bool theory_str::is_concat_eq_type4(expr * concatAst1, expr * concatAst2) {
    // TODO
    return false;
}

void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {

}

bool theory_str::is_concat_eq_type5(expr * concatAst1, expr * concatAst2) {
    // TODO
    return false;
}

void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {

}

bool theory_str::is_concat_eq_type6(expr * concatAst1, expr * concatAst2) {
    // TODO
    return false;
}

void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {

}

/*
 * Look through the equivalence class of n to find a string constant.
 * Return that constant if it is found, and set hasEqcValue to true.
 * Otherwise, return n, and set hasEqcValue to false.
 */
expr * theory_str::get_eqc_value(expr * n, bool & hasEqcValue) {
	context & ctx = get_context();
	enode * nNode = ctx.get_enode(n);
	enode * eqcNode = nNode;
	do {
		app * ast = eqcNode->get_owner();
		if (is_string(eqcNode)) {
			hasEqcValue = true;
			return ast;
		}
		eqcNode = eqcNode->get_next();
	} while (eqcNode != nNode);
	// not found
	hasEqcValue = false;
	return n;
}

/*
 * Decide whether n1 and n2 are already in the same equivalence class.
 * This only checks whether the core considers them to be equal;
 * they may not actually be equal.
 */
bool theory_str::in_same_eqc(expr * n1, expr * n2) {
    if (n1 == n2) return true;
    context & ctx = get_context();
    enode * n1Node = ctx.get_enode(n1);
    enode * n2Node = ctx.get_enode(n2);

    // here's what the old Z3str2 would have done; we can do something much better
    /*
    n1Node->get_root();
    enode * curr = n1Node->get_next();
    while (curr != n1Node) {
        if (curr == n2Node) {
            return true;
        }
        curr = curr->get_next();
    }
    return false;
    */
    return n1Node->get_root() == n2Node->get_root();
}

/*
bool canTwoNodesEq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  Z3_ast n1_curr = n1;
  Z3_ast n2_curr = n2;

  // case 0: n1_curr is const string, n2_curr is const string
  if (isConstStr(t, n1_curr) && isConstStr(t, n2_curr)) {
    if (n1_curr != n2_curr) {
      return false;
    }
  }
  // case 1: n1_curr is concat, n2_curr is const string
  else if (isConcatFunc(t, n1_curr) && isConstStr(t, n2_curr)) {
    std::string n2_curr_str = getConstStrValue(t, n2_curr);
    if (canConcatEqStr(t, n1_curr, n2_curr_str) != 1) {
      return false;
    }
  }
  // case 2: n2_curr is concat, n1_curr is const string
  else if (isConcatFunc(t, n2_curr) && isConstStr(t, n1_curr)) {
    std::string n1_curr_str = getConstStrValue(t, n1_curr);
    if (canConcatEqStr(t, n2_curr, n1_curr_str) != 1) {
      return false;
    }
  } else if (isConcatFunc(t, n1_curr) && isConcatFunc(t, n2_curr)) {
    if (canConcatEqConcat(t, n1_curr, n2_curr) != 1) {
      return false;
    }
  }

  return true;
}
*/

bool theory_str::can_concat_eq_str(expr * concat, std::string str) {
    // TODO
    return true;
}

bool theory_str::can_concat_eq_concat(expr * concat1, expr * concat2) {
    // TODO
    return true;
}

/*
 * Check whether n1 and n2 could be equal.
 * Returns true if n1 could equal n2 (maybe),
 * and false if n1 is definitely not equal to n2 (no).
 */
bool theory_str::can_two_nodes_eq(expr * n1, expr * n2) {
    app * n1_curr = to_app(n1);
    app * n2_curr = to_app(n2);

    // case 0: n1_curr is const string, n2_curr is const string
    if (is_string(n1_curr) && is_string(n2_curr)) {
      if (n1_curr != n2_curr) {
        return false;
      }
    }
    // case 1: n1_curr is concat, n2_curr is const string
    else if (is_concat(n1_curr) && is_string(n2_curr)) {
        const char * tmp = 0;
        m_strutil.is_string(n2_curr, & tmp);
        std::string n2_curr_str(tmp);
        if (!can_concat_eq_str(n1_curr, n2_curr_str)) {
            return false;
        }
    }
    // case 2: n2_curr is concat, n1_curr is const string
    else if (is_concat(n2_curr) && is_string(n1_curr)) {
        const char * tmp = 0;
        m_strutil.is_string(n1_curr, & tmp);
        std::string n1_curr_str(tmp);
        if (!can_concat_eq_str(n2_curr, n1_curr_str)) {
            return false;
        }
    }
    // case 3: both are concats
    else if (is_concat(n1_curr) && is_concat(n2_curr)) {
      if (!can_concat_eq_concat(n1_curr, n2_curr)) {
        return false;
      }
    }

    return true;
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


            expr_ref premise(ctx.mk_eq_atom(concat, str), m);
            expr_ref c1(ctx.mk_eq_atom(a1, str), m);
            expr_ref c2(ctx.mk_eq_atom(a2, str), m);
            expr_ref conclusion(m.mk_and(c1, c2), m);
            assert_implication(premise, conclusion);

            return;
        }
        bool arg1_has_eqc_value = false;
        bool arg2_has_eqc_value = false;
        expr * arg1 = get_eqc_value(a1, arg1_has_eqc_value);
        expr * arg2 = get_eqc_value(a2, arg2_has_eqc_value);
        expr_ref newConcat(m);
        if (arg1 != a1 || arg2 != a2) {
        	TRACE("t_str", tout << "resolved concat argument(s) to eqc string constants" << std::endl;);
        	int iPos = 0;
        	app * item1[2];
        	if (a1 != arg1) {
        		item1[iPos++] = ctx.mk_eq_atom(a1, arg1);
        	}
        	if (a2 != arg2) {
        		item1[iPos++] = ctx.mk_eq_atom(a2, arg2);
        	}
        	expr_ref implyL1(m);
        	if (iPos == 1) {
        		implyL1 = item1[0];
        	} else {
        		implyL1 = m.mk_and(item1[0], item1[1]);
        	}
        	newConcat = mk_concat(arg1, arg2);
        	if (newConcat != str) {
        		expr_ref implyR1(ctx.mk_eq_atom(concat, newConcat), m);
        		assert_implication(implyL1, implyR1);
        	}
        } else {
        	newConcat = concat;
        }
        if (newConcat == str) {
        	return;
        }
        if (!is_concat(to_app(newConcat))) {
        	return;
        }
        if (arg1_has_eqc_value && arg2_has_eqc_value) {
        	// Case 1: Concat(const, const) == const
        	TRACE("t_str", tout << "Case 1: Concat(const, const) == const" << std::endl;);
        	const char * str1;
        	m_strutil.is_string(arg1, & str1);
        	std::string arg1_str(str1);

        	const char * str2;
        	m_strutil.is_string(arg2, & str2);
        	std::string arg2_str(str2);

        	std::string result_str = arg1_str + arg2_str;
        	if (result_str != const_str) {
        		// Inconsistency
        		TRACE("t_str", tout << "inconsistency detected: \""
        				<< arg1_str << "\" + \"" << arg2_str <<
						"\" != \"" << const_str << "\"" << std::endl;);
        		expr_ref equality(ctx.mk_eq_atom(concat, str), m);
        		expr_ref diseq(m.mk_not(equality), m);
        		assert_axiom(diseq);
        		return;
        	}
        } else if (!arg1_has_eqc_value && arg2_has_eqc_value) {
        	// Case 2: Concat(var, const) == const
        	TRACE("t_str", tout << "Case 2: Concat(var, const) == const" << std::endl;);
        	const char * str2;
			m_strutil.is_string(arg2, & str2);
			std::string arg2_str(str2);
			int resultStrLen = const_str.length();
			int arg2StrLen = arg2_str.length();
			if (resultStrLen < arg2StrLen) {
				// Inconsistency
				TRACE("t_str", tout << "inconsistency detected: \""
						 << arg2_str <<
						"\" is longer than \"" << const_str << "\","
						<< " so cannot be concatenated with anything to form it" << std::endl;);
				expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
				expr_ref diseq(m.mk_not(equality), m);
				assert_axiom(diseq);
				return;
			} else {
				int varStrLen = resultStrLen - arg2StrLen;
				std::string firstPart = const_str.substr(0, varStrLen);
				std::string secondPart = const_str.substr(varStrLen, arg2StrLen);
				if (arg2_str != secondPart) {
					// Inconsistency
					TRACE("t_str", tout << "inconsistency detected: "
							<< "suffix of concatenation result expected \"" << secondPart << "\", "
							<< "actually \"" << arg2_str << "\""
							<< std::endl;);
					expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
					expr_ref diseq(m.mk_not(equality), m);
					assert_axiom(diseq);
					return;
				} else {
					expr_ref tmpStrConst(m_strutil.mk_string(firstPart), m);
					expr_ref premise(ctx.mk_eq_atom(newConcat, str), m);
					expr_ref conclusion(ctx.mk_eq_atom(arg1, tmpStrConst), m);
					assert_implication(premise, conclusion);
					return;
				}
			}
        } else if (arg1_has_eqc_value && !arg2_has_eqc_value) {
        	// Case 3: Concat(const, var) == const
        	TRACE("t_str", tout << "Case 3: Concat(const, var) == const" << std::endl;);
        	const char * str1;
			m_strutil.is_string(arg1, & str1);
			std::string arg1_str(str1);
			int resultStrLen = const_str.length();
			int arg1StrLen = arg1_str.length();
			if (resultStrLen < arg1StrLen) {
				// Inconsistency
				TRACE("t_str", tout << "inconsistency detected: \""
						 << arg1_str <<
						"\" is longer than \"" << const_str << "\","
						<< " so cannot be concatenated with anything to form it" << std::endl;);
				expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
				expr_ref diseq(m.mk_not(equality), m);
				assert_axiom(diseq);
				return;
			} else {
				int varStrLen = resultStrLen - arg1StrLen;
				std::string firstPart = const_str.substr(0, arg1StrLen);
				std::string secondPart = const_str.substr(arg1StrLen, varStrLen);
				if (arg1_str != firstPart) {
					// Inconsistency
					TRACE("t_str", tout << "inconsistency detected: "
							<< "prefix of concatenation result expected \"" << secondPart << "\", "
							<< "actually \"" << arg1_str << "\""
							<< std::endl;);
					expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
					expr_ref diseq(m.mk_not(equality), m);
					assert_axiom(diseq);
					return;
				} else {
					expr_ref tmpStrConst(m_strutil.mk_string(secondPart), m);
					expr_ref premise(ctx.mk_eq_atom(newConcat, str), m);
					expr_ref conclusion(ctx.mk_eq_atom(arg2, tmpStrConst), m);
					assert_implication(premise, conclusion);
					return;
				}
			}
        } else {
        	// Case 4: Concat(var, var) == const
        	TRACE("t_str", tout << "Case 4: Concat(var, var) == const" << std::endl;);
        	// TODO large additions required in this section
        	if (true) { /* if (Concat(arg1, arg2) == NULL) { */
        		int arg1Len = -1; /* = getLenValue(arg1); */
        		int arg2Len = -1; /* = getLenValue(arg2); */
        		if (arg1Len != -1 || arg2Len != -1) {
        			NOT_IMPLEMENTED_YET(); // TODO
        		} else { /* ! (arg1Len != 1 || arg2Len != 1) */
        			expr_ref xorFlag(m);
        			std::pair<expr*, expr*> key1(arg1, arg2);
        			std::pair<expr*, expr*> key2(arg2, arg1);
        			std::map<std::pair<expr*, expr*>, std::map<int, expr*> >::iterator varBreak_key1 =
        					varForBreakConcat.find(key1);
        			std::map<std::pair<expr*, expr*>, std::map<int, expr*> >::iterator varBreak_key2 =
							varForBreakConcat.find(key2);
        			if (varBreak_key1 == varForBreakConcat.end() && varBreak_key2 == varForBreakConcat.end()) {
        				xorFlag = mk_internal_xor_var();
        				varForBreakConcat[key1][0] = xorFlag;
        			} else if (varBreak_key1 != varForBreakConcat.end()) {
        				xorFlag = varForBreakConcat[key1][0];
        			} else { // varBreak_key2 != varForBreakConcat.end()
        				xorFlag = varForBreakConcat[key2][0];
        			}

        			int concatStrLen = const_str.length();
        			int xor_pos = 0;
        			int and_count = 1;
        			/*
        			expr ** xor_items = new expr*[concatStrLen + 1];
        			expr ** and_items = new expr*[4 * (concatStrLen+1) + 1];
        			*/
        			expr ** xor_items = alloc_svect(expr*, (concatStrLen+1));
        			expr ** and_items = alloc_svect(expr*, (4 * (concatStrLen+1) + 1));

        			for (int i = 0; i < concatStrLen + 1; ++i) {
        				std::string prefixStr = const_str.substr(0, i);
        				std::string suffixStr = const_str.substr(i, concatStrLen - i);
        				// skip invalid options
        				// TODO canConcatEqStr() checks:
        				/*
							if (isConcatFunc(t, arg1) && canConcatEqStr(t, arg1, prefixStr) == 0) {
							  continue;
							}
							if (isConcatFunc(t, arg2) && canConcatEqStr(t, arg2, suffixStr) == 0) {
							  continue;
							}
        				 */
        				expr_ref xorAst(ctx.mk_eq_atom(xorFlag, m_autil.mk_numeral(rational(xor_pos), true)), m);
        				xor_items[xor_pos++] = xorAst;

        				expr_ref prefixAst(m_strutil.mk_string(prefixStr), m);
        				expr_ref arg1_eq (ctx.mk_eq_atom(arg1, prefixAst), m);
        				and_items[and_count++] = ctx.mk_eq_atom(xorAst, arg1_eq);

        				expr_ref suffixAst(m_strutil.mk_string(suffixStr), m);
        				expr_ref arg2_eq (ctx.mk_eq_atom(arg2, suffixAst), m);
        				and_items[and_count++] = ctx.mk_eq_atom(xorAst, arg2_eq);
        			}

        			expr_ref implyL(ctx.mk_eq_atom(concat, str), m);
        			expr_ref implyR1(m);
        			if (xor_pos == 0) {
        				// negate
        				expr_ref concat_eq_str(ctx.mk_eq_atom(concat, str), m);
        				expr_ref negate_ast(m.mk_not(concat_eq_str), m);
        				assert_axiom(negate_ast);
        			} else {
        				if (xor_pos == 1) {
        				    and_items[0] = xor_items[0];
        				    implyR1 = m.mk_and(and_count, and_items);
        				} else {
        				    and_items[0] = m.mk_or(xor_pos, xor_items);
        				    implyR1 = m.mk_and(and_count, and_items);
        				}
        				assert_implication(implyL, implyR1);
        			}
        			delete[] xor_items;
        			delete[] and_items;
        		} /* (arg1Len != 1 || arg2Len != 1) */
        	} /* if (Concat(arg1, arg2) == NULL) */
        }
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
    // I'm disabling this entire code block for now. It may no longer be useful.
    // Z3 seems to be putting LHS and RHS into the same equivalence class extremely early.
    // As a result, simplify_concat_equality() is never getting called,
    // and if it were called, it would probably get called with the same element on both sides.
    /*
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
    */
    if (eqc_lhs_concat.size() != 0 && eqc_rhs_concat.size() != 0) {
        // let's pick the first concat in the LHS's eqc
        // and find some concat in the RHS's eqc that is
        // distinct from the first one we picked
        expr * lhs = *eqc_lhs_concat.begin();
        std::set<expr*>::iterator itor2 = eqc_rhs_concat.begin();
        for (; itor2 != eqc_rhs_concat.end(); ++itor2) {
            expr * rhs = *itor2;
            if (lhs != rhs) {
                simplify_concat_equality(lhs, rhs);
                break;
            }
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

    // TODO simplify_parent over eqc

    // TODO regex unroll? (much later)
}

void theory_str::set_up_axioms(expr * ex) {
    // TODO check to make sure we don't set up axioms on the same term twice
    ast_manager & m = get_manager();
    context & ctx = get_context();

    sort * ex_sort = m.get_sort(ex);
    sort * str_sort = m.mk_sort(get_family_id(), STRING_SORT);

    if (ex_sort == str_sort) {
        TRACE("t_str_detail", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) <<
                ": expr is of sort String" << std::endl;);
        // set up basic string axioms
        enode * n = ctx.get_enode(ex);
        SASSERT(n);
        m_basicstr_axiom_todo.push_back(n);

        // if additionally ex is a concatenation, set up concatenation axioms
        if (is_app(ex) && is_concat(to_app(ex))) {
            m_concat_axiom_todo.push_back(n);
        }
    } else {
        TRACE("t_str_detail", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) <<
                ": expr is of wrong sort, ignoring" << std::endl;);
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
     * might not get a chance to see.
     */
    expr_ref_vector assignments(m);
    ctx.get_assignments(assignments);
    for (expr_ref_vector::iterator i = assignments.begin(); i != assignments.end(); ++i) {
        expr * ex = *i;
        if (m.is_eq(ex)) {
            TRACE("t_str_detail", tout << "processing assignment " << mk_ismt2_pp(ex, m) <<
                    ": expr is equality" << std::endl;);
            app * eq = (app*)ex;
            SASSERT(eq->get_num_args() == 2);
            expr * lhs = eq->get_arg(0);
            expr * rhs = eq->get_arg(1);

            enode * e_lhs = ctx.get_enode(lhs);
            enode * e_rhs = ctx.get_enode(rhs);
            std::pair<enode*,enode*> eq_pair(e_lhs, e_rhs);
            m_str_eq_todo.push_back(eq_pair);
        } else {
            TRACE("t_str_detail", tout << "processing assignment " << mk_ismt2_pp(ex, m)
                    << ": expr ignored" << std::endl;);
        }
    }

    TRACE("t_str", tout << "search started" << std::endl;);
    search_started = true;
}

void theory_str::new_eq_eh(theory_var x, theory_var y) {
    //TRACE("t_str_detail", tout << "new eq: v#" << x << " = v#" << y << std::endl;);
    TRACE("t_str", tout << "new eq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    handle_equality(get_enode(x)->get_owner(), get_enode(y)->get_owner());
}

void theory_str::new_diseq_eh(theory_var x, theory_var y) {
    //TRACE("t_str_detail", tout << "new diseq: v#" << x << " != v#" << y << std::endl;);
    TRACE("t_str", tout << "new diseq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " != " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
}

void theory_str::relevant_eh(app * n) {
    TRACE("t_str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << std::endl;);
}

void theory_str::assign_eh(bool_var v, bool is_true) {
    context & ctx = get_context();
    TRACE("t_str", tout << "assert: v" << v << " #" << ctx.bool_var2expr(v)->get_id() << " is_true: " << is_true << std::endl;);
}

void theory_str::push_scope_eh() {
    TRACE("t_str", tout << "push" << std::endl;);
}

void theory_str::pop_scope_eh(unsigned num_scopes) {
    TRACE("t_str", tout << "pop " << num_scopes << std::endl;);
    context & ctx = get_context();
    unsigned sLevel = ctx.get_scope_level();
    std::map<expr*, std::stack<T_cut *> >::iterator varItor = cut_var_map.begin();
    while (varItor != cut_var_map.end()) {
        while ((varItor->second.size() > 0) && (varItor->second.top()->level != 0) && (varItor->second.top()->level >= sLevel)) {
            T_cut * aCut = varItor->second.top();
            varItor->second.pop();
            dealloc(aCut);
        }
        if (varItor->second.size() == 0) {
            cut_var_map.erase(varItor);
        }
        ++varItor;
    }
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

/*
 * Helper function for mk_value().
 * Attempts to resolve the expression 'n' to a string constant.
 * Stronger than get_eqc_value() in that it will perform recursive descent
 * through every subexpression and attempt to resolve those to concrete values as well.
 * Returns the concrete value obtained from this process,
 * guaranteed to satisfy m_strutil.is_string(),
 * if one could be obtained,
 * or else returns NULL if no concrete value was derived.
 */
app * theory_str::mk_value_helper(app * n) {
    if (m_strutil.is_string(n)) {
        return n;
    } else if (is_concat(n)) {
        // recursively call this function on each argument
        SASSERT(n->get_num_args() == 2);
        expr * a0 = n->get_arg(0);
        expr * a1 = n->get_arg(1);

        app * a0_conststr = mk_value_helper(to_app(a0));
        app * a1_conststr = mk_value_helper(to_app(a1));

        if (a0_conststr != NULL && a1_conststr != NULL) {
            const char * a0_str = 0;
            m_strutil.is_string(a0_conststr, &a0_str);

            const char * a1_str = 0;
            m_strutil.is_string(a1_conststr, &a1_str);

            std::string a0_s(a0_str);
            std::string a1_s(a1_str);
            std::string result = a0_s + a1_s;
            return m_strutil.mk_string(result);
        }
    }
    // fallback path
    // try to find some constant string, anything, in the equivalence class of n
    bool hasEqc = false;
    expr * n_eqc = get_eqc_value(n, hasEqc);
    if (hasEqc) {
        return to_app(n_eqc);
    } else {
        return NULL;
    }
}

model_value_proc * theory_str::mk_value(enode * n, model_generator & mg) {
    TRACE("t_str", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) <<
                                " (sort " << mk_ismt2_pp(get_manager().get_sort(n->get_owner()), get_manager()) << ")" << std::endl;);
    ast_manager & m = get_manager();
    context & ctx = get_context();
    app_ref owner(m);
    owner = n->get_owner();

    // If the owner is not internalized, it doesn't have an enode associated.
    SASSERT(ctx.e_internalized(owner));

    app * val = mk_value_helper(owner);
    if (val != NULL) {
        return alloc(expr_wrapper_proc, val);
    } else {
        m.raise_exception("failed to find concrete value"); return NULL;
    }
}

void theory_str::finalize_model(model_generator & mg) {}

}; /* namespace smt */
