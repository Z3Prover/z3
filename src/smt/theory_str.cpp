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
#include<list>

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
		initialize_charset();
}

theory_str::~theory_str() {
}

void theory_str::initialize_charset() {
	bool defaultCharset = true;
	if (defaultCharset) {
		// valid C strings can't contain the null byte ('\0')
		charSetSize = 255;
		char_set = alloc_svect(char, charSetSize);
		int idx = 0;
		// small letters
		for (int i = 97; i < 123; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// caps
		for (int i = 65; i < 91; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// numbers
		for (int i = 48; i < 58; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// printable marks - 1
		for (int i = 32; i < 48; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// printable marks - 2
		for (int i = 58; i < 65; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// printable marks - 3
		for (int i = 91; i < 97; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// printable marks - 4
		for (int i = 123; i < 127; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// non-printable - 1
		for (int i = 1; i < 32; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
		// non-printable - 2
		for (int i = 127; i < 256; i++) {
			char_set[idx] = (char) i;
			charSetLookupTable[char_set[idx]] = idx;
			idx++;
		}
	} else {
		const char setset[] = { 'a', 'b', 'c' };
		int fSize = sizeof(setset) / sizeof(char);

		char_set = alloc_svect(char, fSize);
		charSetSize = fSize;
		for (int i = 0; i < charSetSize; i++) {
			char_set[i] = setset[i];
			charSetLookupTable[setset[i]] = i;
		}
	}
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

expr * theory_str::mk_internal_lenTest_var(expr * node, int lTries) {
	ast_manager & m = get_manager();

	std::stringstream ss;
	ss << "$$_len_" << mk_ismt2_pp(node, m) << "_" << lTries;
	std::string name = ss.str();
	return mk_str_var(name);

	/*
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << "$$_len_" << Z3_ast_to_string(ctx, node) << "_" << lTries;
  std::string name = ss.str();
  return my_mk_str_var(t, name.c_str());
  */
}

expr * theory_str::mk_internal_valTest_var(expr * node, int len, int vTries) {
	ast_manager & m = get_manager();
	std::stringstream ss;
	ss << "$$_val_" << mk_ismt2_pp(node, m) << "_" << len << "_" << vTries;
	std::string name = ss.str();
	return mk_str_var(name);

	/*
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << "$$_val_" << Z3_ast_to_string(ctx, node) << "_" << len << "_" << vTries;
  std::string name = ss.str();
  return my_mk_str_var(t, name.c_str());
  */
}

app * theory_str::mk_internal_xor_var() {
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

app * theory_str::mk_str_var(std::string name) {
	context & ctx = get_context();
	ast_manager & m = get_manager();

	TRACE("t_str_detail", tout << "creating string variable " << name << std::endl;);

	sort * string_sort = m.mk_sort(m_strutil.get_family_id(), STRING_SORT);
	char * new_buffer = alloc_svect(char, name.length() + 1);
	strcpy(new_buffer, name.c_str());
	symbol sym(new_buffer);

	app * a = m.mk_const(m.mk_const_decl(sym, string_sort));

	// I have a hunch that this may not get internalized for free...
	ctx.internalize(a, false);
	SASSERT(ctx.get_enode(a) != NULL);
	SASSERT(ctx.e_internalized(a));
	m_basicstr_axiom_todo.push_back(ctx.get_enode(a));

	variable_set.insert(a);
	internal_variable_set.insert(a);

	return a;
}

app * theory_str::mk_nonempty_str_var() {
    context & ctx = get_context();
    ast_manager & m = get_manager();

    std::stringstream ss;
    ss << tmpStringVarCount;
    tmpStringVarCount++;
    std::string name = "$$_str" + ss.str();

    TRACE("t_str_detail", tout << "creating nonempty string variable " << name << std::endl;);

    sort * string_sort = m.mk_sort(m_strutil.get_family_id(), STRING_SORT);
    char * new_buffer = alloc_svect(char, name.length() + 1);
    strcpy(new_buffer, name.c_str());
    symbol sym(new_buffer);

    app* a = m.mk_const(m.mk_const_decl(sym, string_sort));
    ctx.internalize(a, false);
    SASSERT(ctx.get_enode(a) != NULL);
    // assert a variation of the basic string axioms that ensures this string is nonempty
    {
        // build LHS
        expr * len_str = mk_strlen(a);
        SASSERT(len_str);
        // build RHS
        expr * zero = m_autil.mk_numeral(rational(0), true);
        SASSERT(zero);
        // build LHS > RHS and assert
        // we have to build !(LHS <= RHS) instead
        app * lhs_gt_rhs = m.mk_not(m_autil.mk_le(len_str, zero));
        SASSERT(lhs_gt_rhs);
        assert_axiom(lhs_gt_rhs);
    }

    // add 'a' to variable sets, so we can keep track of it
    variable_set.insert(a);
    internal_variable_set.insert(a);

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

        for (unsigned i = 0; i < m_concat_axiom_todo.size(); ++i) {
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

    ast_manager & m = get_manager();

    // build LHS
    expr_ref len_xy(m);
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

/*************************************************************
 * Type 1: concat(x, y) = concat(m, n)
 *         x, y, m and n all variables
 *************************************************************/
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
            << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
            << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
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
            // TODO these are crashing the solvers because the integer theory
            // expects a constant on the right-hand side.
            // The things we want to assert here are len(m) > len(x) and len(y) > len(n).
            // We rewrite A > B as A-B > 0 and then as not(A-B <= 0),
            // and then, *because we aren't allowed to use subtraction*,
            // as not(A + -1*B <= 0)
            and_item[pos++] = ctx.mk_eq_atom(or_item[option],
                    mgr.mk_not(m_autil.mk_le(
                    		m_autil.mk_add(mk_strlen(m), m_autil.mk_mul(mk_int(-1), mk_strlen(x))),
							mk_int(0))) );
            and_item[pos++] = ctx.mk_eq_atom(or_item[option],
                    mgr.mk_not(m_autil.mk_le(
                    		m_autil.mk_add(mk_strlen(y),m_autil.mk_mul(mk_int(-1), mk_strlen(n))),
							mk_int(0))) );

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
            // want len(x) > len(m) and len(n) > len(y)
            and_item[pos++] = ctx.mk_eq_atom(or_item[option],
            		mgr.mk_not(m_autil.mk_le(
            				m_autil.mk_add(mk_strlen(x), m_autil.mk_mul(mk_int(-1), mk_strlen(m))),
							mk_int(0))) );
            and_item[pos++] = ctx.mk_eq_atom(or_item[option],
            		mgr.mk_not(m_autil.mk_le(
            				m_autil.mk_add(mk_strlen(n), m_autil.mk_mul(mk_int(-1), mk_strlen(y))),
							mk_int(0))) );


            option++;

            add_cut_info_merge(t2, ctx.get_scope_level(), x);
            add_cut_info_merge(t2, ctx.get_scope_level(), n);
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
            expr_ref premise(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
            expr_ref conclusion(mgr.mk_and(pos, and_item), mgr);
            assert_implication(premise, conclusion);
        } else {
            TRACE("t_str", tout << "STOP: no split option found for two EQ concats." << std::endl;);
        }
    } // (splitType == -1)
}

/*************************************************************
 * Type 2: concat(x, y) = concat(m, "str")
 *************************************************************/
bool theory_str::is_concat_eq_type2(expr * concatAst1, expr * concatAst2) {
	expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
	expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
	expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
	expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

	if ((!m_strutil.is_string(v1_arg0)) && m_strutil.is_string(v1_arg1)
			&& (!m_strutil.is_string(v2_arg0)) && (!m_strutil.is_string(v2_arg1))) {
		return true;
	} else if ((!m_strutil.is_string(v2_arg0)) && m_strutil.is_string(v2_arg1)
			&& (!m_strutil.is_string(v1_arg0)) && (!m_strutil.is_string(v1_arg1))) {
		return true;
	} else {
		return false;
	}
}

void theory_str::process_concat_eq_type2(expr * concatAst1, expr * concatAst2) {
	ast_manager & mgr = get_manager();
	context & ctx = get_context();
	TRACE("t_str_detail", tout << "process_concat_eq TYPE 2" << std::endl
			<< "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
			<< "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
	);

	if (!is_concat(to_app(concatAst1))) {
		TRACE("t_str_detail", tout << "concatAst1 is not a concat function" << std::endl;);
		return;
	}
	if (!is_concat(to_app(concatAst2))) {
		TRACE("t_str_detail", tout << "concatAst2 is not a concat function" << std::endl;);
		return;
	}

	expr * x = NULL;
	expr * y = NULL;
	expr * strAst = NULL;
	expr * m = NULL;

	expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
	expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
	expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
	expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

	if (m_strutil.is_string(v1_arg1) && !m_strutil.is_string(v2_arg1)) {
		m = v1_arg0;
		strAst = v1_arg1;
		x = v2_arg0;
		y = v2_arg1;
	} else {
		m = v2_arg0;
		strAst = v2_arg1;
		x = v1_arg0;
		y = v1_arg1;
	}

	const char * strValue_tmp = 0;
	m_strutil.is_string(strAst, &strValue_tmp);
	std::string strValue(strValue_tmp);
	// TODO integer theory interaction
	/*
	int x_len = getLenValue(t, x);
	int y_len = getLenValue(t, y);
	int m_len = getLenValue(t, m);
	int str_len = getLenValue(t, strAst);
	*/

	int x_len = -1;
	int y_len = -1;
	int m_len = -1;
	int str_len = -1;

	// setup

	expr * xorFlag = NULL;
	expr * temp1 = NULL;
	std::pair<expr*, expr*> key1(concatAst1, concatAst2);
	std::pair<expr*, expr*> key2(concatAst2, concatAst1);

	if (varForBreakConcat.find(key1) == varForBreakConcat.end()
			&& varForBreakConcat.find(key2) == varForBreakConcat.end()) {
		temp1 = mk_nonempty_str_var();
		xorFlag = mk_internal_xor_var();
		varForBreakConcat[key1][0] = temp1;
		varForBreakConcat[key1][1] = xorFlag;
	} else {
		if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
			temp1 = varForBreakConcat[key1][0];
			xorFlag = varForBreakConcat[key1][1];
		} else if (varForBreakConcat.find(key2) != varForBreakConcat.end()) {
			temp1 = varForBreakConcat[key2][0];
			xorFlag = varForBreakConcat[key2][1];
		}
	}

	int splitType = -1;
	if (x_len != -1 && m_len != -1) {
		if (x_len < m_len)
			splitType = 0;
		else if (x_len == m_len)
			splitType = 1;
		else
			splitType = 2;
	}
	if (splitType == -1 && y_len != -1 && str_len != -1) {
		if (y_len > str_len)
			splitType = 0;
		else if (y_len == str_len)
			splitType = 1;
		else
			splitType = 2;
	}

	TRACE("t_str_detail", tout << "Split type " << splitType << std::endl;);

	// Provide fewer split options when length information is available.

	if (splitType == 0) {
		NOT_IMPLEMENTED_YET(); // TODO
	} else if (splitType == 1) {
		NOT_IMPLEMENTED_YET(); // TODO
	} else if (splitType == 2) {
		NOT_IMPLEMENTED_YET(); // TODO
	} else {
		// Split type -1: no idea about the length...
		int optionTotal = 2 + strValue.length();
		expr ** or_item = alloc_svect(expr*, optionTotal);
		expr ** and_item = alloc_svect(expr*, (1 + 6 + 4 * (strValue.length() + 1)));
		int option = 0;
		int pos = 1;

		expr_ref temp1_strAst(mk_concat(temp1, strAst), mgr); // TODO assert concat axioms?

		// m cuts y
		if (can_two_nodes_eq(y, temp1_strAst)) {
			if (!avoidLoopCut || !has_self_cut(m, y)) {
				// break down option 2-1
				// TODO
				or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));
				expr_ref x_temp1(mk_concat(x, temp1), mgr); // TODO assert concat axioms?
				and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(m, x_temp1));
				and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(y, temp1_strAst));

				and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(m),
						m_autil.mk_add(mk_strlen(x), mk_strlen(temp1))));

				++option;
				add_cut_info_merge(temp1, ctx.get_scope_level(), y);
				add_cut_info_merge(temp1, ctx.get_scope_level(), m);
			} else {
				loopDetected = true;
				TRACE("t_str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
				// TODO printCutVar(m, y)
			}
		}

		for (int i = 0; i <= (int)strValue.size(); ++i) {
			std::string part1Str = strValue.substr(0, i);
			std::string part2Str = strValue.substr(i, strValue.size() - i);
			expr_ref prefixStr(m_strutil.mk_string(part1Str), mgr);
			expr_ref x_concat(mk_concat(m, prefixStr), mgr); // TODO concat axioms?
			expr_ref cropStr(m_strutil.mk_string(part2Str), mgr);
			if (can_two_nodes_eq(x, x_concat) && can_two_nodes_eq(y, cropStr)) {
				// break down option 2-2
				or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));
				and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(x, x_concat));
				and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(y, cropStr));
				and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(y), mk_int(part2Str.length())));
				++option;
			}
		}

		if (option > 0) {
			if (option == 1) {
				and_item[0] = or_item[0];
			} else {
				and_item[0] = mgr.mk_or(option, or_item);
			}
			expr_ref implyR(mgr.mk_and(pos, and_item), mgr);
			assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
		} else {
			TRACE("t_str", tout << "STOP: Should not split two EQ concats." << std::endl;);
		}
	} // (splitType == -1)
}

/*************************************************************
 * Type 3: concat(x, y) = concat("str", n)
 *************************************************************/
bool theory_str::is_concat_eq_type3(expr * concatAst1, expr * concatAst2) {
    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    if (m_strutil.is_string(v1_arg0) && (!m_strutil.is_string(v1_arg1))
            && (!m_strutil.is_string(v2_arg0)) && (!m_strutil.is_string(v2_arg1))) {
        return true;
    } else if (m_strutil.is_string(v2_arg0) && (!m_strutil.is_string(v2_arg1))
            && (!m_strutil.is_string(v1_arg0)) && (!m_strutil.is_string(v1_arg1))) {
        return true;
    } else {
        return false;
    }
}

void theory_str::process_concat_eq_type3(expr * concatAst1, expr * concatAst2) {
    ast_manager & mgr = get_manager();
    context & ctx = get_context();
    TRACE("t_str_detail", tout << "process_concat_eq TYPE 3" << std::endl
            << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
            << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
    );

    if (!is_concat(to_app(concatAst1))) {
        TRACE("t_str_detail", tout << "concatAst1 is not a concat function" << std::endl;);
        return;
    }
    if (!is_concat(to_app(concatAst2))) {
        TRACE("t_str_detail", tout << "concatAst2 is not a concat function" << std::endl;);
        return;
    }

    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    expr * x = NULL;
    expr * y = NULL;
    expr * strAst = NULL;
    expr * n = NULL;

    if (m_strutil.is_string(v1_arg0) && !m_strutil.is_string(v2_arg0)) {
        strAst = v1_arg0;
        n = v1_arg1;
        x = v2_arg0;
        y = v2_arg1;
    } else {
        strAst = v2_arg0;
        n = v2_arg1;
        x = v1_arg0;
        y = v1_arg1;
    }

    const char * strValue_tmp = 0;
    m_strutil.is_string(strAst, &strValue_tmp);
    std::string strValue(strValue_tmp);
    // TODO integer theory interaction
    /*
    int x_len = getLenValue(t, x);
    int y_len = getLenValue(t, y);
    int str_len = getLenValue(t, strAst);
    int n_len = getLenValue(t, n);
    */
    int x_len = -1;
    int y_len = -1;
    int str_len = -1;
    int n_len = -1;

    expr_ref xorFlag(mgr);
    expr_ref temp1(mgr);
    std::pair<expr*, expr*> key1(concatAst1, concatAst2);
    std::pair<expr*, expr*> key2(concatAst2, concatAst1);
    if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
        temp1 = mk_nonempty_str_var();
        xorFlag = mk_internal_xor_var();

        varForBreakConcat[key1][0] = temp1;
        varForBreakConcat[key1][1] = xorFlag;
    } else {
        if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
            temp1 = varForBreakConcat[key1][0];
            xorFlag = varForBreakConcat[key1][1];
        } else if (varForBreakConcat.find(key2) != varForBreakConcat.end()) {
            temp1 = varForBreakConcat[key2][0];
            xorFlag = varForBreakConcat[key2][1];
        }
    }



    int splitType = -1;
    if (x_len != -1) {
        if (x_len < str_len)
            splitType = 0;
        else if (x_len == str_len)
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

    TRACE("t_str_detail", tout << "Split type " << splitType << std::endl;);

    // Provide fewer split options when length information is available.
    if (splitType == 0) {
        NOT_IMPLEMENTED_YET(); // TODO
    }
    else if (splitType == 1) {
        NOT_IMPLEMENTED_YET(); // TODO
    }
    else if (splitType == 2) {
        NOT_IMPLEMENTED_YET(); // TODO
    }
    else {
        // Split type -1. We know nothing about the length...

        int optionTotal = 2 + strValue.length();
        expr ** or_item = alloc_svect(expr*, optionTotal);
        int option = 0;
        expr ** and_item = alloc_svect(expr*, (2 + 4 * optionTotal));
        int pos = 1;
        for (int i = 0; i <= (int) strValue.size(); i++) {
            std::string part1Str = strValue.substr(0, i);
            std::string part2Str = strValue.substr(i, strValue.size() - i);
            expr_ref cropStr(m_strutil.mk_string(part1Str), mgr);
            expr_ref suffixStr(m_strutil.mk_string(part2Str), mgr);
            expr_ref y_concat(mk_concat(suffixStr, n), mgr); // TODO concat axioms?

            if (can_two_nodes_eq(x, cropStr) && can_two_nodes_eq(y, y_concat)) {
                // break down option 3-1
                expr_ref x_eq_str(ctx.mk_eq_atom(x, cropStr), mgr);
                or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));
                and_item[pos++] = ctx.mk_eq_atom(or_item[option], x_eq_str);
                and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(y, y_concat));

                and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(x), mk_strlen(cropStr)));
                //        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, y_concat)));

                // adding length constraint for _ = constStr seems slowing things down.
                option++;
            }
        }

        expr_ref strAst_temp1(mk_concat(strAst, temp1), mgr);


        //--------------------------------------------------------
        // x cut n
        //--------------------------------------------------------
        if (can_two_nodes_eq(x, strAst_temp1)) {
            if (!avoidLoopCut || !(has_self_cut(x, n))) {
                // break down option 3-2
                or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));

                expr_ref temp1_y(mk_concat(temp1, y), mgr);
                and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(x, strAst_temp1));
                and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(n, temp1_y));

                and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(x),
                        m_autil.mk_add(mk_strlen(strAst), mk_strlen(temp1)) ));
                option++;

                add_cut_info_merge(temp1, ctx.get_scope_level(), x);
                add_cut_info_merge(temp1, ctx.get_scope_level(), n);
            } else {
                loopDetected = true;
                TRACE("t_str", tout << "AVOID LOOP: SKIPPED." << std::endl;);
                // TODO printCutVAR(x, n)
            }
        }


        if (option > 0) {
            if (option == 1) {
                and_item[0] = or_item[0];
            } else {
                and_item[0] = mgr.mk_or(option, or_item);
            }
            expr_ref implyR(mgr.mk_and(pos, and_item), mgr);
            assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
        } else {
            TRACE("t_str", tout << "STOP: should not split two eq. concats" << std::endl;);
        }
    }

}

/*************************************************************
 * Type 4: concat("str1", y) = concat("str2", n)
 *************************************************************/
bool theory_str::is_concat_eq_type4(expr * concatAst1, expr * concatAst2) {
    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    if (m_strutil.is_string(v1_arg0) && (!m_strutil.is_string(v1_arg1))
            && m_strutil.is_string(v2_arg0) && (!m_strutil.is_string(v2_arg1))) {
      return true;
    } else {
      return false;
    }
}

void theory_str::process_concat_eq_type4(expr * concatAst1, expr * concatAst2) {
    ast_manager & mgr = get_manager();
    context & ctx = get_context();
    TRACE("t_str_detail", tout << "process_concat_eq TYPE 4" << std::endl
            << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
            << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
    );

    if (!is_concat(to_app(concatAst1))) {
        TRACE("t_str_detail", tout << "concatAst1 is not a concat function" << std::endl;);
        return;
    }
    if (!is_concat(to_app(concatAst2))) {
        TRACE("t_str_detail", tout << "concatAst2 is not a concat function" << std::endl;);
        return;
    }

    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    expr * str1Ast = v1_arg0;
    expr * y = v1_arg1;
    expr * str2Ast = v2_arg0;
    expr * n = v2_arg1;

    const char *tmp = 0;
    m_strutil.is_string(str1Ast, &tmp);
    std::string str1Value(tmp);
    m_strutil.is_string(str2Ast, &tmp);
    std::string str2Value(tmp);

    int str1Len = str1Value.length();
    int str2Len = str2Value.length();

    int commonLen = (str1Len > str2Len) ? str2Len : str1Len;
    if (str1Value.substr(0, commonLen) != str2Value.substr(0, commonLen)) {
        TRACE("t_str_detail", tout << "Conflict: " << mk_ismt2_pp(concatAst1, mgr)
                << " has no common prefix with " << mk_ismt2_pp(concatAst2, mgr) << std::endl;);
        expr_ref toNegate(mgr.mk_not(ctx.mk_eq_atom(concatAst1, concatAst2)), mgr);
        assert_axiom(toNegate);
        return;
    } else {
        if (str1Len > str2Len) {
            std::string deltaStr = str1Value.substr(str2Len, str1Len - str2Len);
            expr_ref tmpAst(mk_concat(m_strutil.mk_string(deltaStr), y), mgr);
            if (!in_same_eqc(tmpAst, n)) {
                // break down option 4-1
                expr_ref implyR(ctx.mk_eq_atom(n, tmpAst), mgr);
                assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
            }
        } else if (str1Len == str2Len) {
            if (!in_same_eqc(n, y)) {
                //break down option 4-2
                expr_ref implyR(ctx.mk_eq_atom(n, y), mgr);
                assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
            }
        } else {
            std::string deltaStr = str2Value.substr(str1Len, str2Len - str1Len);
            expr_ref tmpAst(mk_concat(m_strutil.mk_string(deltaStr), n), mgr);
            if (!in_same_eqc(y, tmpAst)) {
                //break down option 4-3
                expr_ref implyR(ctx.mk_eq_atom(y, tmpAst), mgr);
                assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
            }
        }
    }
}

/*************************************************************
 *  case 5: concat(x, "str1") = concat(m, "str2")
 *************************************************************/
bool theory_str::is_concat_eq_type5(expr * concatAst1, expr * concatAst2) {
    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    if ((!m_strutil.is_string(v1_arg0)) && m_strutil.is_string(v1_arg1)
            && (!m_strutil.is_string(v2_arg0)) && m_strutil.is_string(v2_arg1)) {
        return true;
    } else {
        return false;
    }
}

void theory_str::process_concat_eq_type5(expr * concatAst1, expr * concatAst2) {
    ast_manager & mgr = get_manager();
    context & ctx = get_context();
    TRACE("t_str_detail", tout << "process_concat_eq TYPE 5" << std::endl
            << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
            << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
    );

    if (!is_concat(to_app(concatAst1))) {
        TRACE("t_str_detail", tout << "concatAst1 is not a concat function" << std::endl;);
        return;
    }
    if (!is_concat(to_app(concatAst2))) {
        TRACE("t_str_detail", tout << "concatAst2 is not a concat function" << std::endl;);
        return;
    }

    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    expr * x = v1_arg0;
    expr * str1Ast = v1_arg1;
    expr * m = v2_arg0;
    expr * str2Ast = v2_arg1;

    const char *tmp = 0;
    m_strutil.is_string(str1Ast, &tmp);
    std::string str1Value(tmp);
    m_strutil.is_string(str2Ast, &tmp);
    std::string str2Value(tmp);

    int str1Len = str1Value.length();
    int str2Len = str2Value.length();

    int cLen = (str1Len > str2Len) ? str2Len : str1Len;
    if (str1Value.substr(str1Len - cLen, cLen) != str2Value.substr(str2Len - cLen, cLen)) {
        TRACE("t_str_detail", tout << "Conflict: " << mk_ismt2_pp(concatAst1, mgr)
                << " has no common suffix with " << mk_ismt2_pp(concatAst2, mgr) << std::endl;);
        expr_ref toNegate(mgr.mk_not(ctx.mk_eq_atom(concatAst1, concatAst2)), mgr);
        assert_axiom(toNegate);
        return;
    } else {
        if (str1Len > str2Len) {
            std::string deltaStr = str1Value.substr(0, str1Len - str2Len);
            expr_ref x_deltaStr(mk_concat(x, m_strutil.mk_string(deltaStr)), mgr);
            if (!in_same_eqc(m, x_deltaStr)) {
                expr_ref implyR(ctx.mk_eq_atom(m, x_deltaStr), mgr);
                assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
            }
        } else if (str1Len == str2Len) {
            // test
            if (!in_same_eqc(x, m)) {
                expr_ref implyR(ctx.mk_eq_atom(x, m), mgr);
                assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
            }
        } else {
            std::string deltaStr = str2Value.substr(0, str2Len - str1Len);
            expr_ref m_deltaStr(mk_concat(m, m_strutil.mk_string(deltaStr)), mgr);
            if (!in_same_eqc(x, m_deltaStr)) {
                expr_ref implyR(ctx.mk_eq_atom(x, m_deltaStr), mgr);
                assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
            }
        }
    }
}

/*************************************************************
 *  case 6: concat("str1", y) = concat(m, "str2")
 *************************************************************/
bool theory_str::is_concat_eq_type6(expr * concatAst1, expr * concatAst2) {
    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

    if (m_strutil.is_string(v1_arg0) && (!m_strutil.is_string(v1_arg1))
            && (!m_strutil.is_string(v2_arg0)) && m_strutil.is_string(v2_arg1)) {
        return true;
    } else if (m_strutil.is_string(v2_arg0) && (!m_strutil.is_string(v2_arg1))
            && (!m_strutil.is_string(v1_arg0)) && m_strutil.is_string(v1_arg1)) {
        return true;
    } else {
        return false;
    }
}

void theory_str::process_concat_eq_type6(expr * concatAst1, expr * concatAst2) {
    ast_manager & mgr = get_manager();
    context & ctx = get_context();
    TRACE("t_str_detail", tout << "process_concat_eq TYPE 6" << std::endl
            << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
            << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
    );

    if (!is_concat(to_app(concatAst1))) {
        TRACE("t_str_detail", tout << "concatAst1 is not a concat function" << std::endl;);
        return;
    }
    if (!is_concat(to_app(concatAst2))) {
        TRACE("t_str_detail", tout << "concatAst2 is not a concat function" << std::endl;);
        return;
    }

    expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
    expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
    expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
    expr * v2_arg1 = to_app(concatAst2)->get_arg(1);


    expr * str1Ast = NULL;
    expr * y = NULL;
    expr * m = NULL;
    expr * str2Ast = NULL;

    if (m_strutil.is_string(v1_arg0)) {
        str1Ast = v1_arg0;
        y = v1_arg1;
        m = v2_arg0;
        str2Ast = v2_arg1;
    } else {
        str1Ast = v2_arg0;
        y = v2_arg1;
        m = v1_arg0;
        str2Ast = v1_arg1;
    }

    const char *tmp = 0;
    m_strutil.is_string(str1Ast, &tmp);
    std::string str1Value(tmp);
    m_strutil.is_string(str2Ast, &tmp);
    std::string str2Value(tmp);

    int str1Len = str1Value.length();
    int str2Len = str2Value.length();

    //----------------------------------------
    //(a)  |---str1---|----y----|
    //     |--m--|-----str2-----|
    //
    //(b)  |---str1---|----y----|
    //     |-----m----|--str2---|
    //
    //(c)  |---str1---|----y----|
    //     |------m------|-str2-|
    //----------------------------------------

    std::list<int> overlapLen;
    overlapLen.push_back(0);

    for (int i = 1; i <= str1Len && i <= str2Len; i++) {
        if (str1Value.substr(str1Len - i, i) == str2Value.substr(0, i))
            overlapLen.push_back(i);
    }

    //----------------------------------------------------------------
    expr * commonVar = NULL;
    expr * xorFlag = NULL;
    std::pair<expr*, expr*> key1(concatAst1, concatAst2);
    std::pair<expr*, expr*> key2(concatAst2, concatAst1);
    if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
        commonVar = mk_nonempty_str_var();
        xorFlag = mk_internal_xor_var();
        varForBreakConcat[key1][0] = commonVar;
        varForBreakConcat[key1][1] = xorFlag;
    } else {
        if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
            commonVar = varForBreakConcat[key1][0];
            xorFlag = varForBreakConcat[key1][1];
        } else {
            commonVar = varForBreakConcat[key2][0];
            xorFlag = varForBreakConcat[key2][1];
        }
    }

    expr ** or_item = alloc_svect(expr*, (overlapLen.size() + 1));
    int option = 0;
    expr ** and_item = alloc_svect(expr*, (1 + 4 * (overlapLen.size() + 1)));
    int pos = 1;

    if (!avoidLoopCut || !has_self_cut(m, y)) {
        or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));

        expr_ref str1_commonVar(mk_concat(str1Ast, commonVar), mgr);
        and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(m, str1_commonVar));

        expr_ref commonVar_str2(mk_concat(commonVar, str2Ast), mgr);
        and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(y, commonVar_str2));

        and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(m),
                m_autil.mk_add(mk_strlen(str1Ast), mk_strlen(commonVar)) ));

        //    addItems[0] = mk_length(t, commonVar);
        //    addItems[1] = mk_length(t, str2Ast);
        //    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), Z3_mk_add(ctx, 2, addItems)));

        option++;
    } else {
        loopDetected = true;
        TRACE("t_str", tout << "AVOID LOOP: SKIPPED." << std::endl;);
        // TODO printCutVAR(m, y)
    }

    for (std::list<int>::iterator itor = overlapLen.begin(); itor != overlapLen.end(); itor++) {
        int overLen = *itor;
        std::string prefix = str1Value.substr(0, str1Len - overLen);
        std::string suffix = str2Value.substr(overLen, str2Len - overLen);
        or_item[option] = ctx.mk_eq_atom(xorFlag, mk_int(option));

        expr_ref prefixAst(m_strutil.mk_string(prefix), mgr);
        expr_ref x_eq_prefix(ctx.mk_eq_atom(m, prefixAst), mgr);
        and_item[pos++] = ctx.mk_eq_atom(or_item[option], x_eq_prefix);

        and_item[pos++] = ctx.mk_eq_atom(or_item[option],
                ctx.mk_eq_atom(mk_strlen(m), mk_strlen(prefixAst)));

        // adding length constraint for _ = constStr seems slowing things down.

        expr_ref suffixAst(m_strutil.mk_string(suffix), mgr);
        expr_ref y_eq_suffix(ctx.mk_eq_atom(y, suffixAst), mgr);
        and_item[pos++] = ctx.mk_eq_atom(or_item[option], y_eq_suffix);

        and_item[pos++] = ctx.mk_eq_atom(or_item[option], ctx.mk_eq_atom(mk_strlen(y), mk_strlen(suffixAst)));

        option++;
    }

    //  case 6: concat("str1", y) = concat(m, "str2")
    and_item[0] = mgr.mk_or(option, or_item);
    expr_ref implyR(mgr.mk_and(pos, and_item), mgr);
    assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
}

/*
 * Look through the equivalence class of n to find a string constant.
 * Return that constant if it is found, and set hasEqcValue to true.
 * Otherwise, return n, and set hasEqcValue to false.
 */
expr * theory_str::get_eqc_value(expr * n, bool & hasEqcValue) {
	context & ctx = get_context();
	// I hope this works
	ctx.internalize(n, false);
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


        if (is_app(ex)) {
            app * ap = to_app(ex);
            if (is_concat(ap)) {
                // if ex is a concat, set up concat axioms later
                m_concat_axiom_todo.push_back(n);
            } else if (is_strlen(ap)) {
            	// if the argument is a variable,
            	// keep track of this for later, we'll need it during model gen
            	expr * var = ap->get_arg(0);
            	app * aVar = to_app(var);
            	if (aVar->get_num_args() == 0 && !is_string(aVar)) {
            		input_var_in_len.insert(var);
            	}
            } else if (ap->get_num_args() == 0 && !is_string(ap)) {
                // if ex is a variable, add it to our list of variables
                TRACE("t_str_detail", tout << "tracking variable " << mk_ismt2_pp(ap, get_manager()) << std::endl;);
                variable_set.insert(ex);
            }
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
    /*
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
    */

    TRACE("t_str", tout << "search started" << std::endl;);
    search_started = true;
}

void theory_str::new_eq_eh(theory_var x, theory_var y) {
    //TRACE("t_str_detail", tout << "new eq: v#" << x << " = v#" << y << std::endl;);
    TRACE("t_str", tout << "new eq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
    handle_equality(get_enode(x)->get_owner(), get_enode(y)->get_owner());

    TRACE("t_str_dump_assign", dump_assignments(););
}

void theory_str::new_diseq_eh(theory_var x, theory_var y) {
    //TRACE("t_str_detail", tout << "new diseq: v#" << x << " != v#" << y << std::endl;);
    TRACE("t_str", tout << "new diseq: " << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " != " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);

    TRACE("t_str_dump_assign", dump_assignments(););
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
    int sLevel = ctx.get_scope_level();
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

void theory_str::dump_assignments() {
	ast_manager & m = get_manager();
	context & ctx = get_context();
	TRACE("t_str_detail",
	tout << "dumping all assignments:" << std::endl;
	expr_ref_vector assignments(m);
	ctx.get_assignments(assignments);
	for (expr_ref_vector::iterator i = assignments.begin(); i != assignments.end(); ++i) {
		expr * ex = *i;
		tout << mk_ismt2_pp(ex, m) << std::endl;
	}
	);
}

void theory_str::classify_ast_by_type(expr * node, std::map<expr*, int> & varMap,
		std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap) {

	// check whether the node is a non-internal string variable;
	// testing set membership here bypasses several expensive checks
	if (variable_set.find(node) != variable_set.end()
			&& internal_variable_set.find(node) == internal_variable_set.end()) {
		varMap[node] = 1;
	}
	// check whether the node is a function that we want to inspect
	else if (is_app(node)) { // TODO
		app * aNode = to_app(node);
		if (is_strlen(aNode)) {
			// Length
			return;
		} else if (is_concat(aNode)) {
			expr * arg0 = aNode->get_arg(0);
			expr * arg1 = aNode->get_arg(1);
			bool arg0HasEq = false;
			bool arg1HasEq = false;
			expr * arg0Val = get_eqc_value(arg0, arg0HasEq);
			expr * arg1Val = get_eqc_value(arg1, arg1HasEq);

			int canskip = 0;
			if (arg0HasEq && arg0Val == m_strutil.mk_string("")) {
				canskip = 1;
			}
			if (canskip == 0 && arg1HasEq && arg1Val == m_strutil.mk_string("")) {
				canskip = 1;
			}
			if (canskip == 0 && concatMap.find(node) == concatMap.end()) {
				concatMap[node] = 1;
			}
		} else if (false) { // TODO is_unroll()
			// Unroll
			if (unrollMap.find(node) == unrollMap.end()) {
				unrollMap[node] = 1;
			}
		}
		// recursively visit all arguments
		for (unsigned i = 0; i < aNode->get_num_args(); ++i) {
			expr * arg = aNode->get_arg(i);
			classify_ast_by_type(arg, varMap, concatMap, unrollMap);
		}
	}
}

// NOTE: this function used to take an argument `Z3_ast node`;
// it was not used and so was removed from the signature
void theory_str::classify_ast_by_type_in_positive_context(std::map<expr*, int> & varMap,
		std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap) {

	context & ctx = get_context();
	ast_manager & m = get_manager();
	expr_ref_vector assignments(m);
	ctx.get_assignments(assignments);

	for (expr_ref_vector::iterator it = assignments.begin(); it != assignments.end(); ++it) {
		expr * argAst = *it;
		// the original code jumped through some hoops to check whether the AST node
		// is a function, then checked whether that function is "interesting".
		// however, the only thing that's considered "interesting" is an equality predicate.
		// so we bypass a huge amount of work by doing the following...

		if (m.is_eq(argAst)) {
			classify_ast_by_type(argAst, varMap, concatMap, unrollMap);
		}
	}
}

inline expr * theory_str::get_alias_index_ast(std::map<expr*, expr*> & aliasIndexMap, expr * node) {
  if (aliasIndexMap.find(node) != aliasIndexMap.end())
    return aliasIndexMap[node];
  else
    return node;
}

inline expr * theory_str::getMostLeftNodeInConcat(expr * node) {
	app * aNode = to_app(node);
	if (!is_concat(aNode)) {
		return node;
	} else {
		expr * concatArgL = aNode->get_arg(0);
		return getMostLeftNodeInConcat(concatArgL);
	}
}

inline expr * theory_str::getMostRightNodeInConcat(expr * node) {
	app * aNode = to_app(node);
	if (!is_concat(aNode)) {
		return node;
	} else {
		expr * concatArgR = aNode->get_arg(1);
		return getMostRightNodeInConcat(concatArgR);
	}
}

/*
 * Dependence analysis from current context assignment
 * - "freeVarMap" contains a set of variables that doesn't constrained by Concats.
 *    But it's possible that it's bounded by unrolls
 *    For the case of
 *    (1) var1 = unroll(r1, t1)
 *        var1 is in the freeVarMap
 *        > should unroll r1 for var1
 *    (2) var1 = unroll(r1, t1) /\ var1 = Concat(var2, var3)
 *        var2, var3 are all in freeVar
 *        > should split the unroll function so that var2 and var3 are bounded by new unrolls
 */
int theory_str::ctx_dep_analysis(std::map<expr*, int> & strVarMap, std::map<expr*, int> & freeVarMap,
		std::map<expr*, std::set<expr*> > & unrollGroupMap) {
	std::map<expr*, int> concatMap;
	std::map<expr*, int> unrollMap;
	std::map<expr*, expr*> aliasIndexMap;
	std::map<expr*, expr*> var_eq_constStr_map;
	std::map<expr*, expr*> concat_eq_constStr_map;
	std::map<expr*, std::map<expr*, int> > var_eq_concat_map;
	std::map<expr*, std::map<expr*, int> > var_eq_unroll_map;
	std::map<expr*, std::map<expr*, int> > concat_eq_concat_map;
	std::map<expr*, std::map<expr*, int> > depMap;

	context & ctx = get_context();
	ast_manager & m = get_manager();

	// note that the old API concatenated these assignments into
	// a massive conjunction; we may have the opportunity to avoid that here
	expr_ref_vector assignments(m);
	ctx.get_assignments(assignments);

	// Step 1: get variables / concat AST appearing in the context
	// the thing we iterate over should just be variable_set - internal_variable_set
	// so we avoid computing the set difference (but this might be slower)
	for(std::set<expr*>::iterator it = variable_set.begin(); it != variable_set.end(); ++it) {
		expr* var = *it;
		if (internal_variable_set.find(var) == internal_variable_set.end()) {
		    strVarMap[*it] = 1;
		}
	}
	classify_ast_by_type_in_positive_context(strVarMap, concatMap, unrollMap);

	// TODO unroll()
	/*
	std::map<Z3_ast, Z3_ast> aliasUnrollSet;
	std::map<Z3_ast, int>::iterator unrollItor = unrollMap.begin();
	for (; unrollItor != unrollMap.end(); unrollItor++) {
	    if (aliasUnrollSet.find(unrollItor->first) != aliasUnrollSet.end())
	        continue;
	    Z3_ast aRoot = NULL;
	    Z3_ast curr = unrollItor->first;
	    do {
	        if (isUnrollFunc(t, curr)) {
	            if (aRoot == NULL) {
	                aRoot = curr;
	            }
	            aliasUnrollSet[curr] = aRoot;
	        }
	        curr = Z3_theory_get_eqc_next(t, curr);
	    } while (curr != unrollItor->first);
	}

	for (unrollItor = unrollMap.begin(); unrollItor != unrollMap.end(); unrollItor++) {
	    Z3_ast unrFunc = unrollItor->first;
	    Z3_ast urKey = aliasUnrollSet[unrFunc];
	    unrollGroupMap[urKey].insert(unrFunc);
	}
	*/

	// Step 2: collect alias relation
	// e.g. suppose we have the equivalence class {x, y, z};
	// then we set aliasIndexMap[y] = x
	// and aliasIndexMap[z] = x

	std::map<expr*, int>::iterator varItor = strVarMap.begin();
	for (; varItor != strVarMap.end(); ++varItor) {
	    if (aliasIndexMap.find(varItor->first) != aliasIndexMap.end()) {
	        continue;
	    }
	    expr * aRoot = NULL;
	    expr * curr = varItor->first;
	    do {
	        if (variable_set.find(curr) != variable_set.end()) { // TODO internal_variable_set?
	            if (aRoot == NULL) {
	                aRoot = curr;
	            } else {
	                aliasIndexMap[curr] = aRoot;
	            }
	        }
	        // curr = get_eqc_next(curr);
	        enode * eqcNode = ctx.get_enode(curr);
	        eqcNode = eqcNode->get_next();
	        curr = eqcNode->get_owner();
	    } while (curr != varItor->first);
	}

	// Step 3: Collect interested cases

	varItor = strVarMap.begin();
	for (; varItor != strVarMap.end(); ++varItor) {
	    expr * deAliasNode = get_alias_index_ast(aliasIndexMap, varItor->first);
	    // Case 1: variable = string constant
	    // e.g. z = "str1" ::= var_eq_constStr_map[z] = "str1"

	    if (var_eq_constStr_map.find(deAliasNode) == var_eq_constStr_map.end()) {
	        bool nodeHasEqcValue = false;
	        expr * nodeValue = get_eqc_value(deAliasNode, nodeHasEqcValue);
	        if (nodeHasEqcValue) {
	            var_eq_constStr_map[deAliasNode] = nodeValue;
	        }
	    }

	    // Case 2: var_eq_concat
	    // e.g. z = concat("str1", b) ::= var_eq_concat[z][concat(c, "str2")] = 1
	    // var_eq_unroll
	    // e.g. z = unroll(...) ::= var_eq_unroll[z][unroll(...)] = 1

	    if (var_eq_concat_map.find(deAliasNode) == var_eq_concat_map.end()) {
	        enode * e_curr = ctx.get_enode(deAliasNode);
	        expr * curr = e_curr->get_next()->get_owner();
	        while (curr != deAliasNode) {
	            app * aCurr = to_app(curr);
	            // collect concat
	            if (is_concat(aCurr)) {
	                expr * arg0 = aCurr->get_arg(0);
	                expr * arg1 = aCurr->get_arg(1);
	                bool arg0HasEqcValue = false;
	                bool arg1HasEqcValue = false;
	                expr * arg0_value = get_eqc_value(arg0, arg0HasEqcValue);
	                expr * arg1_value = get_eqc_value(arg1, arg1HasEqcValue);

	                bool is_arg0_emptyStr = false;
	                if (arg0HasEqcValue) {
	                    const char * strval = 0;
	                    m_strutil.is_string(arg0_value, &strval);
	                    if (strcmp(strval, "") == 0) {
	                        is_arg0_emptyStr = true;
	                    }
	                }

	                bool is_arg1_emptyStr = false;
	                if (arg1HasEqcValue) {
	                    const char * strval = 0;
	                    m_strutil.is_string(arg1_value, &strval);
	                    if (strcmp(strval, "") == 0) {
	                        is_arg1_emptyStr = true;
	                    }
	                }

	                if (!is_arg0_emptyStr && !is_arg1_emptyStr) {
	                    var_eq_concat_map[deAliasNode][curr] = 1;
	                }
	            }
	            // TODO: collect unroll functions
	            /*
	            else if (isUnrollFunc(t, curr)) {
	                var_eq_unroll_map[deAliasNode][curr] = 1;
	            }
	            */

	            // curr = get_eqc_next(curr)
	            e_curr = ctx.get_enode(curr);
	            curr = e_curr->get_next()->get_owner();
	        }
	    }

	} // for(varItor in strVarMap)

	// --------------------------------------------------
	// * collect aliasing relation among eq concats
	//   e.g EQC={concat1, concat2, concat3}
	//       concats_eq_Index_map[concat2] = concat1
	//       concats_eq_Index_map[concat3] = concat1
	// --------------------------------------------------

	std::map<expr*, expr*> concats_eq_index_map;
	std::map<expr*, int>::iterator concatItor = concatMap.begin();
	for(; concatItor != concatMap.end(); ++concatItor) {
		if (concats_eq_index_map.find(concatItor->first) != concats_eq_index_map.end()) {
			continue;
		}
		expr * aRoot = NULL;
		expr * curr = concatItor->first;
		do {
			if (is_concat(to_app(curr))) {
				if (aRoot == NULL) {
					aRoot = curr;
				} else {
					concats_eq_index_map[curr] = aRoot;
				}
			}
			// curr = get_eqc_next(curr);
			enode * e_curr = ctx.get_enode(curr);
			curr = e_curr->get_next()->get_owner();
		} while (curr != concatItor->first);
	}

	concatItor = concatMap.begin();
	for(; concatItor != concatMap.end(); ++concatItor) {
		expr * deAliasConcat = NULL;
		if (concats_eq_index_map.find(concatItor->first) != concats_eq_index_map.end()) {
			deAliasConcat = concats_eq_index_map[concatItor->first];
		} else {
			deAliasConcat = concatItor->first;
		}

		// (3) concat_eq_conststr, e.g. concat(a,b) = "str1"
		if (concat_eq_constStr_map.find(deAliasConcat) == concat_eq_constStr_map.end()) {
			bool nodeHasEqcValue = false;
			expr * nodeValue = get_eqc_value(deAliasConcat, nodeHasEqcValue);
			if (nodeHasEqcValue) {
				concat_eq_constStr_map[deAliasConcat] = nodeValue;
			}
		}

		// (4) concat_eq_concat, e.g.
		// concat(a,b) = concat("str1", c) AND z = concat(a,b) AND z = concat(e,f)
		if (concat_eq_concat_map.find(deAliasConcat) == concat_eq_concat_map.end()) {
			expr * curr = deAliasConcat;
			do {
				if (is_concat(to_app(curr))) {
					// curr cannot be reduced
					if (concatMap.find(curr) != concatMap.end()) {
						concat_eq_concat_map[deAliasConcat][curr] = 1;
					}
				}
				// curr = get_eqc_next(curr);
				enode * e_curr = ctx.get_enode(curr);
				curr = e_curr->get_next()->get_owner();
			} while (curr != deAliasConcat);
		}
	}

	// TODO this would be a great place to print some debugging information

	// TODO compute Contains
	/*
	if (containPairBoolMap.size() > 0) {
		computeContains(t, aliasIndexMap, concats_eq_Index_map, var_eq_constStr_map, concat_eq_constStr_map, var_eq_concat_map);
	}
	*/

	// step 4: dependence analysis

	// (1) var = string constant
	for (std::map<expr*, expr*>::iterator itor = var_eq_constStr_map.begin();
			itor != var_eq_constStr_map.end(); ++itor) {
		expr * var = get_alias_index_ast(aliasIndexMap, itor->first);
		expr * strAst = itor->second;
		depMap[var][strAst] = 1;
	}

	// (2) var = concat
	for (std::map<expr*, std::map<expr*, int> >::iterator itor = var_eq_concat_map.begin();
			itor != var_eq_concat_map.end(); ++itor) {
		expr * var = get_alias_index_ast(aliasIndexMap, itor->first);
		for (std::map<expr*, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); ++itor1) {
			expr * concat = itor1->first;
			std::map<expr*, int> inVarMap;
			std::map<expr*, int> inConcatMap;
			std::map<expr*, int> inUnrollMap;
			classify_ast_by_type(concat, inVarMap, inConcatMap, inUnrollMap);
			for (std::map<expr*, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); ++itor2) {
				expr * varInConcat = get_alias_index_ast(aliasIndexMap, itor2->first);
				if (!(depMap[var].find(varInConcat) != depMap[var].end() && depMap[var][varInConcat] == 1)) {
					depMap[var][varInConcat] = 2;
				}
			}
		}
	}

	for (std::map<expr*, std::map<expr*, int> >::iterator itor = var_eq_unroll_map.begin();
		itor != var_eq_unroll_map.end(); itor++) {
		expr * var = get_alias_index_ast(aliasIndexMap, itor->first);
		for (std::map<expr*, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
			expr * unrollFunc = itor1->first;
			std::map<expr*, int> inVarMap;
			std::map<expr*, int> inConcatMap;
			std::map<expr*, int> inUnrollMap;
			classify_ast_by_type(unrollFunc, inVarMap, inConcatMap, inUnrollMap);
			for (std::map<expr*, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++) {
				expr * varInFunc = get_alias_index_ast(aliasIndexMap, itor2->first);

				TRACE("t_str_detail", tout << "var in unroll = " <<
						mk_ismt2_pp(itor2->first, m) << std::endl
						<< "dealiased var = " << mk_ismt2_pp(varInFunc, m) << std::endl;);

				// it's possible that we have both (Unroll $$_regVar_0 $$_unr_0) /\ (Unroll abcd $$_unr_0),
				// while $$_regVar_0 = "abcd"
				// have to exclude such cases
				bool varHasValue = false;
				get_eqc_value(varInFunc, varHasValue);
				if (varHasValue)
					continue;

				if (depMap[var].find(varInFunc) == depMap[var].end()) {
					depMap[var][varInFunc] = 6;
				}
			}
		}
	}

	// (3) concat = string constant
	for (std::map<expr*, expr*>::iterator itor = concat_eq_constStr_map.begin();
			itor != concat_eq_constStr_map.end(); itor++) {
		expr * concatAst = itor->first;
		expr * constStr = itor->second;
		std::map<expr*, int> inVarMap;
		std::map<expr*, int> inConcatMap;
		std::map<expr*, int> inUnrollMap;
		classify_ast_by_type(concatAst, inVarMap, inConcatMap, inUnrollMap);
		for (std::map<expr*, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++) {
			expr * varInConcat = get_alias_index_ast(aliasIndexMap, itor2->first);
			if (!(depMap[varInConcat].find(constStr) != depMap[varInConcat].end() && depMap[varInConcat][constStr] == 1))
				depMap[varInConcat][constStr] = 3;
		}
	}

	// (4) equivalent concats
	//     - possibility 1 : concat("str", v1) = concat(concat(v2, v3), v4) = concat(v5, v6)
	//         ==> v2, v5 are constrained by "str"
	//     - possibliity 2 : concat(v1, "str") = concat(v2, v3) = concat(v4, v5)
	//         ==> v2, v4 are constrained by "str"
	//--------------------------------------------------------------

	std::map<expr*, expr*> mostLeftNodes;
	std::map<expr*, expr*> mostRightNodes;

	std::map<expr*, int> mLIdxMap;
	std::map<int, std::set<expr*> > mLMap;
	std::map<expr*, int> mRIdxMap;
	std::map<int, std::set<expr*> > mRMap;
	std::set<expr*> nSet;

	for (std::map<expr*, std::map<expr*, int> >::iterator itor = concat_eq_concat_map.begin();
			itor != concat_eq_concat_map.end(); itor++) {
		mostLeftNodes.clear();
		mostRightNodes.clear();

		expr * mLConst = NULL;
		expr * mRConst = NULL;

		for (std::map<expr*, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
			expr * concatNode = itor1->first;
			expr * mLNode = getMostLeftNodeInConcat(concatNode);
			const char * strval;
			if (m_strutil.is_string(to_app(mLNode), & strval)) {
				if (mLConst == NULL && strcmp(strval, "") != 0) {
					mLConst = mLNode;
				}
			} else {
				mostLeftNodes[mLNode] = concatNode;
			}

			expr * mRNode = getMostRightNodeInConcat(concatNode);
			if (m_strutil.is_string(to_app(mRNode), & strval)) {
				if (mRConst == NULL && strcmp(strval, "") != 0) {
					mRConst = mRNode;
				}
			} else {
				mostRightNodes[mRNode] = concatNode;
			}
		}

		if (mLConst != NULL) {
			// -------------------------------------------------------------------------------------
			// The left most variable in a concat is constrained by a constant string in eqc concat
			// -------------------------------------------------------------------------------------
			// e.g. Concat(x, ...) = Concat("abc", ...)
			// -------------------------------------------------------------------------------------
			for (std::map<expr*, expr*>::iterator itor1 = mostLeftNodes.begin();
					itor1 != mostLeftNodes.end(); itor1++) {
				expr * deVar = get_alias_index_ast(aliasIndexMap, itor1->first);
				if (depMap[deVar].find(mLConst) == depMap[deVar].end() || depMap[deVar][mLConst] != 1) {
					depMap[deVar][mLConst] = 4;
				}
			}
		}

		{
			// -------------------------------------------------------------------------------------
			// The left most variables in eqc concats are constrained by each other
			// -------------------------------------------------------------------------------------
			// e.g. concat(x, ...) = concat(u, ...) = ...
			//      x and u are constrained by each other
			// -------------------------------------------------------------------------------------
			nSet.clear();
			std::map<expr*, expr*>::iterator itl = mostLeftNodes.begin();
			for (; itl != mostLeftNodes.end(); itl++) {
				bool lfHasEqcValue = false;
				get_eqc_value(itl->first, lfHasEqcValue);
				if (lfHasEqcValue)
					continue;
				expr * deVar = get_alias_index_ast(aliasIndexMap, itl->first);
				nSet.insert(deVar);
			}

			if (nSet.size() > 1) {
				int lId = -1;
				for (std::set<expr*>::iterator itor2 = nSet.begin(); itor2 != nSet.end(); itor2++) {
					if (mLIdxMap.find(*itor2) != mLIdxMap.end()) {
						lId = mLIdxMap[*itor2];
						break;
					}
				}
				if (lId == -1)
					lId = mLMap.size();
				for (std::set<expr*>::iterator itor2 = nSet.begin(); itor2 != nSet.end(); itor2++) {
					bool itorHasEqcValue = false;
					get_eqc_value(*itor2, itorHasEqcValue);
					if (itorHasEqcValue)
						continue;
					mLIdxMap[*itor2] = lId;
					mLMap[lId].insert(*itor2);
				}
			}
		}

		if (mRConst != NULL) {
			for (std::map<expr*, expr*>::iterator itor1 = mostRightNodes.begin();
					itor1 != mostRightNodes.end(); itor1++) {
				expr * deVar = get_alias_index_ast(aliasIndexMap, itor1->first);
				if (depMap[deVar].find(mRConst) == depMap[deVar].end() || depMap[deVar][mRConst] != 1) {
					depMap[deVar][mRConst] = 5;
				}
			}
		}

		{
			nSet.clear();
			std::map<expr*, expr*>::iterator itr = mostRightNodes.begin();
			for (; itr != mostRightNodes.end(); itr++) {
				expr * deVar = get_alias_index_ast(aliasIndexMap, itr->first);
				nSet.insert(deVar);
			}
			if (nSet.size() > 1) {
				int rId = -1;
				std::set<expr*>::iterator itor2 = nSet.begin();
				for (; itor2 != nSet.end(); itor2++) {
					if (mRIdxMap.find(*itor2) != mRIdxMap.end()) {
						rId = mRIdxMap[*itor2];
						break;
					}
				}
				if (rId == -1)
					rId = mRMap.size();
				for (itor2 = nSet.begin(); itor2 != nSet.end(); itor2++) {
					bool rHasEqcValue = false;
					get_eqc_value(*itor2, rHasEqcValue);
					if (rHasEqcValue)
						continue;
					mRIdxMap[*itor2] = rId;
					mRMap[rId].insert(*itor2);
				}
			}
		}
	}

	// TODO this would be a great place to print the dependence map

	// step, errr, 5: compute free variables based on the dependence map

	// the case dependence map is empty, every var in VarMap is free
	//---------------------------------------------------------------
	// remove L/R most var in eq concat since they are constrained with each other
	std::map<expr*, std::map<expr*, int> > lrConstrainedMap;
	for (std::map<int, std::set<expr*> >::iterator itor = mLMap.begin(); itor != mLMap.end(); itor++) {
		for (std::set<expr*>::iterator it1 = itor->second.begin(); it1 != itor->second.end(); it1++) {
			std::set<expr*>::iterator it2 = it1;
			it2++;
			for (; it2 != itor->second.end(); it2++) {
				expr * n1 = *it1;
				expr * n2 = *it2;
				lrConstrainedMap[n1][n2] = 1;
				lrConstrainedMap[n2][n1] = 1;
			}
		}
	}
	for (std::map<int, std::set<expr*> >::iterator itor = mRMap.begin(); itor != mRMap.end(); itor++) {
		for (std::set<expr*>::iterator it1 = itor->second.begin(); it1 != itor->second.end(); it1++) {
			std::set<expr*>::iterator it2 = it1;
			it2++;
			for (; it2 != itor->second.end(); it2++) {
				expr * n1 = *it1;
				expr * n2 = *it2;
				lrConstrainedMap[n1][n2] = 1;
				lrConstrainedMap[n2][n1] = 1;
			}
		}
	}

	if (depMap.size() == 0) {
		std::map<expr*, int>::iterator itor = strVarMap.begin();
		for (; itor != strVarMap.end(); itor++) {
			expr * var = get_alias_index_ast(aliasIndexMap, itor->first);
			if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
				freeVarMap[var] = 1;
			} else {
				int lrConstainted = 0;
				std::map<expr*, int>::iterator lrit = freeVarMap.begin();
				for (; lrit != freeVarMap.end(); lrit++) {
					if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
						lrConstainted = 1;
						break;
					}
				}
				if (lrConstainted == 0) {
					freeVarMap[var] = 1;
				}
			}
		}
	} else {
		// if the keys in aliasIndexMap are not contained in keys in depMap, they are free
		// e.g.,  x= y /\ x = z /\ t = "abc"
		//        aliasIndexMap[y]= x, aliasIndexMap[z] = x
		//        depMap        t ~ "abc"(1)
		//        x should be free
		std::map<expr*, int>::iterator itor2 = strVarMap.begin();
		for (; itor2 != strVarMap.end(); itor2++) {
			if (aliasIndexMap.find(itor2->first) != aliasIndexMap.end()) {
				expr * var = aliasIndexMap[itor2->first];
				if (depMap.find(var) == depMap.end()) {
					if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
						freeVarMap[var] = 1;
					} else {
						int lrConstainted = 0;
						std::map<expr*, int>::iterator lrit = freeVarMap.begin();
						for (; lrit != freeVarMap.end(); lrit++) {
							if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
								lrConstainted = 1;
								break;
							}
						}
						if (lrConstainted == 0) {
							freeVarMap[var] = 1;
						}
					}
				}
			} else if (aliasIndexMap.find(itor2->first) == aliasIndexMap.end()) {
				// if a variable is not in aliasIndexMap and not in depMap, it's free
				if (depMap.find(itor2->first) == depMap.end()) {
					expr * var = itor2->first;
					if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
						freeVarMap[var] = 1;
					} else {
						int lrConstainted = 0;
						std::map<expr*, int>::iterator lrit = freeVarMap.begin();
						for (; lrit != freeVarMap.end(); lrit++) {
							if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
								lrConstainted = 1;
								break;
							}
						}
						if (lrConstainted == 0) {
							freeVarMap[var] = 1;
						}
					}
				}
			}
		}

		std::map<expr*, std::map<expr*, int> >::iterator itor = depMap.begin();
		for (; itor != depMap.end(); itor++) {
			for (std::map<expr*, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
				if (variable_set.find(itor1->first) != variable_set.end()) { // expr type = var
					expr * var = get_alias_index_ast(aliasIndexMap, itor1->first);
					// if a var is dep on itself and all dependence are type 2, it's a free variable
					// e.g {y --> x(2), y(2), m --> m(2), n(2)} y,m are free
					{
						if (depMap.find(var) == depMap.end()) {
							if (freeVarMap.find(var) == freeVarMap.end()) {
								if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
									freeVarMap[var] = 1;
								} else {
									int lrConstainted = 0;
									std::map<expr*, int>::iterator lrit = freeVarMap.begin();
									for (; lrit != freeVarMap.end(); lrit++) {
										if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
											lrConstainted = 1;
											break;
										}
									}
									if (lrConstainted == 0) {
										freeVarMap[var] = 1;
									}
								}

							} else {
								freeVarMap[var] = freeVarMap[var] + 1;
							}
						}
					}
				}
			}
		}
	}

	return 0;
}

final_check_status theory_str::final_check_eh() {
    context & ctx = get_context();
    ast_manager & m = get_manager();

    TRACE("t_str", tout << "final check" << std::endl;);
    TRACE("t_str_detail", dump_assignments(););

    // run dependence analysis to find free string variables
    std::map<expr*, int> varAppearInAssign;
    std::map<expr*, int> freeVar_map;
    std::map<expr*, std::set<expr*> > unrollGroup_map;
    int conflictInDep = ctx_dep_analysis(varAppearInAssign, freeVar_map, unrollGroup_map);
    if (conflictInDep == -1) {
    	// return Z3_TRUE;
    	return FC_DONE;
    }

    // Check every variable to see if it's eq. to some string constant.
    // If not, mark it as free.
    bool needToAssignFreeVars = false;
    std::set<expr*> free_variables;
    TRACE("t_str_detail", tout << variable_set.size() << " variables in variable_set" << std::endl;);
    for (std::set<expr*>::iterator it = variable_set.begin(); it != variable_set.end(); ++it) {
        TRACE("t_str_detail", tout << "checking eqc of variable " << mk_ismt2_pp(*it, m) << std::endl;);
        bool has_eqc_value = false;
        get_eqc_value(*it, has_eqc_value);
        if (!has_eqc_value) {
            needToAssignFreeVars = true;
            free_variables.insert(*it);
        }
    }

    if (!needToAssignFreeVars) {
        TRACE("t_str", tout << "All variables are assigned. Done!" << std::endl;);
        return FC_DONE;
    }

    // -----------------------------------------------------------
    // variables in freeVar are those not bounded by Concats
    // classify variables in freeVarMap:
    // (1) freeVar = unroll(r1, t1)
    // (2) vars are not bounded by either concat or unroll
    // -----------------------------------------------------------
    std::map<expr*, std::set<expr*> > fv_unrolls_map;
    std::set<expr*> tmpSet;
    expr * constValue = NULL;
    for (std::map<expr*, int>::iterator fvIt2 = freeVar_map.begin(); fvIt2 != freeVar_map.end(); fvIt2++) {
    	expr * var = fvIt2->first;
    	tmpSet.clear();
    	get_eqc_allUnroll(var, constValue, tmpSet);
    	if (tmpSet.size() > 0) {
    		fv_unrolls_map[var] = tmpSet;
    	}
    }
    // erase var bounded by an unroll function from freeVar_map
    for (std::map<expr*, std::set<expr*> >::iterator fvIt3 = fv_unrolls_map.begin();
    		fvIt3 != fv_unrolls_map.end(); fvIt3++) {
    	expr * var = fvIt3->first;
    	freeVar_map.erase(var);
    }

    // collect the case:
    //   * Concat(X, Y) = unroll(r1, t1) /\ Concat(X, Y) = unroll(r2, t2)
    //     concatEqUnrollsMap[Concat(X, Y)] = {unroll(r1, t1), unroll(r2, t2)}

    std::map<expr*, std::set<expr*> > concatEqUnrollsMap;
    for (std::map<expr*, std::set<expr*> >::iterator urItor = unrollGroup_map.begin();
    		urItor != unrollGroup_map.end(); urItor++) {
    	expr * unroll = urItor->first;
    	expr * curr = unroll;
    	do {
    		if (is_concat(to_app(curr))) {
    			concatEqUnrollsMap[curr].insert(unroll);
    			concatEqUnrollsMap[curr].insert(unrollGroup_map[unroll].begin(), unrollGroup_map[unroll].end());
    		}
    		enode * e_curr = ctx.get_enode(curr);
    		curr = e_curr->get_next()->get_owner();
    		// curr = get_eqc_next(curr);
    	} while (curr != unroll);
    }

    std::map<expr*, std::set<expr*> > concatFreeArgsEqUnrollsMap;
    std::set<expr*> fvUnrollSet;
    for (std::map<expr*, std::set<expr*> >::iterator concatItor = concatEqUnrollsMap.begin();
    		concatItor != concatEqUnrollsMap.end(); concatItor++) {
    	expr * concat = concatItor->first;
    	expr * concatArg1 = to_app(concat)->get_arg(0);
    	expr * concatArg2 = to_app(concat)->get_arg(1);
    	bool arg1Bounded = false;
    	bool arg2Bounded = false;
    	// arg1
		if (variable_set.find(concatArg1) != variable_set.end()) {
			if (freeVar_map.find(concatArg1) == freeVar_map.end()) {
				arg1Bounded = true;
			} else {
				fvUnrollSet.insert(concatArg1);
			}
		} else if (is_concat(to_app(concatArg1))) {
			if (concatEqUnrollsMap.find(concatArg1) == concatEqUnrollsMap.end()) {
				arg1Bounded = true;
			}
		}
		// arg2
		if (variable_set.find(concatArg2) != variable_set.end()) {
			if (freeVar_map.find(concatArg2) == freeVar_map.end()) {
				arg2Bounded = true;
			} else {
				fvUnrollSet.insert(concatArg2);
			}
		} else if (is_concat(to_app(concatArg2))) {
			if (concatEqUnrollsMap.find(concatArg2) == concatEqUnrollsMap.end()) {
				arg2Bounded = true;
			}
		}
		if (!arg1Bounded && !arg2Bounded) {
			concatFreeArgsEqUnrollsMap[concat].insert(
					concatEqUnrollsMap[concat].begin(),
					concatEqUnrollsMap[concat].end());
		}
    }
    for (std::set<expr*>::iterator vItor = fvUnrollSet.begin(); vItor != fvUnrollSet.end(); vItor++) {
    	freeVar_map.erase(*vItor);
    }

    // Assign free variables
    std::set<expr*> fSimpUnroll;

    constValue = NULL;

    // TODO this would be a great place to print debugging information

    // TODO process_concat_eq_unroll()
    /*
    for (std::map<expr*, std::set<expr*> >::iterator fvIt2 = concatFreeArgsEqUnrollsMap.begin();
    		fvIt2 != concatFreeArgsEqUnrollsMap.end(); fvIt2++) {
    	expr * concat = fvIt2->first;
    	for (std::set<expr*>::iterator urItor = fvIt2->second.begin(); urItor != fvIt2->second.end(); urItor++) {
    		Z3_ast unroll = *urItor;
    		processConcatEqUnroll(concat, unroll);
    	}
    }
    */

    // --------
    // experimental free variable assignment - begin
    //   * special handling for variables that are not used in concat
    // --------
    bool testAssign = true;
    if (!testAssign) {
    	for (std::map<expr*, int>::iterator fvIt = freeVar_map.begin(); fvIt != freeVar_map.end(); fvIt++) {
    		expr * freeVar = fvIt->first;
    		/*
    		std::string vName = std::string(Z3_ast_to_string(ctx, freeVar));
    		if (vName.length() >= 9 && vName.substr(0, 9) == "$$_regVar") {
    			continue;
    		}
    		*/
    		// TODO if this variable represents a regular expression, continue
    		expr * toAssert = gen_len_val_options_for_free_var(freeVar, NULL, "");
    		if (toAssert != NULL) {
    			assert_axiom(toAssert);
    		}
    	}
    } else {
    	process_free_var(freeVar_map);
    }
    // experimental free variable assignment - end

    // TODO more unroll stuff
    /*
    for (std::map<expr*, std::set<expr*> >::iterator fvIt1 = fv_unrolls_map.begin();
    		fvIt1 != fv_unrolls_map.end(); fvIt1++) {
    	Z3_ast var = fvIt1->first;
    	fSimpUnroll.clear();
    	get_eqc_simpleUnroll(t, var, constValue, fSimpUnroll);
    	if (fSimpUnroll.size() == 0) {
    		genAssignUnrollReg(t, fv_unrolls_map[var]);
    	} else {
    		Z3_ast toAssert = genAssignUnrollStr2Reg(t, var, fSimpUnroll);
    		if (toAssert != NULL) {
    			addAxiom(t, toAssert, __LINE__);
    		}
    	}
    }
    */

    return FC_CONTINUE; // since by this point we've added axioms
}

inline std::string int_to_string(int i) {
	std::stringstream ss;
	ss << i;
	return ss.str();
}

inline std::string longlong_to_string(long long i) {
  std::stringstream ss;
  ss << i;
  return ss.str();
}

void theory_str::print_value_tester_list(svector<std::pair<int, expr*> > & testerList) {
	ast_manager & m = get_manager();
	TRACE("t_str_detail",
		int ss = testerList.size();
		tout << "valueTesterList = {";
		for (int i = 0; i < ss; ++i) {
			if (i % 4 == 0) {
				tout << std::endl;
			}
			tout << "(" << testerList[i].first << ", ";
			tout << mk_ismt2_pp(testerList[i].second, m);
			tout << "), ";
		}
		tout << std::endl << "}" << std::endl;
	);
}

std::string theory_str::gen_val_string(int len, int_vector & encoding) {
    SASSERT(charSetSize > 0);
    SASSERT(char_set != NULL);

    std::string re = std::string(len, char_set[0]);
    for (int i = 0; i < (int) encoding.size() - 1; i++) {
        int idx = encoding[i];
        re[len - 1 - i] = char_set[idx];
    }
    return re;
}

/*
 * The return value indicates whether we covered the search space.
 *   - If the next encoding is valid, return false
 *   - Otherwise, return true
 */
bool theory_str::get_next_val_encode(int_vector & base, int_vector & next) {
	SASSERT(charSetSize > 0);

    int s = 0;
    int carry = 0;
    next.reset();

    for (int i = 0; i < (int) base.size(); i++) {
        if (i == 0) {
            s = base[i] + 1;
            carry = s / charSetSize;
            s = s % charSetSize;
            next.push_back(s);
        } else {
            s = base[i] + carry;
            carry = s / charSetSize;
            s = s % charSetSize;
            next.push_back(s);
        }
    }
    if (next[next.size() - 1] > 0) {
        next.reset();
        return true;
    } else {
        return false;
    }
}

expr * theory_str::gen_val_options(expr * freeVar, expr * len_indicator, expr * val_indicator,
		std::string lenStr, int tries) {
	ast_manager & m = get_manager();

	int distance = 32;

	// ----------------------------------------------------------------------------------------
	// generate value options encoding
	// encoding is a vector of size (len + 1)
	// e.g, len = 2,
	//      encoding {1, 2, 0} means the value option is "charSet[2]"."charSet[1]"
	//      the last item in the encoding indicates whether the whole space is covered
	//      for example, if the charSet = {a, b}. All valid encodings are
	//        {0, 0, 0}, {1, 0, 0}, {0, 1, 0}, {1, 1, 0}
	//      if add 1 to the last one, we get
	//        {0, 0, 1}
	//      the last item "1" shows this is not a valid encoding, and we have covered all space
	// ----------------------------------------------------------------------------------------
	int len = atoi(lenStr.c_str());
	bool coverAll = false;
	svector<int_vector> options;
	int_vector base;

	TRACE("t_str_detail", tout
			<< "freeVar = " << mk_ismt2_pp(freeVar, m) << std::endl
			<< "len_indicator = " << mk_ismt2_pp(len_indicator, m) << std::endl
			<< "val_indicator = " << mk_ismt2_pp(val_indicator, m) << std::endl
			<< "lenstr = " << lenStr << std::endl
			<< "tries = " << tries << std::endl
			;);

	if (tries == 0) {
		base = int_vector(len + 1, 0);
		coverAll = false;
	} else {
		expr * lastestValIndi = fvar_valueTester_map[freeVar][len][tries - 1].second;
		TRACE("t_str_detail", tout << "last value tester = " << mk_ismt2_pp(lastestValIndi, m) << std::endl;);
		coverAll = get_next_val_encode(val_range_map[lastestValIndi], base);
	}

	long long l = (tries) * distance;
	long long h = l;
	for (int i = 0; i < distance; i++) {
		if (coverAll)
			break;
		options.push_back(base);
		h++;
		coverAll = get_next_val_encode(options[options.size() - 1], base);
	}
	val_range_map[val_indicator] = options[options.size() - 1];

	TRACE("t_str_detail",
			tout << "value tester encoding " << "{" << std::endl;
		    int_vector vec = val_range_map[val_indicator];

		    for (int_vector::iterator it = vec.begin(); it != vec.end(); ++it) {
		    	tout << *it << std::endl;
		    }
			tout << "}" << std::endl;
	);

	// ----------------------------------------------------------------------------------------

	ptr_vector<expr> orList;
	ptr_vector<expr> andList;

	for (long long i = l; i < h; i++) {
		orList.push_back(m.mk_eq(val_indicator, m_strutil.mk_string(longlong_to_string(i).c_str()) ));
		std::string aStr = gen_val_string(len, options[i - l]);
		expr * strAst = m_strutil.mk_string(aStr);
		andList.push_back(m.mk_eq(orList[orList.size() - 1], m.mk_eq(freeVar, strAst)));
	}
	if (!coverAll) {
		orList.push_back(m.mk_eq(val_indicator, m_strutil.mk_string("more")));
	}

	expr ** or_items = alloc_svect(expr*, orList.size());
	expr ** and_items = alloc_svect(expr*, andList.size() + 1);

	for (int i = 0; i < (int) orList.size(); i++) {
		or_items[i] = orList[i];
	}
	if (orList.size() > 1)
		and_items[0] = m.mk_or(orList.size(), or_items);
	else
		and_items[0] = or_items[0];

	for (int i = 0; i < (int) andList.size(); i++) {
		and_items[i + 1] = andList[i];
	}
	expr * valTestAssert = m.mk_and(andList.size() + 1, and_items);

	// ---------------------------------------
	// If the new value tester is $$_val_x_16_i
	// Should add ($$_len_x_j = 16) /\ ($$_val_x_16_i = "more")
	// ---------------------------------------
	andList.reset();
	andList.push_back(m.mk_eq(len_indicator, m_strutil.mk_string(lenStr.c_str())));
	for (int i = 0; i < tries; i++) {
		expr * vTester = fvar_valueTester_map[freeVar][len][i].second;
		if (vTester != val_indicator)
			andList.push_back(m.mk_eq(vTester, m_strutil.mk_string("more")));
	}
	expr * assertL = NULL;
	if (andList.size() == 1) {
		assertL = andList[0];
	} else {
		expr ** and_items = alloc_svect(expr*, andList.size());
		for (int i = 0; i < (int) andList.size(); i++) {
			and_items[i] = andList[i];
		}
		assertL = m.mk_and(andList.size(), and_items);
	}

	// (assertL => valTestAssert) <=> (!assertL OR valTestAssert)
	valTestAssert = m.mk_or(m.mk_not(assertL), valTestAssert);
	return valTestAssert;
}

expr * theory_str::gen_free_var_options(expr * freeVar, expr * len_indicator,
		std::string len_valueStr, expr * valTesterInCbEq, std::string valTesterValueStr) {
	context & ctx = get_context();
	ast_manager & m = get_manager();

	int sLevel = ctx.get_scope_level();

	int len = atoi(len_valueStr.c_str());

	if (fvar_valueTester_map[freeVar].find(len) == fvar_valueTester_map[freeVar].end()) {
		TRACE("t_str_detail", tout << "no previous value testers" << std::endl;);
		int tries = 0;
		expr * val_indicator = mk_internal_valTest_var(freeVar, len, tries);
		valueTester_fvar_map[val_indicator] = freeVar;
		fvar_valueTester_map[freeVar][len].push_back(std::make_pair(sLevel, val_indicator));
		print_value_tester_list(fvar_valueTester_map[freeVar][len]);
		return gen_val_options(freeVar, len_indicator, val_indicator, len_valueStr, tries);
	} else {
		TRACE("t_str_detail", tout << "checking previous value testers" << std::endl;);
		// go through all previous value testers
		// If some doesn't have an eqc value, add its assertion again.
		int testerTotal = fvar_valueTester_map[freeVar][len].size();
		int i = 0;
		for (; i < testerTotal; i++) {
			expr * aTester = fvar_valueTester_map[freeVar][len][i].second;

			if (aTester == valTesterInCbEq) {
				break;
			}

			bool anEqcHasValue = false;
			// Z3_ast anEqc = get_eqc_value(t, aTester, anEqcHasValue);
			get_eqc_value(aTester, anEqcHasValue);
			if (!anEqcHasValue) {
				TRACE("t_str_detail", tout << "value tester " << mk_ismt2_pp(aTester, m)
						<< "doesn't have an equivalence class value." << std::endl;);

				expr * makeupAssert = gen_val_options(freeVar, len_indicator, aTester, len_valueStr, i);

				TRACE("t_str_detail", tout << "var: " << mk_ismt2_pp(freeVar, m) << std::endl
						<< mk_ismt2_pp(makeupAssert, m) << std::endl;);
				assert_axiom(makeupAssert);
			}
		}

		if (valTesterValueStr == "more") {
			expr * valTester = NULL;
			if (i + 1 < testerTotal) {
				valTester = fvar_valueTester_map[freeVar][len][i + 1].second;
			} else {
				valTester = mk_internal_valTest_var(freeVar, len, i + 1);
				valueTester_fvar_map[valTester] = freeVar;
				fvar_valueTester_map[freeVar][len].push_back(std::make_pair(sLevel, valTester));
				print_value_tester_list(fvar_valueTester_map[freeVar][len]);
			}
			expr * nextAssert = gen_val_options(freeVar, len_indicator, valTester, len_valueStr, i + 1);
			return nextAssert;
		}

		return NULL;
	}
}

expr * theory_str::gen_len_test_options(expr * freeVar, expr * indicator, int tries) {
	ast_manager & m = get_manager();

	TRACE("t_str_detail", tout << "entry" << std::endl;);

	expr * freeVarLen = mk_strlen(freeVar);
	SASSERT(freeVarLen);

	ptr_vector<expr> orList;
	ptr_vector<expr> andList;

	int distance = 3;
	int l = (tries - 1) * distance;
	int h = tries * distance;

	TRACE("t_str_detail", tout << "building andList and orList" << std::endl;);

	for (int i = l; i < h; ++i) {
		expr * or_expr = m.mk_eq(indicator, m_strutil.mk_string(int_to_string(i).c_str()));
		TRACE("t_str_detail", tout << "or_expr = " << mk_ismt2_pp(or_expr, m) << std::endl;);
		orList.push_back(or_expr);

		expr * and_expr = m.mk_eq(orList[orList.size() - 1], m.mk_eq(freeVarLen, mk_int(i)));
		TRACE("t_str_detail", tout << "and_expr = " << mk_ismt2_pp(and_expr, m) << std::endl;);
		andList.push_back(and_expr);
	}

	orList.push_back(m.mk_eq(indicator, m_strutil.mk_string("more")));
	andList.push_back(m.mk_eq(orList[orList.size() - 1], m_autil.mk_ge(freeVarLen, mk_int(h))));

	expr ** or_items = alloc_svect(expr*, orList.size());
	expr ** and_items = alloc_svect(expr*, andList.size() + 1);

	for (unsigned i = 0; i < orList.size(); ++i) {
		SASSERT(orList[i] != NULL);
		or_items[i] = orList[i];
	}

	and_items[0] = m.mk_or(orList.size(), or_items);
	SASSERT(and_items[0] != NULL);
	for(unsigned i = 0; i < andList.size(); ++i) {
		SASSERT(andList[i] != NULL);
		and_items[i+1] = andList[i];
	}
	expr * lenTestAssert = m.mk_and(andList.size() + 1, and_items);
	SASSERT(lenTestAssert != NULL);

	TRACE("t_str_detail", tout << "lenTestAssert = " << mk_ismt2_pp(lenTestAssert, m) << std::endl;);

	expr * assertL = NULL;
	int testerCount = tries - 1;
	if (testerCount > 0) {
		expr ** and_items_LHS = alloc_svect(expr*, testerCount);
		expr * moreAst = m_strutil.mk_string("more");
		for (int i = 0; i < testerCount; ++i) {
			and_items_LHS[i] = m.mk_eq(fvar_lenTester_map[freeVar][i], moreAst);
		}
		if (testerCount == 1) {
			assertL = and_items_LHS[0];
		} else {
			assertL = m.mk_and(testerCount, and_items_LHS);
		}
	}

	if (assertL != NULL) {
		TRACE("t_str_detail", tout << "assertL = " << mk_ismt2_pp(assertL, m) << std::endl;);
		// return the axiom (assertL -> lenTestAssert)
		// would like to use mk_implies() here but...
		lenTestAssert = m.mk_or(m.mk_not(assertL), lenTestAssert);
	}

	TRACE("t_str_detail", tout << "exit" << std::endl;);

	return lenTestAssert;

}

// -----------------------------------------------------------------------------------------------------
// True branch will be taken in final_check:
//   - When we discover a variable is "free" for the first time
//     lenTesterInCbEq = NULL
//     lenTesterValue = ""
// False branch will be taken when invoked by new_eq_eh().
//   - After we set up length tester for a "free" var in final_check,
//     when the tester is assigned to some value (e.g. "more" or "4"),
//     lenTesterInCbEq != NULL, and its value will be passed by lenTesterValue
// The difference is that in new_eq_eh(), lenTesterInCbEq and its value have NOT been put into a same eqc
// -----------------------------------------------------------------------------------------------------
expr * theory_str::gen_len_val_options_for_free_var(expr * freeVar, expr * lenTesterInCbEq, std::string lenTesterValue) {

	ast_manager & m = get_manager();

	TRACE("t_str_detail", tout << "gen for free var " << mk_ismt2_pp(freeVar, m) << std::endl;);
	// no length assertions for this free variable have ever been added.
	if (fvar_len_count_map.find(freeVar) == fvar_len_count_map.end()) {

		TRACE("t_str_detail", tout << "no length assertions yet" << std::endl;);

		fvar_len_count_map[freeVar] = 1;
		unsigned int testNum = fvar_len_count_map[freeVar];

		expr * indicator = mk_internal_lenTest_var(freeVar, testNum);
		SASSERT(indicator != NULL);

		fvar_lenTester_map[freeVar].push_back(indicator);
		lenTester_fvar_map[indicator] = freeVar;

		expr * lenTestAssert = gen_len_test_options(freeVar, indicator, testNum);
		SASSERT(lenTestAssert != NULL);
		return lenTestAssert;
	} else {
		TRACE("t_str_detail", tout << "found previous length assertions" << std::endl;);
		expr * effectiveLenInd = NULL;
		std::string effectiveLenIndiStr = "";
		int lenTesterCount = (int) fvar_lenTester_map[freeVar].size();

		int i = 0;
		for (; i < lenTesterCount; ++i) {
			expr * len_indicator_pre = fvar_lenTester_map[freeVar][i];
			bool indicatorHasEqcValue = false;
			expr * len_indicator_value = get_eqc_value(len_indicator_pre, indicatorHasEqcValue);
			TRACE("t_str_detail", tout << "length indicator " << mk_ismt2_pp(len_indicator_pre, m) <<
					" = " << mk_ismt2_pp(len_indicator_value, m) << std::endl;);
			if (indicatorHasEqcValue) {
				const char * val = 0;
				m_strutil.is_string(len_indicator_value, & val);
				std::string len_pIndiStr(val);
				if (len_pIndiStr != "more") {
					effectiveLenInd = len_indicator_pre;
					effectiveLenIndiStr = len_pIndiStr;
					break;
				}
			} else {
				if (lenTesterInCbEq != len_indicator_pre) {
					TRACE("t_str", tout << "WARNING: length indicator " << mk_ismt2_pp(len_indicator_pre, m)
							<< " does not have an equivalence class value."
							<< " i = " << i << ", lenTesterCount = " << lenTesterCount << std::endl;);
					if (i > 0) {
						effectiveLenInd = fvar_lenTester_map[freeVar][i - 1];
						if (effectiveLenInd == lenTesterInCbEq) {
							effectiveLenIndiStr = lenTesterValue;
						} else {
							bool effectiveHasEqcValue = false;
							const char * val = 0;
							m_strutil.is_string(get_eqc_value(effectiveLenInd, effectiveHasEqcValue), & val);
							effectiveLenIndiStr = val;
						}
					}
					break;
				}
				// lenTesterInCbEq == len_indicator_pre
				else {
					if (lenTesterValue != "more") {
						effectiveLenInd = len_indicator_pre;
						effectiveLenIndiStr = lenTesterValue;
						break;
					}
				}
			} // !indicatorHasEqcValue
		} // for (i : [0..lenTesterCount-1])
		if (effectiveLenIndiStr == "more" || effectiveLenIndiStr == "") {
			TRACE("t_str", tout << "length is not fixed; generating length tester options for free var" << std::endl;);
			expr * indicator = NULL;
			unsigned int testNum = 0;

			TRACE("t_str", tout << "effectiveLenIndiStr = " << effectiveLenIndiStr
					<< ", i = " << i << ", lenTesterCount = " << lenTesterCount << std::endl;);

			if (i == lenTesterCount) {
				fvar_len_count_map[freeVar] = fvar_len_count_map[freeVar] + 1;
				testNum = fvar_len_count_map[freeVar];
				indicator = mk_internal_lenTest_var(freeVar, testNum);
				fvar_lenTester_map[freeVar].push_back(indicator);
				lenTester_fvar_map[indicator] = freeVar;
			} else {
				indicator = fvar_lenTester_map[freeVar][i];
				testNum = i + 1;
			}
			expr * lenTestAssert = gen_len_test_options(freeVar, indicator, testNum);
			return lenTestAssert;
		} else {
			TRACE("t_str", tout << "length is fixed; generating models for free var" << std::endl;);
			// length is fixed
			expr * valueAssert = gen_free_var_options(freeVar, effectiveLenInd, effectiveLenIndiStr, NULL, "");
			return valueAssert;
		}
	} // fVarLenCountMap.find(...)
}

void theory_str::get_var_in_eqc(expr * n, std::set<expr*> & varSet) {
	context & ctx = get_context();

	expr * eqcNode = n;
	do {
		if (variable_set.find(eqcNode) != variable_set.end()) {
			varSet.insert(eqcNode);
		}
		enode * e_eqc = ctx.get_enode(eqcNode);
		eqcNode = e_eqc->get_next()->get_owner();
		// eqcNode = Z3_theory_get_eqc_next(t, eqcNode);
	} while (eqcNode != n);
}

void theory_str::process_free_var(std::map<expr*, int> & freeVar_map) {
	context & ctx = get_context();
	ast_manager & m = get_manager();

	std::set<expr*> eqcRepSet;
	std::set<expr*> leafVarSet;
	std::map<int, std::set<expr*> > aloneVars;

	for (std::map<expr*, int>::iterator fvIt = freeVar_map.begin(); fvIt != freeVar_map.end(); fvIt++) {
		expr * freeVar = fvIt->first;
		/*
		std::string vName = std::string(Z3_ast_to_string(ctx, freeVar));
		if (vName.length() >= 9 && vName.substr(0, 9) == "$$_regVar") {
			continue;
		}
		*/
		// TODO skip all regular expression vars

		// Iterate the EQC of freeVar, its eqc variable should not be in the eqcRepSet.
		// If found, have to filter it out
		std::set<expr*> eqVarSet;
		get_var_in_eqc(freeVar, eqVarSet);
		bool duplicated = false;
		expr * dupVar = NULL;
		for (std::set<expr*>::iterator itorEqv = eqVarSet.begin(); itorEqv != eqVarSet.end(); itorEqv++) {
			if (eqcRepSet.find(*itorEqv) != eqcRepSet.end()) {
				duplicated = true;
				dupVar = *itorEqv;
				break;
			}
		}
		if (duplicated && dupVar != NULL) {
			TRACE("t_str_detail", tout << "Duplicated free variable found:" << mk_ismt2_pp(freeVar, m)
					<< " = " << mk_ismt2_pp(dupVar, m) << " (SKIP)" << std::endl;);
			continue;
		} else {
			eqcRepSet.insert(freeVar);
		}
	}

	for (std::set<expr*>::iterator fvIt = eqcRepSet.begin(); fvIt != eqcRepSet.end(); fvIt++) {
		bool standAlone = true;
		expr * freeVar = *fvIt;
		// has length constraint initially
		if (input_var_in_len.find(freeVar) != input_var_in_len.end()) {
			standAlone = false;
		}
		// iterate parents
		if (standAlone) {
			// I hope this works!
			enode * e_freeVar = ctx.get_enode(freeVar);
			enode_vector::iterator it = e_freeVar->begin_parents();
			for (; it != e_freeVar->end_parents(); ++it) {
				expr * parentAst = (*it)->get_owner();
				if (is_concat(to_app(parentAst))) {
					standAlone = false;
					break;
				}
			}
		}

		if (standAlone) {
			// TODO
			// int lenValue = getLenValue(freeVar);
			int lenValue = -1;
			if (lenValue != -1) {
				leafVarSet.insert(freeVar);
			} else {
				aloneVars[lenValue].insert(freeVar);
			}
		} else {
			leafVarSet.insert(freeVar);
		}
	}

	// TODO here's a great place for debugging info

	for(std::set<expr*>::iterator itor1 = leafVarSet.begin();
			itor1 != leafVarSet.end(); ++itor1) {
		expr * toAssert = gen_len_val_options_for_free_var(*itor1, NULL, "");
		SASSERT(toAssert != NULL);
		assert_axiom(toAssert);
	}

	for (std::map<int, std::set<expr*> >::iterator mItor = aloneVars.begin();
			mItor != aloneVars.end(); ++mItor) {
		std::set<expr*>::iterator itor2 = mItor->second.begin();
		for(; itor2 != mItor->second.end(); ++itor2) {
			expr * toAssert = gen_len_val_options_for_free_var(*itor2, NULL, "");
			SASSERT(toAssert != NULL);
			assert_axiom(toAssert);
		}
	}
}

/*
 * Collect all unroll functions
 * and constant string in eqc of node n
 */
void theory_str::get_eqc_allUnroll(expr * n, expr * &constStr, std::set<expr*> & unrollFuncSet) {
  constStr = NULL;
  unrollFuncSet.clear();
  context & ctx = get_context();

  expr * curr = n;
  do {
    if (is_string(to_app(curr))) {
      constStr = curr;
    } else if (false) /*(td->Unroll == Z3_get_app_decl(ctx, Z3_to_app(ctx, curr)))*/ { // TODO
      if (unrollFuncSet.find(curr) == unrollFuncSet.end()) {
        unrollFuncSet.insert(curr);
      }
    }
    enode * e_curr = ctx.get_enode(curr);
    curr = e_curr->get_next()->get_owner();
    // curr = get_eqc_next(t, curr);
  } while (curr != n);
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
        TRACE("t_str", tout << "WARNING: failed to find a concrete value, falling back" << std::endl;);
        // TODO make absolutely sure the reason we can't find a concrete value is because of an unassigned temporary
        // e.g. for an expression like (Concat X $$_str0)
        //return alloc(expr_wrapper_proc, m_strutil.mk_string(""));
        NOT_IMPLEMENTED_YET();
    }
}

void theory_str::finalize_model(model_generator & mg) {}

}; /* namespace smt */
