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

void theory_str::assert_axiom(unsigned num_lits, literal * lits) {
    context & ctx = get_context();
    TRACE("t_str_detail",
          tout << "assert_axiom: literals:\n";
          for (unsigned i = 0; i < num_lits; ++i) {
              expr * e = ctx.bool_var2expr(lits[i].var());
              if (lits[i].sign())
                  tout << "not ";
              tout << mk_pp(e, get_manager()) << " ";
              tout << "\n";
          });
    ctx.mk_th_axiom(get_id(), num_lits, lits);
}

void theory_str::assert_axiom(literal l) {
    assert_axiom(1, &l);
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

    if (is_concat(term)) {
        instantiate_concat_axiom(e);
    }

    return true;
}

app * theory_str::mk_strlen(app * e) {
    if (m_strutil.is_string(e)) {
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
    app * len_x_plus_len_y = m_autil.mk_add(len_x, len_y);
    SASSERT(len_x_plus_len_y);

    TRACE("t_str", tout << mk_bounded_pp(len_xy, m) << " = " << mk_bounded_pp(len_x_plus_len_y, m) << "\n";);

    // finally assert equality between the two subexpressions
    literal l(mk_eq(len_xy, len_x_plus_len_y, true));
    ctx.mark_as_relevant(l);
    assert_axiom(l);
}

void theory_str::attach_new_th_var(enode * n) {
    context & ctx = get_context();
    theory_var v = mk_var(n);
    ctx.attach_th_var(n, this, v);
    TRACE("t_str_detail", tout << "new theory var: " << mk_ismt2_pp(n->get_owner(), get_manager()) << " := " << v << "\n";);
}

void theory_str::init_search_eh() {
    ast_manager & m = get_manager();
    context & ctx = get_context();
    TRACE("t_str",
        tout << "search started, assignments are:" << std::endl;
        expr_ref_vector assignment(m);
        ctx.get_assignments(assignment);
        for (expr_ref_vector::iterator i = assignment.begin(); i != assignment.end(); ++i) {
            expr * ex = *i;
            tout << mk_ismt2_pp(ex, m) << std::endl;
        }
    );
    search_started = true;
}

void theory_str::new_eq_eh(theory_var x, theory_var y) {
    // TODO
    TRACE("t_str", tout << "new eq: " << x << " = " << y << std::endl;);
    TRACE("t_str_detail", tout << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " = " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
}

void theory_str::new_diseq_eh(theory_var x, theory_var y) {
    // TODO
    TRACE("t_str", tout << "new diseq: " << x << " != " << y << std::endl;);
    TRACE("t_str_detail", tout << mk_ismt2_pp(get_enode(x)->get_owner(), get_manager()) << " != " <<
                                  mk_ismt2_pp(get_enode(y)->get_owner(), get_manager()) << std::endl;);
}

void theory_str::relevant_eh(app * n) {
    TRACE("t_str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << "\n";);
}

void theory_str::assign_eh(bool_var v, bool is_true) {
    context & ctx = get_context();
    TRACE("t_str", tout << "assert: v" << v << " #" << ctx.bool_var2expr(v)->get_id() << " is_true: " << is_true << "\n";);
}

void theory_str::push_scope_eh() {
    TRACE("t_str", tout << "push" << std::endl;);
}

final_check_status theory_str::final_check_eh() {
    // TODO
    TRACE("t_str", tout << "final check" << std::endl;);
    return FC_DONE;
}

}; /* namespace smt */
