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

namespace smt {

theory_str::theory_str(ast_manager &m):
        theory(m.mk_family_id("str"))
{
}

theory_str::~theory_str() {
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

    return true;
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
