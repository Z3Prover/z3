/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    specrel_solver.h

Abstract:

    Theory plugin for special relations

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/specrel_solver.h"
#include "sat/smt/euf_solver.h"
#include "ast/euf/euf_specrel_plugin.h"

namespace euf {
    class solver;
}

namespace specrel {

    solver::solver(euf::solver& ctx, theory_id id) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        sp(m)
    {
        ctx.get_egraph().add_plugin(alloc(euf::specrel_plugin, ctx.get_egraph()));
    }

    void solver::asserted(sat::literal l) {

    }

    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {    
        TRACE("specrel", tout << "new-eq\n");
        if (eq.is_eq()) {
            auto* p = ctx.get_egraph().get_plugin(sp.get_family_id());
            p->merge_eh(var2enode(eq.v1()), var2enode(eq.v2()));
            TRACE("specrel", tout << eq.v1() << " " << eq.v2() << "\n");                       
        }
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {        
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        return false;
    }

    bool solver::include_func_interp(func_decl* f) const {
        return false;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        auto lit = ctx.expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        visit_rec(m, e, false, false);
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::post_visit(expr* term, bool sign, bool root) {
        euf::enode* n = expr2enode(term);
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n)
            n = mk_enode(term);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        TRACE("specrel", tout << ctx.bpp(n) << "\n");
        return true;
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var r = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, r);
        return r;
    }
}
