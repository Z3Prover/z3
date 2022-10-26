/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_th.cpp

Abstract:

    Theory plugin base classes

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "sat/smt/sat_th.h"
#include "sat/smt/euf_solver.h"
#include "tactic/tactic_exception.h"

namespace euf {

    bool th_internalizer::visit_rec(ast_manager& m, expr* a, bool sign, bool root) {
        IF_VERBOSE(110, verbose_stream() << "internalize: " << mk_pp(a, m) << "\n");
        svector<sat::eframe>::scoped_stack _sc(m_stack);
        unsigned sz = m_stack.size();
        visit(a);
        while (m_stack.size() > sz) {
        loop:
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            unsigned fsz = m_stack.size();
            expr* e = m_stack[fsz-1].m_e;
            if (visited(e)) {
                m_stack.pop_back();
                continue;
            }
            unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;

            while (m_stack[fsz - 1].m_idx < num) {
                expr* arg = to_app(e)->get_arg(m_stack[fsz - 1].m_idx);
                m_stack[fsz - 1].m_idx++;
                if (!visit(arg))
                    goto loop;
            }
            if (!visited(e) && !post_visit(e, sign, root && a == e))
                return false;
            m_stack.pop_back();
        }
        return true;
    }

    th_euf_solver::th_euf_solver(euf::solver& ctx, symbol const& name, euf::theory_id id):
        th_solver(ctx.get_manager(), name, id),
        ctx(ctx)
    {}

    smt_params const& th_euf_solver::get_config() const {
        return ctx.get_config(); 
    }

    region& th_euf_solver::get_region() {
        return ctx.get_region();
    }

    trail_stack& th_euf_solver::get_trail_stack() {
        return ctx.get_trail_stack();
    }

    enode* th_euf_solver::expr2enode(expr* e) const { 
        return ctx.get_enode(e); 
    }

    sat::literal th_euf_solver::expr2literal(expr* e) const {
        return ctx.expr2literal(e);
    }

    expr* th_euf_solver::bool_var2expr(sat::bool_var v) const {
        return ctx.bool_var2expr(v);
    }

    expr_ref th_euf_solver::literal2expr(sat::literal lit) const { 
        return ctx.literal2expr(lit);
    }

    theory_var th_euf_solver::mk_var(enode * n) {
        force_push();
        SASSERT(!is_attached_to_var(n));
        euf::theory_var v = m_var2enode.size();
        m_var2enode.push_back(n);
        return v;
    }

    bool th_euf_solver::is_attached_to_var(enode* n) const {
        theory_var v = n->get_th_var(get_id());
        return v != null_theory_var && var2enode(v) == n;
    }

    theory_var th_euf_solver::get_th_var(expr* e) const {
        return get_th_var(ctx.get_enode(e));
    }

    theory_var th_euf_solver::get_representative(theory_var v) const {
        euf::enode* r = var2enode(v)->get_root();
        return get_th_var(r);
    }
    
    void th_euf_solver::push_core() {
        m_var2enode_lim.push_back(m_var2enode.size());
    }

    void th_euf_solver::pop_core(unsigned num_scopes) {
        unsigned new_lvl = m_var2enode_lim.size() - num_scopes;
        m_var2enode.shrink(m_var2enode_lim[new_lvl]);
        m_var2enode_lim.shrink(new_lvl);
    }

    void th_euf_solver::pop(unsigned n) {
        unsigned k = std::min(m_num_scopes, n);
        m_num_scopes -= k;
        n -= k;
        if (n > 0)
            pop_core(n);        
    }

    bool th_euf_solver::add_unit(sat::literal lit, th_proof_hint const* ps) {
        if (ctx.use_drat() && !ps)
            ps = ctx.mk_smt_clause(name(), 1, &lit);
        bool was_true = is_true(lit);
        ctx.s().add_clause(1, &lit, sat::status::th(false, get_id(), ps));
        ctx.add_root(lit);
        return !was_true;
    }

    bool th_euf_solver::add_units(sat::literal_vector const& lits) {
        bool is_new = false;
        for (auto lit : lits)
            if (add_unit(lit))
                is_new = true;
        return is_new;
    }
    
    bool th_euf_solver::add_clause(sat::literal a, sat::literal b, th_proof_hint const* ph) {
        sat::literal lits[2] = { a, b };
        return add_clause(2, lits, ph);
    }

    bool th_euf_solver::add_clause(sat::literal a, sat::literal b, sat::literal c, th_proof_hint const* ps) {
        sat::literal lits[3] = { a, b, c };
        return add_clause(3, lits, ps);
    }

    bool th_euf_solver::add_clause(sat::literal a, sat::literal b, sat::literal c, sat::literal d, th_proof_hint const* ps) {
        sat::literal lits[4] = { a, b, c, d };
        return add_clause(4, lits, ps);
    }

    bool th_euf_solver::add_clause(unsigned n, sat::literal* lits, th_proof_hint const* ps, bool is_redundant) {
        if (ctx.use_drat() && !ps) 
            ps = ctx.mk_smt_clause(name(), n, lits);
                
        bool was_true = false;
        for (unsigned i = 0; i < n; ++i)       
            was_true |= is_true(lits[i]);
        ctx.add_root(n, lits);
        s().add_clause(n, lits, sat::status::th(is_redundant, get_id(), ps));
        return !was_true;
    }

    void th_euf_solver::add_equiv(sat::literal a, sat::literal b) {
        add_clause(~a, b);
        add_clause(a, ~b);
    }

    void th_euf_solver::add_equiv_and(sat::literal a, sat::literal_vector const& bs) {
        for (auto b : bs)
            add_clause(~a, b);
        sat::literal_vector _bs;
        for (auto b : bs)
            _bs.push_back(~b);
        _bs.push_back(a);
        add_clause(_bs);
    }

    bool th_euf_solver::is_true(sat::literal lit) { 
        return ctx.s().value(lit) == l_true; 
    }

    euf::enode* th_euf_solver::mk_enode(expr* e, bool suppress_args) {
        m_args.reset();
        if (!suppress_args)
            for (expr* arg : *to_app(e))
                m_args.push_back(expr2enode(arg));
        euf::enode* n = ctx.mk_enode(e, m_args.size(), m_args.data());
        ctx.attach_node(n);
        return n;
    }

    void th_euf_solver::rewrite(expr_ref& a) {
        ctx.get_rewriter()(a);
    }

    expr_ref th_euf_solver::mk_eq(expr* e1, expr* e2) { 
        return ctx.mk_eq(e1, e2); 
    }

    sat::literal th_euf_solver::mk_literal(expr* e) const {
        return ctx.mk_literal(e);
    }

    sat::literal th_euf_solver::eq_internalize(expr* a, expr* b) { 
        return mk_literal(ctx.mk_eq(a, b)); 
    }

    euf::enode* th_euf_solver::e_internalize(expr* e) {
        return ctx.e_internalize(e);
    }

    unsigned th_euf_solver::random() {
        return ctx.s().rand()();
    }

    size_t th_explain::get_obj_size(unsigned num_lits, unsigned num_eqs) {
        return sat::constraint_base::obj_size(sizeof(th_explain) + sizeof(sat::literal) * num_lits + sizeof(enode_pair) * num_eqs);
    }

    th_explain::th_explain(unsigned n_lits, sat::literal const* lits, unsigned n_eqs, enode_pair const* eqs, sat::literal c, enode_pair const& p, th_proof_hint const* pma) {
        m_consequent = c;
        m_eq = p;
        m_proof_hint = pma;
        m_num_literals = n_lits;
        m_num_eqs = n_eqs;
        char * base_ptr = reinterpret_cast<char*>(this) + sizeof(th_explain); 
        m_literals = reinterpret_cast<literal*>(base_ptr);
        unsigned i;
        for (i = 0; i < n_lits; ++i)
            m_literals[i] = lits[i];
        base_ptr += sizeof(literal) * n_lits;
        m_eqs = reinterpret_cast<enode_pair*>(base_ptr);
        for (i = 0; i < n_eqs; ++i)
            m_eqs[i] = eqs[i];
    }

    th_explain* th_explain::mk(th_euf_solver& th, unsigned n_lits, sat::literal const* lits, unsigned n_eqs, enode_pair const* eqs, sat::literal c, enode* x, enode* y, th_proof_hint const* pma) {
        region& r = th.ctx.get_region();
        void* mem = r.allocate(get_obj_size(n_lits, n_eqs));
        sat::constraint_base::initialize(mem, &th);
        return new (sat::constraint_base::ptr2mem(mem)) th_explain(n_lits, lits, n_eqs, eqs, c, enode_pair(x, y), pma);
    }

    th_explain* th_explain::propagate(th_euf_solver& th, sat::literal_vector const& lits, enode_pair_vector const& eqs, sat::literal consequent, th_proof_hint const* ph) {
        return mk(th, lits.size(), lits.data(), eqs.size(), eqs.data(), consequent, nullptr, nullptr, ph);
    }

    th_explain* th_explain::propagate(th_euf_solver& th, sat::literal_vector const& lits, enode_pair_vector const& eqs, euf::enode* x, euf::enode* y, th_proof_hint const* ph) {
        return mk(th, lits.size(), lits.data(), eqs.size(), eqs.data(), sat::null_literal, x, y, ph);
    }

    th_explain* th_explain::propagate(th_euf_solver& th, enode_pair_vector const& eqs, euf::enode* x, euf::enode* y, th_proof_hint const* ph) {
        return mk(th, 0, nullptr, eqs.size(), eqs.data(), sat::null_literal, x, y, ph);
    }

    th_explain* th_explain::propagate(th_euf_solver& th, sat::literal lit, euf::enode* x, euf::enode* y, th_proof_hint const* ph) {
        return mk(th, 1, &lit, 0, nullptr, sat::null_literal, x, y, ph);
    }

    th_explain* th_explain::conflict(th_euf_solver& th, sat::literal_vector const& lits, enode_pair_vector const& eqs, th_proof_hint const* ph) {
        return conflict(th, lits.size(), lits.data(), eqs.size(), eqs.data(), ph);
    }

    th_explain* th_explain::conflict(th_euf_solver& th, unsigned n_lits, sat::literal const* lits, unsigned n_eqs, enode_pair const* eqs, th_proof_hint const* ph) {
        return mk(th, n_lits, lits, n_eqs, eqs, sat::null_literal, nullptr, nullptr, ph);
    }

    th_explain* th_explain::conflict(th_euf_solver& th, enode_pair_vector const& eqs, th_proof_hint const* ph) {
        return conflict(th, 0, nullptr, eqs.size(), eqs.data(), ph);
    }

    th_explain* th_explain::conflict(th_euf_solver& th, sat::literal lit, th_proof_hint const* ph) {
        return conflict(th, 1, &lit, 0, nullptr, ph);
    }

    th_explain* th_explain::conflict(th_euf_solver& th, sat::literal lit, euf::enode* x, euf::enode* y, th_proof_hint const* ph) {
        enode_pair eq(x, y);
        return conflict(th, 1, &lit, 1, &eq, ph);
    }

    th_explain* th_explain::conflict(th_euf_solver& th, euf::enode* x, euf::enode* y, th_proof_hint const* ph) {
        enode_pair eq(x, y);
        return conflict(th, 0, nullptr, 1, &eq, ph);
    }

    std::ostream& th_explain::display(std::ostream& out) const {
        for (auto lit : euf::th_explain::lits(*this))
            out << lit << " ";
        for (auto eq : euf::th_explain::eqs(*this))
            out << eq.first->get_expr_id() << " == " << eq.second->get_expr_id() << " ";
        if (m_consequent != sat::null_literal)
            out << "--> " << m_consequent;
        if (m_eq.first != nullptr)
            out << "--> " << m_eq.first->get_expr_id() << " == " << m_eq.second->get_expr_id();
        if (m_proof_hint != nullptr)
            out << " p ";
        return out;
    }


}
