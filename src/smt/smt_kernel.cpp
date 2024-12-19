/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_kernel.cpp

Abstract:

    New frontend for smt::context.
    
Author:

    Leonardo de Moura (leonardo) 2012-02-09.

Revision History:

--*/
#include "smt/smt_kernel.h"
#include "smt/smt_context.h"
#include "smt/smt_lookahead.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_util.h"
#include "smt/params/smt_params_helper.hpp"

namespace smt {

    struct kernel::imp {
        smt::context m_kernel;
        params_ref   m_params;
        
        imp(ast_manager & m, smt_params & fp, params_ref const & p):
            m_kernel(m, fp, p),
            m_params(p) {
        }
     
        ast_manager & m() const {
            return m_kernel.get_manager();
        }

        void display(std::ostream & out) const {
            // m_kernel.display(out); <<< for external users it is just junk
            // TODO: it will be replaced with assertion_stack.display
            unsigned num = m_kernel.get_num_asserted_formulas();
            out << "(kernel";
            for (unsigned i = 0; i < num; i++) {
                expr* f = m_kernel.get_asserted_formula(i);
                out << "\n  " << mk_ismt2_pp(f, m(), 2);
            }
            out << ")";
        } 
        
    };

    kernel::kernel(ast_manager & m, smt_params & fp, params_ref const & p) {
        m_imp = alloc(imp, m, fp, p);
    }

    kernel::~kernel() {
        dealloc(m_imp);
    }

    ast_manager & kernel::m() const {
        return m_imp->m_kernel.get_manager();
    }

    void  kernel::copy(kernel& src, kernel& dst, bool override_base) {
        context::copy(src.m_imp->m_kernel, dst.m_imp->m_kernel, override_base);
    }

    bool kernel::set_logic(symbol logic) {
        return m_imp->m_kernel.set_logic(logic);
    }

    void kernel::set_progress_callback(progress_callback * callback) {
        m_imp->m_kernel.set_progress_callback(callback);
    }

    void kernel::assert_expr(expr * e) {
        m_imp->m_kernel.assert_expr(e);
    }

    void kernel::assert_expr(expr_ref_vector const& es) {
        for (unsigned i = 0; i < es.size(); ++i) 
            m_imp->m_kernel.assert_expr(es[i]);
    }

    void kernel::assert_expr(expr * e, proof * pr) {
        m_imp->m_kernel.assert_expr(e, pr);
    }

    unsigned kernel::size() const {
        return m_imp->m_kernel.get_num_asserted_formulas();
    }
    
    expr* kernel::get_formula(unsigned i) const {
        return m_imp->m_kernel.get_asserted_formula(i);
    }

    void kernel::push() {
        m_imp->m_kernel.push();
    }

    void kernel::pop(unsigned num_scopes) {
        m_imp->m_kernel.pop(num_scopes);
    }

    unsigned kernel::get_scope_level() const {
        return m_imp->m_kernel.get_scope_level();
    }

    void kernel::reset() {
        ast_manager & _m = m();
        smt_params& fps = m_imp->m_kernel.get_fparams();
        params_ref ps = m_imp->m_params;
        m_imp->~imp();
        m_imp = new (m_imp) imp(_m, fps, ps);        
    }

    bool kernel::inconsistent() {
        return m_imp->m_kernel.inconsistent();
    }

    lbool kernel::setup_and_check() {
        return m_imp->m_kernel.setup_and_check();
    }

    lbool kernel::check(unsigned num_assumptions, expr * const * assumptions) {
        lbool r = m_imp->m_kernel.check(num_assumptions, assumptions);
        TRACE("smt_kernel", tout << "check result: " << r << "\n";);
        return r;
    }

    lbool kernel::check(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) {
        return m_imp->m_kernel.check(cube, clauses);
    }

    lbool kernel::get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq, expr_ref_vector& unfixed) {
        return m_imp->m_kernel.get_consequences(assumptions, vars, conseq, unfixed);
    }

    lbool kernel::preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) {
        return m_imp->m_kernel.preferred_sat(asms, cores);
    }

    lbool kernel::find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
        return m_imp->m_kernel.find_mutexes(vars, mutexes);
    }

    void kernel::get_model(model_ref & m) {
        m_imp->m_kernel.get_model(m);
    }

    proof * kernel::get_proof() {
        return m_imp->m_kernel.get_proof();
    }

    unsigned kernel::get_unsat_core_size() const {
        return m_imp->m_kernel.get_unsat_core_size();
    }
        
    expr * kernel::get_unsat_core_expr(unsigned idx) const {
        return m_imp->m_kernel.get_unsat_core_expr(idx);
    }

    failure kernel::last_failure() const {
        return m_imp->m_kernel.get_last_search_failure();
    }

    std::string kernel::last_failure_as_string() const {
        return m_imp->m_kernel.last_failure_as_string();
    }

    void kernel::set_reason_unknown(char const* msg) {
        m_imp->m_kernel.set_reason_unknown(msg);
    }

    void kernel::get_assignments(expr_ref_vector & result) {
        m_imp->m_kernel.get_assignments(result);
    }

    void kernel::get_units(expr_ref_vector & result) {
        m_imp->m_kernel.get_units(result);
    }    
        
    void kernel::get_relevant_labels(expr * cnstr, buffer<symbol> & result) {
        m_imp->m_kernel.get_relevant_labels(cnstr, result);
    }
    
    void kernel::get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result) {
        m_imp->m_kernel.get_relevant_labeled_literals(at_lbls, result);
    }

    void kernel::get_relevant_literals(expr_ref_vector & result) {
        m_imp->m_kernel.get_relevant_literals(result);
    }

    void kernel::get_guessed_literals(expr_ref_vector & result) {
        m_imp->m_kernel.get_guessed_literals(result);
    }

    expr_ref kernel::next_cube() {
        lookahead lh(m_imp->m_kernel);
        return lh.choose();
    }        

    expr_ref_vector kernel::cubes(unsigned depth) {
        lookahead lh(m_imp->m_kernel);
        return lh.choose_rec(depth);
    }        

    std::ostream& kernel::display(std::ostream & out) const {
        m_imp->display(out);
        return out;
    }

    void kernel::solve_for(vector<solver::solution>& sol) {
        vector<smt::solution> solution;
        for (auto const& [v, t, g] : sol)
            solution.push_back({ v, t, g });
        m_imp->m_kernel.solve_for(solution);
        sol.reset();
        for (auto s : solution)
            sol.push_back({ s.var, s.term, s.guard });       
    }

    expr* kernel::congruence_root(expr * e) {
        smt::enode* n = m_imp->m_kernel.find_enode(e);        
        if (!n)
            return e;
        return n->get_root()->get_expr();
    }

    expr* kernel::congruence_next(expr * e) {
        smt::enode* n = m_imp->m_kernel.find_enode(e);
        if (!n)
            return e;
        return n->get_next()->get_expr();
    }

    expr_ref kernel::congruence_explain(expr* a, expr* b) {
        auto& ctx = m_imp->m_kernel;
        ast_manager& m = ctx.get_manager();
        smt::enode* n1 = ctx.find_enode(a);
        smt::enode* n2 = ctx.find_enode(b);
        if (!n1 || !n2 || n1->get_root() != n2->get_root())
            return expr_ref(m.mk_eq(a, b), m);
        literal_vector lits;
        ctx.get_cr().eq2literals(n1, n2, lits);
        expr_ref_vector es(m);
        for (auto lit : lits)
            es.push_back(ctx.literal2expr(lit));        
        return mk_and(es);
    }

    void kernel::collect_statistics(::statistics & st) const {
        m_imp->m_kernel.collect_statistics(st);
    }
        
    void kernel::reset_statistics() {
    }

    void kernel::display_statistics(std::ostream & out) const {
        m_imp->m_kernel.display_statistics(out);
    }

    void kernel::display_istatistics(std::ostream & out) const {
        m_imp->m_kernel.display_istatistics(out);
    }

    bool kernel::canceled() const {
        return m_imp->m_kernel.get_cancel_flag();
    }

    void kernel::updt_params(params_ref const & p) {
        return m_imp->m_kernel.updt_params(p);
    }

    void kernel::collect_param_descrs(param_descrs & d) {
        smt_params_helper::collect_param_descrs(d);
    }

    context & kernel::get_context() {
        return m_imp->m_kernel;
    }

    void kernel::get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) {
        m_imp->m_kernel.get_levels(vars, depth);
    }

    expr_ref_vector kernel::get_trail(unsigned max_level) {
        return m_imp->m_kernel.get_trail(max_level);
    }

    void kernel::user_propagate_init(
        void*                ctx, 
        user_propagator::push_eh_t&   push_eh,
        user_propagator::pop_eh_t&    pop_eh,
        user_propagator::fresh_eh_t&  fresh_eh) {
        m_imp->m_kernel.user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }

    void kernel::register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) {
        m_imp->m_kernel.register_on_clause(ctx, on_clause);
    }

    void kernel::user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) {
        m_imp->m_kernel.user_propagate_register_fixed(fixed_eh);
    }
    
    void kernel::user_propagate_register_final(user_propagator::final_eh_t& final_eh) {
        m_imp->m_kernel.user_propagate_register_final(final_eh);
    }
    
    void kernel::user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) {
        m_imp->m_kernel.user_propagate_register_eq(eq_eh);
    }
    
    void kernel::user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) {
        m_imp->m_kernel.user_propagate_register_diseq(diseq_eh);
    }

    void kernel::user_propagate_register_expr(expr* e) {
        m_imp->m_kernel.user_propagate_register_expr(e);
    }        

    void kernel::user_propagate_register_created(user_propagator::created_eh_t& r) {
        m_imp->m_kernel.user_propagate_register_created(r);
    }

    void kernel::user_propagate_register_decide(user_propagator::decide_eh_t& r) {
        m_imp->m_kernel.user_propagate_register_decide(r);
    }
    
    void kernel::user_propagate_initialize_value(expr* var, expr* value) {
        m_imp->m_kernel.user_propagate_initialize_value(var, value);
    }

};
