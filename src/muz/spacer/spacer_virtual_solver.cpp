/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_virtual_solver.cpp

Abstract:

   multi-solver view of a single solver

Author:

    Arie Gurfinkel

Notes:

--*/

#include "muz/spacer/spacer_virtual_solver.h"
#include "ast/ast_util.h"
#include "ast/ast_pp_util.h"
#include "muz/spacer/spacer_util.h"
#include "ast/rewriter/bool_rewriter.h"

#include "ast/proofs/proof_checker.h"
#include "ast/proofs/proof_utils.h"

#include "ast/scoped_proof.h"

#include "smt/smt_kernel.h"

namespace spacer {
virtual_solver::virtual_solver(virtual_solver_factory &factory, app* pred) :
    solver_na2as(factory.get_manager()),
    m_factory(factory),
    m(factory.get_manager()),
    m_context(factory.get_base_solver()),
    m_pred(pred, m),
    m_virtual(!m.is_true(pred)),
    m_assertions(m),
    m_head(0),
    m_flat(m),
    m_pushed(false),
    m_in_delay_scope(false),
    m_dump_benchmarks(false /*factory.fparams().m_dump_benchmarks*/),
    m_dump_counter(0),
    m_proof(m)
{
    // -- insert m_pred->true background assumption this will not
    // -- change m_context, but will add m_pred to
    // -- the private field solver_na2as::m_assumptions
    if (m_virtual)
    { solver_na2as::assert_expr_core2(m.mk_true(), m_pred); }
}

virtual_solver::~virtual_solver()
{
    SASSERT(!m_pushed || get_scope_level() > 0);
    if (m_pushed) { pop(get_scope_level()); }

    if (m_virtual) {
        m_pred = m.mk_not(m_pred);
        m_context.assert_expr(m_pred);
    }
}

namespace {


// TBD: move to ast/proofs/elim_aux_assertions


}

proof *virtual_solver::get_proof()
{
    scoped_watch _t_(m_factory.m_proof_watch);

    if (!m_proof.get()) {
        elim_aux_assertions pc(m_pred);
        m_proof = m_context.get_proof();
        pc(m, m_proof.get(), m_proof);
    }
    return m_proof.get();
}

bool virtual_solver::is_aux_predicate(expr *p)
{return is_app(p) && to_app(p) == m_pred.get();}

lbool virtual_solver::check_sat_core(unsigned num_assumptions,
                                     expr *const * assumptions)
{
    SASSERT(!m_pushed || get_scope_level() > 0);
    m_proof.reset();
    scoped_watch _t_(m_factory.m_check_watch);
    m_factory.m_stats.m_num_smt_checks++;

    stopwatch sw;
    sw.start();
    internalize_assertions();
    if (false) {
        std::stringstream file_name;
        file_name << "virt_solver";
        if (m_virtual) { file_name << "_" << m_pred->get_decl()->get_name(); }
        file_name << "_" << (m_dump_counter++) << ".smt2";

        verbose_stream() << "Dumping SMT2 benchmark: " << file_name.str() << "\n";

        std::ofstream out(file_name.str().c_str());

        to_smt2_benchmark(out, m_context, num_assumptions, assumptions,
                          "virt_solver");

        out << "(exit)\n";
        out.close();
    }
    lbool res = m_context.check_sat(num_assumptions, assumptions);
    sw.stop();
    if (res == l_true) {
        m_factory.m_check_sat_watch.add(sw);
        m_factory.m_stats.m_num_sat_smt_checks++;
    } else if (res == l_undef) {
        m_factory.m_check_undef_watch.add(sw);
        m_factory.m_stats.m_num_undef_smt_checks++;
    }
    set_status(res);

    if (false /*m_dump_benchmarks &&
                sw.get_seconds() >= m_factory.fparams().m_dump_min_time*/) {
        std::stringstream file_name;
        file_name << "virt_solver";
        if (m_virtual) { file_name << "_" << m_pred->get_decl()->get_name(); }
        file_name << "_" << (m_dump_counter++) << ".smt2";

        std::ofstream out(file_name.str().c_str());


        out << "(set-info :status ";
        if (res == l_true) { out << "sat"; }
        else if (res == l_false) { out << "unsat"; }
        else { out << "unknown"; }
        out << ")\n";

        to_smt2_benchmark(out, m_context, num_assumptions, assumptions,
                          "virt_solver");

        out << "(exit)\n";
        ::statistics st;
        m_context.collect_statistics(st);
        st.update("time", sw.get_seconds());
        st.display_smt2(out);


        if (false /* m_factory.fparams().m_dump_recheck */) {
            scoped_no_proof _no_proof_(m);
            smt_params p;
            stopwatch sw2;
            smt::kernel kernel(m, p);
            for (unsigned i = 0, sz = m_context.get_num_assertions(); i < sz; ++i)
                { kernel.assert_expr(m_context.get_assertion(i)); }
            sw2.start();
            kernel.check(num_assumptions, assumptions);
            sw2.stop();
            verbose_stream() << file_name.str() << " :orig "
                             << sw.get_seconds() << " :new " << sw2.get_seconds();

            out << ";; :orig " << sw.get_seconds()
                << " :new " << sw2.get_seconds() << "\n"
                << ";; :new is time to solve with fresh smt::kernel\n";
        }

        out.close();
    }


    return res;
}

void virtual_solver::push_core()
{
    SASSERT(!m_pushed || get_scope_level() > 0);
    if (m_in_delay_scope) {
        // second push
        internalize_assertions();
        m_context.push();
        m_pushed = true;
        m_in_delay_scope = false;
    }

    if (!m_pushed) { m_in_delay_scope = true; }
    else {
        SASSERT(m_pushed);
        SASSERT(!m_in_delay_scope);
        m_context.push();
    }
}
void virtual_solver::pop_core(unsigned n) {
    SASSERT(!m_pushed || get_scope_level() > 0);
    if (m_pushed) {
        SASSERT(!m_in_delay_scope);
        m_context.pop(n);
        m_pushed = get_scope_level() - n > 0;
    }
    else {
        m_in_delay_scope = get_scope_level() - n > 0;
    }
}

void virtual_solver::get_unsat_core(ptr_vector<expr> &r)
{
    ptr_vector<expr> core;
    m_context.get_unsat_core(core);

    for (unsigned i = 0, sz = core.size(); i < sz; ++i) {
        if (is_aux_predicate(core.get(i))) { continue; }
        r.push_back(core.get(i));
    }
}

void virtual_solver::assert_expr_core(expr *e)
{
    SASSERT(!m_pushed || get_scope_level() > 0);
    if (m.is_true(e)) { return; }
    if (m_in_delay_scope) {
        internalize_assertions();
        m_context.push();
        m_pushed = true;
        m_in_delay_scope = false;
    }

    if (m_pushed)
    { m_context.assert_expr(e); }
    else {
        m_flat.push_back(e);
        flatten_and(m_flat);
        m_assertions.append(m_flat);
        m_flat.reset();
    }
}
void virtual_solver::internalize_assertions()
{
    SASSERT(!m_pushed || m_head == m_assertions.size());
    for (unsigned sz = m_assertions.size(); m_head < sz; ++m_head) {
        expr_ref f(m);
        f = m.mk_implies(m_pred, (m_assertions.get(m_head)));
        m_context.assert_expr(f);
    }
}

void virtual_solver::get_labels(svector<symbol> &r)
{m_context.get_labels(r);}

solver* virtual_solver::translate(ast_manager& m, params_ref const& p)
{
    UNREACHABLE();
    return nullptr;
}
void virtual_solver::updt_params(params_ref const &p) {m_context.updt_params(p);}
void virtual_solver::reset_params(params_ref const &p) {m_context.reset_params(p);}
const params_ref &virtual_solver::get_params() const {return m_context.get_params();}
void virtual_solver::push_params(){m_context.push_params();}
void virtual_solver::pop_params(){m_context.pop_params();}
void virtual_solver::collect_param_descrs(param_descrs &r) { m_context.collect_param_descrs(r); }
void virtual_solver::set_produce_models(bool f) { m_context.set_produce_models(f); }

void virtual_solver::to_smt2_benchmark(std::ostream &out,
                                       solver &context,
                                       unsigned num_assumptions,
                                       expr * const * assumptions,
                                       char const * name,
                                       symbol const &logic,
                                       char const * status,
                                       char const * attributes)
{
    ast_pp_util pp(m);
    expr_ref_vector asserts(m);

    context.get_assertions(asserts);
    pp.collect(asserts);
    pp.collect(num_assumptions, assumptions);
    pp.display_decls(out);
    pp.display_asserts(out, asserts);
    out << "(check-sat ";
    for (unsigned i = 0; i < num_assumptions; ++i)
    { out << mk_pp(assumptions[i], m) << " "; }
    out << ")\n";
}


virtual_solver_factory::virtual_solver_factory(solver &base) :
    m(base.get_manager()), m_context(base) {m_stats.reset();}

virtual_solver* virtual_solver_factory::mk_solver()
{
    std::stringstream name;
    name << "vsolver#" << m_solvers.size();
    app_ref pred(m);
    pred = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());
    SASSERT(m_context.get_scope_level() == 0);
    m_solvers.push_back(alloc(virtual_solver, *this, pred));
    return m_solvers.back();
}

void virtual_solver_factory::collect_statistics(statistics &st) const
{
    m_context.collect_statistics(st);
    st.update("time.virtual_solver.smt.total", m_check_watch.get_seconds());
    st.update("time.virtual_solver.smt.total.sat", m_check_sat_watch.get_seconds());
    st.update("time.virtual_solver.smt.total.undef", m_check_undef_watch.get_seconds());
    st.update("time.virtual_solver.proof", m_proof_watch.get_seconds());
    st.update("virtual_solver.checks", m_stats.m_num_smt_checks);
    st.update("virtual_solver.checks.sat", m_stats.m_num_sat_smt_checks);
    st.update("virtual_solver.checks.undef", m_stats.m_num_undef_smt_checks);
}
void virtual_solver_factory::reset_statistics()
{
    m_stats.reset();
    m_check_sat_watch.reset();
    m_check_undef_watch.reset();
    m_check_watch.reset();
    m_proof_watch.reset();
}

virtual_solver_factory::~virtual_solver_factory()
{
    for (unsigned i = 0, e = m_solvers.size(); i < e; ++i)
    { dealloc(m_solvers[i]); }
}



}
