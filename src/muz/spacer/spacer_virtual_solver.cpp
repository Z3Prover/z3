/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_virtual_solver.cpp

Abstract:

   multi-solver view of a single smt::kernel

Author:

    Arie Gurfinkel

Notes:

--*/

#include "muz/spacer/spacer_virtual_solver.h"
#include "ast/ast_util.h"
#include "ast/ast_pp_util.h"
#include "muz/spacer/spacer_util.h"
#include "ast/rewriter/bool_rewriter.h"

#include "ast/proof_checker/proof_checker.h"

#include "ast/scoped_proof.h"

namespace spacer {
virtual_solver::virtual_solver(virtual_solver_factory &factory,
                               smt::kernel &context, app* pred) :
    solver_na2as(context.m()),
    m_factory(factory),
    m(context.m()),
    m_context(context),
    m_pred(pred, m),
    m_virtual(!m.is_true(pred)),
    m_assertions(m),
    m_head(0),
    m_flat(m),
    m_pushed(false),
    m_in_delay_scope(false),
    m_dump_benchmarks(factory.fparams().m_dump_benchmarks),
    m_dump_counter(0),
    m_proof(m)
{
    // -- insert m_pred->true background assumption this will not
    // -- change m_context, but will add m_pred to
    // -- the private field solver_na2as::m_assumptions
    if (m_virtual)
    { solver_na2as::assert_expr(m.mk_true(), m_pred); }
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
static bool matches_fact(expr_ref_vector &args, expr* &match)
{
    ast_manager &m = args.get_manager();
    expr *fact = args.back();
    for (unsigned i = 0, sz = args.size() - 1; i < sz; ++i) {
        expr *arg = args.get(i);
        if (m.is_proof(arg) &&
                m.has_fact(to_app(arg)) &&
                m.get_fact(to_app(arg)) == fact) {
            match = arg;
            return true;
        }
    }
    return false;
}


class elim_aux_assertions {
    app_ref m_aux;
public:
    elim_aux_assertions(app_ref aux) : m_aux(aux) {}

    void mk_or_core(expr_ref_vector &args, expr_ref &res)
    {
        ast_manager &m = args.get_manager();
        unsigned j = 0;
        for (unsigned i = 0, sz = args.size(); i < sz; ++i) {
            if (m.is_false(args.get(i))) { continue; }
            if (i != j) { args [j] = args.get(i); }
            ++j;
        }
        SASSERT(j >= 1);
        res = j > 1 ? m.mk_or(j, args.c_ptr()) : args.get(0);
    }

    void mk_app(func_decl *decl, expr_ref_vector &args, expr_ref &res)
    {
        ast_manager &m = args.get_manager();
        bool_rewriter brwr(m);

        if (m.is_or(decl))
        { mk_or_core(args, res); }
        else if (m.is_iff(decl) && args.size() == 2)
            // avoiding simplifying equalities. In particular,
            // we don't want (= (not a) (not b)) to be reduced to (= a b)
        { res = m.mk_iff(args.get(0), args.get(1)); }
        else
        { brwr.mk_app(decl, args.size(), args.c_ptr(), res); }
    }

    void operator()(ast_manager &m, proof *pr, proof_ref &res)
    {
        DEBUG_CODE(proof_checker pc(m);
                   expr_ref_vector side(m);
                   SASSERT(pc.check(pr, side));
                  );
        obj_map<app, app*> cache;
        bool_rewriter brwr(m);

        // for reference counting of new proofs
        app_ref_vector pinned(m);

        ptr_vector<app> todo;
        todo.push_back(pr);

        expr_ref not_aux(m);
        not_aux = m.mk_not(m_aux);

        expr_ref_vector args(m);

        while (!todo.empty()) {
            app *p, *r;
            expr *a;

            p = todo.back();
            if (cache.find(pr, r)) {
                todo.pop_back();
                continue;
            }

            SASSERT(!todo.empty() || pr == p);
            bool dirty = false;
            unsigned todo_sz = todo.size();
            args.reset();
            for (unsigned i = 0, sz = p->get_num_args(); i < sz; ++i) {
                expr* arg = p->get_arg(i);
                if (arg == m_aux.get()) {
                    dirty = true;
                    args.push_back(m.mk_true());
                } else if (arg == not_aux.get()) {
                    dirty = true;
                    args.push_back(m.mk_false());
                }
                // skip (asserted m_aux)
                else if (m.is_asserted(arg, a) && a == m_aux.get()) {
                    dirty = true;
                }
                // skip (hypothesis m_aux)
                else if (m.is_hypothesis(arg, a) && a == m_aux.get()) {
                    dirty = true;
                } else if (is_app(arg) && cache.find(to_app(arg), r)) {
                    dirty |= (arg != r);
                    args.push_back(r);
                } else if (is_app(arg))
                { todo.push_back(to_app(arg)); }
                else
                    // -- not an app
                { args.push_back(arg); }

            }
            if (todo_sz < todo.size()) {
                // -- process parents
                args.reset();
                continue;
            }

            // ready to re-create
            app_ref newp(m);
            if (!dirty) { newp = p; }
            else if (m.is_unit_resolution(p)) {
                if (args.size() == 2)
                    // unit resolution with m_aux that got collapsed to nothing
                { newp = to_app(args.get(0)); }
                else {
                    ptr_vector<proof> parents;
                    for (unsigned i = 0, sz = args.size() - 1; i < sz; ++i)
                    { parents.push_back(to_app(args.get(i))); }
                    SASSERT(parents.size() == args.size() - 1);
                    newp = m.mk_unit_resolution(parents.size(), parents.c_ptr());
                    // XXX the old and new facts should be
                    // equivalent. The test here is much
                    // stronger. It might need to be relaxed.
                    SASSERT(m.get_fact(newp) == args.back());
                    pinned.push_back(newp);
                }
            } else if (matches_fact(args, a)) {
                newp = to_app(a);
            } else {
                expr_ref papp(m);
                mk_app(p->get_decl(), args, papp);
                newp = to_app(papp.get());
                pinned.push_back(newp);
            }
            cache.insert(p, newp);
            todo.pop_back();
            CTRACE("virtual",
                   p->get_decl_kind() == PR_TH_LEMMA &&
                   p->get_decl()->get_parameter(0).get_symbol() == "arith" &&
                   p->get_decl()->get_num_parameters() > 1 &&
                   p->get_decl()->get_parameter(1).get_symbol() == "farkas",
                   tout << "Old pf: " << mk_pp(p, m) << "\n"
                   << "New pf: " << mk_pp(newp, m) << "\n";);
        }

        proof *r;
        VERIFY(cache.find(pr, r));

        DEBUG_CODE(
            proof_checker pc(m);
            expr_ref_vector side(m);
            SASSERT(pc.check(r, side));
        );

        res = r ;
    }
};
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
    lbool res = m_context.check(num_assumptions, assumptions);
    sw.stop();
    if (res == l_true) {
        m_factory.m_check_sat_watch.add(sw);
        m_factory.m_stats.m_num_sat_smt_checks++;
    } else if (res == l_undef) {
        m_factory.m_check_undef_watch.add(sw);
        m_factory.m_stats.m_num_undef_smt_checks++;
    }
    set_status(res);

    if (m_dump_benchmarks &&
            sw.get_seconds() >= m_factory.fparams().m_dump_min_time) {
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

        out.close();

        if (m_factory.fparams().m_dump_recheck) {
            scoped_no_proof _no_proof_(m);
            smt_params p;
            stopwatch sw2;
            smt::kernel kernel(m, p);
            for (unsigned i = 0, sz = m_context.size(); i < sz; ++i)
                { kernel.assert_expr(m_context.get_formula(i)); }
            sw2.start();
            kernel.check(num_assumptions, assumptions);
            sw2.stop();
            verbose_stream() << file_name.str() << " :orig "
                             << sw.get_seconds() << " :new " << sw2.get_seconds();
        }
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
void virtual_solver::pop_core(unsigned n)
{
    SASSERT(!m_pushed || get_scope_level() > 0);
    if (m_pushed) {
        SASSERT(!m_in_delay_scope);
        m_context.pop(n);
        m_pushed = get_scope_level() - n > 0;
    } else
    { m_in_delay_scope = get_scope_level() - n > 0; }
}

void virtual_solver::get_unsat_core(ptr_vector<expr> &r)
{
    for (unsigned i = 0, sz = m_context.get_unsat_core_size(); i < sz; ++i) {
        expr *core = m_context.get_unsat_core_expr(i);
        if (is_aux_predicate(core)) { continue; }
        r.push_back(core);
    }
}

void virtual_solver::assert_expr(expr *e)
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
void virtual_solver::refresh()
{
    SASSERT(!m_pushed);
    m_head = 0;
}

void virtual_solver::reset()
{
    SASSERT(!m_pushed);
    m_head = 0;
    m_assertions.reset();
    m_factory.refresh();
}

void virtual_solver::get_labels(svector<symbol> &r)
{
    r.reset();
    buffer<symbol> tmp;
    m_context.get_relevant_labels(0, tmp);
    r.append(tmp.size(), tmp.c_ptr());
}

solver* virtual_solver::translate(ast_manager& m, params_ref const& p)
{
    UNREACHABLE();
    return 0;
}
void virtual_solver::updt_params(params_ref const &p)
{ m_factory.updt_params(p); }
void virtual_solver::collect_param_descrs(param_descrs &r)
{ m_factory.collect_param_descrs(r); }
void virtual_solver::set_produce_models(bool f)
{ m_factory.set_produce_models(f); }
bool virtual_solver::get_produce_models()
{return m_factory.get_produce_models(); }
smt_params &virtual_solver::fparams()
{return m_factory.fparams();}

void virtual_solver::to_smt2_benchmark(std::ostream &out,
                                       smt::kernel &context,
                                       unsigned num_assumptions,
                                       expr * const * assumptions,
                                       char const * name,
                                       symbol const &logic,
                                       char const * status,
                                       char const * attributes)
{
    ast_pp_util pp(m);
    expr_ref_vector asserts(m);


    for (unsigned i = 0, sz = context.size(); i < sz; ++i) {
        asserts.push_back(context.get_formula(i));
        pp.collect(asserts.back());
    }
    pp.collect(num_assumptions, assumptions);
    pp.display_decls(out);
    pp.display_asserts(out, asserts);
    out << "(check-sat ";
    for (unsigned i = 0; i < num_assumptions; ++i)
    { out << mk_pp(assumptions[i], m) << " "; }
    out << ")\n";
}


virtual_solver_factory::virtual_solver_factory(ast_manager &mgr, smt_params &fparams) :
    m_fparams(fparams), m(mgr), m_context(m, m_fparams)
{
    m_stats.reset();
}

virtual_solver* virtual_solver_factory::mk_solver()
{
    std::stringstream name;
    name << "vsolver#" << m_solvers.size();
    app_ref pred(m);
    pred = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());
    SASSERT(m_context.get_scope_level() == 0);
    m_solvers.push_back(alloc(virtual_solver, *this, m_context, pred));
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
    m_context.reset_statistics();
    m_stats.reset();
    m_check_sat_watch.reset();
    m_check_undef_watch.reset();
    m_check_watch.reset();
    m_proof_watch.reset();
}

void virtual_solver_factory::refresh()
{
    m_context.reset();
    for (unsigned i = 0, e = m_solvers.size(); i < e; ++i)
    { m_solvers [i]->refresh(); }
}

virtual_solver_factory::~virtual_solver_factory()
{
    for (unsigned i = 0, e = m_solvers.size(); i < e; ++i)
    { dealloc(m_solvers [i]); }
}



}
