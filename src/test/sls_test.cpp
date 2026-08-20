
#include "ast/sls/sls_bv_eval.h"
#include "ast/sls/sls_bv_terms.h"
#include "ast/fpa_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"

namespace bv {

    class my_sat_solver_context : public sls::sat_solver_context {
        vector<sat::clause_info> m_clauses;
        indexed_uint_set s;
        reslimit m_limit;
    public:
        int m_eval_calls = 0;
        unsigned m_last_num_nodes = 0;
        unsigned m_last_num_vars = 0;
        unsigned m_last_num_candidates = 0;

        my_sat_solver_context() {}

        vector<sat::clause_info> const& clauses() const override { return m_clauses; }
        sat::clause_info const& get_clause(unsigned idx) const override { return m_clauses[idx]; }
        ptr_iterator<unsigned> get_use_list(sat::literal lit) override { return ptr_iterator<unsigned>(nullptr, nullptr); }
        void flip(sat::bool_var v) override {  }
        sat::bool_var external_flip() override { return sat::null_bool_var; }
        double reward(sat::bool_var v) override { return 0; }
        double get_weigth(unsigned clause_idx) override { return 0; }
        bool is_true(sat::literal lit) override { return true; }
        bool try_rotate(sat::bool_var v, sat::bool_var_set& rotated, unsigned& bound) override { return false; }
        unsigned m_num_vars = 0;
        unsigned num_vars() const override { return m_num_vars; }
        indexed_uint_set const& unsat() const override { return s; }
        indexed_uint_set const& unsat_vars() const override { return s; }
        void shift_weights() override {}
        void on_model(model_ref& mdl) override {}
        unsigned num_external_in_unsat_vars() const override { return 0; }
        sat::bool_var add_var() override { 
            return m_num_vars++;
        }
        void add_clause(unsigned n, sat::literal const* lits) override {}
        void force_restart() override {}
        std::ostream& display(std::ostream& out)  override { return out; }
        reslimit& rlimit() override { return m_limit; }
        uint64_t timestamp(sat::bool_var v) override { return 0; }
        int eval_fpa_candidates(expr* atom, bool desired, ptr_vector<expr> const& dag, ptr_vector<expr> const& vars, ptr_vector<expr> const& values, unsigned num_candidates) override {
            ++m_eval_calls;
            m_last_num_nodes = dag.size();
            m_last_num_vars = vars.size();
            m_last_num_candidates = num_candidates;
            return num_candidates == 0 ? -1 : 0;
        }
    };


    class sls_test {
        ast_manager& m;
        bv_util bv;

    public:
        sls_test(ast_manager& m):
            m(m),
            bv(m)
        {}

        void check_eval(expr* a, expr* b, unsigned j) {
            auto es = create_exprs(a, b, j);
            for (expr* e : es)
                check_eval(e);
        }

        void check_eval(expr* e) {
            expr_ref_vector es(m);
            bv_util bv(m);
            es.push_back(e);

            my_sat_solver_context solver;
            sls::context ctx(m, solver);
            sls::bv_terms terms(ctx);
            sls::bv_eval ev(terms, ctx);
            for (auto e : subterms_postorder::all(es)) 
                ev.register_term(e);            
            ev.init();
            th_rewriter rw(m);
            expr_ref r(e, m);
            rw(r);

            if (bv.is_bv(e)) {
                auto const & val = ev.wval(e);
                rational n1, n2;

                n1 = val.get_value();

                VERIFY(bv.is_numeral(r, n2));
                ENSURE(n1 == n2);
            }
            else if (m.is_bool(e)) {
                auto val1 = ev.bval1(to_app(e));
                auto val2 = m.is_true(r);
                ENSURE(val1 == val2);
            }
        }

        expr_ref_vector create_exprs(expr* a, expr* b, unsigned j) {
            expr_ref_vector result(m);
            result.push_back(bv.mk_bv_add(a, b))
                .push_back(bv.mk_bv_mul(a, b))
                .push_back(bv.mk_bv_sub(a, b))
                .push_back(bv.mk_bv_udiv(a, b))
                .push_back(bv.mk_bv_sdiv(a, b))
                .push_back(bv.mk_bv_srem(a, b))
                .push_back(bv.mk_bv_urem(a, b))
                .push_back(bv.mk_bv_smod(a, b))
                .push_back(bv.mk_bv_shl(a, b))
                .push_back(bv.mk_bv_ashr(a, b))
                .push_back(bv.mk_bv_lshr(a, b))
                .push_back(bv.mk_bv_and(a, b))
                .push_back(bv.mk_bv_or(a, b))
                .push_back(bv.mk_bv_xor(a, b))
                .push_back(bv.mk_bv_neg(a))
                .push_back(bv.mk_bv_not(a))
                .push_back(bv.mk_bvumul_ovfl(a, b))
                .push_back(bv.mk_bvumul_no_ovfl(a, b))
                .push_back(bv.mk_zero_extend(3, a))
                .push_back(bv.mk_sign_extend(3, a))
                .push_back(bv.mk_ule(a, b))
                .push_back(bv.mk_sle(a, b))
                .push_back(bv.mk_concat(a, b))
                .push_back(bv.mk_extract(4, 2, a))
                .push_back(bv.mk_bvuadd_ovfl(a, b))
                .push_back(bv.mk_bv_rotate_left(a, j))
                .push_back(bv.mk_bv_rotate_right(a, j))
                .push_back(bv.mk_bv_rotate_left(a, b))
                .push_back(bv.mk_bv_rotate_right(a, b));
            return result;
        }

        void check_repair(expr* a, expr* b, unsigned j) {
            expr_ref x(m.mk_const("x", bv.mk_sort(bv.get_bv_size(a))), m);
            expr_ref y(m.mk_const("y", bv.mk_sort(bv.get_bv_size(b))), m);
            auto es1 = create_exprs(a, b, j);
            auto es2 = create_exprs(x, b, j);
            auto es3 = create_exprs(a, y, j);
            for (unsigned i = 0; i < es1.size(); ++i) {                
                auto e1 = es1.get(i);
                auto e2 = es2.get(i);
                auto e3 = es3.get(i);
                if (bv.is_bv_sdiv(e1))
                    continue;
                if (bv.is_bv_srem(e1))
                    continue;
                if (bv.is_bv_smod(e1))
                    continue;
                if (is_app_of(e1, bv.get_fid(), OP_BUADD_OVFL))
                    continue;
                check_repair_idx(e1, e2, 0, x);
                if (is_app(e1) && to_app(e1)->get_num_args() == 2)
                    check_repair_idx(e1, e3, 1, y);
            }
        }

        random_gen rand;

        void check_repair_idx(expr* e1, expr* e2, unsigned idx, expr* x) {            
            expr_ref_vector es(m);
            bv_util bv(m);
            th_rewriter rw(m);
            expr_ref r(e1, m);
            rw(r);
            es.push_back(m.is_false(r) ? m.mk_not(e1) : e1);
            es.push_back(m.is_false(r) ? m.mk_not(e2) : e2);

            my_sat_solver_context solver;
            sls::context ctx(m, solver);
            sls::bv_terms terms(ctx);
            sls::bv_eval ev(terms, ctx);
            for (auto e : subterms_postorder::all(es))
                ev.register_term(e);
            ev.init();

            if (m.is_bool(e1)) {
                ENSURE(m.is_true(r) || m.is_false(r));
                auto val = m.is_true(r);
                auto val2 = ev.bval1(to_app(e2));
                if (val != val2) {
                    ev.set(e2, val);
                    auto rep1 = ev.repair_down(to_app(e2), idx);
                    if (rep1) {
                        auto val3 = ev.bval0(e2);
                        ENSURE(val3 == val);
                    }
                }
            }
            if (bv.is_bv(e1)) {
                auto& val1 = ev.wval(e1);
                auto& val2 = ev.wval(e2);
                if (!val1.eq(val2)) {
                    val2.set(val1.bits());
                    auto rep2 = ev.repair_down(to_app(e2), idx);
                    if (rep2) {
                        auto val3 = ev.wval(e2);
                        VERIFY(val3.commit_eval_check_tabu());
                    }
                }
            }
        }
    };
}

[[maybe_unused]] static void test_eval1() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);

    bv::sls_test validator(m);

    unsigned k = 0;
    unsigned bw = 6;
    for (unsigned i = 0; i < 1ul << bw; ++i) {
        expr_ref a(bv.mk_numeral(rational(i), bw), m);
        for (unsigned j = 0; j < 1ul << bw; ++j) {
            expr_ref b(bv.mk_numeral(rational(j), bw), m);
            ++k;
            validator.check_eval(a, b, j);
        }
    }
}

[[maybe_unused]] static void test_repair1() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    bv::sls_test validator(m);

    unsigned k = 0;
    unsigned bw = 6;
    for (unsigned i = 0; i < 1ul << bw; ++i) {
        expr_ref a(bv.mk_numeral(rational(i), bw), m);
        for (unsigned j = 0; j < 1ul << bw; ++j) {
            expr_ref b(bv.mk_numeral(rational(j), bw), m);
            ++k;
            validator.check_repair(a, b, j);
        }
    }
}

static expr_ref mk_fp_one(ast_manager& m, fpa_util& fpa, sort* s) {
    scoped_mpf one(fpa.fm());
    fpa.fm().set(one, fpa.get_ebits(s), fpa.get_sbits(s), 1);
    return expr_ref(fpa.mk_value(one), m);
}

static void test_fp_plugin_ground_eval() {
    ast_manager m;
    reg_decl_plugins(m);
    fpa_util fpa(m);
    bv::my_sat_solver_context solver;
    sls::context ctx(m, solver);

    sort_ref fps(fpa.mk_float_sort(8, 24), m);
    expr_ref rm(fpa.mk_round_nearest_ties_to_even(), m);
    expr_ref z0(fpa.mk_pzero(fps), m);
    expr_ref sum(fpa.mk_add(rm, z0, z0), m);
    expr_ref eq(fpa.mk_float_eq(sum, z0), m);

    ctx.add_input_assertion(eq);
    ENSURE(ctx.check() == l_true);
    ENSURE(fpa.is_zero(ctx.get_value(sum)));
}

static void test_fp_plugin_simple_repair() {
    ast_manager m;
    reg_decl_plugins(m);
    fpa_util fpa(m);
    bv::my_sat_solver_context solver;
    sls::context ctx(m, solver);

    sort_ref fps(fpa.mk_float_sort(8, 24), m);
    expr_ref x(m.mk_const("x", fps), m);
    expr_ref one = mk_fp_one(m, fpa, fps);
    expr_ref eq(fpa.mk_float_eq(x, one), m);

    ctx.add_input_assertion(eq);
    ENSURE(ctx.check() == l_true);
    scoped_mpf xv(fpa.fm()), ov(fpa.fm());
    ENSURE(fpa.is_numeral(ctx.get_value(x), xv));
    ENSURE(fpa.is_numeral(one, ov));
    ENSURE(fpa.fm().eq(xv, ov));
}

static void test_fp_plugin_reverse_eq_repair() {
    ast_manager m;
    reg_decl_plugins(m);
    fpa_util fpa(m);
    bv::my_sat_solver_context solver;
    sls::context ctx(m, solver);

    sort_ref fps(fpa.mk_float_sort(8, 24), m);
    expr_ref x(m.mk_const("x", fps), m);
    expr_ref one = mk_fp_one(m, fpa, fps);
    expr_ref eq(fpa.mk_float_eq(one, x), m);

    ctx.add_input_assertion(eq);
    ENSURE(ctx.check() == l_true);
    scoped_mpf xv(fpa.fm()), ov(fpa.fm());
    ENSURE(fpa.is_numeral(ctx.get_value(x), xv));
    ENSURE(fpa.is_numeral(one, ov));
    ENSURE(fpa.fm().eq(xv, ov));
}

static void test_fp_plugin_or_dag_repair() {
    ast_manager m;
    reg_decl_plugins(m);
    fpa_util fpa(m);
    bv::my_sat_solver_context solver;
    sls::context ctx(m, solver);

    sort_ref fps(fpa.mk_float_sort(8, 24), m);
    expr_ref x(m.mk_const("x", fps), m);
    expr_ref y(m.mk_const("y", fps), m);
    expr_ref one = mk_fp_one(m, fpa, fps);
    scoped_mpf two_mpf(fpa.fm());
    fpa.fm().set(two_mpf, fpa.get_ebits(fps), fpa.get_sbits(fps), 2);
    expr_ref two(fpa.mk_value(two_mpf), m);
    expr_ref ex(fpa.mk_float_eq(x, one), m);
    expr_ref ey(fpa.mk_float_eq(y, two), m);
    expr_ref disj(m.mk_or(ex, ey), m);

    ctx.add_input_assertion(disj);
    ENSURE(ctx.check() == l_true);
    ENSURE(m.is_true(ctx.get_value(disj)));
}

static void test_fp_plugin_runtime_override() {
    ast_manager m;
    reg_decl_plugins(m);
    fpa_util fpa(m);
    bv::my_sat_solver_context solver;
    sls::context ctx(m, solver);

    sort_ref fps(fpa.mk_float_sort(8, 24), m);
    expr_ref x(m.mk_const("x", fps), m);
    expr_ref y(m.mk_const("y", fps), m);
    expr_ref one = mk_fp_one(m, fpa, fps);
    scoped_mpf two_mpf(fpa.fm());
    fpa.fm().set(two_mpf, fpa.get_ebits(fps), fpa.get_sbits(fps), 2);
    expr_ref two(fpa.mk_value(two_mpf), m);
    expr_ref ex(fpa.mk_float_eq(x, one), m);
    expr_ref ey(fpa.mk_float_eq(y, two), m);
    expr_ref disj(m.mk_or(ex, ey), m);

    ctx.add_input_assertion(disj);
    ENSURE(ctx.check() == l_true);
    ENSURE(solver.m_eval_calls > 0);
    ENSURE(solver.m_last_num_nodes >= 3);
    ENSURE(solver.m_last_num_vars >= 1);
    ENSURE(solver.m_last_num_candidates >= 1);
}

static void test_fp_plugin_callback_gated_by_params() {
    ast_manager m;
    reg_decl_plugins(m);
    fpa_util fpa(m);
    bv::my_sat_solver_context solver;
    sls::context ctx(m, solver);

    params_ref p;
    p.set_sym(symbol("fp.mode"), symbol("cpu"));
    p.set_bool("fp.use_callback", true);
    ctx.updt_params(p);

    sort_ref fps(fpa.mk_float_sort(8, 24), m);
    expr_ref x(m.mk_const("x", fps), m);
    expr_ref y(m.mk_const("y", fps), m);
    expr_ref one = mk_fp_one(m, fpa, fps);
    scoped_mpf two_mpf(fpa.fm());
    fpa.fm().set(two_mpf, fpa.get_ebits(fps), fpa.get_sbits(fps), 2);
    expr_ref two(fpa.mk_value(two_mpf), m);
    expr_ref ex(fpa.mk_float_eq(x, one), m);
    expr_ref ey(fpa.mk_float_eq(y, two), m);
    expr_ref disj(m.mk_or(ex, ey), m);

    ctx.add_input_assertion(disj);
    ENSURE(ctx.check() == l_true);
    ENSURE(solver.m_eval_calls == 0);
}




void tst_sls_test() {
    test_fp_plugin_ground_eval();
    test_fp_plugin_simple_repair();
    test_fp_plugin_reverse_eq_repair();
    test_fp_plugin_or_dag_repair();
    test_fp_plugin_runtime_override();
    test_fp_plugin_callback_gated_by_params();
}
