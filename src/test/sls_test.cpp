
#include "ast/sls/sls_bv_eval.h"
#include "ast/sls/sls_bv_terms.h"
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
        unsigned num_vars() const override { return 0; }
        indexed_uint_set const& unsat() const override { return s; }
        indexed_uint_set const& unsat_vars() const override { return s; }
        void shift_weights() override {}
        void on_model(model_ref& mdl) override {}
        unsigned num_external_in_unsat_vars() const override { return 0; }
        sat::bool_var add_var() override { return sat::null_bool_var;}
        void add_clause(unsigned n, sat::literal const* lits) override {}
        //        void collect_statistics(statistics& st) const override {}
        // void reset_statistics() override {}
        void force_restart() override {}
        std::ostream& display(std::ostream& out)  override { return out; }
        reslimit& rlimit() override { return m_limit; }
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
            std::function<bool(expr*, unsigned)> value = [](expr*, unsigned) {
                return false;
            };
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
                auto const& val = ev.wval(e);
                rational n1, n2;

                n1 = val.get_value();

                VERIFY(bv.is_numeral(r, n2));
                if (n1 != n2) {
                    verbose_stream() << mk_pp(e, m) << " computed value " << val << "\n";
                    verbose_stream() << "should be " << n2 << "\n";
                }
                SASSERT(n1 == n2);
                VERIFY(n1 == n2);
            }
            else if (m.is_bool(e)) {
                auto val1 = ev.bval1(to_app(e));
                auto val2 = m.is_true(r);
                if (val1 != val2) {
                    verbose_stream() << mk_pp(e, m) << " computed value " << val1 
                        << " at odds with definition " << val2 << "\n";
                }
                SASSERT(val1 == val2);
                VERIFY(val1 == val2);
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
                .push_back(bv.mk_bv_rotate_right(a, b))
    //            .push_back(bv.mk_bvsadd_ovfl(a, b))
    //            .push_back(bv.mk_bvneg_ovfl(a))
    //            .push_back(bv.mk_bvsmul_no_ovfl(a, b))
    //            .push_back(bv.mk_bvsmul_no_udfl(a, b))
    //            .push_back(bv.mk_bvsmul_ovfl(a, b))
    //            .push_back(bv.mk_bvsdiv_ovfl(a, b))
                ;
            return result;
        }


        // e = op(a, b), 
        // update value of a to "random"
        // repair a based on computed values.
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
            std::function<bool(expr*, unsigned)> value = [&](expr*, unsigned) {
                return rand() % 2 == 0;
                };
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
                SASSERT(m.is_true(r) || m.is_false(r));
                auto val = m.is_true(r);
                auto val2 = ev.bval1(to_app(e2));
                if (val != val2) {
                    ev.set(e2, val);
                    auto rep1 = ev.repair_down(to_app(e2), idx);
                    if (!rep1) {
                        verbose_stream() << "Not repaired " << mk_pp(e1, m) << " " << mk_pp(e2, m) << " r: " << r << "\n";
                    }
                    auto val3 = ev.bval0(e2);
                    if (val3 != val) {
                        verbose_stream() << "Repaired but not corrected " << mk_pp(e2, m) << "\n";
                        ev.display(std::cout);
                        exit(0);
                    }
                    //SASSERT(rep1);
                }
            }
            if (bv.is_bv(e1)) {
                auto& val1 = ev.wval(e1);
                auto& val2 = ev.wval(e2);
                if (!val1.eq(val2)) {
                    val2.set(val1.bits());
                    auto rep2 = ev.repair_down(to_app(e2), idx);
                    if (!rep2) {
                        verbose_stream() << "Not repaired " << mk_pp(e2, m) << "\n";
                    }                    
                    auto val3 = ev.wval(e2);
                    verbose_stream() << val3 << "\n";
                    VERIFY(val3.commit_eval_check_tabu());
                    if (!val3.eq(val1)) {
                        verbose_stream() << "Repaired but not corrected " << mk_pp(e2, m) << "\n";
                    }
                    //SASSERT(rep2);
                }
            }
        }

        // todo: 
        void test_fixed() {

        }
    };
}


static void test_eval1() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);

    expr_ref e(m);

    bv::sls_test validator(m);

    unsigned k = 0;
    unsigned bw = 6;
    for (unsigned i = 0; i < 1ul << bw; ++i) {
        expr_ref a(bv.mk_numeral(rational(i), bw), m);
        for (unsigned j = 0; j < 1ul << bw; ++j) {
            expr_ref b(bv.mk_numeral(rational(j), bw), m);
            ++k;
            if (k % 1000 == 0)
                verbose_stream() << "tests " << k << "\n";
            validator.check_eval(a, b, j);
        }
    }
}

static void test_repair1() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    expr_ref e(m);
    bv::sls_test validator(m);

    unsigned k = 0;
    unsigned bw = 6;
    for (unsigned i = 0; i < 1ul << bw; ++i) {
        expr_ref a(bv.mk_numeral(rational(i), bw), m);
        for (unsigned j = 0; j < 1ul << bw; ++j) {
            expr_ref b(bv.mk_numeral(rational(j), bw), m);
            ++k;
            if (k % 1000 == 0)
                verbose_stream() << "tests " << k << "\n";
            validator.check_repair(a, b, j);
        }
    }
}

void tst_sls_test() {
    //test_eval1();
    //test_repair1();

}
