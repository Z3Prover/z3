
#include "ast/sls/bv_sls_eval.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"

namespace bv {
    class sls_test {
        ast_manager& m;
        bv_util bv;

    public:
        sls_test(ast_manager& m):
            m(m),
            bv(m)
        {}

        void check_eval(expr* e) {
            std::function<bool(expr*, unsigned)> value = [](expr*, unsigned) {
                return false;
            };
            expr_ref_vector es(m);
            bv_util bv(m);
            es.push_back(e);
            sls_eval ev(m);
            ev.init_eval(es, value);
            th_rewriter rw(m);
            expr_ref r(e, m);
            rw(r);

            if (bv.is_bv(e)) {
                auto const& val = ev.wval0(e);
                rational n1, n2;

                val.get_value(val.bits, n1);

                VERIFY(bv.is_numeral(r, n2));
                if (n1 != n2) {
                    verbose_stream() << mk_pp(e, m) << " computed value " << val << "\n";
                    verbose_stream() << "should be " << n2 << "\n";
                }
                SASSERT(n1 == n2);
                VERIFY(n1 == n2);
            }
            else if (m.is_bool(e)) {
                auto val1 = ev.bval0(e);
                auto val2 = m.is_true(r) ? true : false;
                if (val1 != val2) {
                    verbose_stream() << mk_pp(e, m) << " computed value " << val1 << " at odds with definition\n";
                }
                SASSERT(val1 == val2);
                VERIFY(val1 == val2);
            }
        }

        void check(expr* a, expr* b) {
            expr_ref e(m);
            auto& validator = *this;
            e = bv.mk_bv_add(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_mul(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_sub(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_udiv(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_sdiv(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_srem(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_urem(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_smod(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_shl(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_ashr(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_lshr(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_and(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_or(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_xor(a, b);
            validator.check_eval(e);

            e = bv.mk_bv_neg(a);
            validator.check_eval(e);

            e = bv.mk_bv_not(a);
            validator.check_eval(e);

            e = bv.mk_bvumul_ovfl(a, b);
            validator.check_eval(e);

            e = bv.mk_bvumul_no_ovfl(a, b);
            validator.check_eval(e);

            e = bv.mk_zero_extend(3, a);
            validator.check_eval(e);

            e = bv.mk_sign_extend(3, a);
            validator.check_eval(e);

            e = bv.mk_ule(a, b);
            validator.check_eval(e);

            e = bv.mk_sle(a, b);
            validator.check_eval(e);

            e = bv.mk_concat(a, b);
            validator.check_eval(e);

            e = bv.mk_extract(6, 3, a);
            validator.check_eval(e);

            e = bv.mk_bvuadd_ovfl(a, b);
            validator.check_eval(e);


#if 0

            e = bv.mk_bvsadd_ovfl(a, b);
            validator.check_eval(e);

            e = bv.mk_bvneg_ovfl(a);
            validator.check_eval(e);

            e = bv.mk_bvsmul_no_ovfl(a, b);
            validator.check_eval(e);

            e = bv.mk_bvsmul_no_udfl(a, b);
            validator.check_eval(e);

            e = bv.mk_bvsmul_ovfl(a, b);
            validator.check_eval(e);

            e = bv.mk_bvsdiv_ovfl(a, b);
            validator.check_eval(e);

#endif

#if 0
            e = bv.mk_rotate_left(a, b);
            validator.check_eval(e);

            e = bv.mk_rotate_right(a, b);
            validator.check_eval(e);

            e = bv.mk_rotate_left_ext(a, b);
            validator.check_eval(e);

            e = bv.mk_rotate_right_ext(a, b);
            validator.check_eval(e);

#endif
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
    for (unsigned i = 0; i < 256; ++i) {
        expr_ref a(bv.mk_numeral(rational(i), 8), m);
        for (unsigned j = 0; j < 256; ++j) {
            expr_ref b(bv.mk_numeral(rational(j), 8), m);

            ++k;
            if (k % 1000 == 0)
                verbose_stream() << "tests " << k << "\n";

            validator.check(a, b);

        }
    }
}

void tst_sls_test() {
    test_eval1();
}
