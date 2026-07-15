
#include "ast/euf/ho_matcher.h"

namespace euf {
    class test_ho_matcher {
        struct plugins {
            plugins(ast_manager& m) {
                reg_decl_plugins(m);
            }
        };
        ast_manager   m;
        plugins       m_plugins;
        trail_stack   m_trail;
        ho_matcher    m_matcher;
        arith_util    m_arith;
        array_util    m_array;
        sort_ref      m_int;
        func_decl_ref m_f;

    public:
        test_ho_matcher() : m_plugins(m), m_matcher(m, m_trail), m_arith(m), m_array(m), m_int(m), m_f(m) {
            m_int = m_arith.mk_int();
            m_f = m.mk_func_decl(symbol("f"), m_int, m_int, m_int);

            std::function<void(ho_subst& s)> on_match = [&](ho_subst& s) {
                s.display(verbose_stream() << "match\n");                
            };

            m_matcher.set_on_match(on_match);
        }

        // f(v0, v1) = f(1, 0)
        void test1() {
            expr_ref v0(m.mk_var(0, m_int), m);
            expr_ref v1(m.mk_var(1, m_int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref_vector args(m);
            args.push_back(v0);
            args.push_back(v1);
            expr_ref pat(m.mk_app(m_f, args), m);
            args.reset();
            args.push_back(one);
            args.push_back(zero);
            expr_ref t(m.mk_app(m_f, args), m);
            m_matcher.add_pattern(pat.get());
            IF_VERBOSE(0, verbose_stream() << "test2 " << pat << " ~ " << t << "\n");
            m_matcher(pat, t, 2);
        }

        // f(v0, v0) = f(1, 0)
        // should fail
        void test2() {
            expr_ref v0(m.mk_var(0, m_int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref_vector args(m);
            args.push_back(v0);
            args.push_back(v0);
            expr_ref pat(m.mk_app(m_f, args), m);
            args.reset();
            args.push_back(one);
            args.push_back(zero);
            expr_ref t(m.mk_app(m_f, args), m);
            m_matcher.add_pattern(pat.get());
            IF_VERBOSE(0, verbose_stream() << "test2 " << pat << " ~ " << t << "\n");
            m_matcher(pat, t, 1);
        }

        // v0(1) = 0
        void test3() {
            sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
            expr_ref v0(m.mk_var(0, int2int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref p(m_array.mk_select(v0, one), m);
            m_matcher.add_pattern(p.get());
            IF_VERBOSE(0, verbose_stream() << "test3 " << p << " ~ " << zero << "\n");
            m_matcher(p, zero, 1);
        }

        // v0(1) = 1
        void test4() {
            sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
            expr_ref v0(m.mk_var(0, int2int), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref p(m_array.mk_select(v0, one), m);
            m_matcher.add_pattern(p.get());
            IF_VERBOSE(0, verbose_stream() << "test4 " << p << " ~ " << one << "\n");
            m_matcher(p, one, 1);
        }

        // f(l') + sum l u f 
        void test5() {
            sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
            expr_ref F(m.mk_var(0, int2int), m);
            expr_ref L1(m.mk_var(1, m_int), m);
            expr_ref L(m.mk_var(2, m_int), m);
            expr_ref U(m.mk_var(3, m_int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            sort* domain[3] = { m_int.get(), m_int.get(), int2int.get() };
            func_decl_ref sum(m.mk_func_decl(symbol("sum"), 3, domain, m_int), m);
            func_decl_ref f(m.mk_func_decl(symbol("f"), m_int, m_int), m);
            expr* args[3] = { L, U, F };
            expr_ref pat(m); 
            expr_ref u(m.mk_const(symbol("u"), m_int), m);
            symbol x("x");
            sort* int_s = m_int.get();
            expr_ref s(m.mk_app(sum.get(), one.get(), u.get(), m.mk_lambda(1, &int_s, &x, m.mk_app(f, m.mk_var(0, m_int)))), m);
            s = m_arith.mk_add(s, m.mk_app(f.get(), zero));


            pat = m_arith.mk_add(m.mk_app(sum, (unsigned)3, args), m_array.mk_select(F, L1));
            IF_VERBOSE(0, verbose_stream() << "test5a: " << pat << " =?= " << s << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, s, 4);

            pat = m_arith.mk_add(m_array.mk_select(F, L1), m.mk_app(sum, (unsigned)3, args));
            IF_VERBOSE(0, verbose_stream() << "test5b: " << pat << " =?= " << s << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, s, 4);
        }

        // test patterns
        // H (2, 0) = f(2)
        // G (1) (2, 0) = f(1, 2)
        // G (1) (2, 1) = f(1, 2) // not unitary
        // H (0, 1) = f(2) // fail
        void test6() {
            sort_ref intint2int(m_array.mk_array_sort(m_int, m_int, m_int), m);
            func_decl_ref f1(m.mk_func_decl(symbol("f"), m_int, m_int), m);
            func_decl_ref f2(m.mk_func_decl(symbol("f"), m_int, m_int, m_int), m);
            expr_ref v0(m.mk_var(0, m_int), m);
            expr_ref v1(m.mk_var(1, m_int), m);
            expr_ref v2(m.mk_var(2, m_int), m);
            expr_ref H(m.mk_var(3, intint2int), m);
            expr* args[3] = { H.get(), v2, v0 };
            expr_ref pat(m_array.mk_select(3, args), m);
            expr_ref t(m.mk_app(f1.get(), v2), m);
            IF_VERBOSE(0, verbose_stream() << "test6a: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            expr* args2[3] = { H.get(), v1, v0 };
            pat = m_array.mk_select(3, args2);
            t = m.mk_app(f2.get(), v0, v1);
            IF_VERBOSE(0, verbose_stream() << "test6b: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            sort_ref int2intt(m_array.mk_array_sort(m_int, intint2int), m);
            expr_ref(m.mk_var(3, int2intt), m);
            expr_ref G(m.mk_var(3, int2intt), m);
            pat = m_array.mk_select(G.get(), v1);
            pat = m_array.mk_select(pat.get(), v2, v0);
            t = m.mk_app(f2.get(), v1, v2);
            IF_VERBOSE(0, verbose_stream() << "test6c: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            pat = m_array.mk_select(G, v1);
            pat = m_array.mk_select(pat, v2, v1);
            IF_VERBOSE(0, verbose_stream() << "test6d: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            pat = m_array.mk_select(H, v0, v2);
            IF_VERBOSE(0, verbose_stream() << "test6e: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);
        }

            // Structural regression test derived from TPTP ANA067^1 (which fails
            // under smt.ho_matching=true inside the full solver).
            // pattern:  (select (select v0 v3) v2)   with v0 a doubly-nested array (flex head)
            // term:     (select K ...)               matched term is itself array-sorted.
            // Exercises imitation/projection of a flex head against an array-sorted
            // term. The matcher must build only well-sorted bindings; the debug
            // asserts in match_goals::push and mk_project catch any regression that
            // commits an ill-sorted (extra array level) lambda/select.
            void test7() {
                sort_ref r(m_arith.mk_real(), m);
                sort_ref arr_rb(m_array.mk_array_sort(r, m.mk_bool_sort()), m);      // (Array Real Bool)
                sort_ref arr_r_rb(m_array.mk_array_sort(r, arr_rb), m);             // (Array Real (Array Real Bool))
                sort_ref arr_r_r_rb(m_array.mk_array_sort(r, arr_r_rb), m);         // v0 sort

                expr_ref v0(m.mk_var(0, arr_r_r_rb), m);
                expr_ref v2(m.mk_var(2, r), m);
                expr_ref v3(m.mk_var(3, r), m);
                expr_ref pat(m_array.mk_select(v0, v3), m);
                pat = m_array.mk_select(pat, v2);

                expr_ref K(m.mk_const(symbol("K"), arr_r_rb), m);
                expr_ref b(m.mk_const(symbol("b"), r), m);
                expr_ref t(m_array.mk_select(K, b), m);

                IF_VERBOSE(0, verbose_stream() << "test7: " << pat << " =?= " << t << "\n";);
                m_matcher.add_pattern(pat.get());
                m_matcher(pat, t, 5);

                // Faithful variant: the term index argument is itself
                // (select fun (lambda (t) c)) as in ANA067^1, i.e. a term whose
                // subterm is a function(array)-valued lambda. This forces the
                // matcher to decompose/imitate against a lambda-bearing term.
                sort_ref arr_rr(m_array.mk_array_sort(r, r), m);                    // (Array Real Real)
                sort_ref fun_sort(m_array.mk_array_sort(arr_rr, r), m);            // (Array (Array Real Real) Real)
                symbol tt("t");
                sort* r_s = r.get();
                expr_ref c0(m.mk_const(symbol("c0"), r), m);
                expr_ref lam(m.mk_lambda(1, &r_s, &tt, c0), m);                    // (lambda (t Real) c0)
                expr_ref fun(m.mk_const(symbol("fun"), fun_sort), m);
                expr_ref idx(m_array.mk_select(fun, lam), m);                      // : Real
                expr_ref t2(m_array.mk_select(K, idx), m);
                IF_VERBOSE(0, verbose_stream() << "test7b: " << pat << " =?= " << t2 << "\n";);
                m_matcher.add_pattern(pat.get());
                m_matcher(pat, t2, 5);
            }

            // Structural regression test derived from TPTP PHI008^4 (which fails
            // under smt.ho_matching=true inside the full solver).
            // pattern:  (select v3 v4)     v3 flex head, v4 a flex arg of an array sort
            // term:     (select P ...)     P a concrete array constant.
            // Exercises projecting/imitating a flex head over a function(array)-sorted
            // argument (incl. a lambda-valued term arg). The matcher must build only
            // well-sorted bindings; debug asserts guard against regressions.
            void test8() {
                sort_ref i(m.mk_uninterpreted_sort(symbol("qML_i")), m);
                sort_ref mu(m.mk_uninterpreted_sort(symbol("qML_mu")), m);
                sort_ref arr_ib(m_array.mk_array_sort(i, m.mk_bool_sort()), m);     // (Array qML_i Bool)
                sort_ref arr_mu_ib(m_array.mk_array_sort(mu, arr_ib), m);           // (Array qML_mu (Array qML_i Bool))
                sort_ref p_sort(m_array.mk_array_sort(arr_mu_ib, arr_ib), m);       // P sort

                expr_ref v3(m.mk_var(3, p_sort), m);
                expr_ref v4(m.mk_var(4, arr_mu_ib), m);
                expr_ref pat(m_array.mk_select(v3, v4), m);

                expr_ref P(m.mk_const(symbol("P"), p_sort), m);
                expr_ref ell(m.mk_const(symbol("ell"), arr_mu_ib), m);
                expr_ref t(m_array.mk_select(P, ell), m);

                IF_VERBOSE(0, verbose_stream() << "test8: " << pat << " =?= " << t << "\n";);
                m_matcher.add_pattern(pat.get());
                m_matcher(pat, t, 9);

                // Variant with a lambda-valued term argument, mirroring PHI008's
                // (select scott_P (lambda (Y) (lambda (Z) ...))) goal that forces
                // the matcher to decompose a flex head against a lambda term.
                symbol yv("Y");
                sort* mu_s = mu.get();
                expr_ref cbody(m.mk_const(symbol("C"), arr_ib), m);
                expr_ref lam(m.mk_lambda(1, &mu_s, &yv, cbody), m);   // (lambda (Y qML_mu) C) : arr_mu_ib
                expr_ref t2(m_array.mk_select(P, lam), m);
                IF_VERBOSE(0, verbose_stream() << "test8b: " << pat << " =?= " << t2 << "\n";);
                m_matcher.add_pattern(pat.get());
                m_matcher(pat, t2, 9);
            }

            // Structural regression test for the ITP127-style shape (fails under
            // smt.ho_matching=true inside the full solver). The flex head H has an
            // applied result sort that is *itself* an array (monomo = (Array d Bool)).
            // Matching (select (select H x1) x2) =?= f where f is array-sorted is a
            // case where imitation could build a lambda with an extra array level
            // (an ill-sorted select). The matcher must build only well-sorted
            // bindings; debug asserts guard against regressions.
            void test9() {
                sort_ref c(m.mk_uninterpreted_sort(symbol("c")), m);
                sort_ref d(m.mk_uninterpreted_sort(symbol("d")), m);
                sort_ref monomo(m_array.mk_array_sort(d, m.mk_bool_sort()), m);    // (Array d Bool)
                sort_ref h1(m_array.mk_array_sort(c, monomo), m);                  // (Array c monomo)
                sort_ref h2(m_array.mk_array_sort(c, h1), m);                      // (Array c (Array c monomo))

                expr_ref H(m.mk_var(0, h2), m);
                expr_ref x1(m.mk_var(1, c), m);
                expr_ref x2(m.mk_var(2, c), m);
                expr_ref pat(m_array.mk_select(H, x1), m);
                pat = m_array.mk_select(pat, x2);                                  // (select (select H x1) x2) : monomo

                expr_ref f(m.mk_const(symbol("f"), monomo), m);                    // f : (Array d Bool)
                IF_VERBOSE(0, verbose_stream() << "test9: " << pat << " =?= " << f << "\n";);
                m_matcher.add_pattern(pat.get());
                m_matcher(pat, f, 3);
            }

            // Faithful isolation test for the refine-time sort guard used by
            // ho_matcher::refine_ho_match (throws "sort mismatch ..." on failure).
            // Mirrors the SEV510^1 family where a bound-variable binding's sort
            // disagrees with the pattern variable it would fill. subst_sorts_match
            // must detect the mismatch (return false) and accept the matching case.
            void test10() {
                sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
                // pattern (select v0 v1): v0 is the array (idx 0), v1 the index (idx 1)
                expr_ref v0(m.mk_var(0, int2int), m);
                expr_ref v1(m.mk_var(1, m_int), m);
                expr_ref pat(m_array.mk_select(v0, v1), m);

                // std_order=true: var idx maps to s[size-idx-1], so idx0->s[1], idx1->s[0].
                expr_ref arr(m.mk_const(symbol("arr"), int2int), m);
                expr_ref i0(m_arith.mk_int(0), m);

                // Well-sorted substitution: idx0 -> arr (array), idx1 -> 0 (int).
                expr_ref_vector s_ok(m);
                s_ok.push_back(i0);   // s[0] -> var idx 1 (Int) OK
                s_ok.push_back(arr);  // s[1] -> var idx 0 (Array) OK
                VERIFY(ho_matcher::subst_sorts_match(m, pat, s_ok, true));

                // Ill-sorted substitution: idx0 (array var) bound to an Int -> mismatch.
                expr_ref_vector s_bad(m);
                s_bad.push_back(i0);  // s[0] -> var idx 1 (Int) OK
                s_bad.push_back(i0);  // s[1] -> var idx 0 expects Array, got Int -> mismatch
                VERIFY(!ho_matcher::subst_sorts_match(m, pat, s_bad, true));
                IF_VERBOSE(0, verbose_stream() << "test10: subst_sorts_match detects sort mismatch\n";);
            }
    };

}

void tst_ho_matcher() {
    euf::test_ho_matcher tm;
    try {    
        tm.test1();
        tm.test2();
        tm.test3();
        tm.test4();
        tm.test5();
        tm.test6();
        tm.test7();
        tm.test8();
        tm.test9();
        tm.test10();
    }
    catch (std::exception const& ex) {
        std::cout << ex.what() << "\n";
    }
}
