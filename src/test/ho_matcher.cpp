
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


            pat = m_arith.mk_add(m.mk_app(sum, 3, args), m_array.mk_select(F, L1));
            IF_VERBOSE(0, verbose_stream() << "test5a: " << pat << " =?= " << s << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, s, 4);

            pat = m_arith.mk_add(m_array.mk_select(F, L1), m.mk_app(sum, 3, args));
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
    }
    catch (std::exception const& ex) {
        std::cout << ex.what() << "\n";
    }
}
