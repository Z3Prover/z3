
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/ast.h"
#include "qe/nlarith_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "qe/qe.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_functors.h"

namespace nlarith {

    typedef app_ref_vector poly;
    enum comp { LE, LT, EQ, NE};
    typedef vector<poly> polys;
    typedef svector<comp> comps;

    class util::literal_set {
        app_ref         m_inf;
        app_ref         m_sup;
        app*            m_x;

        app_ref_vector  m_lits;
        vector<poly>    m_polys;
        svector<comp>   m_comps;

    public:
        literal_set(ast_manager& m) : m_inf(m), m_sup(m), m_x(nullptr), m_lits(m) {}
        unsigned size() const { return m_lits.size(); }

        app_ref_vector& lits() { return m_lits; }
        vector<poly>& polys() { return m_polys; }
        svector<comp>& comps() { return m_comps; }

        poly const& get_poly(unsigned i) const { return m_polys[i]; }
        // Note: comp comp(unsigned i) is not valid C++.
        // it works on VC++, but it is rejected by gcc.
        comp compare(unsigned i) const { return m_comps[i]; }
        app* literal(unsigned i) const { return m_lits[i]; }

        app* x() const { return m_x; }
        void set_x(app* x) { SASSERT(!m_x); m_x = x; }

        app* x_inf() {
            if (!m_inf) {
                mk_const("inf", m_inf);
            }
            return m_inf;
        }

        app* x_sup() {
            if (!m_sup) {
                mk_const("sup", m_sup);
            }
            return m_sup;
        }

    private:
        void mk_const(char const* suffix, app_ref& v) {
            ast_manager& m = m_lits.get_manager();
            std::string name = m_x->get_decl()->get_name().str();
            name += suffix;
            sort* r = m.get_sort(m_x);
            v= m.mk_const(symbol(name.c_str()), r);
        }
    };

    class util::imp {

        ast_manager& m_manager;
        arith_util m_arith;
        bool       m_enable_linear;
        app_ref m_zero;
        app_ref m_one;
        smt_params m_params;
        bool_rewriter  m_bs;
        arith_rewriter m_rw;
        expr_ref_vector m_trail;

        ast_manager& m() const { return m_manager; }
        arith_util& a() { return m_arith; }
        app* z() { return m_zero.get();}
        app* one() { return m_one.get(); }

        std::ostream& display(std::ostream& out, comp c) {
            switch(c) {
            case LE: out << "<="; return out;
            case LT: out << "<"; return out;
            case EQ: out << "="; return out;
            case NE: out << "!="; return out;
            }
            return out;
        }

    public:
        imp(ast_manager& m) : 
            m_manager(m), m_arith(m), 
            m_enable_linear(false),
            m_zero(num(0),m), m_one(num(1),m), 
            m_bs(m),
            m_rw(m), m_trail(m) {
        }
        
        //
        // create branches and substitutions according to case analysis.
        //
        bool create_branches(app* x, unsigned num_lits, expr* const* lits, 
                             branch_conditions& branch_conds) {
            polys polys;
            comps comps;
            contains_app contains_x(m(), x);
            branch_conds.reset();
            m_trail.reset(); // use scope?

            if (!a().is_real(x)) {
                return false;
            }

            if (!get_polys(contains_x, num_lits, lits, polys, comps, &branch_conds, nullptr)) {
                TRACE("nlarith", 
                      tout << "could not extract polynomials " << mk_pp(x, m()) << "\n";
                      for (unsigned i = 0; i < num_lits; ++i) {
                          tout << mk_pp(lits[i], m()) << " ";
                      }
                      tout << "\n";
                      );
                return false;
            }
            if (is_degree_two_plus(polys)) {
                return false;                
            }
            if (!m_enable_linear && is_linear(polys)) {
                TRACE("nlarith", tout << "this is a linear problem " << mk_pp(x,m()) << "\n"; display(tout, polys););
                return false;
            }
            unsigned idx;
            if (has_single_degree2(polys, comps, idx)) {
                for (unsigned i = 0; i < polys.size(); ++i) {
                    create_branch_l(idx, i, polys, comps, branch_conds);
                }
            }
            else {                
                for (unsigned i = 0; i < polys.size(); ++i) {
                    create_branch(i, polys, comps, branch_conds);
                }
            }
            inf_branch(polys, comps, branch_conds);
            TRACE("nlarith", 
                  for (unsigned i = 0; i < num_lits; ++i) {
                      tout << mk_pp(lits[i], m()) << " ";
                  }
                  tout << "\n";
                  display_branching(tout, x, branch_conds);
                  );
            return true;
        }

        void set_enable_linear(bool enable_linear) { m_enable_linear = enable_linear; }

        void extract_non_linear(unsigned sz, app* const* es, ptr_vector<app>& nl_vars) {
            ast_mark visit;
            for (unsigned i = 0; i < sz; ++i) {
                extract_non_linear(es[i], visit, nl_vars);
            }
        }

        void extract_non_linear(expr* e, ptr_vector<app>& nl_vars) {  
            ast_mark visit;
            extract_non_linear(e, visit, nl_vars);
        }

        void extract_non_linear(expr* e, ast_mark& visit, ptr_vector<app>& nl_vars) {  
            if (visit.is_marked(e)) {
                return;
            }
            ast_mark nonlin;
            ptr_vector<expr> todo;
            todo.push_back(e);
            while(!todo.empty()) {
                e = todo.back();
                todo.pop_back();
                if (is_var(e)) {
                    continue;
                }
                if (is_quantifier(e)) {
                    e = to_quantifier(e)->get_expr();
                    if (!visit.is_marked(e)) {
                        todo.push_back(e);
                    }
                }
                SASSERT(is_app(e));
                app* a = to_app(e);
                bool nl = m_enable_linear || nonlin.is_marked(e) || is_nonlinear(a);
                if (is_arithmetical(a)) {
                    // TBD: overshoots in the case of 'ite' expressions.
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        expr* arg = a->get_arg(i);
                        bool nl2 = nonlin.is_marked(arg);
                        if (!visit.is_marked(arg) || (nl && !nl2)) {
                            todo.push_back(to_app(arg));
                            visit.mark(arg, true);
                            if (nl) {
                                nonlin.mark(arg, true);
                            }
                        }
                    }
                }
                else if (is_variable(a)) {
                    if (nl) {
                        nl_vars.push_back(a);
                    }
                }
                else {
                    for (unsigned i = 0; i < a->get_num_args(); ++i) {
                        expr* arg = a->get_arg(i);
                        if (!visit.is_marked(arg) || !nonlin.is_marked(arg)) {
                            todo.push_back(to_app(arg));
                            visit.mark(arg, true);
                            nonlin.mark(arg, true);
                        }
                    }
                }
            }

            TRACE("nlarith",
                  tout << "Non-linear variables: ";
                  for (unsigned i = 0; i < nl_vars.size(); ++i) {
                      tout << mk_pp(nl_vars[i], m()) << " ";
                  }
                  tout << "\n";);
        }


    private:
        void track(expr* e) {
            m_trail.push_back(e);
        }

        app* mk_lt(expr* p) { 
            expr_ref r(m());
            m_rw.mk_lt(p, z(), r);
            track(r);
            return to_app(r);
        }
        app* mk_le(expr* p) { 
            expr_ref r(m());
            m_rw.mk_le(p, z(), r);
            track(r);
            return to_app(r);
        }
        app* mk_gt(expr* p) { return mk_lt(mk_uminus(p)); }
        app* mk_ge(expr* p) { return mk_le(mk_uminus(p)); }
        app* mk_eq(expr* p) { 
            expr_ref r(m());
            m_bs.mk_eq(p, z(), r);
            track(r);
            return to_app(r);
        }
        app* mk_ne(expr* p) { 
            expr_ref r(m());
            m_bs.mk_eq(p, z(), r);
            m_bs.mk_not(r, r);
            track(r);
            return to_app(r);
        }
        app* num(int i) { return a().mk_numeral(rational(i), false); }



        //
        // TBD: perhaps merge with arith_rewriter using a app_ref buffer?
        //
        app* mk_uminus(expr* e) {
            expr_ref r(m());
            m_rw.mk_uminus(e, r);
            track(r);
            return to_app(r);
        }

        app* mk_add(unsigned sz, expr* const* args) {
            expr_ref r(m());
            m_rw.mk_add(sz, args, r);
            track(r);
            return to_app(r);
        }

        app* mk_add(expr* t, expr* s) {
            expr_ref r(m());
            expr* args[2] = { t, s};
            m_rw.mk_add(2, args, r);
            track(r);
            return to_app(r);
        }

        app* mk_add(expr* t, expr* s, expr* u) {
            return mk_add(t, mk_add(s, u));
        }

        app* mk_mul(expr* t, expr* s) {
            expr_ref r(m());
            expr* args[2] = { t, s};
            m_rw.mk_mul(2, args, r);
            track(r);
            return to_app(r);
        }

        app* mk_sub(expr* t, expr* s) {
            expr_ref r(m());
            expr* args[2] = { t, s};
            m_rw.mk_sub(2, args, r);
            track(r);
            return to_app(r);
        }

        app* mk_mul(expr* t, expr* s, expr* u) {
            return mk_mul(t, mk_mul(s, u));
        }

        app* mk_and(unsigned num_args, expr* const* args) {
            expr_ref r(m());
            m_bs.mk_and(num_args, args, r);
            track(r);
            return to_app(r);
        }

        app* mk_and(expr* a, expr* b) {
            expr* args[2] = { a, b };
            return mk_and(2, args);
        }

        app* mk_or(unsigned num_args, expr* const* args) {
            expr_ref r(m());
            m_bs.mk_or(num_args, args, r);
            track(r);
            return to_app(r);
        }

        app* mk_or(expr* a, expr* b) {
            expr* args[2] = { a, b };
            return mk_or(2, args);
        }
        void display_branching(
            std::ostream& out, app* x,
            branch_conditions const& bc) const {
                out << mk_pp(x, m()) << ":\n";
                for (unsigned i = 0; i < bc.preds().size(); ++i) {
                    out << "Pred: " << mk_pp(bc.preds()[i], m()) << "\n";
                }

                for (unsigned i = 0; i < bc.branches().size(); ++i) {
                    out << "Branch:\n" << mk_pp(bc.branches()[i], m()) << "\n";
                    for (unsigned j = 0; j < bc.subst()[i].size(); ++j) {
                        out << mk_pp(bc.preds()[j], m()) << " |-> " 
                            << mk_pp(bc.subst(i)[j], m()) << "\n";
                    }
                    out << "Def: " << mk_pp(bc.def(i), m()) << "\n";
                }
        }

        struct abc_poly {
            app_ref m_a;
            app_ref m_b;
            app_ref m_c;
            abc_poly(imp& I, app* a, app* b, app* c):
                m_a(a, I.m()), m_b(b, I.m()), m_c(c, I.m()) {}
        };


        struct sqrt_form {
            app_ref m_a;
            int     m_b;
            app_ref m_c;
            app_ref m_d;
            sqrt_form(imp& I, app* a, int b, app* c, app* d) : 
                m_a(a, I.m()), m_b(b), m_c(c, I.m()), m_d(d, I.m()) {
                SASSERT(d != I.z());
            }
            void display(std::ostream& out) const {
                ast_manager& m = m_a.get_manager();
                out << "(/ (+ " << mk_pp(m_a, m) << " (* " << m_b << " (sqrt " << mk_pp(m_c, m) << "))) " << mk_pp(m_d, m) << ")";
            }
        };

        expr* mk_abs(expr* e) { 
            return m().mk_ite(mk_lt(e), mk_uminus(e), e);
        }


        //
        // result = (a + b*sqrt(c))/d
        //
        expr* to_expr(sqrt_form const& s) {
            arith_util& A = a();
            expr* result;
            // result = (a + b*sqrt(c))/d
            if (s.m_c == z() || s.m_b == 0) { 
                result = A.mk_div(s.m_a, s.m_d); 
            }
            else {
                expr* half = A.mk_numeral(rational(1,2), false);
                result = A.mk_div(mk_add(s.m_a, mk_mul(num(s.m_b), A.mk_power(mk_abs(s.m_c), half))), s.m_d);
            }
            return result;
        }


        // 
        // 
        // Given p(x): ax^2 + bx + c < 0
        //   then the derivative is d p(x)/dx = 2ax + b
        // cases:
        // 1. a != 0, b != 0:
        //    zero: (- b +- sqrt(b^2 - 4ac))/ 2a
        //    then slope of x at zero is:
        //    2a*zero + b = +- sqrt(..), 
        //    so the slope is given by the sign of the solution.
        // 
        //    return zero + epsilon * (if sign > 0 then -1 else 1)
        // 
        // 2. a = 0, b != 0:
        //    zero : -c/b
        //    slope is b.
        //    return -c/b + epsilon * (if b > 0 then -1 else 1)
        //    
        // Given p(x): ax^2 + bx + c <= 0, ax^2 + bx + c = 0,
        //    use epsilon = 0.
        // Given p(x): ax^2 + bx + c <= 0, ax^2 + bx + c = 0,
        //    use epsilon as in < case.
        //

        expr* mk_def(comp cmp, abc_poly const& p, sqrt_form const& s) {
            expr* result = to_expr(s);
            if (is_strict(cmp)) {
                if (p.m_a == z()) {
                    result = mk_add(result, mk_mul(mk_epsilon(), m().mk_ite(mk_lt(p.m_b),num(1),num(-1))));
                }
                else {
                    if (s.m_b > 0) {
                        result = mk_add(result, mk_mul(num(-1),mk_epsilon()));
                    }
                    else {
                        result = mk_add(result, mk_epsilon());
                    }
                }
            }
            return result;
        }

        // 
        // TBD: Compute an espilon based on the terms
        // used in the constraints.
        //  
        expr* mk_epsilon() {
            return a().mk_numeral(rational(1,10000), false);
        }

        // 
        // TBD: Compute an inf based on the terms
        // used in the constraints. Eg., use a symbolic
        // constant for epsilon and inf and then solve for
        // it postiori.
        // 
        expr* mk_inf() {
            return a().mk_numeral(rational(-10000), false);
        }

        // lower bounds for each case:
        // a*x^2 + b*x + c + eps = 0 & a = 0 & b = 0 => x < 0
        // a*x^2 + b*x + c + eps = 0 & a = 0 & b != 0 => x < - (c / b) < - (c^2 +1) * (1 + 1/b^2) 
        // a*x^2 + b*x + c + eps = 0 & a != 0  => x < (-|b| - sqrt(b^2 - 4ac))/2|a| < - (b^2*(1 + 1/a^2) + (c^2+1))

        app* sq(expr* e) {  
            return mk_mul(e,e);
        }

        app* sq1(expr * e) { 
            return mk_add(num(1), sq(e)); 
        }

        app* inv(expr * e) { 
            return a().mk_div(num(1), e); 
        }

        expr* mk_inf(branch_conditions const& bc) { 
            return mk_inf();
#if 0
            if (bc.size() > 0) {
                // pick a number lower than the symbolic lower bounds.
                for(unsigned i = 0; i < bc.size(); ++i) {
                    expr * a = bc.a(i);
                    expr * b = bc.b(i);
                    expr * c = bc.c(i);
                    expr * e = 
                        m().mk_ite(
                            mk_eq(a),
                            m().mk_ite(
                                mk_eq(b),
                                num(0),
                                mk_mul(mk_add(sq(c),num(1)), sq1(inv(b)))),
                            mk_add(mk_mul(sq(b),sq1(inv(a))), sq1(c)));
                    r = mk_add(e, r);
                }
                return mk_uminus(r);
            }
#endif
        }

        void inf_branch(
            polys const& polys, comps const& comps, branch_conditions& bc) {
            // /\_j p_j -> p_j[-oo / x]            
            app_ref t1(m());
            expr_ref_vector es(m()), subst(m());
            for (unsigned j = 0; j < polys.size(); ++j) {
                minus_inf_subst sub(*this);
                apply_subst(sub, comps[j],  polys[j], t1); 
                es.push_back(m().mk_implies(bc.preds(j), t1));
                subst.push_back(t1);
                TRACE("nlarith_verbose", 
                      display(tout << "inf", polys[j]); 
                      display(tout, comps[j]); 
                      tout << " 0 [-oo] --> " << mk_pp(t1.get(), m()) << "\n";);
            }
            TRACE("nlarith", tout << "inf-branch\n";);
            bc.add_branch(mk_and(es.size(), es.c_ptr()), m().mk_true(), subst, mk_inf(bc), z(), z(), z());
        }

        void create_branch_l(unsigned j, unsigned i, polys const& polys, comps const& comps, 
                            branch_conditions& bc) {          
            comp cmp = comps[i];
            poly const& p = polys[i];
            if (i == j) cmp = LE; // non-strict to avoid epsilon substitution mode.
            app* a, *b, *c;
            get_coefficients(p, a, b, c);
            app_ref t1(m());
            expr_ref a2(m()), d(m()), t2(m()), cond(m());
            expr_ref_vector es(m()), subst(m());

            if (b != z()) {
                sqrt_form e0(*this, mk_uminus(c), 0,   z(), b);
                // a_i = 0 /\ b_i != 0 /\ phi[e_i/x]
                TRACE("nlarith", display(tout << "a_i != 0 & b_i != 0 & hi[e_i / x]", p);tout<<"\n";);
                scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m());
                expr_substitution sub(m());
                sub.insert(a, z());
                rp->set_substitution(&sub);
                if (a != z()) es.push_back(mk_eq(a));
                es.push_back(mk_ne(b));
                cond = mk_and(es.size(), es.c_ptr());
                es.push_back(bc.preds(i));
                for (unsigned k = 0; k < polys.size(); ++k) {
                    mk_subst(cmp, polys[k], comps[k], e0, t1);
                    (*rp)(t1, t2);
                    es.push_back(m().mk_implies(bc.preds(k), t2));
                    subst.push_back(t1);
                }
                bc.add_branch(mk_and(es.size(), es.c_ptr()), cond, subst, mk_def(cmp, abc_poly(*this, z(), b, c), e0), a, b, c);
            }

            if (i == j && a != z()) {
                // a != 0 & phi[-b/(2a)/x]
                TRACE("nlarith", display(tout << "a != 0 & phi[-b/2a / x]", p);tout<<"\n";);
                app* a2 = mk_mul(num(2), a);
                sqrt_form e1(*this, mk_uminus(b), 0, z(), a2);
                es.reset();
                subst.reset();
                cond = mk_ne(a);
                es.push_back(cond);
                es.push_back(bc.preds(i));

                for (unsigned k = 0; k < polys.size(); ++k) {
                    mk_subst(cmp, polys[k], comps[k], e1, t1);
                    es.push_back(m().mk_implies(bc.preds(k), t1));
                    subst.push_back(t1);
                }
                bc.add_branch(mk_and(es.size(), es.c_ptr()), cond, subst, mk_def(cmp, abc_poly(*this, a2, b, z()),e1), a, b, c);
            }
        }

        void create_branch(unsigned i, polys const& polys, comps const& comps, branch_conditions& bc) {
            comp cmp = comps[i];
            poly const& p = polys[i];
            app* a, *b, *c;
            get_coefficients(p, a, b, c);
            app_ref  t1(m()), a2(m()), d(m());
            expr_ref cond(m()), t2(m()), branch(m());
            expr_ref_vector es(m()), subst(m());
            d = mk_sub(mk_mul(b,b), mk_mul(num(4), a, c));
            a2 = mk_mul(a, num(2));            

            TRACE("nlarith", 
                  display(tout, p); tout << "\n";
                  tout << "a:" << mk_pp(a, m()) << "\n";
                  tout << "b:" << mk_pp(b,m())  << "\n";
                  tout << "c:" << mk_pp(c,m())  << "\n";
                  tout << "d:" << mk_pp(d, m()) << "\n";);
            // p & a = 0 & b != 0 & /\_j p_j -> p_j[e0/x]
            // p & a != 0 & 0 <= d & /\_j p_j -> (p_j[e1/x] \/ p_j[e2/x])
            // or:
            // p & a = 0 & b != 0 /\_j p_j -> p[e0+eps/x]
            // p & a != 0 & 0 <= d /\_j p_j -> p[e1+eps/x] \/ p[e2+eps/x]

            if (b != z()) {
                sqrt_form e0(*this, mk_uminus(c), 0,     z(), b);
                es.reset();
                subst.reset();
                scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m());
                expr_substitution sub(m());
                sub.insert(a, z());
                rp->set_substitution(&sub);
                if (a != z()) es.push_back(mk_eq(a));
                es.push_back(mk_ne(b));
                cond = mk_and(es.size(), es.c_ptr());
                es.push_back(bc.preds(i));
                for (unsigned j = 0; j < polys.size(); ++j) {
                    mk_subst(cmp, polys[j], comps[j], e0, t1);
                    (*rp)(t1, t2);
                    es.push_back(m().mk_implies(bc.preds(j), t2));
                    subst.push_back(t2);
                }
                branch = mk_and(es.size(), es.c_ptr());
                bc.add_branch(branch, cond, subst, mk_def(cmp, abc_poly(*this, z(), b, c), e0), a, b, c); 
            }

            if (a != z()) {
                sqrt_form e1(*this, mk_uminus(b), 1,  d,   a2);
                sqrt_form e2(*this, mk_uminus(b), -1, d,   a2);
                es.reset();
                subst.reset();
                es.push_back(mk_ne(a));
                es.push_back(mk_ge(d));
                cond = mk_and(es.size(), es.c_ptr());
                es.push_back(bc.preds(i));
                for (unsigned j = 0; j < polys.size(); ++j) {
                    mk_subst(cmp, polys[j], comps[j], e1, t1);
                    es.push_back(m().mk_implies(bc.preds(j), t1));
                    subst.push_back(t1);
                }
                branch = mk_and(es.size(), es.c_ptr());
                bc.add_branch(branch, cond, subst, mk_def(cmp, abc_poly(*this, a, b, c), e1), a, b, c);
                TRACE("nlarith", tout << mk_pp(branch,m()) << "\n";);

                TRACE("nlarith", 
                      tout << "0 <= " << mk_pp(d,m()) << "\n";
                      tout << mk_pp(mk_ge(d), m()) << "\n";);

                es.resize(3);
                subst.reset();
                for (unsigned j = 0; j < polys.size(); ++j) {
                    mk_subst(cmp, polys[j], comps[j], e2, t1);
                    es.push_back(m().mk_implies(bc.preds(j), t1));
                    subst.push_back(t1);
                }
                branch = mk_and(es.size(), es.c_ptr());
                bc.add_branch(branch, cond, subst, mk_def(cmp, abc_poly(*this, a, b, c), e2), a, b, c);
                TRACE("nlarith", tout << mk_pp(branch,m()) << "\n";);
            }
        }        

        bool is_strict(comp c) const {
            return c == LT || c == NE;
        }
        void mk_subst(comp c1, poly const& p, comp c, sqrt_form const& e, app_ref& r) {
            sqrt_subst sub(*this, e);
            if (is_strict(c1)) {
                plus_eps_subst sub2(*this, sub);
                apply_subst(sub2, c, p, r);
            }
            else {
                apply_subst(sub, c, p, r); 
            }
            TRACE("nlarith_verbose", 
                  display(tout, p); 
                  display(tout, c); 
                  e.display(tout << " 0 "); 
                  tout << " --> " << mk_pp(r.get(), m()) << "\n";);
        } 

        void get_coefficients(poly const& p, app*& a, app*& b, app*& c) {
            a = b = c = z();
            if (!p.empty()) c = p[0];
            if (p.size() > 1) b = p[1];
            if (p.size() > 2) a = p[2];
            SASSERT(p.size() <= 3);
        }

        bool is_le(expr* e, expr*& s, expr*& t) {
            return a().is_ge(e, t, s) || a().is_le(e, s, t);
        }
        bool is_lt(expr* e, expr*& s, expr*& t) {
            return a().is_gt(e, t, s) || a().is_lt(e, s, t);
        }

        bool is_degree_two_plus(polys const& ps) {
            for (unsigned i = 0; i < ps.size(); ++i) {
                if (ps[i].size() > 3) {
                    TRACE("nlarith", tout << "not second-degree: ";
                      display(tout, ps[i]); tout <<"\n"; );
                    return true;
                }
            }
            return false;
        }

        bool is_linear(polys& ps) const {
            rational n;
            for (unsigned i = 0; i < ps.size(); ++i) {
                if (ps[i].size() > 2) return false;
                if (ps[i].size() == 2) {
                    if (is_numeral(ps[i][1].get(), n)) {
                        ps[i][1] = m_arith.mk_numeral(n, false);
                    }
                    else {
                        return false;
                    }
                }
            }
            return true;
        }


        bool has_single_degree2(polys const& ps, comps const& comps, unsigned& idx) const {
            unsigned n = 0;
            for (unsigned i = 0; i < ps.size(); ++i) {
                if (ps[i].size() == 3) {
                    ++n;
                    idx = i;
                    if (comps[i] == EQ) {
                        return false;
                    }
                }
            }
            return n == 1;
        }
        /**
           \brief Create branch conditions for each atomic formulI.
        */
        bool get_polys(contains_app& contains_x, unsigned num_lits, expr* const* lits, 
                       polys& polys, comps& comps, branch_conditions* bc, 
                       app_ref_vector* literals) {
            ast_manager& M = m();
            expr* e1, *e2, *e3;
            app_ref t(M);
            poly p(M);
            comp c;

            for (unsigned i = 0; i < num_lits; ++i) {
                if (!contains_x(lits[i])) {
                    continue;
                }
                // e1 <= e2
                if (is_le(lits[i], e1, e2)) {
                    t = mk_sub(e1, e2);
                    c = LE;
                }
                // ! (e2 <= e3) <=> e3 < e2
                else if (M.is_not(lits[i], e1) && is_le(e1, e2, e3)) {
                    t = mk_sub(e3, e2);
                    c = LT;
                }
                // e1 < e2
                else if (is_lt(lits[i], e1, e2)) {
                    t = mk_sub(e1, e2);
                    c = LT;
                }           
                // ! (e2 < e3) <=> e3 <= e2
                else if (M.is_not(lits[i], e1) && is_lt(e1, e2, e3)) {
                    t = mk_sub(e3, e2);
                    c = LE;
                }
                else if (M.is_eq(lits[i], e1, e2)) {
                    t = mk_sub(e1, e2);
                    c = EQ;
                }
                else if (M.is_not(lits[i], e1) && M.is_eq(e1, e2, e3)) {
                    t = mk_sub(e2, e3);                    
                    c = NE;
                }
                else {
                    return false;
                }
                if (!get_decomposition(t, contains_x, p)) {
                    return false;
                }
                polys.push_back(p);
                comps.push_back(c);
                if (bc) {
                    bc->add_pred(lits[i]);
                }
                if (literals) {
                    literals->push_back(to_app(lits[i]));
                }
                TRACE("nlarith_verbose", 
                      tout << mk_pp(lits[i], m()) << " -> ";
                      display(tout, p); tout << "\n"; );
            }            
            return true;
        }


        void display(std::ostream& out, poly const& p) {
            out << "(";
            for (unsigned i = 0; i < p.size(); ++i) {
                 out << i << ": " << mk_pp(p[i], m());
                 if (i + 1 < p.size()) out << ", ";
            }
            out << ")";
        }

        void display(std::ostream& out, polys const& ps) {
            for (unsigned i = 0; i < ps.size(); ++i) {
                display(out, ps[i]);
                out << " ";
            }
        }


        bool is_numeral(expr* t, rational& n) const {
            if (!is_app(t)) return false;
            app* e = to_app(t);
            func_decl* f = e->get_decl();
            if (f->get_family_id() != m_arith.get_family_id()) {
                return false;
            }            
            rational m;
            switch(f->get_decl_kind()) {
            case OP_ADD:
#define MK_AOP(_mk_op_)                                                 \
                SASSERT(e->get_num_args() > 0);                         \
                if (!is_numeral(e->get_arg(0), n)) return false;        \
                for (unsigned i = 1; i < e->get_num_args(); ++i) {      \
                    if (!is_numeral(e->get_arg(i), m)) return false;    \
                    n = n _mk_op_ m;                                    \
                } 
                MK_AOP(+);
                return true;
            case OP_MUL:
                MK_AOP(*);
                return true;
            case OP_SUB:
                MK_AOP(-);
                return true;
            case OP_UMINUS:
                if (!is_numeral(e->get_arg(0), n)) return false;
                n.neg();
                return true;
            case OP_NUM:
                return m_arith.is_numeral(e, n);
            default:
                return false;
            }
        }
        /**
           \brief Decompose polynomial into sum of powers of 'x'.
           
           p = result[0] + x*result[1] + x*x*result[2] + ...
        */
        bool get_decomposition(expr* t, contains_app& contains_x, poly& result) {
            result.reset();
            if (!is_app(t)) {
                return false;
            }
            app* e = to_app(t);
            if (!contains_x(e)) {
                result.push_back(e);
                return true;
            }
            if (contains_x.x() == e) {
                result.push_back(z());
                result.push_back(one());
                return true;
            }

            func_decl* f = e->get_decl();
            if (f->get_family_id() != a().get_family_id()) {
                return false;
            }            
            poly r(m());
            switch(f->get_decl_kind()) {
            case OP_ADD:
#define MK_OP(_mk_op_)                                                                  \
                SASSERT(e->get_num_args() > 0);                                         \
                if (!get_decomposition(e->get_arg(0), contains_x, result)) return false;\
                for (unsigned i = 1; i < e->get_num_args(); ++i) {                      \
                    if (!get_decomposition(e->get_arg(i), contains_x, r)) return false; \
                    _mk_op_(result, r);                                                 \
                } 
                MK_OP(mk_add);
                return true;
            case OP_MUL:
                MK_OP(mk_mul);
                return true;
            case OP_SUB:
                MK_OP(mk_sub);
                return true;
            case OP_UMINUS:
                if(!get_decomposition(e->get_arg(0), contains_x, result)) return false;
                mk_uminus(result);
                return true;
            default:
                TRACE("nlarith", tout << "Cannot decompose " << mk_pp(f, m()) << "\n" << mk_pp(e, m()) << "\n";);
                return false;
            }
        }

        void mk_uminus(poly& p) {
            for (unsigned i = 0; i < p.size(); ++i) {
                p[i] = mk_uminus(p[i].get());
            }
        }

        void mk_sub(poly& r, poly const& other) {
            for (unsigned i = 0; i < r.size() && i < other.size(); ++i) {
                r[i] = mk_sub(r[i].get(), other[i]);
            }
            for (unsigned i = r.size(); i < other.size(); ++i) {
                r.push_back(mk_uminus(other[i]));
            }
        }

        void mk_add(poly& r, poly const& other) {
            for (unsigned i = 0; i < r.size() && i < other.size(); ++i) {
                r[i] = mk_add(r[i].get(), other[i]);
            }
            for (unsigned i = r.size(); i < other.size(); ++i) {
                r.push_back(other[i]);
            }
        }

        // r[0]*o[0]
        // r[0]*o[1] + r[1]*o[0]
        // r[0]*o[2] + r[1]*o[1] + r[2]*o[0]
        //
        //     r[sz-1]*o[sz-2] + r[sz-2]*o[sz-1]
        //                       r[sz-1]*o[sz-1]
        void mk_mul(poly& r, poly const& other) {
            poly result(m());
            for (unsigned i = 0; i + 1 < r.size() + other.size(); ++i) {
                app_ref t(z(), m());
                for (unsigned j = 0; j <= i && j < r.size(); ++j) {
                    unsigned k = i - j;
                    if (k < other.size()) {
                        t = mk_add(t, mk_mul(r[j].get(),other[k]));
                    }
                }
                result.push_back(t);
            }
            TRACE("nlarith_verbose", display(tout, r); display(tout <<" * ", other); display(tout << " = ", result); tout <<"\n";);
            r.reset();
            r.append(result.size(), result.c_ptr());
        }

        void mk_mul(poly& p, expr* e) {
            for (unsigned i = 0; i < p.size(); ++i) {
                p[i] = mk_mul(p[i].get(), e);
            }
        }

        void mk_add(poly& p, unsigned shift, expr* e) {
            while (p.size() <= shift) {
                p.push_back(z());
            }
            p[shift] = mk_add(p[shift].get(), e);
        }


        /**
           \brief Symbolic differentiation with respect to 'x'.

           result = [p[1],  2*p[2], 
                     3*p[3],..,(num_terms-1)*p[num_terms-1]]
                      
        */

        void mk_differentiate(poly const& p, app_ref_vector& result) {
            for (unsigned i = 1; i < p.size(); ++i) {
                result.push_back(mk_mul(num(i), p[i]));
            }        
        }

        class isubst {
        protected:
            imp& m_imp;
        public:
            isubst(imp& i) : m_imp(i) {}
            virtual void mk_lt(poly const& p, app_ref& r) = 0;
            virtual void mk_eq(poly const& p, app_ref& r) = 0;
            virtual void mk_le(poly const& p, app_ref& r) { 
                imp& I = m_imp;
                app_ref r1(I.m()), r2(I.m());
                mk_lt(p, r1);
                mk_eq(p, r2);
                r = I.mk_or(r1, r2);  
            }
            virtual void mk_ne(poly const& p, app_ref& r) {  
                imp& I = m_imp;
                mk_eq(p, r);
                r = I.m().mk_not(r); 
            }
        };

        void apply_subst(isubst& sub, comp c, poly const& p, app_ref& r) {
            switch(c) {
            case EQ: sub.mk_eq(p, r); return;
            case LE: sub.mk_le(p, r); return;
            case LT: sub.mk_lt(p, r); return;
            case NE: sub.mk_ne(p, r); return;
            }
        }

        class basic_subst : public isubst {
            app* m_x;
        public:
            basic_subst(imp& i, app* x) : isubst(i), m_x(x) {}
            void mk_lt(poly const& p, app_ref& r) override {
                imp& I = m_imp;
                app_ref result(I.m());
                I.mk_polynomial(m_x, p, result);
                r = I.mk_lt(result);
            }
            void mk_eq(poly const& p, app_ref& r) override {
                imp& I = m_imp;
                app_ref result(I.m());
                I.mk_polynomial(m_x, p, result);
                r = I.mk_eq(result);
            }
        };

        class sqrt_subst : public isubst {
            sqrt_form const& m_s;
        public:
            sqrt_subst(imp& i, sqrt_form const& s): isubst(i), m_s(s) {}

            // p[e/x] < 0: (a*parity(d) < 0 /\ 0 < a*a - b*b*c) \/
            //             (b*parity(d) <= 0 /\ (a*parity(d) < 0 \/ a*a - b*b*c < 0))  
            void mk_lt(poly const& p, app_ref& r) override {
                imp& I = m_imp;
                ast_manager& m = I.m();
                app_ref a(m), b(m), c(m_s.m_c), d(m);
                I.mk_instantiate(p, m_s, a, b, d);
                app_ref ad(a, m), bd(b, m), aabbc(m);
                if (is_even(p.size())) { 
                    ad = I.mk_mul(a, d); 
                    bd = I.mk_mul(b, d); 
                }
                if (m_s.m_b == 0) {
                   r = I.mk_lt(ad);
                }
                else {
                    aabbc = I.mk_sub(I.mk_mul(a,a), I.mk_mul(b,b,c));
                    r = I.mk_or(I.mk_and(I.mk_lt(ad), I.mk_gt(aabbc)),
                                I.mk_and(I.mk_le(bd), I.mk_or(I.mk_lt(ad), I.mk_lt(aabbc))));
                }
            }


            // p[e/x] = 0: a*b <= 0 & a*a - b*b*c = 0
            void mk_eq(poly const& p, app_ref& r) override {
                imp& I = m_imp;
                ast_manager& m = I.m();
                app_ref a(m), b(m), c(m_s.m_c),d(m), aabbc(m);
                I.mk_instantiate(p, m_s, a, b, d);
                if (m_s.m_b == 0) {
                    r = I.mk_eq(a);
                }
                else {
                    aabbc = I.mk_sub(I.mk_mul(a, a), I.mk_mul(b, b, c));
                    r = I.mk_and(I.mk_le(I.mk_mul(a, b)), I.mk_eq(aabbc));
                }
            }

            // p[e/x] <= 0: a*parity(d) <= 0 /\ 0 <= a*a - b*b*c \/ b*parity(d) <= 0 /\ a*a - b*b*c <= 0
            void mk_le(poly const& p, app_ref& r) override {
                imp& I = m_imp;
                ast_manager& m = I.m();
                app_ref a(m), b(m), c(m_s.m_c), d(m);
                I.mk_instantiate(p, m_s, a, b, d);
                app_ref ad(a, m), bd(b, m), aabbc(m);
                if (is_even(p.size())) { 
                    ad = I.mk_mul(a, d); 
                    bd = I.mk_mul(b, d); 
                }
                if (m_s.m_b == 0) {
                    r = I.mk_le(ad);
                }
                else {
                    aabbc = I.mk_sub(I.mk_mul(a, a), I.mk_mul(b, b, c));
                    r = I.mk_or(I.mk_and(I.mk_le(ad), I.mk_ge(aabbc)),
                                I.mk_and(I.mk_le(bd), I.mk_le(aabbc)));
                }
            }
        };

        class plus_eps_subst : public isubst {
            isubst& m_s;
            /**
               \brief compute nu(p):
               nu(p) = p < 0 if degree(x) = 0
               nu(p) = p < 0 \/ (p = 0 /\ nu(p'))

               Then p(x+epsilon) < 0 iff nu(p(x))
            */

            void mk_nu(poly const& p, app_ref& r) {
                imp& I = m_imp;
                ast_manager& m = I.m();
                app_ref_vector t1(m);
                app_ref t3(m), t4(m);
                m_s.mk_lt(p, r);
                if (p.size() > 1) {
                    m_s.mk_eq(p, t3);
                    I.mk_differentiate(p, t1);
                    mk_nu(t1, t4);
                    // p < 0 \/ (p = 0 /\ nu(p'))
                    r = I.mk_or(r, I.mk_and(t3, t4));
                }
            }

        public:
            plus_eps_subst(imp& i, isubst& s) : isubst(i), m_s(s) {}
            
            void mk_lt(poly const& p, app_ref& r) override { mk_nu(p, r); }

            // /\ p[i] = 0
            void mk_eq(poly const& p, app_ref& r) override { r = m_imp.mk_zero(p); }
        };

        class minus_eps_subst : public isubst {
            isubst& m_s;
            /**
               \brief compute nu(p):
               nu(p, t) = p < 0 if degree(x) = 0
               nu(p, f) = p > 0 if degree(x) = 0
               nu(p, t) = p < 0 \/ (p = 0 /\ nu(p', f))
               nu(p, f) = p > 0 \/ (p = 0 /\ nu(p', t))

               Then p(x-epsilon) < 0 iff nu(p(x), t)
            */

            void mk_lt(poly const& p, bool even, app_ref& r) {
                imp& I = m_imp;
                if (even) {
                    m_s.mk_lt(p, r);
                }
                else {
                    poly p1(p);
                    I.mk_uminus(p1);
                    m_s.mk_lt(p1, r);
                }
            }

            void mk_nu(poly const& p, bool even, app_ref& r) {
                imp& I = m_imp;
                ast_manager& m = I.m();
                app_ref_vector t1(m);
                app_ref t3(m), t4(m);
                mk_lt(p, even, r);
                if (p.size() > 1) {
                    m_s.mk_eq(p, t3);
                    I.mk_differentiate(p, t1);
                    mk_nu(t1, !even, t4);
                    // p < 0 \/ (p = 0 /\ nu(p'))
                    r = I.mk_or(r, I.mk_and(t3, t4));
                }
            }
        public:
            minus_eps_subst(imp& i, isubst& s) : isubst(i), m_s(s) {}
            
            void mk_lt(poly const& p, app_ref& r) override { mk_nu(p, true, r); }

            // /\ p[i] = 0
            void mk_eq(poly const& p, app_ref& r) override { r = m_imp.mk_zero(p); }
        };

        class minus_inf_subst : public isubst {  
            /**
               \brief compute mu(p) given by.
               
               p = p[0] + x*p[1] + x*x*p[2] + ...
               
               mu(p) = p[num_terms-1]*(-1)^(parity num_terms-1) < 0 \/
               p[num_terms-1] = 0 /\
               mu(num_terms-1, terms)
            */

            app* mk_lt(poly const& p, unsigned i) {
                imp& I = m_imp;
                ast_manager& m = I.m();                
                if (i == 0) {
                    return m.mk_false();
                }
                --i;
                expr* t = p[i];
                app* e = is_even(i)?I.mk_lt(t):I.mk_gt(t);
                if (i == 0) {
                    return e;
                }
                else {
                    return I.mk_or(e, I.mk_and(I.mk_eq(t), mk_lt(p, i)));
                }            
            }
        public:
            minus_inf_subst(imp& i) : isubst(i) {}

            void mk_lt(poly const& p, app_ref& r) override {
                r = mk_lt(p, p.size());
            }

            // /\ p[i] = 0
            void mk_eq(poly const& p, app_ref& r) override { r = m_imp.mk_zero(p); }
        };


        class plus_inf_subst : public isubst {  

            app* mk_lt(poly const& p, unsigned i) {
                imp& I = m_imp;
                ast_manager& m = I.m();
                if (i == 0) {
                    return m.mk_false();
                }
                --i;
                expr* t = p[i];
                app* e = I.mk_lt(t);
                if (i == 0) {
                    return e;
                }
                else {
                    return I.mk_or(e, I.mk_and(I.mk_eq(t), mk_lt(p, i)));
                }            
            }
        public:
            plus_inf_subst(imp& i) : isubst(i) {}

            void mk_lt(poly const& p, app_ref& r) override { r = mk_lt(p, p.size()); }

            // /\ p[i] = 0
            void mk_eq(poly const& p, app_ref& r) override { r = m_imp.mk_zero(p); }
        };
        
        /**
           \brief create polynomail expression.

           result = p[0] + x*p[1] + x*x*p[2] + ...
        */
        void mk_polynomial(app* x, poly const& p, app_ref& result) {
            if (p.empty()) {
                result = z();
                return;
            }
            app_ref xx(x, m());
            expr_ref_vector tmp(m());
            tmp.push_back(p[0]);
            for (unsigned i = 1; i < p.size(); ++i) {
                tmp.push_back(mk_mul(xx.get(), p[i]));
                xx = mk_mul(x, xx.get());                      
            }
            result = mk_add(tmp.size(), tmp.c_ptr());
        }

        app* mk_zero(poly const& p) {
            app_ref_vector tmp(m());
            mk_zero(p, tmp);
            return mk_and(tmp.size(), reinterpret_cast<expr*const*>(tmp.c_ptr()));
        }

        void mk_zero(poly const& p, app_ref_vector& zeros) {
            for (unsigned i = 0; i < p.size(); ++i) {
                zeros.push_back(mk_eq(p[i]));
            }
        }
       

        /**
           \brief Formal replacement of x by (a + b*sqrt(c))/d in p.
           
           where:
             p = p[0] + x*p[1] + x*x*p[2] + ...

           The result is an expression (a' + b'*sqrt(c))/d'
        */

        void mk_instantiate(poly const& p, 
                            sqrt_form const& s,
                            app_ref& ar, app_ref& br, app_ref& dr) {
            app* a = s.m_a, *c = s.m_c, *d = s.m_d;
            app_ref b(num(s.m_b), m());
            br = z();
            dr = one();
            if (p.empty()) {
                ar = z();
                return;
            }
            unsigned i = p.size() - 1;
            ar = p[i];
            while (i > 0) {
                --i;
                // compute
                //   p[i] + x * (ar + br*sqrt(c))/dr
                // =
                //   p[i] + (a + b*sqrt(c))/d * (ar + br*sqrt(c))/dr
                // =
                //   p[i] + (a*ar + b*br*c + (a*br + ar*b)*sqrt(c))/d*dr
                // = 
                //   (d*dr*p[i] + a*ar + b*br*c + (a*br + ar*b)*sqrt(c))/d*dr
                // 
                app_ref tmp1(mk_add(mk_mul(d, dr, p[i]), mk_mul(a, ar), mk_mul(b, br, c)), m());
                br = mk_add(mk_mul(a, br), mk_mul(ar, b));
                dr = mk_mul(d, dr);
                ar = tmp1;
            }
            TRACE("nlarith_verbose", 
                  display(tout, p);
                  s.display(tout << " ");
                  tout << " " << mk_pp(ar, m()) << " " << mk_pp(br, m()) << " " << mk_pp(dr, m()) << "\n";);
        }

        static bool is_even(unsigned n) { return 0 == (n&0x1); }

        bool is_variable(app* e) {
            return 
                a().is_real(e) && 
                e->get_family_id() == null_family_id &&
                e->get_num_args() == 0;
        }
        
        bool is_arithmetical(app* e) {
            if (e->get_family_id() == m().get_basic_family_id()) {
                return true;
            }
            if (e->get_family_id() == a().get_family_id()) {
                return true;
            }
            return false;
        }
        
        bool is_nonlinear(app* e) {
            if (a().is_mul(e)) {
                unsigned n = 0;
                for (unsigned i = 0; n < 2 && i < e->get_num_args(); ++i) {
                    if (!a().is_numeral(e->get_arg(i))) {
                        ++n;
                    }
                }
                return n == 2;
            }    
            return false;
        }

    private:

        // u = v*q + r
        void quot_rem(poly const& u, poly const& v, poly& q, poly& r, app_ref& lc, unsigned& power) {
            lc = v.empty()?num(0):v[v.size()-1];
            power = 0;
            if (u.size() < v.size() || v.empty()) {
                q.reset();
                r.reset();
                r.append(u);
                return;
            }
            SASSERT(u.size() >= v.size() && v.size() > 0);
            unsigned n = v.size()-1;
            if (a().is_numeral(v[n])) {
                numeric_quot_rem(u, v, q, r);
            }
            else {
                pseudo_quot_rem(u, v, q, r, power);
            }
        }

        //
        // Compute q and r such that
        //    u = v*q + r, 
        // assuming the leading coefficient of v is a numeral.
        //
        void numeric_quot_rem(poly const& u, poly const& v, poly& q, poly& r) {
            SASSERT(u.size() > 0 && v.size() > 0);
            unsigned m = u.size()-1, n = v.size()-1;
            q.reset();
            r.reset();
            r.append(u);
            rational v_n;
            VERIFY(a().is_numeral(v[n], v_n));
            app_ref v_inv(a().mk_numeral(rational(1)/v_n, false), m_manager);
            bool is_one = v_n.is_one();
            for (int k = m-n+1; k > 0; ) {
                --k;
                if (is_one) {
                    q[k] = u[n+k];
                }
                else {
                    q[k] = mk_mul(u[n+k], v_inv.get());
                }
                for (int j = n + k - 1; j >= k; --j) {
                    r[j] = mk_sub(r[j].get(), mk_mul(q[k].get(), v[j-k]));
                }
            }
            SASSERT(test_quot_rem(u, v, q, r));
        }

        //
        // Compute q and r such that
        //    lc(v)^{m-n+1}*u = v*q + r, 
        // where lc(v) is the leading coefficient of v
        // of degree 'n' and the most significant coefficient 
        // in u has degree 'm'.
        //
        void pseudo_quot_rem(poly const& u, poly const& v, poly& q, poly& r, unsigned& power) {
            SASSERT(u.size() > 0 && v.size() > 0);
            unsigned m = u.size()-1, n = v.size()-1;
            app* v_n = v[n];
            power = m- n + 1;
            q.reset();
            r.reset();
            r.append(u);
            q.resize(m-n+1);
            poly powers_v(m_manager);
            powers_v.push_back(num(1));
            for (unsigned i = 1; i < m-n+2; ++i) {
                powers_v[i] = mk_mul(powers_v[i-1].get(), v_n);
            }
            for (int k = m-n+1; k > 0; ) {
                --k;
                q[k] = mk_mul(u[n+k], powers_v[k].get()); 
                for (int j = n + k; j > 0; ) {
                    --j;        
                    r[j] = mk_mul(v_n, r[j].get()); // n + k != j
                    if (j >= k) {
                        r[j] = mk_sub(r[j].get(), mk_mul(r[n+k].get(), v[j-k]));
                    }
                }
            }            
            DEBUG_CODE(
                poly u1(u);
                mk_mul(u1, powers_v[m-n+1].get());
                SASSERT(test_quot_rem(u1, v, q, r));
                );
        }

        // validate: u = q*v + r
        bool test_quot_rem(poly const& u, poly const& v, poly const& q, poly const& r) {
            poly u1(u), q1(q);
            mk_mul(q1, v);
            mk_add(q1, r);
            mk_sub(q1, u);
            for (unsigned i = 0; i < q1.size(); ++i) {
                if (z() != q1[i].get()) {
                    TRACE("nlarith", display(tout, q1););
                    return false;
                }
            }
            return true;
        }

        /**
            \brief create case split predicates for polynomial elimination.

        */

        void mk_derivative(poly& p) {
            if(p.empty()) { 
                return;
            }
            if (p.size() > 1) {
                p[0] = p[1].get();
                for (unsigned i = 1; i + 1 < p.size(); ++i) {
                    p[i] = mk_mul(num(i), p[i+1].get());
                }
            }
            p.resize(p.size()-1);
        }

        void mk_derivative(unsigned k, poly& p) {
            for (unsigned i = 0; i < k; ++i) {
                mk_derivative(p);
            }
        }

        void mk_inf_sign(isubst& sub, util::literal_set const& literals, app_ref& fml, app_ref_vector& new_atoms) {
            new_atoms.reset();
            expr_ref_vector equivs(m());
            app_ref tmp(m());
            for (unsigned i = 0; i < literals.size(); ++i) {
                if (literals.compare(i) == EQ) {
                    continue;
                }
                apply_subst(sub, literals.compare(i), literals.get_poly(i), tmp); 
                equivs.push_back(m().mk_implies(literals.literal(i), tmp));
                new_atoms.push_back(tmp);
            }
            fml = mk_and(equivs.size(), equivs.c_ptr());
        }
        void mk_plus_inf_sign(util::literal_set const& literals, app_ref& fml, app_ref_vector& new_atoms) {
            plus_inf_subst sub(*this);
            mk_inf_sign(sub, literals, fml, new_atoms);
        }
        void mk_minus_inf_sign(util::literal_set const& literals, app_ref& fml, app_ref_vector& new_atoms) {
            minus_inf_subst sub(*this);
            mk_inf_sign(sub, literals, fml, new_atoms);
        }


        // one of the literals is 0 at x_sup and x_inf, other
        // literals have their derivative close.

        void mk_bound(util::literal_set& literals, app_ref& fml, app_ref_vector& new_atoms) {
            new_atoms.reset();
            app_ref tmp(m());
            expr_ref_vector conjs(m());
            mk_exists_zero(literals, true,  nullptr, conjs, new_atoms);
            mk_same_sign  (literals, true,  conjs, new_atoms);
            mk_exists_zero(literals, false, nullptr, conjs, new_atoms);
            mk_same_sign  (literals, false, conjs, new_atoms);
            mk_lt(literals.x(), literals.x_inf(), conjs, new_atoms);
            mk_lt(literals.x_sup(), literals.x(), conjs, new_atoms);
            fml = mk_and(conjs.size(), conjs.c_ptr());
        }
        void mk_lt(app* x, app* y, expr_ref_vector& conjs, app_ref_vector& new_atoms) {
            app* atm = mk_lt(mk_sub(x,y));
            new_atoms.push_back(atm);
            conjs.push_back(atm);
        }
        void mk_exists_zero(util::literal_set& literals, bool is_sup, poly const* p1, expr_ref_vector& conjs, app_ref_vector& new_atoms) {
            app* x = is_sup?literals.x_sup():literals.x_inf();
            expr_ref_vector ors(m());
            app_ref fml(m());
            basic_subst sub(*this, x);
            for (unsigned i = 0; i < literals.size(); ++i) {
                if (literals.compare(i) == EQ) {
                    continue;
                }
                apply_subst(sub, EQ, literals.get_poly(i), fml); 
                new_atoms.push_back(fml);
                ors.push_back(fml);
            }
            if (p1) {
                apply_subst(sub, EQ, *p1, fml); 
                new_atoms.push_back(fml);
                ors.push_back(fml);
            }
            conjs.push_back(mk_or(ors.size(), ors.c_ptr()));
        }

        /*
          z < x < y:
          z is sup, y is inf
             /\_j (p_j(x) < 0 -> p_j(z) < 0 \/ p_j(z) = 0 /\ p'_j(z) < 0) /\
             /\_j (p_j(x) < 0 -> p_j(y) < 0 \/ p'_j(y) = 0 /\ -p'_j(y) < 0)
        */
        void mk_same_sign(util::literal_set& literals, bool is_sup, expr_ref_vector& conjs, app_ref_vector& new_atoms) {
            app* x = is_sup?literals.x_sup():literals.x_inf();
            app_ref fml(m());
            for (unsigned i = 0; i < literals.size(); ++i) {
                switch(literals.compare(i)) {
                case EQ:
                    break;
                case LT:
                    mk_same_sign(
                        x, is_sup, 
                        literals.get_poly(i), literals.literal(i), 
                        fml, new_atoms);
                   conjs.push_back(fml);              
                   break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
        } 

        void mk_same_sign(app* x, bool is_sup, poly const& p, app* l, 
                          app_ref& fml, app_ref_vector& new_atoms) {
            basic_subst sub0(*this, x);
            if (is_sup) {
                plus_eps_subst sub(*this, sub0);
                apply_subst(sub, LT, p, fml);
            }
            else {
                minus_eps_subst sub(*this, sub0);
                apply_subst(sub, LT, p, fml);
            }
            collect_atoms(fml, new_atoms);
            fml  = m().mk_implies(l, fml);
        }

        void collect_atoms(app* fml, app_ref_vector& atoms) {
            ptr_vector<app> todo;
            todo.push_back(fml);
            while (!todo.empty()) {
                fml = todo.back();
                todo.pop_back();
                if (m().is_and(fml) || m().is_or(fml)) {
                    unsigned sz = fml->get_num_args();
                    for (unsigned i = 0; i < sz; ++i) {
                        todo.push_back(to_app(fml->get_arg(i)));
                    }
                }
                else {
                    atoms.push_back(fml);
                }
            }
        }

        class simple_branch : public util::branch {
            app_ref m_cnstr;
            app_ref_vector m_atoms;
            svector<util::atom_update> m_updates;
        public:
            simple_branch(ast_manager& m, app* cnstr):
              m_cnstr(cnstr, m), m_atoms(m) {}
            ~simple_branch() override {}
            app* get_constraint() override { return m_cnstr.get(); }
            void get_updates(ptr_vector<app>& atoms, svector<util::atom_update>& updates) override {
                for (unsigned i = 0; i < m_atoms.size(); ++i) {
                    atoms.push_back(m_atoms[i].get());
                    updates.push_back(m_updates[i]);
                }
            }
            void update(app* a, util::atom_update u) {
                m_atoms.push_back(a);
                m_updates.push_back(u);
            }
            void insert(app* a) { update(a, util::INSERT); }
            void remove(app* a) { update(a, util::REMOVE); }
        };

        class ins_rem_branch : public simple_branch {
        public:
            ins_rem_branch(ast_manager& m, app* a, app* r, app* cnstr):
              simple_branch(m, cnstr) { insert(a); remove(r); }             
            ~ins_rem_branch() override {}
        };

        /**
           \brief Compute branches given u = 0 & v = 0.
               u has degree m, v has degree n.
               m >= n
            1. u = 0 & lc(v) = 0 & v' = 0  remove v = 0, add v' = 0
            2. let q, r be such that, m >= n 
                 lc(v)^{m-n+1}*u = v*q + r
               then
               v = 0 & r = 0               remove u = 0, add r = 0
        */    

        void get_sign_branches_eq(util::literal_set& lits, unsigned i, unsigned j, ptr_vector<util::branch>& branches) {
            SASSERT(lits.compare(i) == EQ);
            SASSERT(lits.compare(j) == EQ);
            poly const* u = &lits.get_poly(i); 
            poly const* v = &lits.get_poly(j);
            app* l0 = lits.literal(i);
            app* l1 = lits.literal(j);
            if (u->size() < v->size()) {
                std::swap(u, v);
                std::swap(l0, l1);
            }
            app_ref lc_v0(m()), v2_eq(m()), r_eq(m()), lc(m());
            poly v2(m()), q(m()), r(m());
            unsigned n = v->size()-1;

            basic_subst sub(*this, lits.x());
            unsigned power;
            v2.set(*v);
            v2.resize(n);
            quot_rem(*u, *v, q, r, lc_v0, power);
            lc_v0 = mk_eq(lc);            
            sub.mk_eq(v2, v2_eq);
            sub.mk_eq(r, r_eq);

            branches.push_back(alloc(ins_rem_branch, m(), v2_eq, l1, mk_and(lc_v0, v2_eq)));
            branches.push_back(alloc(ins_rem_branch, m(), r_eq,  l0, r_eq));
            // TBD: add constraints that coefficients to l0 are non-zero?
            branches.push_back(alloc(simple_branch, m(), m().mk_not(l0))); 
            branches.push_back(alloc(simple_branch, m(), m().mk_not(l1))); 
        }

        /**
            \brief Compute branch where all predicates are non-zero.

            p_infty \/ p_minus_infty \/ mk_bound

            where mk_bound = 
                  z < x < y /\
                  (\/_j p_j(z) = 0) /\_j (p_j(x) < 0 -> p_j(z) < 0 \/ p_j(z) = 0 /\ p'_j(z) < 0) /\
                  (\/_j p_j(y) = 0) /\_j (p_j(x) < 0 -> p_j(y) < 0 \/ p'_j(y) = 0 /\ -p'_j(z) < 0)

                  p_j ranges over predicates 'p_j(x) < 0'

        */
        void get_sign_branches_neq(util::literal_set& lits, ptr_vector<util::branch>& branches) {
            app_ref_vector new_atoms(m());
            app_ref fml(m());
            branches.push_back(mk_inf_branch(lits, true));
            branches.push_back(mk_inf_branch(lits, false));

            mk_bound(lits, fml, new_atoms);
            simple_branch* br = alloc(simple_branch, m(), fml);
            swap_atoms(br, lits.lits(), new_atoms);
            branches.push_back(br);            
        }

        util::branch* mk_inf_branch(util::literal_set& literals, bool is_pos) {
            app_ref fml(m());
            app_ref_vector new_atoms(m());
            if (is_pos) {
                mk_plus_inf_sign(literals, fml, new_atoms);
            }
            else {
                mk_minus_inf_sign(literals, fml, new_atoms);
            }
            simple_branch* br = alloc(simple_branch, m(), fml);
            swap_atoms(br, literals.lits(), new_atoms);
            return br;
        }

        void swap_atoms(simple_branch* br, app_ref_vector const& old_atoms, app_ref_vector const& new_atoms) {
            for (unsigned i = 0; i < old_atoms.size(); ++i) {
                br->remove(old_atoms[i]);
            }
            for (unsigned i = 0; i < new_atoms.size(); ++i) {
                br->insert(new_atoms[i]);
            }
        }

        /** 
            \brief Compute branches where one equality holds.

            p != 0        \/ 
            lc(p) = 0     \/ 
            p' = 0        \/ 
            p_j(x) < 0 -> p_j(infty) < 0 \/
            p_j(x) < 0 -> p_j(-infty) < 0 \/
            p(z) < 0 < p(y) /\ p'(x) > 0 /\ m_bound(-p') \/
            p(y) < 0 < p(z) /\ p'(x) < 0 /\ m_bound(p')

            where mk_bound(q) = 
                  z < x < y /\             
                  /\_j p_j(x) < 0 -> r_j(x) < 0
                  (\/_j r_j(z) = 0) /\_j (p_j(x) < 0 -> r_j(x) < 0 /\ r_j(z-epsilon) < 0
                  (\/_j r_j(y) = 0) /\_j (p_j(x) < 0 -> r_j(x) < 0 /\ r_j(y+epsilon) < 0

                  p_j ranges over predicates 'p_j(x) < 0', q(x) < 0
                  r_j is obtained by quot_rem(p, p_j, q_j, r_j)

            z < x < y:
              z is sup, y is inf
        */
        void get_sign_branches_eq_neq(util::literal_set& lits, unsigned i, ptr_vector<util::branch>& branches) {
            SASSERT(lits.size() > i);
            SASSERT(lits.compare(i) == EQ);
            poly const& p = lits.get_poly(i);
            poly p1(m());
            mk_differentiate(p, p1);
            app_ref eq(m()), lc_p0(m()), l1(m());
            basic_subst sub_x(*this, lits.x());
            apply_subst(sub_x, EQ, p1, eq);
            lc_p0 = mk_eq(p[p.size()-1]);
            poly p2(p);
            p2.resize(p.size()-1);
            apply_subst(sub_x, EQ, p2, l1);

            branches.push_back(alloc(simple_branch, m(), m().mk_not(lits.literal(i))));
            branches.push_back(alloc(simple_branch, m(), eq));
            branches.push_back(alloc(ins_rem_branch, m(), l1, lits.literal(i), lc_p0));
            branches.push_back(mk_inf_branch(lits, true));
            branches.push_back(mk_inf_branch(lits, false));
            branches.push_back(mk_bound_ext(lits, p, p1, lits.x()));  
        }

        simple_branch* mk_bound_ext(util::literal_set& lits, 
            poly const& p, poly const& p1, app* x) {
            //
            // Assuming p(x) = 0, p'(x) != 0, lc(p) != 0
            // x < y < z
            // (p'(x) < 0 & p(y) < 0 < p(z) | p'(x) > 0 & p(y) > 0 > p(z))
            // \/ p'(y) = 0 \/_j p_j(y) = 0
            // \/ p'(z) = 0 \/_j p_j(z) = 0
            // /\_j p_j(x) < 0 -> sign_adjust(lc, parity, r_j(y+epsilon))
            // /\_j p_j(x) < 0 -> sign_adjust(lc, parity, r_j(z-epsilon))
            // p'(x) < 0 -> r(y+epsilon) < 0 & r(z-epsilon) < 0
            // p'(x) > 0 -> r(y+epsilon) > 0 & r(z-epsilon) > 0
            // sign_adjust(lc, even, r) = r < 0 
            // sign_adjust(lc, odd,  r) = (lc > 0 -> r < 0) & (lc < 0 -> r > 0)
            // 
            
            app_ref eq(m()), fml(m()), l1(m()), l2(m()), l3(m());
            app_ref p1_lt0(m()), p1_gt0(m());
            app_ref_vector new_atoms(m());
            expr_ref_vector conjs(m());
            poly p_m(p), p1_m(p1);
            mk_uminus(p_m);
            mk_uminus(p1_m);
            
            mk_lt(lits.x(), lits.x_inf(), conjs, new_atoms);  // y < x < z
            mk_lt(lits.x_sup(), lits.x(), conjs, new_atoms);
            basic_subst sub_x(*this, x);
            basic_subst sub_y(*this, lits.x_sup());
            basic_subst sub_z(*this, lits.x_inf());
            apply_subst(sub_y, LT, p,  l1);                   // p(y) < 0
            apply_subst(sub_z, LT, p_m,l2);                   // 0 < p(z)
            apply_subst(sub_x, LT, p1_m, p1_gt0);             // p1(x) > 0             
            new_atoms.push_back(l1);            
            new_atoms.push_back(l2);  
            new_atoms.push_back(p1_gt0);     
            conjs.push_back(m().mk_implies(p1_gt0, mk_and(l1, l2))); // p'(x) > 0 -> p(y) < 0 < p(z)

            apply_subst(sub_y, LT, p_m,  l1);                 // p(y) > 0
            apply_subst(sub_z, LT, p,    l2);                 // 0 > p(z)
            apply_subst(sub_x, LT, p1, p1_lt0);               // p1(x) < 0 
            new_atoms.push_back(l1);            
            new_atoms.push_back(l2);  
            new_atoms.push_back(p1_lt0);
            conjs.push_back(m().mk_implies(p1_lt0, mk_and(l1, l2))); // p'(x) < 0 -> p(y) > 0 > p(z)

            conjs.push_back(fml);
            mk_exists_zero(lits, true,  &p1, conjs, new_atoms); // p'(z) = 0 \/_j p_j(z) = 0
            mk_exists_zero(lits, false, &p1, conjs, new_atoms); // p'(y) = 0 \/_j p_j(y) = 0

            for (unsigned i = 0; i < lits.size(); ++i) {
                if (lits.compare(i) == LT) {
                    mk_bound_ext(lits.literal(i), lits.get_poly(i), p, lits.x_sup(), lits.x_inf(), conjs, new_atoms);
                }
            }
            // p'(x) < 0 -> r(y+epsilon) < 0 & r(z-epsilon) < 0
            // p'(x) > 0 -> r(y+epsilon) > 0 & r(z-epsilon) > 0
            mk_bound_ext(p1_lt0, p1,   p, lits.x_sup(), lits.x_inf(), conjs, new_atoms);
            mk_bound_ext(p1_gt0, p1_m, p, lits.x_sup(), lits.x_inf(), conjs, new_atoms);
            fml = mk_and(conjs.size(), conjs.c_ptr());
            simple_branch* br = alloc(simple_branch, m(), fml);
            swap_atoms(br, lits.lits(), new_atoms);
            return br;
        }

        void mk_bound_ext(app* l_j, poly const& p_j, poly const& p, app* y, app* z, expr_ref_vector& conjs, app_ref_vector& new_atoms) {
            poly q(m()), r(m());
            app_ref eq(m()), fml(m()), l1(m()), l2(m()), l3(m()), l4(m());
            // lc(p)^{m-n+1}*p_i = p*q + r
            app_ref lc(m()), lc_m(m());
            basic_subst sub_y(*this, y);
            basic_subst sub_z(*this, z);
            unsigned power;
            quot_rem(p_j, p, q, r, lc, power);
            poly r_m(r);
            mk_uminus(r_m);
            lc_m = mk_uminus(lc);
            plus_eps_subst sub_ye(*this, sub_y);
            minus_eps_subst sub_ze(*this, sub_z);                

            // p_j(x) < 0 -> sign_adjust(lc, parity, r_j(y+epsilon))
            // p_j(x) < 0 -> sign_adjust(lc, parity, r_j(z-epsilon))
            if ((power % 2) == 0) {
                apply_subst(sub_ye, LT, r,   l1);
                apply_subst(sub_ze, LT, r,   l2);
                fml = mk_and(l1, l2);
            }
            else {
                apply_subst(sub_ye, LT, r,   l1);
                apply_subst(sub_ye, LT, r_m, l2);
                l1 = m().mk_implies(mk_lt(lc_m), l1);
                l2 = m().mk_implies(mk_lt(lc),   l2);
                apply_subst(sub_ze, LT, r_m, l3);
                apply_subst(sub_ze, LT, r_m, l4);
                l3 = m().mk_implies(mk_lt(lc_m), l3);
                l4 = m().mk_implies(mk_lt(lc),   l4);
                expr* args[4] = { l1, l2, l3, l4 };
                fml = mk_and(4, args);
            }
            collect_atoms(fml, new_atoms);
            fml = m().mk_implies(l_j, fml);
            conjs.push_back(fml);             
        }        

    public:
        /**
            \brief Generate branch formulas depending on the current evaluation of literals.
            There are 3 cases:
            1. Two or more equalities are true
            2. Precisely one equality is true
            3. No equality is true
        */
        void get_sign_branches(util::literal_set& lits, util::eval& eval, 
                               ptr_vector<util::branch>& branches) {
            m_trail.reset();
            unsigned z1 = UINT_MAX, z2 = UINT_MAX;
            for (unsigned i = 0; i < lits.size(); ++i) {
                if (lits.compare(i) == EQ && l_true == eval(lits.literal(i))) {
                    if (z1 == UINT_MAX) {
                        z1 = i;
                    }
                    else {
                        SASSERT(z2 == UINT_MAX);
                        z2 = i;
                        break;
                    }
                }
            }
            if (z1 == UINT_MAX) {
                get_sign_branches_neq(lits, branches);                
            }
            else if (z2 == UINT_MAX) {
                get_sign_branches_eq_neq(lits, z1, branches);
            }
            else {
                get_sign_branches_eq(lits, z1, z2, branches);
            }
        }


        bool get_sign_literals(util::atoms const& atoms, util::eval& eval, util::literal_set*& lits) {
            // TBD: use 'eval' to select non-linear literals that are relevant.
            m_trail.reset();
            ptr_vector<app> nlvars, atms;
            util::atoms::iterator it = atoms.begin(), end = atoms.end();
            for (; it != end; ++it) {
                atms.push_back(*it);
            }
            extract_non_linear(atms.size(), atms.begin(), nlvars);
            if (nlvars.empty()) {
                lits = nullptr;
                return true;
            }
            app* x = nlvars.back();
            contains_app contains_x(m(), x);
            expr* const* _atoms = (expr*const*)atms.begin();
            lits = alloc(util::literal_set, m());
            lits->set_x(x);
            if (get_polys(contains_x, atms.size(), _atoms, lits->polys(), lits->comps(), nullptr, &lits->lits())) {
                return true;
            }
            dealloc(lits);
            lits = nullptr;
            return false;
        }                  

        // Sign matrix algorithm (Cohen-Hormander)
    public:
        enum sign { Negative, Zero, NonZero, Positive, Unknown };
        typedef svector<sign> sign_vector;
        typedef vector<sign_vector> sign_matrix;
        void mk_sign_matrix(vector<poly> const& polys, sign_matrix& result) {

        }                            
    private:
        // remove points that don't contain Zero
        void condense(sign_matrix& mat) {
            unsigned i = 0, j = 0;
            SASSERT(mat.size() % 2 == 0);
            for (; i + 1 < mat.size(); i += 2) {
                if (mat[i+1].contains(Zero)) {
                    if (i != j) {
                        mat[j] = mat[i];
                        mat[j+1] = mat[i+1];
                    }
                    j += 2;
                }
            }
            mat.resize(j);
        }

        // set sign of p(x) to sign of q_i(x) where p_i(x) = 0
        void infer_psign(sign_vector& pqs) {
            unsigned n = pqs.size()/2;
            for (unsigned i = 0; i < n; ++i) {
                if (Zero == pqs[i]) {
                    sign s = pqs[i+n];
                    pqs.resize(n);
                    cons(s, pqs);
                    return;
                }
            }
            pqs.resize(n);
            cons(Unknown, pqs);
        }

        void cons(sign s, sign_vector& v) {
            for (unsigned i = 0; i < v.size(); ++i) {
                std::swap(s, v[i]);
            }
            v.push_back(s);
        }
        
        // Deduce matrix for p, p1, .., pn from p', p1, .., pn, q0, .., qn
        void deduce_matrix(sign_matrix& m) {
            for (unsigned i = 0; i < m.size(); ++i) {
                infer_psign(m[i]);
            }
            condense(m);
        }
        
    };        

    util::util(ast_manager& m) {
        m_imp = alloc(imp, m);
    }

    util::~util() { dealloc(m_imp); }

    
    bool util::create_branches(app* x, unsigned num_lits, expr* const* lits, branch_conditions& bc) {
        return m_imp->create_branches(x, num_lits, lits, bc);
    }

    void util::set_enable_linear(bool enable_linear) { m_imp->set_enable_linear(enable_linear); }

    void util::extract_non_linear(expr* e, ptr_vector<app>& nl_vars) {
        m_imp->extract_non_linear(e, nl_vars);
    }

    void util::deallocate(literal_set* lits) {
        dealloc(lits);
    }

    bool util::get_sign_literals(atoms const& atoms, eval& ev, literal_set*& lits) {
        return m_imp->get_sign_literals(atoms, ev, lits);
    }

    void util::get_sign_branches(literal_set& lits, eval& ev, ptr_vector<branch>& branches) {
        m_imp->get_sign_branches(lits, ev, branches);
    }
};


