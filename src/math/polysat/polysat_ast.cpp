/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat to ast conversion

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#include "math/polysat/polysat_ast.h"
#include "math/polysat/solver.h"
#include "math/polysat/umul_ovfl_constraint.h"
#include "util/util.h"
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "util/uint_map.h"

namespace polysat {

    struct polysat_ast_d {
        ast_manager m;
        scoped_ptr<bv_util> bv;
        uint_map<expr> var_expr;

        decl_ref_vector decls;
        expr_ref_vector formulas;

        // just keep all expressions alive
        ast_ref_vector storage;

        polysat_ast_d(): m(), decls(m), formulas(m), storage(m)
        {
            reg_decl_plugins(m);
            bv = alloc(bv_util, m);
        }

        ~polysat_ast_d() = default;

        ast*  store(ast*  a) { storage.push_back(ast_ref{a, m}); return a; }
        expr* store(expr* e) { storage.push_back(ast_ref{e, m}); return e; }
        app*  store(app*  a) { storage.push_back(ast_ref{a, m}); return a; }
    };

    polysat_ast::polysat_ast(solver& s)
        : s(s)
        , d(alloc(polysat_ast_d))
    { }

    polysat_ast::~polysat_ast() = default;

    ast_manager& polysat_ast::m() const { return d->m; }
    bv_util& polysat_ast::bv() const { return *d->bv; }

    expr* polysat_ast::mk_fresh_bool_const(char const* prefix) {
        app* b = d->store(m().mk_fresh_const(prefix, m().mk_bool_sort()));
        d->decls.push_back(b->get_decl());
        return b;
    }

    expr* polysat_ast::mk_val(rational const& val, unsigned bit_width) {
        return d->store(bv().mk_numeral(val, bit_width));
    }

    expr* polysat_ast::mk_var(pvar x) {
        expr* node;
        if (!d->var_expr.find(x, node)) {
            unsigned bit_width = s.size(x);
            std::string name = "v";
            name += std::to_string(x);
            func_decl* decl = m().mk_const_decl(name, bv().mk_sort(bit_width));
            d->decls.push_back(decl);
            node = d->store(m().mk_const(decl));
            d->var_expr.insert(x, node);
            // if x is defined by an op_constraint, add it as background assumption.
            signed_constraint c = s.m_constraints.find_op_by_result_var(x);
            if (c)
                add(mk_lit(c));
        }
        return node;
    }

    expr* polysat_ast::mk_mono(dd::pdd_monomial const& mono, unsigned bit_width) {
        if (mono.vars.empty())
            return mk_val(mono.coeff, bit_width);
        if (mono.coeff.is_one() && mono.vars.size() == 1)
            return mk_var(mono.vars[0]);
        ptr_vector<expr> args;
        if (!mono.coeff.is_one())
            args.push_back(mk_val(mono.coeff, bit_width));
        for (pvar x : mono.vars) {
            VERIFY_EQ(s.size(x), bit_width);
            args.push_back(mk_var(x));
        }
        return d->store(bv().mk_bv_mul(args));
    }

    expr* polysat_ast::mk_poly(pdd const& p) {
        unsigned const N = p.power_of_2();
        if (p.is_val())
            return mk_val(p.val(), N);
        if (p.is_var())
            return mk_var(p.var());
        if (p.is_monomial())
            return mk_mono(*p.begin(), N);
        ptr_vector<expr> args;
        for (auto const& mono : p)
            args.push_back(mk_mono(mono, N));
        return d->store(bv().mk_bv_add(args));
    }

    expr* polysat_ast::mk_parity(pdd const& p) {
        unsigned const N = p.power_of_2();
        if (p.is_val())
            return mk_val(rational(p.val().parity(N)), N);
        app*  parity = d->store(m().mk_fresh_const("parity", bv().mk_sort(N)));
        d->decls.push_back(parity->get_decl());
        expr* parity_1 = d->store(bv().mk_bv_add(parity, mk_val(rational(1), N)));
        expr* v = mk_poly(p);
        // if v = 0
        //   then parity = N
        //   else v = (v >> parity) << parity
        //        && v != (v >> parity+1) << parity+1
        // TODO: what about:  v[k:] = 0  &&  v[k+1:] != 0  ==>  parity = k  for each k?
        // TODO: add helper axiom like parity <= N ?
        expr* definition =
            m().mk_ite(
                m().mk_eq(v, mk_val(rational(0), N)),
                m().mk_eq(parity, mk_val(rational(N), N)),
                m().mk_and(
                    m().mk_eq(v, bv().mk_bv_shl(bv().mk_bv_lshr(v, parity), parity)),
                    m().mk_not(m().mk_eq(v, bv().mk_bv_shl(bv().mk_bv_lshr(v, parity_1), parity_1)))
                ));
        add(definition);
        return parity;
    }

    expr* polysat_ast::mk_inv(pdd const& p, pdd const& p_inv) {
        unsigned const N = p.power_of_2();
        // p_inv == smallest_pseudo_inverse(p)
        expr* v = mk_poly(p);
        expr* v_inv = mk_poly(p_inv);
        expr* parity = mk_parity(p);
        expr* one = mk_val(rational(1), N);
        // 2^parity = v * v_inv
        expr* definition1 = m().mk_eq(bv().mk_bv_shl(one, parity), bv().mk_bv_mul(v, v_inv));
        // v_inv <= 2^(N - parity) - 1
        expr* v_inv_max = bv().mk_bv_sub(bv().mk_bv_shl(one, bv().mk_bv_sub(mk_val(rational(N), N), parity)), one);
        expr* definition2 = bv().mk_ule(v_inv, v_inv_max);
        // conditional on b
        expr* b = mk_fresh_bool_const("parity_enable");
        add(m().mk_iff(b, definition1));
        add(m().mk_iff(b, definition2));
        return b;
    }

    expr* polysat_ast::mk_not(expr* e) {
        return d->store(m().mk_not(e));
    }

    expr* polysat_ast::mk_ule(pdd const& p, pdd const& q) {
        if (q.is_zero())
            return d->store(m().mk_eq(mk_poly(p), mk_poly(q)));
        else
            return d->store(bv().mk_ule(mk_poly(p), mk_poly(q)));
    }

    expr* polysat_ast::mk_ule(pdd const& p, pdd const& q, bool sign) {
        expr* e = mk_ule(p, q);
        if (sign)
            e = mk_not(e);
        return e;
    }

    expr* polysat_ast::mk_umul_ovfl(pdd const& p, pdd const& q, bool sign) {
        expr* e = d->store(bv().mk_bvumul_no_ovfl(mk_poly(p), mk_poly(q)));
        if (!sign)
            e = mk_not(e);
        return e;
    }

    expr* polysat_ast::mk_lit(sat::literal lit) {
        return mk_lit(s.lit2cnstr(lit));
    }

    expr* polysat_ast::mk_lit(signed_constraint c) {
        if (c->is_ule())
            return mk_ule(c->to_ule().lhs(), c->to_ule().rhs(), c.sign());
        if (c->is_umul_ovfl())
            return mk_umul_ovfl(c->to_umul_ovfl().p(), c->to_umul_ovfl().q(), c.sign());
        if (c->is_op()) {
            op_constraint& op = c->to_op();
            switch (op.get_op()) {
            case op_constraint::code::inv_op:
                return mk_inv(op.p(), op.r());
            default:
                break;
            }
        }
        verbose_stream() << "polysat_ast not yet supported: " << c << "\n";
        m_ok = false;
        // NOT_IMPLEMENTED_YET();
        return d->store(m().mk_true());
    }

    expr* polysat_ast::mk_clause(clause& cl) {
        ptr_vector<expr> args;
        for (sat::literal lit : cl)
            args.push_back(mk_lit(lit));
        return d->store(m().mk_or(args));
    }

    void polysat_ast::add(expr* e) {
        d->formulas.push_back(e);
    }

    std::ostream& polysat_ast::display(std::ostream& out) const {
        if (m_status == l_true)
            out << "(set-info :status sat)\n";
        else if (m_status == l_false)
            out << "(set-info :status unsat)\n";
        if (!m_description.empty()) {
            out << "(set-info :source |\n";
            out << m_description;
            if (m_description.back() != '\n')
                out << '\n';
            out << "|)\n";
        }
        params_ref p;
        p.set_uint("max_depth", 4294967295u);
        p.set_uint("min_alias_size", 4294967295u);
        for (decl* d : d->decls)
            out << mk_pp(d, m(), p) << "\n";
        for (expr* e : d->formulas) {
            out << "(assert\n";
            out << "    " << mk_pp(e, m(), p, 4) << "\n";
            out << ")\n";
        }
        out << "(check-sat)\n";
        return out;
    }

}
