/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bvarray2uf_rewriter.cpp

Abstract:

    Rewriter that rewrites bit-vector arrays into bit-vector
    (uninterpreted) functions.

Author:

    Christoph (cwinter) 2015-11-04

Notes:

--*/

#include"cooperate.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"params.h"
#include"ast_pp.h"
#include"bvarray2uf_rewriter.h"
#include"rewriter_def.h"
#include"ref_util.h"

// [1] C. M. Wintersteiger, Y. Hamadi, and L. de Moura: Efficiently Solving
//     Quantified Bit-Vector Formulas, in Formal Methods in System Design,
//     vol. 42, no. 1, pp. 3-23, Springer, 2013.

bvarray2uf_rewriter_cfg::bvarray2uf_rewriter_cfg(ast_manager & m, params_ref const & p) :
    m_manager(m),
    m_out(m),
    m_bindings(m),
    m_bv_util(m),
    m_array_util(m),
    m_emc(0),
    m_fmc(0),
    extra_assertions(m) {
    updt_params(p);
    // We need to make sure that the mananger has the BV and array plugins loaded.
    symbol s_bv("bv");
    if (!m_manager.has_plugin(s_bv))
        m_manager.register_plugin(s_bv, alloc(bv_decl_plugin));
    symbol s_array("array");
    if (!m_manager.has_plugin(s_array))
        m_manager.register_plugin(s_array, alloc(array_decl_plugin));
}

bvarray2uf_rewriter_cfg::~bvarray2uf_rewriter_cfg() {
    dec_ref_map_key_values(m_manager, m_arrays_fs);
}

void bvarray2uf_rewriter_cfg::reset() {}

sort * bvarray2uf_rewriter_cfg::get_index_sort(expr * e) {
    return get_index_sort(m_manager.get_sort(e));
}

sort * bvarray2uf_rewriter_cfg::get_index_sort(sort * s) {
    SASSERT(s->get_num_parameters() >= 2);
    unsigned total_width = 0;
    for (unsigned i = 0; i < s->get_num_parameters() - 1; i++) {
        parameter const & p = s->get_parameter(i);
        SASSERT(p.is_ast() && is_sort(to_sort(p.get_ast())));
        SASSERT(m_bv_util.is_bv_sort(to_sort(p.get_ast())));
        total_width += m_bv_util.get_bv_size(to_sort(p.get_ast()));
    }
    return m_bv_util.mk_sort(total_width);
}

sort * bvarray2uf_rewriter_cfg::get_value_sort(expr * e) {
    return get_value_sort(m_manager.get_sort(e));
}

sort * bvarray2uf_rewriter_cfg::get_value_sort(sort * s) {
    SASSERT(s->get_num_parameters() >= 2);
    parameter const & p = s->get_parameter(s->get_num_parameters() - 1);
    SASSERT(p.is_ast() && is_sort(to_sort(p.get_ast())));
    return to_sort(p.get_ast());
}

bool bvarray2uf_rewriter_cfg::is_bv_array(expr * e) {
    return is_bv_array(m_manager.get_sort(e));
}

bool bvarray2uf_rewriter_cfg::is_bv_array(sort * s) {
    if (!m_array_util.is_array(s))
        return false;

    SASSERT(s->get_num_parameters() >= 2);
    for (unsigned i = 0; i < s->get_num_parameters(); i++) {
        parameter const & p = s->get_parameter(i);
        if (!p.is_ast() || !is_sort(to_sort(p.get_ast())) ||
            !m_bv_util.is_bv_sort(to_sort(p.get_ast())))
            return false;
    }

    return true;
}

func_decl_ref bvarray2uf_rewriter_cfg::mk_uf_for_array(expr * e) {
    SASSERT(is_bv_array(e));

    if (m_array_util.is_as_array(e))
        return func_decl_ref(static_cast<func_decl*>(to_app(e)->get_decl()->get_parameter(0).get_ast()), m_manager);
    else {
        func_decl * bv_f = 0;
        if (!m_arrays_fs.find(e, bv_f)) {
            sort * domain = get_index_sort(e);
            sort * range = get_value_sort(e);
            bv_f = m_manager.mk_fresh_func_decl("f_t", "", 1, &domain, range);
            TRACE("bvarray2uf_rw", tout << "for " << mk_ismt2_pp(e, m_manager) << " new func_decl is " << mk_ismt2_pp(bv_f, m_manager) << std::endl; );
            if (is_uninterp_const(e)) {
                if (m_emc)
                    m_emc->insert(to_app(e)->get_decl(),
                                  m_array_util.mk_as_array(m_manager.get_sort(e), bv_f));
            }
            else if (m_fmc)
                m_fmc->insert(bv_f);
            m_arrays_fs.insert(e, bv_f);
            m_manager.inc_ref(e);
            m_manager.inc_ref(bv_f);
        }
        else {
            TRACE("bvarray2uf_rw", tout << "for " << mk_ismt2_pp(e, m_manager) << " found " << mk_ismt2_pp(bv_f, m_manager) << std::endl; );
        }

        return func_decl_ref(bv_f, m_manager);
    }
}

br_status bvarray2uf_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    br_status res = BR_FAILED;

    if (m_manager.is_eq(f) && is_bv_array(f->get_domain()[0])) {
        SASSERT(num == 2);
        // From [1]: Finally, we replace equations of the form t = s,
        // where t and s are arrays, with \forall x . f_t(x) = f_s(x).
        if (m_manager.are_equal(args[0], args[1])) {
            result = m_manager.mk_true();
            res = BR_DONE;
        }
        else {
            func_decl_ref f_t(mk_uf_for_array(args[0]), m_manager);
            func_decl_ref f_s(mk_uf_for_array(args[1]), m_manager);

            sort * sorts[1] = { get_index_sort(m_manager.get_sort(args[0])) };
            symbol names[1] = { symbol("x") };
            var_ref x(m_manager.mk_var(0, sorts[0]), m_manager);

            expr_ref body(m_manager);
            body = m_manager.mk_eq(m_manager.mk_app(f_t, x.get()), m_manager.mk_app(f_s, x.get()));

            result = m_manager.mk_forall(1, sorts, names, body);
            res = BR_DONE;
        }
    }
    else if (m_manager.is_distinct(f) && is_bv_array(f->get_domain()[0])) {
        result = m_manager.mk_distinct_expanded(num, args);
        res = BR_REWRITE1;
    }
    else if (m_manager.is_term_ite(f) && is_bv_array(f->get_range())) {
        expr_ref c(args[0], m_manager);
        func_decl_ref f_t(mk_uf_for_array(args[1]), m_manager);
        func_decl_ref f_f(mk_uf_for_array(args[2]), m_manager);

        TRACE("bvarray2uf_rw", tout << "(ite " << c << ", " << f_t->get_name()
            << ", " << f_f->get_name() << ")" << std::endl;);

        sort * sorts[1] = { get_index_sort(m_manager.get_sort(args[1])) };
        symbol names[1] = { symbol("x") };
        var_ref x(m_manager.mk_var(0, sorts[0]), m_manager);

        app_ref f_a(m_manager), f_ta(m_manager), f_fa(m_manager);
        f_a = m_manager.mk_app(f, num, args);
        f_ta = m_manager.mk_app(f_t, x.get());
        f_fa = m_manager.mk_app(f_f, x.get());

        app_ref e(m_manager);
        func_decl_ref itefd(m_manager);
        e = m_manager.mk_ite(c, f_ta, f_fa);

        func_decl * bv_f = 0;
        if (!m_arrays_fs.find(f_a, bv_f)) {
            sort * domain = get_index_sort(args[1]);
            sort * range = get_value_sort(args[1]);
            bv_f = m_manager.mk_fresh_func_decl("f_t", "", 1, &domain, range);
            TRACE("bvarray2uf_rw", tout << mk_ismt2_pp(e, m_manager) << " -> " << bv_f->get_name() << std::endl; );
            if (is_uninterp_const(e)) {
                if (m_emc)
                    m_emc->insert(e->get_decl(),
                        m_array_util.mk_as_array(m_manager.get_sort(e), bv_f));
            }
            else if (m_fmc)
                m_fmc->insert(bv_f);
            m_arrays_fs.insert(e, bv_f);
            m_manager.inc_ref(e);
            m_manager.inc_ref(bv_f);
        }

        expr_ref q(m_manager), body(m_manager);
        body = m_manager.mk_eq(m_manager.mk_app(bv_f, x), e);
        q = m_manager.mk_forall(1, sorts, names, body);
        extra_assertions.push_back(q);

        result = m_array_util.mk_as_array(f->get_range(), bv_f);

        TRACE("bvarray2uf_rw", tout << "result: " << mk_ismt2_pp(result, m_manager) << ")" << std::endl;);
        res = BR_DONE;
        
    }
    else if (f->get_family_id() == m_manager.get_basic_family_id() && is_bv_array(f->get_range())) {
        NOT_IMPLEMENTED_YET();
    }
    else if (f->get_family_id() == null_family_id) {
        TRACE("bvarray2uf_rw", tout << "UF APP: " << f->get_name() << std::endl; );

        bool has_bv_arrays = false;
        func_decl_ref f_t(m_manager);
        for (unsigned i = 0; i < num; i++) {
            if (is_bv_array(args[i])) {
                SASSERT(m_array_util.is_as_array(args[i]));
                has_bv_arrays = true;
            }
        }

        expr_ref t(m_manager);
        t = m_manager.mk_app(f, num, args);

        if (is_bv_array(t)) {
            // From [1]: For every array term t we create a fresh uninterpreted function f_t.
            f_t = mk_uf_for_array(t);
            result = m_array_util.mk_as_array(m_manager.get_sort(t), f_t);
            res = BR_DONE;
        }
        else if (has_bv_arrays) {
            result = t;
            res = BR_DONE;
        }
        else
            res = BR_FAILED;
    }
    else if (m_array_util.get_family_id() == f->get_family_id()) {
        TRACE("bvarray2uf_rw", tout << "APP: " << f->get_name() << std::endl; );

        if (m_array_util.is_select(f)) {
            SASSERT(num == 2);
            expr * t = args[0];
            expr * i = args[1];
            TRACE("bvarray2uf_rw", tout <<
                "select; array: " << mk_ismt2_pp(t, m()) <<
                " index: " << mk_ismt2_pp(i, m()) << std::endl;);

            if (!is_bv_array(t))
                res = BR_FAILED;
            else {
                // From [1]: Then, we replace terms of the form select(t, i) with f_t(i).
                func_decl_ref f_t(mk_uf_for_array(t), m_manager);
                result = m_manager.mk_app(f_t, i);
                res = BR_DONE;
            }
        }
        else {
            if (!is_bv_array(f->get_range()))
                res = BR_FAILED;
            else {
                if (m_array_util.is_const(f)) {
                    SASSERT(num == 1);
                    expr_ref t(m_manager.mk_app(f, num, args), m_manager);
                    expr * v = args[0];
                    func_decl_ref f_t(mk_uf_for_array(t), m_manager);

                    result = m_array_util.mk_as_array(f->get_range(), f_t);
                    res = BR_DONE;

                    // Add \forall x . f_t(x) = v
                    sort * sorts[1] = { get_index_sort(f->get_range()) };
                    symbol names[1] = { symbol("x") };
                    var_ref x(m_manager.mk_var(0, sorts[0]), m_manager);

                    expr_ref body(m_manager);
                    body = m_manager.mk_eq(m_manager.mk_app(f_t, x.get()), v);

                    expr_ref frllx(m_manager.mk_forall(1, sorts, names, body), m_manager);
                    extra_assertions.push_back(frllx);
                }
                else if (m_array_util.is_as_array(f)) {
                    res = BR_FAILED;
                }
                else if (m_array_util.is_map(f)) {
                    SASSERT(f->get_num_parameters() == 1);
                    SASSERT(f->get_parameter(0).is_ast());
                    expr_ref t(m_manager.mk_app(f, num, args), m_manager);
                    func_decl_ref f_t(mk_uf_for_array(t), m_manager);
                    func_decl_ref map_f(to_func_decl(f->get_parameter(0).get_ast()), m_manager);

                    func_decl_ref_vector ss(m_manager);
                    for (unsigned i = 0; i < num; i++) {
                        SASSERT(m_array_util.is_array(args[i]));
                        func_decl_ref fd(mk_uf_for_array(args[i]), m_manager);
                        ss.push_back(fd);
                    }

                    // Add \forall x . f_t(x) = map_f(a[x], b[x], ...)
                    sort * sorts[1] = { get_index_sort(f->get_range()) };
                    symbol names[1] = { symbol("x") };
                    var_ref x(m_manager.mk_var(0, sorts[0]), m_manager);

                    expr_ref_vector new_args(m_manager);
                    for (unsigned i = 0; i < num; i++)
                        new_args.push_back(m_manager.mk_app(ss[i].get(), x.get()));

                    expr_ref body(m_manager);
                    body = m_manager.mk_eq(m_manager.mk_app(f_t, x.get()),
                                           m_manager.mk_app(map_f, num, new_args.c_ptr()));

                    expr_ref frllx(m_manager.mk_forall(1, sorts, names, body), m_manager);
                    extra_assertions.push_back(frllx);

                    result = m_array_util.mk_as_array(f->get_range(), f_t);
                    res = BR_DONE;
                }
                else if (m_array_util.is_store(f)) {
                    SASSERT(num == 3);
                    expr * s = args[0];
                    expr * i = args[1];
                    expr * v = args[2];
                    TRACE("bvarray2uf_rw", tout <<
                        "store; array: " << mk_ismt2_pp(s, m()) <<
                        " index: " << mk_ismt2_pp(i, m()) <<
                        " value: " << mk_ismt2_pp(v, m()) << std::endl;);
                    if (!is_bv_array(s))
                        res = BR_FAILED;
                    else {
                        expr_ref t(m_manager.mk_app(f, num, args), m_manager);
                        // From [1]: For every term t of the form store(s, i, v), we add the universal
                        // formula \forall x . x = i \vee f_t(x) = f_s(x), and the ground atom f_t(i) = v.
                        func_decl_ref f_s(mk_uf_for_array(s), m_manager);
                        func_decl_ref f_t(mk_uf_for_array(t), m_manager);

                        result = m_array_util.mk_as_array(f->get_range(), f_t);
                        res = BR_DONE;

                        sort * sorts[1] = { get_index_sort(f->get_range()) };
                        symbol names[1] = { symbol("x") };
                        var_ref x(m_manager.mk_var(0, sorts[0]), m_manager);

                        expr_ref body(m_manager);
                        body = m_manager.mk_or(m_manager.mk_eq(x, i),
                                               m_manager.mk_eq(m_manager.mk_app(f_t, x.get()),
                                                               m_manager.mk_app(f_s, x.get())));

                        expr_ref frllx(m_manager.mk_forall(1, sorts, names, body), m_manager);
                        extra_assertions.push_back(frllx);

                        expr_ref ground_atom(m_manager);
                        ground_atom = m_manager.mk_eq(m_manager.mk_app(f_t, i), v);
                        extra_assertions.push_back(ground_atom);
                        TRACE("bvarray2uf_rw", tout << "ground atom: " << mk_ismt2_pp(ground_atom, m()) << std::endl; );
                    }
                }
                else {
                    NOT_IMPLEMENTED_YET();
                    res = BR_FAILED;
                }
            }
        }
    }

    CTRACE("bvarray2uf_rw", res == BR_DONE, tout << "result: " << mk_ismt2_pp(result, m()) << std::endl; );
    return res;
}

bool bvarray2uf_rewriter_cfg::pre_visit(expr * t)
{
    TRACE("bvarray2uf_rw_q", tout << "pre_visit: " << mk_ismt2_pp(t, m()) << std::endl;);

    if (is_quantifier(t)) {
        quantifier * q = to_quantifier(t);
        TRACE("bvarray2uf_rw_q", tout << "pre_visit quantifier [" << q->get_id() << "]: " << mk_ismt2_pp(q->get_expr(), m()) << std::endl;);
        sort_ref_vector new_bindings(m_manager);
        for (unsigned i = 0; i < q->get_num_decls(); i++)
            new_bindings.push_back(q->get_decl_sort(i));
        SASSERT(new_bindings.size() == q->get_num_decls());
        m_bindings.append(new_bindings);
    }
    return true;
}

bool bvarray2uf_rewriter_cfg::reduce_quantifier(quantifier * old_q,
    expr * new_body,
    expr * const * new_patterns,
    expr * const * new_no_patterns,
    expr_ref & result,
    proof_ref & result_pr) {
    NOT_IMPLEMENTED_YET();
    return true;
}

bool bvarray2uf_rewriter_cfg::reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
    if (t->get_idx() >= m_bindings.size())
        return false;
    NOT_IMPLEMENTED_YET();
    return true;
}

template class rewriter_tpl<bvarray2uf_rewriter_cfg>;
