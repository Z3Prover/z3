/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    static_features.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-16.

Revision History:

--*/
#include "ast/static_features.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/for_each_expr.h"

static_features::static_features(ast_manager & m):
    m(m),
    m_autil(m),
    m_bvutil(m),
    m_arrayutil(m),
    m_fpautil(m),
    m_sequtil(m),
    m_bfid(m.get_basic_family_id()),
    m_afid(m.mk_family_id("arith")),
    m_lfid(m.mk_family_id("label")),
    m_arrfid(m.mk_family_id("array")),
    m_srfid(m.mk_family_id("specrels")),
    m_label_sym("label"),
    m_pattern_sym("pattern"),
    m_expr_list_sym("expr-list") {
    reset();
}

void static_features::reset() {
    m_pre_processed                      .reset();
    m_post_processed.reset();
    m_cnf                                  = true;
    m_num_exprs                            = 0;
    m_num_roots                            = 0;
    m_max_depth                            = 0;
    m_num_quantifiers                      = 0;
    m_num_quantifiers_with_patterns        = 0;
    m_num_quantifiers_with_multi_patterns  = 0;
    m_num_clauses                          = 0;
    m_num_bin_clauses                      = 0;
    m_num_units                            = 0;
    m_sum_clause_size                      = 0;
    m_num_nested_formulas                  = 0;
    m_num_bool_exprs                       = 0;
    m_num_bool_constants                   = 0;
    m_num_ite_trees                        = 0;
    m_max_ite_tree_depth                   = 0;
    m_sum_ite_tree_depth                   = 0;
    m_num_ors                              = 0;
    m_num_ands                             = 0;
    m_num_iffs                             = 0;
    m_num_ite_formulas                     = 0;
    m_num_ite_terms                        = 0;
    m_num_sharing                          = 0;
    m_num_interpreted_exprs                = 0;
    m_num_uninterpreted_exprs              = 0;
    m_num_interpreted_constants            = 0;
    m_num_uninterpreted_constants          = 0;
    m_num_uninterpreted_functions          = 0;
    m_num_eqs                              = 0;
    m_has_rational                         = false;
    m_has_int                              = false;
    m_has_real                             = false; 
    m_has_bv                               = false;
    m_has_fpa                              = false;
    m_has_sr                               = false;
    m_has_str                              = false;
    m_has_seq_non_str                      = false;
    m_has_arrays                           = false;
    m_has_ext_arrays                       = false;
    m_arith_k_sum                          .reset();
    m_num_arith_terms                      = 0;
    m_num_arith_eqs                        = 0;
    m_num_arith_ineqs                      = 0;
    m_num_diff_terms                       = 0;
    m_num_diff_eqs                         = 0;   
    m_num_diff_ineqs                       = 0;   
    m_num_simple_eqs                       = 0;
    m_num_simple_ineqs                     = 0;
    m_num_non_linear                       = 0;
    m_num_apps                             .reset();
    m_num_theory_terms                     .reset();
    m_num_theory_atoms                     .reset();
    m_num_theory_constants                 .reset();
    m_num_theory_eqs                       .reset();
    m_num_aliens                           = 0;
    m_num_aliens_per_family                .reset();
    m_num_theories                         = 0;
    m_theories                             .reset();
    m_max_stack_depth                      = 30;
    flush_cache();
}

void static_features::flush_cache() {
    m_expr2depth.reset(); 
    m_expr2or_and_depth.reset();
    m_expr2ite_depth.reset();
    m_expr2formula_depth.reset();
}


bool static_features::is_diff_term(expr const * e, rational & r) const {
    // lhs can be 'x' or '(+ k x)'
    if (!is_arith_expr(e)) {
        r.reset();
        return true;
    }
    if (is_numeral(e, r))
        return true;
    expr* a1 = nullptr, *a2 = nullptr;
    return m_autil.is_add(e, a1, a2) && is_numeral(a1, r) && !is_arith_expr(a2) && !m.is_ite(a2);
}

bool static_features::is_diff_atom(expr const * e) const {
    if (!is_bool(e))
        return false;
    if (!m.is_eq(e) && !is_arith_expr(e))
        return false;
    SASSERT(to_app(e)->get_num_args() == 2);
    expr * lhs = to_app(e)->get_arg(0);
    expr * rhs = to_app(e)->get_arg(1);
    if (!is_arith_expr(lhs) && !is_arith_expr(rhs) && !m.is_ite(lhs) && !m.is_ite(rhs)) 
        return true;    
    if (!is_numeral(rhs)) 
        return false;    
    // lhs can be 'x' or '(+ x (* -1 y))' or '(+ (* -1 x) y)'
    if (!is_arith_expr(lhs) && !m.is_ite(lhs))
        return true;
    expr* arg1, *arg2;
    if (!m_autil.is_add(lhs, arg1, arg2)) 
        return false;    
    expr* m1, *m2;
    if (!is_arith_expr(arg1) && m_autil.is_mul(arg2, m1, m2) &&  is_minus_one(m1) && !is_arith_expr(m2) && !m.is_ite(m2))
        return true;
    if (!is_arith_expr(arg2) && m_autil.is_mul(arg1, m1, m2) &&  is_minus_one(m1) && !is_arith_expr(m2) && !m.is_ite(m2))
        return true;
    return false;
    
}

bool static_features::is_gate(expr const * e) const {
    if (is_basic_expr(e)) {
        switch (to_app(e)->get_decl_kind()) {
        case OP_ITE: case OP_AND: case OP_OR: case OP_XOR: case OP_IMPLIES:
            return true;
        case OP_EQ:
            return m.is_bool(e);
        }
    }
    return false;
}

void static_features::update_core(expr * e) {
    m_num_exprs++;
    
    // even if a benchmark does not contain any theory interpreted function decls, we still have to install
    // the theory if the benchmark contains constants or function applications of an interpreted sort.
    sort * s      = e->get_sort();
    if (!m.is_uninterp(s))
        mark_theory(s->get_family_id());
    
    bool _is_gate = is_gate(e);
    bool _is_eq   = m.is_eq(e);
    if (_is_gate) {
        m_cnf = false;
        m_num_nested_formulas++;
        switch (to_app(e)->get_decl_kind()) {
        case OP_ITE: 
            if (is_bool(e))
                m_num_ite_formulas++;
            else {
                m_num_ite_terms++;
                // process then&else nodes
                for (unsigned i = 1; i < 3; i++) {
                    expr * arg = to_app(e)->get_arg(i);
                    acc_num(arg);
                    // Must check whether arg is diff logic or not.
                    // Otherwise, problem can be incorrectly tagged as diff logic.
                    sort * arg_s = arg->get_sort(); 
                    family_id fid_arg = arg_s->get_family_id();
                    if (fid_arg == m_afid) {
                        m_num_arith_terms++;
                        rational k;
                        TRACE(diff_term, tout << "diff_term: " << is_diff_term(arg, k) << "\n" << mk_pp(arg, m) << "\n";);
                        if (is_diff_term(arg, k)) {
                            m_num_diff_terms++;
                            acc_num(k);
                        }
                    }
                }
            }
            break;
        case OP_AND: 
            m_num_ands++;
            break;
        case OP_OR:
            m_num_ors++;
            break;
        case OP_EQ: 
            m_num_iffs++;
            break;
        }
    }
    if (is_bool(e)) {
        m_num_bool_exprs++;
        if (is_app(e) && to_app(e)->get_num_args() == 0)
            m_num_bool_constants++;
    }
    if (is_quantifier(e)) {
        m_num_quantifiers++;
        unsigned num_patterns = to_quantifier(e)->get_num_patterns();
        if (num_patterns > 0) {
            m_num_quantifiers_with_patterns++;
            for (unsigned i = 0; i < num_patterns; i++) {
                expr * p = to_quantifier(e)->get_pattern(i);
                if (is_app(p) && to_app(p)->get_num_args() > 1) {
                    m_num_quantifiers_with_multi_patterns++;
                    break;
                }
            }
        }
    }
    bool _is_le_ge = m_autil.is_le(e) || m_autil.is_ge(e);
    if (_is_le_ge) {
        m_num_arith_ineqs++;
        TRACE(diff_atom, tout << "diff_atom: " << is_diff_atom(e) << "\n" << mk_pp(e, m) << "\n";);
        if (is_diff_atom(e))
            m_num_diff_ineqs++;
        if (!is_arith_expr(to_app(e)->get_arg(0)))
            m_num_simple_ineqs++;
        acc_num(to_app(e)->get_arg(1));
    }
    rational r;
    if (is_numeral(e, r)) {
        if (!r.is_int())
            m_has_rational = true;
    }
    if (_is_eq) {
        m_num_eqs++;
        if (is_numeral(to_app(e)->get_arg(1))) {
            acc_num(to_app(e)->get_arg(1));
            m_num_arith_eqs++;
            TRACE(diff_atom, tout << "diff_atom: " << is_diff_atom(e) << "\n" << mk_pp(e, m) << "\n";);
            if (is_diff_atom(e))
                m_num_diff_eqs++;
            if (!is_arith_expr(to_app(e)->get_arg(0)))
                m_num_simple_eqs++;
        }
        sort * s      = to_app(e)->get_arg(0)->get_sort();
        if (!m.is_uninterp(s)) {
            family_id fid = s->get_family_id();
            if (fid != null_family_id && fid != m_bfid)
                inc_theory_eqs(fid);
        }
    }
    if (!m_has_int && m_autil.is_int(e))
        m_has_int  = true;
    if (!m_has_real && m_autil.is_real(e))
        m_has_real = true;
    if (!m_has_bv && m_bvutil.is_bv(e))
        m_has_bv = true;
    if (!m_has_fpa && (m_fpautil.is_float(e) || m_fpautil.is_rm(e)))
        m_has_fpa = true;
    if (is_app(e) && to_app(e)->get_family_id() == m_srfid) 
        m_has_sr = true;
    if (!m_has_arrays && m_arrayutil.is_array(e)) 
        check_array(e->get_sort());
    if (!m_has_ext_arrays && m_arrayutil.is_array(e) && 
        !m_arrayutil.is_select(e) && !m_arrayutil.is_store(e)) 
        m_has_ext_arrays = true;
    if (!m_has_str && m_sequtil.str.is_string_term(e))
        m_has_str = true;
    if (!m_has_seq_non_str && m_sequtil.str.is_non_string_sequence(e)) 
        m_has_seq_non_str = true;
    if (is_app(e)) {
        family_id fid = to_app(e)->get_family_id();
        mark_theory(fid);
        if (fid != null_family_id && fid != m_bfid) {
            m_num_interpreted_exprs++;
            if (is_bool(e))
                inc_theory_atoms(fid);
            else
                inc_theory_terms(fid); 
            if (to_app(e)->get_num_args() == 0) 
                m_num_interpreted_constants++;
        }
        if (fid == m_afid) {
            switch (to_app(e)->get_decl_kind()) {
            case OP_MUL:
                if (!is_numeral(to_app(e)->get_arg(0)) || to_app(e)->get_num_args() > 2) {
                    m_num_non_linear++;
                }
                break;
            case OP_DIV:
            case OP_IDIV:
            case OP_REM:
            case OP_MOD:
                if (!is_numeral(to_app(e)->get_arg(1), r) || r.is_zero()) {
                    m_num_uninterpreted_functions++;
                    m_num_non_linear++;
                }
                break;
            }
        }
        if (fid == null_family_id) {
            m_num_uninterpreted_exprs++;
            if (to_app(e)->get_num_args() == 0) {
                m_num_uninterpreted_constants++;
                sort * s      = e->get_sort();
                if (!m.is_uninterp(s)) {
                    family_id fid = s->get_family_id();
                    if (fid != null_family_id && fid != m_bfid)
                        inc_theory_constants(fid);
                }
            }
        }
        if (m_arrayutil.is_array(e)) {
            TRACE(sf_array, tout << mk_ismt2_pp(e, m) << "\n";);
            sort * ty = to_app(e)->get_decl()->get_range();
            mark_theory(ty->get_family_id());
            unsigned n = ty->get_num_parameters();
            for (unsigned i = 0; i < n; i++) {
                sort * ds = to_sort(ty->get_parameter(i).get_ast());
                update_core(ds);
            }
        }
        func_decl * d = to_app(e)->get_decl();
        inc_num_apps(d);
        if (d->get_arity() > 0 && !is_marked_pre(d)) {
            mark_pre(d);
            if (fid == null_family_id)
                m_num_uninterpreted_functions++;
        }
        if (!_is_eq && !_is_gate) {
            for (expr * arg : *to_app(e)) {
                sort * arg_s = arg->get_sort(); 
                if (!m.is_uninterp(arg_s)) {
                    family_id fid_arg = arg_s->get_family_id();
                    if (fid_arg != fid && fid_arg != null_family_id) {
                        m_num_aliens++;
                        inc_num_aliens(fid_arg);
                        if (fid_arg == m_afid) {
                            SASSERT(!_is_le_ge);
                            m_num_arith_terms++;
                            rational k;
                            TRACE(diff_term, tout << "diff_term: " << is_diff_term(arg, k) << "\n" << mk_pp(arg, m) << "\n";);
                            if (is_diff_term(arg, k)) {
                                m_num_diff_terms++;
                                acc_num(k);
                            }
                        }
                    }
                }
            }
        }
    }
}

void static_features::check_array(sort* s) {
    if (m_arrayutil.is_array(s)) {
        m_has_arrays = true;
        update_core(get_array_range(s));
        for (unsigned i = get_array_arity(s); i-- > 0; )
            update_core(get_array_domain(s, i));
    }
}


void static_features::update_core(sort * s) {
    mark_theory(s->get_family_id());
    if (!m_has_int && m_autil.is_int(s))
        m_has_int = true;
    if (!m_has_real && m_autil.is_real(s))
        m_has_real = true;
    if (!m_has_bv && m_bvutil.is_bv_sort(s))
        m_has_bv = true;
    if (!m_has_fpa && (m_fpautil.is_float(s) || m_fpautil.is_rm(s)))
        m_has_fpa = true;
    check_array(s);
}

bool static_features::pre_process(expr * e, bool form_ctx, bool or_and_ctx, bool ite_ctx) {
    if (is_marked_post(e))
        return true;

    if (is_marked_pre(e))
        return true;

    if (is_var(e)) {
        mark_pre(e);
        mark_post(e);
        return true;
    }

    mark_pre(e);

    update_core(e);

    if (is_quantifier(e)) {
        expr * body = to_quantifier(e)->get_expr();
        if (is_marked_post(body)) 
            return true;                    
        add_process(body, false, false, false);
        return false;
    }

    auto [form_ctx_new, or_and_ctx_new, ite_ctx_new] = new_ctx(e);

    bool all_processed = true;
    for (expr* arg : *to_app(e)) {
        m.is_not(arg, arg);
        if (is_marked_post(arg))
            ++m_num_sharing;
        else {
            add_process(arg, form_ctx_new, or_and_ctx_new, ite_ctx_new);
            all_processed = false;
        }
    }    
    return all_processed;    
}

void static_features::post_process(expr * e, bool form_ctx, bool or_and_ctx, bool ite_ctx) {
    if (is_marked_post(e))
        return;

    mark_post(e);

    if (is_quantifier(e)) {
        expr * body = to_quantifier(e)->get_expr();
        set_depth(e, get_depth(body)+1);
        return;
    }

    unsigned depth = 0;
    unsigned ite_depth = 0;

    auto [form_ctx_new, or_and_ctx_new, ite_ctx_new] = new_ctx(e);

    for (expr* arg : *to_app(e)) {
        m.is_not(arg, arg);
        SASSERT(is_marked_post(arg));
        depth        = std::max(depth, get_depth(arg));
        if (ite_ctx_new)
            ite_depth    = std::max(ite_depth, get_ite_depth(arg));
    }

    depth++;
    set_depth(e, depth);
    if (depth > m_max_depth)
        m_max_depth = depth;
    
    if (ite_ctx_new) {
        ite_depth++;
        if (!ite_ctx) {
            m_num_ite_trees++;
            m_sum_ite_tree_depth += ite_depth;
            if (ite_depth >= m_max_ite_tree_depth)
                m_max_ite_tree_depth = ite_depth;
        }
        set_ite_depth(e, ite_depth);
    }

}

std::tuple<bool, bool, bool> static_features::new_ctx(expr* e) {
    bool form_ctx_new   = false;
    bool or_and_ctx_new = false;
    bool ite_ctx_new    = false;

    if (is_basic_expr(e)) {
        switch (to_app(e)->get_decl_kind()) {
        case OP_ITE:
            form_ctx_new = m.is_bool(e);
            ite_ctx_new  = true;
            break;
        case OP_AND: 
        case OP_OR: 
            form_ctx_new   = true;
            or_and_ctx_new = true;
            break;
        case OP_EQ:
            form_ctx_new   = true;
            break;
        }
    }

    return std::tuple(form_ctx_new, or_and_ctx_new, ite_ctx_new);
}

void static_features::process_all() {
    while (!m_to_process.empty()) {
        auto const& [e, form, or_and, ite] = m_to_process.back();
        if (is_marked_post(e)) {
            m_to_process.pop_back();
            ++m_num_sharing;
            continue;
        }
        if (!pre_process(e, form, or_and, ite))
            continue;
        post_process(e, form, or_and, ite);
        m_to_process.pop_back();
    }
}


void static_features::process_root(expr * e) {
    if (is_marked_post(e)) {
        m_num_sharing++;
        return;
    }
    m_num_roots++;
    if (m.is_or(e)) {
        mark_post(e);
        m_num_clauses++;
        m_num_bool_exprs++;
        unsigned num_args  = to_app(e)->get_num_args();
        m_sum_clause_size += num_args;
        if (num_args == 2)
            m_num_bin_clauses++;
        unsigned depth = 0;
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = to_app(e)->get_arg(i);
            if (m.is_not(arg))
                arg = to_app(arg)->get_arg(0);
            add_process(arg, true, true, false);
            process_all();
            depth        = std::max(depth, get_depth(arg));
        }
        depth++;
        set_depth(e, depth);
        if (depth > m_max_depth)
            m_max_depth = depth;
        return;
    }
    if (!is_gate(e)) {
        m_sum_clause_size++;
        m_num_units++;
        m_num_clauses++;
    }
    add_process(e, false, false, false);
    process_all();
}

void static_features::collect(unsigned num_formulas, expr * const * formulas) {
    for (unsigned i = 0; i < num_formulas; i++)
        process_root(formulas[i]);
}

bool static_features::internal_family(symbol const & f_name) const {
    return f_name == m_label_sym || f_name == m_pattern_sym || f_name == m_expr_list_sym;
}

void static_features::display_family_data(std::ostream & out, char const * prefix, unsigned_vector const & data) const {
    for (unsigned fid = 0; fid < data.size(); fid++) {
        symbol const & n = m.get_family_name(fid);
        if (!internal_family(n))
            out << prefix << "_" << n << " " << data[fid] << "\n";
    }
}

bool static_features::has_uf() const {
    return m_num_uninterpreted_functions > 0;
}

unsigned static_features::num_non_uf_theories() const {
    return m_num_theories;
}

unsigned static_features::num_theories() const {
    return (num_non_uf_theories() + (has_uf() ? 1 : 0));
}

void static_features::display_primitive(std::ostream & out) const {
    out << "BEGIN_PRIMITIVE_STATIC_FEATURES" << "\n";
    out << "CNF " << m_cnf << "\n";
    out << "NUM_EXPRS " << m_num_exprs << "\n";
    out << "NUM_ROOTS " << m_num_roots << "\n";
    out << "MAX_DEPTH " << m_max_depth << "\n";
    out << "NUM_QUANTIFIERS " << m_num_quantifiers << "\n";
    out << "NUM_QUANTIFIERS_WITH_PATTERNS " << m_num_quantifiers_with_patterns << "\n";
    out << "NUM_QUANTIFIERS_WITH_MULTI_PATTERNS " << m_num_quantifiers_with_multi_patterns << "\n";
    out << "NUM_CLAUSES " << m_num_clauses << "\n";
    out << "NUM_BIN_CLAUSES " << m_num_bin_clauses << "\n";
    out << "NUM_UNITS " << m_num_units << "\n";
    out << "SUM_CLAUSE_SIZE " << m_sum_clause_size << "\n";
    out << "NUM_NESTED_FORMULAS " << m_num_nested_formulas << "\n";
    out << "NUM_BOOL_EXPRS " << m_num_bool_exprs << "\n";
    out << "NUM_BOOL_CONSTANTS " << m_num_bool_constants << "\n";
    out << "NUM_ITE_TREES " << m_num_ite_trees << "\n";
    out << "MAX_ITE_TREE_DEPTH " << m_max_ite_tree_depth << "\n";
    out << "SUM_ITE_TREE_DEPTH " << m_sum_ite_tree_depth << "\n";
    out << "NUM_ORS " << m_num_ors << "\n";
    out << "NUM_ANDS " << m_num_ands << "\n";
    out << "NUM_IFFS " << m_num_iffs << "\n";
    out << "NUM_ITE_FORMULAS " << m_num_ite_formulas << "\n";
    out << "NUM_ITE_TERMS " << m_num_ite_terms << "\n";
    out << "NUM_SHARING " << m_num_sharing << "\n";
    out << "NUM_INTERPRETED_EXPRS " << m_num_interpreted_exprs << "\n";
    out << "NUM_UNINTERPRETED_EXPRS " << m_num_uninterpreted_exprs << "\n";
    out << "NUM_INTERPRETED_CONSTANTS " << m_num_interpreted_constants << "\n";
    out << "NUM_UNINTERPRETED_CONSTANTS " << m_num_uninterpreted_constants << "\n";
    out << "NUM_UNINTERPRETED_FUNCTIONS " << m_num_uninterpreted_functions << "\n";
    out << "NUM_EQS " << m_num_eqs << "\n";
    out << "HAS_RATIONAL " << m_has_rational << "\n";
    out << "HAS_INT " << m_has_int << "\n";
    out << "HAS_REAL " << m_has_real << "\n";
    out << "ARITH_K_SUM " << m_arith_k_sum << "\n";
    out << "NUM_ARITH_TERMS " << m_num_arith_terms << "\n";
    out << "NUM_ARITH_EQS " << m_num_arith_eqs << "\n";
    out << "NUM_ARITH_INEQS " << m_num_arith_ineqs << "\n";
    out << "NUM_DIFF_TERMS " << m_num_diff_terms << "\n";
    out << "NUM_DIFF_EQS " << m_num_diff_eqs << "\n";
    out << "NUM_DIFF_INEQS " << m_num_diff_ineqs << "\n";
    out << "NUM_SIMPLE_EQS " << m_num_simple_eqs << "\n";
    out << "NUM_SIMPLE_INEQS " << m_num_simple_ineqs << "\n";
    out << "NUM_NON_LINEAR " << m_num_non_linear << "\n";
    out << "NUM_ALIENS " << m_num_aliens << "\n";
    display_family_data(out, "NUM_TERMS", m_num_theory_terms);
    display_family_data(out, "NUM_ATOMS", m_num_theory_atoms);
    display_family_data(out, "NUM_CONSTANTS", m_num_theory_constants);
    display_family_data(out, "NUM_EQS", m_num_theory_eqs);
    display_family_data(out, "NUM_ALIENS", m_num_aliens_per_family);
    out << "NUM_THEORIES " << num_theories() << "\n";
    out << "END_PRIMITIVE_STATIC_FEATURES" << "\n";
}

void static_features::display(std::ostream & out) const {
    out << "BEGIN_STATIC_FEATURES" << "\n";
    out << "CNF " << m_cnf << "\n";
    out << "MAX_DEPTH " << m_max_depth << "\n";
    out << "MAX_ITE_TREE_DEPTH " << m_max_ite_tree_depth << "\n";
    out << "HAS_INT " << m_has_int << "\n";
    out << "HAS_REAL " << m_has_real << "\n";
    out << "HAS_QUANTIFIERS " << (m_num_quantifiers > 0) << "\n";
    out << "PERC_QUANTIFIERS_WITH_PATTERNS " << (m_num_quantifiers > 0 ? (double) m_num_quantifiers_with_patterns / (double) m_num_quantifiers : 0) << "\n";
    out << "PERC_QUANTIFIERS_WITH_MULTI_PATTERNS " << (m_num_quantifiers > 0 ? (double) m_num_quantifiers_with_multi_patterns / (double) m_num_quantifiers : 0) << "\n";
    out << "IS_NON_LINEAR " << (m_num_non_linear > 0) << "\n";
    out << "THEORY_COMBINATION " << (num_theories() > 1) << "\n";
    out << "AVG_CLAUSE_SIZE " << (m_num_clauses > 0 ? (double) m_sum_clause_size / (double) m_num_clauses : 0) << "\n";
    out << "PERC_BOOL_CONSTANTS " << (m_num_uninterpreted_constants > 0 ? (double) m_num_bool_constants / (double) m_num_uninterpreted_constants : 0) << "\n";
    out << "PERC_NESTED_FORMULAS " << (m_num_bool_exprs > 0 ? (double) m_num_nested_formulas / (double) m_num_bool_exprs : 0) << "\n";
    out << "IS_DIFF " << (m_num_arith_eqs == m_num_diff_eqs && m_num_arith_ineqs == m_num_diff_ineqs && m_num_arith_terms == m_num_diff_terms) << "\n";
    out << "INEQ_EQ_RATIO " << (m_num_arith_eqs > 0 ? (double) m_num_arith_ineqs / (double) m_num_arith_eqs : 0) << "\n";
    out << "PERC_ARITH_EQS " << (m_num_eqs > 0 ? (double) m_num_arith_eqs / (double) m_num_eqs : 0) << "\n";
    out << "PERC_DIFF_EQS " << (m_num_arith_eqs > 0 ? (double) m_num_diff_eqs / (double) m_num_arith_eqs : 0) << "\n";
    out << "PERC_DIFF_INEQS " << (m_num_arith_ineqs > 0 ? (double) m_num_diff_ineqs / (double) m_num_arith_ineqs : 0) << "\n";
    out << "PERC_SIMPLE_EQS " << (m_num_arith_eqs > 0 ? (double) m_num_simple_eqs / (double) m_num_arith_eqs : 0) << "\n";
    out << "PERC_SIMPLE_INEQS " << (m_num_arith_ineqs > 0 ? (double) m_num_simple_ineqs / (double) m_num_arith_ineqs : 0) << "\n";
    out << "PERC_ALIENS " << (m_num_exprs > 0 ? (double) m_num_aliens / (double) m_num_exprs : 0) << "\n";
    out << "END_STATIC_FEATURES" << "\n";
}

void static_features::get_feature_vector(vector<double> & result) {
}

bool static_features::is_dense() const {
    return 
        (m_num_uninterpreted_constants < 1000) &&
        (m_num_arith_eqs + m_num_arith_ineqs) > m_num_uninterpreted_constants * 9;
}
