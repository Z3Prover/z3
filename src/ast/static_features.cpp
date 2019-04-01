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

static_features::static_features(ast_manager & m):
    m_manager(m),
    m_autil(m),
    m_bvutil(m),
    m_arrayutil(m),
    m_fpautil(m),
    m_sequtil(m),
    m_bfid(m.get_basic_family_id()),
    m_afid(m.mk_family_id("arith")),
    m_lfid(m.mk_family_id("label")),
    m_arrfid(m.mk_family_id("array")),
    m_srfid(m.mk_family_id("special_relations")),
    m_label_sym("label"),
    m_pattern_sym("pattern"),
    m_expr_list_sym("expr-list") {
    reset();
}

void static_features::reset() {
    m_already_visited                      .reset();
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
    m_num_formula_trees                    = 0;
    m_max_formula_depth                    = 0;
    m_sum_formula_depth                    = 0;
    m_num_or_and_trees                     = 0;
    m_max_or_and_tree_depth                = 0;
    m_sum_or_and_tree_depth                = 0;
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
    m_max_stack_depth                      = 500;
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
    return m_autil.is_add(e) && to_app(e)->get_num_args() == 2 && is_numeral(to_app(e)->get_arg(0), r) && !is_arith_expr(to_app(e)->get_arg(1));
}

bool static_features::is_diff_atom(expr const * e) const {
    if (!is_bool(e))
        return false;
    if (!m_manager.is_eq(e) && !is_arith_expr(e))
        return false;
    SASSERT(to_app(e)->get_num_args() == 2);
    expr * lhs = to_app(e)->get_arg(0);
    expr * rhs = to_app(e)->get_arg(1);
    if (!is_arith_expr(lhs) && !is_arith_expr(rhs)) 
        return true;    
    if (!is_numeral(rhs)) 
        return false;    
    // lhs can be 'x' or '(+ x (* -1 y))' or '(+ (* -1 x) y)'
    if (!is_arith_expr(lhs))
        return true;
    expr* arg1, *arg2;
    if (!m_autil.is_add(lhs, arg1, arg2)) 
        return false;    
    expr* m1, *m2;
    if (!is_arith_expr(arg1) && m_autil.is_mul(arg2, m1, m2) &&  is_minus_one(m1) && !is_arith_expr(m2))
        return true;
    if (!is_arith_expr(arg2) && m_autil.is_mul(arg1, m1, m2) &&  is_minus_one(m1) && !is_arith_expr(m2))
        return true;
    return false;
    
}

bool static_features::is_gate(expr const * e) const {
    if (is_basic_expr(e)) {
        switch (to_app(e)->get_decl_kind()) {
        case OP_ITE: case OP_AND: case OP_OR: case OP_XOR: case OP_IMPLIES:
            return true;
        case OP_EQ:
            return m_manager.is_bool(e);
        }
    }
    return false;
}

void static_features::update_core(expr * e) {
    m_num_exprs++;
    
    // even if a benchmark does not contain any theory interpreted function decls, we still have to install
    // the theory if the benchmark contains constants or function applications of an interpreted sort.
    sort * s      = m_manager.get_sort(e);
    if (!m_manager.is_uninterp(s))
        mark_theory(s->get_family_id());
    
    bool _is_gate = is_gate(e);
    bool _is_eq   = m_manager.is_eq(e);
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
                    sort * arg_s = m_manager.get_sort(arg); 
                    family_id fid_arg = arg_s->get_family_id();
                    if (fid_arg == m_afid) {
                        m_num_arith_terms++;
                        rational k;
                        TRACE("diff_term", tout << "diff_term: " << is_diff_term(arg, k) << "\n" << mk_pp(arg, m_manager) << "\n";);
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
        TRACE("diff_atom", tout << "diff_atom: " << is_diff_atom(e) << "\n" << mk_pp(e, m_manager) << "\n";);
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
            TRACE("diff_atom", tout << "diff_atom: " << is_diff_atom(e) << "\n" << mk_pp(e, m_manager) << "\n";);
            if (is_diff_atom(e))
                m_num_diff_eqs++;
            if (!is_arith_expr(to_app(e)->get_arg(0)))
                m_num_simple_eqs++;
        }
        sort * s      = m_manager.get_sort(to_app(e)->get_arg(0));
        if (!m_manager.is_uninterp(s)) {
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
        m_has_arrays = true;
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
            // std::cout << mk_pp(e, m_manager) << "\n";
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
                if (!is_numeral(to_app(e)->get_arg(1)))
                    m_num_non_linear++;
                break;
            }
        }
        if (fid == null_family_id) {
            m_num_uninterpreted_exprs++;
            if (to_app(e)->get_num_args() == 0) {
                m_num_uninterpreted_constants++;
                sort * s      = m_manager.get_sort(e);
                if (!m_manager.is_uninterp(s)) {
                    family_id fid = s->get_family_id();
                    if (fid != null_family_id && fid != m_bfid)
                        inc_theory_constants(fid);
                }
            }
        }
        if (m_arrayutil.is_array(e)) {
            TRACE("sf_array", tout << mk_ismt2_pp(e, m_manager) << "\n";);
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
        if (d->get_arity() > 0 && !is_marked(d)) {
            mark(d);
            if (fid == null_family_id)
                m_num_uninterpreted_functions++;
        }
        if (!_is_eq && !_is_gate) {
            unsigned num_args = to_app(e)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg   = to_app(e)->get_arg(i);
                sort * arg_s = m_manager.get_sort(arg); 
                if (!m_manager.is_uninterp(arg_s)) {
                    family_id fid_arg = arg_s->get_family_id();
                    if (fid_arg != fid && fid_arg != null_family_id) {
                        m_num_aliens++;
                        inc_num_aliens(fid_arg);
                        if (fid_arg == m_afid) {
                            SASSERT(!_is_le_ge);
                            m_num_arith_terms++;
                            rational k;
                            TRACE("diff_term", tout << "diff_term: " << is_diff_term(arg, k) << "\n" << mk_pp(arg, m_manager) << "\n";);
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
    if (!m_has_arrays && m_arrayutil.is_array(s))
        m_has_arrays = true;
}

void static_features::process(expr * e, bool form_ctx, bool or_and_ctx, bool ite_ctx, unsigned stack_depth) {
    TRACE("static_features", tout << "processing\n" << mk_pp(e, m_manager) << "\n";);
    if (is_var(e))
        return;
    if (is_marked(e)) {
        m_num_sharing++;
        return;
    }    
    if (stack_depth > m_max_stack_depth) {
        return;
    }
    mark(e);
    update_core(e);


    if (is_quantifier(e)) {
        expr * body = to_quantifier(e)->get_expr();
        process(body, false, false, false, stack_depth+1);
        set_depth(e, get_depth(body)+1);
        return;
    }
    
    bool form_ctx_new   = false;
    bool or_and_ctx_new = false;
    bool ite_ctx_new    = false;

    if (is_basic_expr(e)) {
        switch (to_app(e)->get_decl_kind()) {
        case OP_ITE:
            form_ctx_new = m_manager.is_bool(e);
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
    
    unsigned depth = 0;
    unsigned form_depth = 0;
    unsigned or_and_depth = 0;
    unsigned ite_depth = 0;

    unsigned num_args = to_app(e)->get_num_args();
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = to_app(e)->get_arg(i);
        if (m_manager.is_not(arg))
            arg = to_app(arg)->get_arg(0);
        process(arg, form_ctx_new, or_and_ctx_new, ite_ctx_new, stack_depth+1);
        depth        = std::max(depth, get_depth(arg));
        if (form_ctx_new)
            form_depth   = std::max(form_depth, get_form_depth(arg));
        if (or_and_ctx_new)
            or_and_depth = std::max(or_and_depth, get_or_and_depth(arg));
        if (ite_ctx_new)
            ite_depth    = std::max(ite_depth, get_ite_depth(arg));
    }

    depth++;
    set_depth(e, depth);
    if (depth > m_max_depth)
        m_max_depth = depth;

    if (form_ctx_new) {
        form_depth++;
        if (!form_ctx) {
            m_num_formula_trees++;
            m_sum_formula_depth += form_depth;
            if (form_depth > m_max_formula_depth)
                m_max_formula_depth = form_depth;
        }
        set_form_depth(e, form_depth);
    }
    if (or_and_ctx_new) {
        or_and_depth++;
        if (!or_and_ctx) {
            m_num_or_and_trees++;
            m_sum_or_and_tree_depth += or_and_depth;
            if (or_and_depth > m_max_or_and_tree_depth)
                m_max_or_and_tree_depth = or_and_depth;
        }
        set_or_and_depth(e, or_and_depth);
    }
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

void static_features::process_root(expr * e) {
    if (is_marked(e)) {
        m_num_sharing++;
        return;
    }
    m_num_roots++;
    if (m_manager.is_or(e)) {
        mark(e);
        m_num_clauses++;
        m_num_bool_exprs++;
        unsigned num_args  = to_app(e)->get_num_args();
        m_sum_clause_size += num_args;
        if (num_args == 2)
            m_num_bin_clauses++;
        unsigned depth = 0;
        unsigned form_depth = 0;
        unsigned or_and_depth = 0;
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = to_app(e)->get_arg(i);
            if (m_manager.is_not(arg))
                arg = to_app(arg)->get_arg(0);
            process(arg, true, true, false, 0);
            depth        = std::max(depth, get_depth(arg));
            form_depth   = std::max(form_depth, get_form_depth(arg));
            or_and_depth = std::max(or_and_depth, get_or_and_depth(arg));
        }
        depth++;
        set_depth(e, depth);
        if (depth > m_max_depth)
            m_max_depth = depth;
        form_depth++;
        m_num_formula_trees++;
        m_sum_formula_depth += form_depth;
        if (form_depth > m_max_formula_depth)
            m_max_formula_depth = form_depth;
        set_form_depth(e, form_depth);
        or_and_depth++;
        m_num_or_and_trees++;
        m_sum_or_and_tree_depth += or_and_depth;
        if (or_and_depth > m_max_or_and_tree_depth)
            m_max_or_and_tree_depth = or_and_depth;
        set_or_and_depth(e, or_and_depth);
        return;
    }
    if (!is_gate(e)) {
        m_sum_clause_size++;
        m_num_units++;
        m_num_clauses++;
    }
    process(e, false, false, false, 0);
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
        symbol const & n = m_manager.get_family_name(fid);
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
    out << "NUM_FORMULA_TREES " << m_num_formula_trees << "\n"; 
    out << "MAX_FORMULA_DEPTH " << m_max_formula_depth << "\n";
    out << "SUM_FORMULA_DEPTH " << m_sum_formula_depth << "\n";
    out << "NUM_OR_AND_TREES " << m_num_or_and_trees << "\n";
    out << "MAX_OR_AND_TREE_DEPTH " << m_max_or_and_tree_depth << "\n";
    out << "SUM_OR_AND_TREE_DEPTH " << m_sum_or_and_tree_depth << "\n";
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
    out << "MAX_OR_AND_TREE_DEPTH " << m_max_or_and_tree_depth << "\n";
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
