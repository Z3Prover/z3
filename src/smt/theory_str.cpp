/*++
  Module Name:

  theory_str.cpp

  Abstract:

  String Theory Plugin

  Author:

  Murphy Berzish and Yunhui Zheng

  Revision History:

  --*/
#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_str.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include<list>
#include<algorithm>
#include "smt/theory_seq_empty.h"
#include "smt/theory_arith.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/rewriter/var_subst.h"
#include "smt_kernel.h"
#include "model/model_smt2_pp.h"

namespace smt {


    class seq_expr_solver : public expr_solver {
        kernel m_kernel;
    public:
        seq_expr_solver(ast_manager& m, smt_params& fp):
            m_kernel(m, fp) {}
        lbool check_sat(expr* e) override {
            m_kernel.push();
            m_kernel.assert_expr(e);
            lbool r = m_kernel.check();
            m_kernel.pop(1);
            return r;
        }
    };

    theory_str::theory_str(context& ctx, ast_manager & m, theory_str_params const & params):
        theory(ctx, m.mk_family_id("seq")),
        m_params(params),
        /* Options */
        opt_EagerStringConstantLengthAssertions(true),
        opt_VerifyFinalCheckProgress(false),
        opt_LCMUnrollStep(2),
        opt_NoQuickReturn_IntegerTheory(false),
        opt_DisableIntegerTheoryIntegration(false),
        opt_DeferEQCConsistencyCheck(false),
        opt_CheckVariableScope(true),
        opt_ConcatOverlapAvoid(true),
        /* Internal setup */
        search_started(false),
        m_autil(m),
        u(m),
        sLevel(0),
        finalCheckProgressIndicator(false),
        m_trail(m),
        m_factory(nullptr),
        m_mk_aut(m),
        m_unused_id(0),
        m_delayed_axiom_setup_terms(m),
        m_delayed_assertions_todo(m),
        m_persisted_axioms(m),
        m_persisted_axiom_todo(m),
        tmpStringVarCount(0),
        tmpXorVarCount(0),
        avoidLoopCut(true),
        loopDetected(false),
        m_theoryStrOverlapAssumption_term(m.mk_true(), m),
        contains_map(m),
        string_int_conversion_terms(m),
        totalCacheAccessCount(0),
        cacheHitCount(0),
        cacheMissCount(0),
        m_fresh_id(0),
        m_trail_stack(),
        m_library_aware_trail_stack(),
        m_find(*this),
        fixed_length_subterm_trail(m),
        fixed_length_assumptions(m)
    {
    }

    theory_str::~theory_str() {
        m_trail_stack.reset();
        for (eautomaton * aut : regex_automata) {
            dealloc(aut);
        }
        regex_automata.clear();
        for (auto& kv: var_to_char_subterm_map) dealloc(kv.m_value);
        for (auto& kv: uninterpreted_to_char_subterm_map) dealloc(kv.m_value);
    }

    void theory_str::init() {
        m_mk_aut.set_solver(alloc(seq_expr_solver, get_manager(), ctx.get_fparams()));
    }

    void theory_str::reset_internal_data_structures() {
        //m_trail.reset();
        m_delayed_axiom_setup_terms.reset();
        m_basicstr_axiom_todo.reset();
        m_concat_axiom_todo.reset();
        m_string_constant_length_todo.reset();
        m_concat_eval_todo.reset();
        m_delayed_assertions_todo.reset();
        m_library_aware_axiom_todo.reset();
        m_persisted_axioms.reset();
        m_persisted_axiom_todo.reset();
        axiomatized_terms.reset();
        existing_toplevel_exprs.reset();

        varForBreakConcat.clear();
        loopDetected = false;
        cut_var_map.reset();
        m_cut_allocs.reset();

        //variable_set.reset();
        //internal_variable_set.reset();
        //internal_variable_scope_levels.clear();

        contains_map.reset();
        contain_pair_bool_map.reset();
        contain_pair_idx_map.reset();

        m_automata.reset();
        regex_automata.reset();
        regex_terms.reset();
        regex_terms_by_string.reset();
        regex_automaton_assumptions.reset();
        regex_terms_with_path_constraints.reset();
        regex_terms_with_length_constraints.reset();
        regex_term_to_length_constraint.reset();
        regex_term_to_extra_length_vars.reset();
        regex_last_lower_bound.reset();
        regex_last_upper_bound.reset();
        regex_length_attempt_count.reset();
        regex_fail_count.reset();
        regex_intersection_fail_count.reset();

        string_chars.reset();

        concat_astNode_map.reset();
        string_int_conversion_terms.reset();
        string_int_axioms.reset();
        stringConstantCache.reset();

        length_ast_map.reset();
        //m_trail_stack.reset();
        // m_find.reset();

        fixed_length_subterm_trail.reset();
        fixed_length_assumptions.reset();
        fixed_length_used_len_terms.reset();

        for (auto& kv: var_to_char_subterm_map) dealloc(kv.m_value);
        var_to_char_subterm_map.reset();
        for (auto& kv: uninterpreted_to_char_subterm_map) dealloc(kv.m_value);
        uninterpreted_to_char_subterm_map.reset();
        fixed_length_lesson.reset();
        candidate_model.reset();
    }

    expr * theory_str::mk_string(zstring const& str) {
        if (m_params.m_StringConstantCache) {
            ++totalCacheAccessCount;
            expr * val;
            if (stringConstantCache.find(str, val)) {
                return val;
            } else {
                val = u.str.mk_string(str);
                m_trail.push_back(val);
                stringConstantCache.insert(str, val);
                return val;
            }
        } else {
            return u.str.mk_string(str);
        }
    }

    expr * theory_str::mk_string(const char * str) {
        return u.str.mk_string(str);
    }

    void theory_str::collect_statistics(::statistics & st) const {
        st.update("str refine equation", m_stats.m_refine_eq);
        st.update("str refine negated equation", m_stats.m_refine_neq);
        st.update("str refine function", m_stats.m_refine_f);
        st.update("str refine negated function", m_stats.m_refine_nf);
    }

    void theory_str::assert_axiom(expr * _e) {
        if (_e == nullptr) 
            return;
        if (opt_VerifyFinalCheckProgress) {
            finalCheckProgressIndicator = true;
        }
        ast_manager& m = get_manager();
        SASSERT(!m.is_true(_e));

        if (m.is_true(_e)) return;
        TRACE("str", tout << "asserting " << mk_ismt2_pp(_e, m) << std::endl;);
        expr_ref e(_e, m);
        if (!ctx.b_internalized(e)) {
            ctx.internalize(e, false);
        }
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        if (m.has_trace_stream()) log_axiom_instantiation(e);
        ctx.mk_th_axiom(get_id(), 1, &lit);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";

        // crash/error avoidance: add all axioms to the trail
        m_trail.push_back(e);

        //TRACE("str", tout << "done asserting " << mk_ismt2_pp(e, get_manager()) << std::endl;);
    }

    void theory_str::assert_axiom_rw(expr * e) {
        if (e == nullptr)
            return;
        ast_manager & m = get_manager();
        expr_ref _e(e, m);
        ctx.get_rewriter()(_e);
        if (m.is_true(_e)) return;
        assert_axiom(_e);
    }

    expr * theory_str::rewrite_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        return m.mk_or(mk_not(m, premise), conclusion);
    }

    void theory_str::assert_implication(expr * premise, expr * conclusion) {
        ast_manager & m = get_manager();
        TRACE("str", tout << "asserting implication " << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
        expr_ref axiom(m.mk_or(mk_not(m, premise), conclusion), m);
        assert_axiom(axiom);
    }

    bool theory_str::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    bool theory_str::internalize_term(app * term) {
        ast_manager & m = get_manager();
        SASSERT(term->get_family_id() == get_family_id());

        TRACE("str", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << std::endl;);

        // emulation of user_smt_theory::internalize_term()

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; ++i) {
            ctx.internalize(term->get_arg(i), false);
        }
        if (ctx.e_internalized(term)) {
            enode * e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        // m_parents.push_back(term);
        enode * e = ctx.mk_enode(term, false, m.is_bool(term), true);
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.set_enode_flag(bv, true);
        }
        // make sure every argument is attached to a theory variable
        for (unsigned i = 0; i < num_args; ++i) {
            enode * arg = e->get_arg(i);
            theory_var v_arg = mk_var(arg);
            TRACE("str", tout << "arg has theory var #" << v_arg << std::endl;); (void)v_arg;
        }

        theory_var v = mk_var(e);
        TRACE("str", tout << "term has theory var #" << v << std::endl;); (void)v;

        if (opt_EagerStringConstantLengthAssertions && u.str.is_string(term)) {
            TRACE("str", tout << "eagerly asserting length of string term " << mk_pp(term, m) << std::endl;);
            m_basicstr_axiom_todo.insert(e);
        }
        return true;
    }

    enode* theory_str::ensure_enode(expr* e) {
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    void theory_str::refresh_theory_var(expr * e) {
        enode * en = ensure_enode(e);
        theory_var v = mk_var(en); (void)v;
        TRACE("str", tout << "refresh " << mk_pp(e, get_manager()) << ": v#" << v << std::endl;);
        if (e->get_sort() == u.str.mk_string_sort()) {
            m_basicstr_axiom_todo.push_back(en);
        }
    }

    theory_var theory_str::mk_var(enode* n) {
        TRACE("str", tout << "mk_var for " << mk_pp(n->get_expr(), get_manager()) << std::endl;);
        if (!(n->get_expr()->get_sort() == u.str.mk_string_sort())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            TRACE("str", tout << "already attached to theory var" << std::endl;);
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            m_find.mk_var();
            TRACE("str", tout << "new theory var v#" << v << " find " << m_find.find(v) << std::endl;);
            ctx.attach_th_var(n, this, v);
            ctx.mark_as_relevant(n);
            return v;
        }
    }

    static void cut_vars_map_copy(obj_map<expr, int> & dest, obj_map<expr, int> & src) {
        for (auto const& kv : src) {
            dest.insert(kv.m_key, 1);
        }
    }

    bool theory_str::has_self_cut(expr * n1, expr * n2) {
        if (!cut_var_map.contains(n1)) {
            return false;
        }
        if (!cut_var_map.contains(n2)) {
            return false;
        }
        if (cut_var_map[n1].empty() || cut_var_map[n2].empty()) {
            return false;
        }

        for (auto const& kv : cut_var_map[n1].top()->vars) {
            if (cut_var_map[n2].top()->vars.contains(kv.m_key)) {
                return true;
            }
        }
        return false;
    }

    void theory_str::add_cut_info_one_node(expr * baseNode, int slevel, expr * node) {
        // crash avoidance?
        m_trail.push_back(baseNode);
        m_trail.push_back(node);
        if (!cut_var_map.contains(baseNode)) {
            T_cut * varInfo = alloc(T_cut);
            m_cut_allocs.push_back(varInfo);
            varInfo->level = slevel;
            varInfo->vars.insert(node, 1);
            cut_var_map.insert(baseNode, std::stack<T_cut*>());
            cut_var_map[baseNode].push(varInfo);
            TRACE("str", tout << "add var info for baseNode=" << mk_pp(baseNode, get_manager()) << ", node=" << mk_pp(node, get_manager()) << " [" << slevel << "]" << std::endl;);
        } else {
            if (cut_var_map[baseNode].empty()) {
                T_cut * varInfo = alloc(T_cut);
                m_cut_allocs.push_back(varInfo);
                varInfo->level = slevel;
                varInfo->vars.insert(node, 1);
                cut_var_map[baseNode].push(varInfo);
                TRACE("str", tout << "add var info for baseNode=" << mk_pp(baseNode, get_manager()) << ", node=" << mk_pp(node, get_manager()) << " [" << slevel << "]" << std::endl;);
            } else {
                if (cut_var_map[baseNode].top()->level < slevel) {
                    T_cut * varInfo = alloc(T_cut);
                    m_cut_allocs.push_back(varInfo);
                    varInfo->level = slevel;
                    cut_vars_map_copy(varInfo->vars, cut_var_map[baseNode].top()->vars);
                    varInfo->vars.insert(node, 1);
                    cut_var_map[baseNode].push(varInfo);
                    TRACE("str", tout << "add var info for baseNode=" << mk_pp(baseNode, get_manager()) << ", node=" << mk_pp(node, get_manager()) << " [" << slevel << "]" << std::endl;);
                } else if (cut_var_map[baseNode].top()->level == slevel) {
                    cut_var_map[baseNode].top()->vars.insert(node, 1);
                    TRACE("str", tout << "add var info for baseNode=" << mk_pp(baseNode, get_manager()) << ", node=" << mk_pp(node, get_manager()) << " [" << slevel << "]" << std::endl;);
                } else {
                    get_manager().raise_exception("entered illegal state during add_cut_info_one_node()");
                }
            }
        }
    }

    void theory_str::add_cut_info_merge(expr * destNode, int slevel, expr * srcNode) {
        // crash avoidance?
        m_trail.push_back(destNode);
        m_trail.push_back(srcNode);
        if (!cut_var_map.contains(srcNode)) {
            get_manager().raise_exception("illegal state in add_cut_info_merge(): cut_var_map doesn't contain srcNode");
        }

        if (cut_var_map[srcNode].empty()) {
            get_manager().raise_exception("illegal state in add_cut_info_merge(): cut_var_map[srcNode] is empty");
        }

        if (!cut_var_map.contains(destNode)) {
            T_cut * varInfo = alloc(T_cut);
            m_cut_allocs.push_back(varInfo);
            varInfo->level = slevel;
            cut_vars_map_copy(varInfo->vars, cut_var_map[srcNode].top()->vars);
            cut_var_map.insert(destNode, std::stack<T_cut*>());
            cut_var_map[destNode].push(varInfo);
            TRACE("str", tout << "merge var info for destNode=" << mk_pp(destNode, get_manager()) << ", srcNode=" << mk_pp(srcNode, get_manager()) << " [" << slevel << "]" << std::endl;);
        } else {
            if (cut_var_map[destNode].empty() || cut_var_map[destNode].top()->level < slevel) {
                T_cut * varInfo = alloc(T_cut);
                m_cut_allocs.push_back(varInfo);
                varInfo->level = slevel;
                cut_vars_map_copy(varInfo->vars, cut_var_map[destNode].top()->vars);
                cut_vars_map_copy(varInfo->vars, cut_var_map[srcNode].top()->vars);
                cut_var_map[destNode].push(varInfo);
                TRACE("str", tout << "merge var info for destNode=" << mk_pp(destNode, get_manager()) << ", srcNode=" << mk_pp(srcNode, get_manager()) << " [" << slevel << "]" << std::endl;);
            } else if (cut_var_map[destNode].top()->level == slevel) {
                cut_vars_map_copy(cut_var_map[destNode].top()->vars, cut_var_map[srcNode].top()->vars);
                TRACE("str", tout << "merge var info for destNode=" << mk_pp(destNode, get_manager()) << ", srcNode=" << mk_pp(srcNode, get_manager()) << " [" << slevel << "]" << std::endl;);
            } else {
                get_manager().raise_exception("illegal state in add_cut_info_merge(): inconsistent slevels");
            }
        }
    }

    void theory_str::check_and_init_cut_var(expr * node) {
        if (cut_var_map.contains(node)) {
            return;
        } else if (!u.str.is_string(node)) {
            add_cut_info_one_node(node, -1, node);
        }
    }

    literal theory_str::mk_literal(expr* _e) {
        ast_manager & m = get_manager();
        expr_ref e(_e, m);
        ensure_enode(e);
        return ctx.get_literal(e);
    }

    app * theory_str::mk_int(int n) {
        return m_autil.mk_numeral(rational(n), true);
    }

    app * theory_str::mk_int(rational & q) {
        return m_autil.mk_numeral(q, true);
    }

    void theory_str::track_variable_scope(expr * var) {
        if (internal_variable_scope_levels.find(sLevel) == internal_variable_scope_levels.end()) {
            internal_variable_scope_levels[sLevel] = obj_hashtable<expr>();
        }
        internal_variable_scope_levels[sLevel].insert(var);
    }

    app * theory_str::mk_internal_xor_var() {
        return mk_int_var("$$_xor");
    }

    app * theory_str::mk_fresh_const(char const* name, sort* s) {
        string_buffer<64> buffer;
        buffer << name;
        buffer << "!tmp";
        buffer << m_fresh_id;
        m_fresh_id++;
        return u.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }


    app * theory_str::mk_int_var(std::string name) {
        ast_manager & m = get_manager();

        TRACE("str", tout << "creating integer variable " << name << " at scope level " << sLevel << std::endl;);

        sort * int_sort = m.mk_sort(m_autil.get_family_id(), INT_SORT);
        app * a = mk_fresh_const(name.c_str(), int_sort);

        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != nullptr);
        SASSERT(ctx.e_internalized(a));
        ctx.mark_as_relevant(a);
        // I'm assuming that this combination will do the correct thing in the integer theory.

        //mk_var(ctx.get_enode(a));
        m_trail.push_back(a);
        //variable_set.insert(a);
        //internal_variable_set.insert(a);
        //track_variable_scope(a);

        return a;
    }

    app * theory_str::mk_str_var(std::string name) {

        TRACE("str", tout << "creating string variable " << name << " at scope level " << sLevel << std::endl;);

        sort * string_sort = u.str.mk_string_sort();
        app * a = mk_fresh_const(name.c_str(), string_sort);
        m_trail.push_back(a);

        TRACE("str", tout << "a->get_family_id() = " << a->get_family_id() << std::endl
              << "this->get_family_id() = " << this->get_family_id() << std::endl;);

        // I have a hunch that this may not get internalized for free...
        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != nullptr);
        SASSERT(ctx.e_internalized(a));
        // this might help??
        mk_var(ctx.get_enode(a));
        m_basicstr_axiom_todo.push_back(ctx.get_enode(a));
        TRACE("str", tout << "add " << mk_pp(a, get_manager()) << " to m_basicstr_axiom_todo" << std::endl;);

        variable_set.insert(a);
        internal_variable_set.insert(a);
        track_variable_scope(a);

        return a;
    }

    void theory_str::add_nonempty_constraint(expr * s) {
        ast_manager & m = get_manager();

        expr_ref ax1(mk_not(m, ctx.mk_eq_atom(s, mk_string(""))), m);
        assert_axiom(ax1);

        {
            // build LHS
            expr_ref len_str(mk_strlen(s), m);
            SASSERT(len_str);
            // build RHS
            expr_ref zero(m_autil.mk_numeral(rational(0), true), m);
            SASSERT(zero);
            // build LHS > RHS and assert
            // we have to build !(LHS <= RHS) instead
            expr_ref lhs_gt_rhs(mk_not(m, m_autil.mk_le(len_str, zero)), m);
            SASSERT(lhs_gt_rhs);
            assert_axiom(lhs_gt_rhs);
        }
    }

    app_ref theory_str::mk_nonempty_str_var() {
        ast_manager & m = get_manager();

        std::stringstream ss;
        ss << tmpStringVarCount;
        tmpStringVarCount++;
        std::string name = "$$_str" + ss.str();

        TRACE("str", tout << "creating nonempty string variable " << name << " at scope level " << sLevel << std::endl;);

        sort * string_sort = u.str.mk_string_sort();
        app_ref a(mk_fresh_const(name.c_str(), string_sort), m);

        ctx.internalize(a, false);
        SASSERT(ctx.get_enode(a) != nullptr);
        // this might help??
        mk_var(ctx.get_enode(a));

        // assert a variation of the basic string axioms that ensures this string is nonempty
        {
            // build LHS
            expr_ref len_str(mk_strlen(a), m);
            SASSERT(len_str);
            // build RHS
            expr_ref zero(m_autil.mk_numeral(rational(0), true), m);
            SASSERT(zero);
            // build LHS > RHS and assert
            // we have to build !(LHS <= RHS) instead
            expr_ref lhs_gt_rhs(mk_not(m, m_autil.mk_le(len_str, zero)), m);
            SASSERT(lhs_gt_rhs);
            assert_axiom(lhs_gt_rhs);
        }

        // add 'a' to variable sets, so we can keep track of it
        m_trail.push_back(a);
        variable_set.insert(a);
        internal_variable_set.insert(a);
        track_variable_scope(a);

        return a;
    }

    app * theory_str::mk_contains(expr * haystack, expr * needle) {
        app * contains = u.str.mk_contains(haystack, needle); // TODO double-check semantics/argument order
        m_trail.push_back(contains);
        // immediately force internalization so that axiom setup does not fail
        ctx.internalize(contains, false);
        set_up_axioms(contains);
        return contains;
    }

    // note, this invokes "special-case" handling for the start index being 0
    app * theory_str::mk_indexof(expr * haystack, expr * needle) {
        app * indexof = u.str.mk_index(haystack, needle, mk_int(0));
        m_trail.push_back(indexof);
        // immediately force internalization so that axiom setup does not fail
        ctx.internalize(indexof, false);
        set_up_axioms(indexof);
        return indexof;
    }

    app * theory_str::mk_strlen(expr * e) {
        /*if (m_strutil.is_string(e)) {*/ if (false) {
            zstring strval;
            u.str.is_string(e, strval);
            unsigned int len = strval.length();
            return m_autil.mk_numeral(rational(len), true);
        } else {
            if (false) {
                // use cache
                app * lenTerm = nullptr;
                if (!length_ast_map.find(e, lenTerm)) {
                    lenTerm = u.str.mk_length(e);
                    length_ast_map.insert(e, lenTerm);
                    m_trail.push_back(lenTerm);
                }
                return lenTerm;
            } else {
                // always regen
                return u.str.mk_length(e);
            }
        }
    }

    /*
     * Returns the simplified concatenation of two expressions,
     * where either both expressions are constant strings
     * or one expression is the empty string.
     * If this precondition does not hold, the function returns nullptr.
     * (note: this function was strTheory::Concat())
     */
    expr * theory_str::mk_concat_const_str(expr * n1, expr * n2) {
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        expr * v1 = get_eqc_value(n1, n1HasEqcValue);
        expr * v2 = get_eqc_value(n2, n2HasEqcValue);
        if (u.str.is_string(v1)) {
            n1HasEqcValue = true;
        }
        if (u.str.is_string(v2)) {
            n2HasEqcValue = true;
        }
        if (n1HasEqcValue && n2HasEqcValue) {
            zstring n1_str;
            u.str.is_string(v1, n1_str);
            zstring n2_str;
            u.str.is_string(v2, n2_str);
            zstring result = n1_str + n2_str;
            return mk_string(result);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            zstring n1_str;
            u.str.is_string(v1, n1_str);
            if (n1_str.empty()) {
                return n2;
            }
        } else if (!n1HasEqcValue && n2HasEqcValue) {
            zstring n2_str;
            u.str.is_string(v2, n2_str);
            if (n2_str.empty()) {
                return n1;
            }
        }
        return nullptr;
    }

    expr * theory_str::mk_concat(expr * n1, expr * n2) {
        ast_manager & m = get_manager();
        ENSURE(n1 != nullptr);
        ENSURE(n2 != nullptr);
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        n1 = get_eqc_value(n1, n1HasEqcValue);
        n2 = get_eqc_value(n2, n2HasEqcValue);
        if (n1HasEqcValue && n2HasEqcValue) {
            return mk_concat_const_str(n1, n2);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            bool n2_isConcatFunc = u.str.is_concat(to_app(n2));
            zstring n1_str;
            u.str.is_string(n1, n1_str);
            if (n1_str.empty()) {
                return n2;
            }
            if (n2_isConcatFunc) {
                expr * n2_arg0 = to_app(n2)->get_arg(0);
                expr * n2_arg1 = to_app(n2)->get_arg(1);
                if (u.str.is_string(n2_arg0)) {
                    n1 = mk_concat_const_str(n1, n2_arg0); // n1 will be a constant
                    n2 = n2_arg1;
                }
            }
        } else if (!n1HasEqcValue && n2HasEqcValue) {
            zstring n2_str;
            u.str.is_string(n2, n2_str);
            if (n2_str.empty()) {
                return n1;
            }

            if (u.str.is_concat(to_app(n1))) {
                expr * n1_arg0 = to_app(n1)->get_arg(0);
                expr * n1_arg1 = to_app(n1)->get_arg(1);
                if (u.str.is_string(n1_arg1)) {
                    n1 = n1_arg0;
                    n2 = mk_concat_const_str(n1_arg1, n2); // n2 will be a constant
                }
            }
        } else {
            if (u.str.is_concat(to_app(n1)) && u.str.is_concat(to_app(n2))) {
                expr * n1_arg0 = to_app(n1)->get_arg(0);
                expr * n1_arg1 = to_app(n1)->get_arg(1);
                expr * n2_arg0 = to_app(n2)->get_arg(0);
                expr * n2_arg1 = to_app(n2)->get_arg(1);
                if (u.str.is_string(n1_arg1) && u.str.is_string(n2_arg0)) {
                    expr * tmpN1 = n1_arg0;
                    expr * tmpN2 = mk_concat_const_str(n1_arg1, n2_arg0);
                    n1 = mk_concat(tmpN1, tmpN2);
                    n2 = n2_arg1;
                }
            }
        }

        //------------------------------------------------------
        // * expr * ast1 = mk_2_arg_app(ctx, td->Concat, n1, n2);
        // * expr * ast2 = mk_2_arg_app(ctx, td->Concat, n1, n2);
        // Z3 treats (ast1) and (ast2) as two different nodes.
        //-------------------------------------------------------

        expr * concatAst = nullptr;

        if (!concat_astNode_map.find(n1, n2, concatAst)) {
            concatAst = u.str.mk_concat(n1, n2);
            m_trail.push_back(concatAst);
            concat_astNode_map.insert(n1, n2, concatAst);

            expr_ref concat_length(mk_strlen(concatAst), m);

            ptr_vector<expr> childrenVector;
            get_nodes_in_concat(concatAst, childrenVector);
            expr_ref_vector items(m);
            for (auto el : childrenVector) {
                items.push_back(mk_strlen(el));
            }
            expr_ref lenAssert(ctx.mk_eq_atom(concat_length, m_autil.mk_add(items.size(), items.data())), m);
            assert_axiom(lenAssert);
        }
        return concatAst;
    }

    bool theory_str::can_propagate() {
        return !m_basicstr_axiom_todo.empty()
            || !m_concat_axiom_todo.empty() || !m_concat_eval_todo.empty()
            || !m_library_aware_axiom_todo.empty()
            || !m_delayed_axiom_setup_terms.empty()
            || !m_persisted_axiom_todo.empty()
            || (search_started && !m_delayed_assertions_todo.empty())
        ;
    }

    void theory_str::propagate() {
        candidate_model.reset();
        while (can_propagate()) {
            TRACE("str", tout << "propagating..." << std::endl;);
            while(true) {
                // this can potentially recursively activate itself
                unsigned start_count = m_basicstr_axiom_todo.size();
                ptr_vector<enode> axioms_tmp(m_basicstr_axiom_todo);
                for (auto const& el : axioms_tmp) {
                    instantiate_basic_string_axioms(el);
                }
                unsigned end_count = m_basicstr_axiom_todo.size();
                if (end_count > start_count) {
                    TRACE("str", tout << "new basic string axiom terms added -- checking again" << std::endl;);
                    continue;
                } else {
                    break;
                }
            }
            m_basicstr_axiom_todo.reset();
            TRACE("str", tout << "reset m_basicstr_axiom_todo" << std::endl;);

            for (auto const& el : m_concat_axiom_todo) {
                instantiate_concat_axiom(el);
            }
            m_concat_axiom_todo.reset();

            for (auto const& el : m_concat_eval_todo) {
                try_eval_concat(el);
            }
            m_concat_eval_todo.reset();

            while(true) {
                // Special handling: terms can recursively set up other terms
                // (e.g. indexof can instantiate other indexof terms).
                // - Copy the list so it can potentially be modified during setup.
                // - Don't clear this list if new ones are added in the process;
                //   instead, set up all the new terms before proceeding.
                // TODO see if any other propagate() worklists need this kind of handling
                // TODO we really only need to check the new ones on each pass
                unsigned start_count = m_library_aware_axiom_todo.size();
                ptr_vector<enode> axioms_tmp(m_library_aware_axiom_todo);
                for (auto const& e : axioms_tmp) {
                    app * a = e->get_expr();
                    if (u.str.is_stoi(a)) {
                        instantiate_axiom_str_to_int(e);
                    } else if (u.str.is_itos(a)) {
                        instantiate_axiom_int_to_str(e);
                    } else if (u.str.is_at(a)) {
                        instantiate_axiom_CharAt(e);
                    } else if (u.str.is_prefix(a)) {
                        instantiate_axiom_prefixof(e);
                    } else if (u.str.is_suffix(a)) {
                        instantiate_axiom_suffixof(e);
                    } else if (u.str.is_contains(a)) {
                        instantiate_axiom_Contains(e);
                    } else if (u.str.is_index(a)) {
                        instantiate_axiom_Indexof(e);
                    } else if (u.str.is_extract(a)) {
                        instantiate_axiom_Substr(e);
                    } else if (u.str.is_replace(a)) {
                        instantiate_axiom_Replace(e);
                    } else if (u.str.is_in_re(a)) {
                        instantiate_axiom_RegexIn(e);
                    } else if (u.str.is_is_digit(a)) {
                        instantiate_axiom_is_digit(e);
                    } else if (u.str.is_from_code(a)) {
                        instantiate_axiom_str_from_code(e);
                    } else if (u.str.is_to_code(a)) {
                        instantiate_axiom_str_to_code(e);
                    } else {
                        TRACE("str", tout << "BUG: unhandled library-aware term " << mk_pp(e->get_expr(), get_manager()) << std::endl;);
                        NOT_IMPLEMENTED_YET();
                    }
                }
                unsigned end_count = m_library_aware_axiom_todo.size();
                if (end_count > start_count) {
                    TRACE("str", tout << "new library-aware terms added during axiom setup -- checking again" << std::endl;);
                    continue;
                } else {
                    break;
                }
            }
            //m_library_aware_axiom_todo.reset();
            unsigned nScopes = m_library_aware_trail_stack.get_num_scopes();
            m_library_aware_trail_stack.reset();
            for (unsigned i = 0; i < nScopes; ++i) {
                m_library_aware_trail_stack.push_scope();
            }

            for (auto el : m_delayed_axiom_setup_terms) {
                // I think this is okay
                ctx.internalize(el, false);
                set_up_axioms(el);
            }
            m_delayed_axiom_setup_terms.reset();

            for (expr * a : m_persisted_axiom_todo) {
                assert_axiom(a);
            }
            m_persisted_axiom_todo.reset();

            if (search_started) {
                for (auto const& el : m_delayed_assertions_todo) {
                    assert_axiom(el);
                }
                m_delayed_assertions_todo.reset();
            }
        }
    }

    /*
     * Attempt to evaluate a concat over constant strings,
     * and if this is possible, assert equality between the
     * flattened string and the original term.
     */

    void theory_str::try_eval_concat(enode * cat) {
        app * a_cat = cat->get_expr();
        SASSERT(u.str.is_concat(a_cat));

        ast_manager & m = get_manager();

        TRACE("str", tout << "attempting to flatten " << mk_pp(a_cat, m) << std::endl;);

        std::stack<app*> worklist;
        zstring flattenedString("");
        bool constOK = true;

        {
            app * arg0 = to_app(a_cat->get_arg(0));
            app * arg1 = to_app(a_cat->get_arg(1));

            worklist.push(arg1);
            worklist.push(arg0);
        }

        while (constOK && !worklist.empty()) {
            app * evalArg = worklist.top(); worklist.pop();
            zstring nextStr;
            if (u.str.is_string(evalArg, nextStr)) {
                flattenedString = flattenedString + nextStr;
            } else if (u.str.is_concat(evalArg)) {
                app * arg0 = to_app(evalArg->get_arg(0));
                app * arg1 = to_app(evalArg->get_arg(1));

                worklist.push(arg1);
                worklist.push(arg0);
            } else {
                TRACE("str", tout << "non-constant term in concat -- giving up." << std::endl;);
                constOK = false;
                break;
            }
        }
        if (constOK) {
            TRACE("str", tout << "flattened to \"" << flattenedString.encode() << '"' << std::endl;);
            expr_ref constStr(mk_string(flattenedString), m);
            expr_ref axiom(ctx.mk_eq_atom(a_cat, constStr), m);
            assert_axiom(axiom);
        }
    }

    /*
     * Instantiate an axiom of the following form:
     * Length(Concat(x, y)) = Length(x) + Length(y)
     */
    void theory_str::instantiate_concat_axiom(enode * cat) {
        ast_manager & m = get_manager();
        app * a_cat = cat->get_expr();
        TRACE("str", tout << "instantiating concat axiom for " << mk_ismt2_pp(a_cat, m) << std::endl;);
        if (!u.str.is_concat(a_cat)) {
            return;
        }

        // build LHS
        expr_ref len_xy(m);
        len_xy = mk_strlen(a_cat);
        SASSERT(len_xy);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app * a_x = to_app(a_cat->get_arg(0));
        app * a_y = to_app(a_cat->get_arg(1));

        expr_ref len_x(m);
        len_x = mk_strlen(a_x);
        SASSERT(len_x);

        expr_ref len_y(m);
        len_y = mk_strlen(a_y);
        SASSERT(len_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_autil.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        // finally assert equality between the two subexpressions
        app * eq = m.mk_eq(len_xy, len_x_plus_len_y);
        SASSERT(eq);
        assert_axiom(eq);
    }

    /*
     * Add axioms that are true for any string variable:
     * 1. Length(x) >= 0
     * 2. Length(x) == 0 <=> x == ""
     * If the term is a string constant, we can assert something stronger:
     *    Length(x) == strlen(x)
     */
    void theory_str::instantiate_basic_string_axioms(enode * str) {
        ast_manager & m = get_manager();

        TRACE("str", tout << "set up basic string axioms on " << mk_pp(str->get_expr(), m) << std::endl;);

        {
            sort * a_sort = str->get_expr()->get_sort();
            sort * str_sort = u.str.mk_string_sort();
            if (a_sort != str_sort) {
                TRACE("str", tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_expr(), m) << std::endl;);
                return;
            }
        }

        // TESTING: attempt to avoid a crash here when a variable goes out of scope
        if (str->get_iscope_lvl() > ctx.get_scope_level()) {
            TRACE("str", tout << "WARNING: skipping axiom setup on out-of-scope string term" << std::endl;);
            return;
        }

        // generate a stronger axiom for constant strings
        app * a_str = str->get_expr();

        if (u.str.is_string(a_str)) {
            expr_ref len_str(m);
            len_str = mk_strlen(a_str);
            SASSERT(len_str);

            zstring strconst;
            u.str.is_string(str->get_expr(), strconst);
            TRACE("str", tout << "instantiating constant string axioms for \"" << strconst.encode() << '"' << std::endl;);
            unsigned int l = strconst.length();
            expr_ref len(m_autil.mk_numeral(rational(l), true), m);

            literal lit(mk_eq(len_str, len, false));
            ctx.mark_as_relevant(lit);
            if (m.has_trace_stream()) log_axiom_instantiation(ctx.bool_var2expr(lit.var()));
            ctx.mk_th_axiom(get_id(), 1, &lit);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        } else {
            // build axiom 1: Length(a_str) >= 0
            {
                // build LHS
                expr_ref len_str(m);
                len_str = mk_strlen(a_str);
                SASSERT(len_str);
                // build RHS
                expr_ref zero(m);
                zero = m_autil.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app * lhs_ge_rhs = m_autil.mk_ge(len_str, zero);
                SASSERT(lhs_ge_rhs);
                TRACE("str", tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);
                assert_axiom(lhs_ge_rhs);
            }

            // build axiom 2: Length(a_str) == 0 <=> a_str == ""
            {
                // build LHS of iff
                expr_ref len_str(m);
                len_str = mk_strlen(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_autil.mk_numeral(rational(0), true);
                SASSERT(zero);
                expr_ref lhs(m);
                lhs = ctx.mk_eq_atom(len_str, zero);
                SASSERT(lhs);
                // build RHS of iff
                expr_ref empty_str(m);
                empty_str = mk_string("");
                SASSERT(empty_str);
                expr_ref rhs(m);
                rhs = ctx.mk_eq_atom(a_str, empty_str);
                SASSERT(rhs);
                // build LHS <=> RHS and assert
                TRACE("str", tout << "string axiom 2: " << mk_ismt2_pp(lhs, m) << " <=> " << mk_ismt2_pp(rhs, m) << std::endl;);
                literal l(mk_eq(lhs, rhs, true));
                ctx.mark_as_relevant(l);
                if (m.has_trace_stream()) log_axiom_instantiation(ctx.bool_var2expr(l.var()));
                ctx.mk_th_axiom(get_id(), 1, &l);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            }

        }
    }

    /*
     * Add an axiom of the form:
     * (lhs == rhs) -> ( Length(lhs) == Length(rhs) )
     */
    void theory_str::instantiate_str_eq_length_axiom(enode * lhs, enode * rhs) {
        ast_manager & m = get_manager();

        app * a_lhs = lhs->get_expr();
        app * a_rhs = rhs->get_expr();

        // build premise: (lhs == rhs)
        expr_ref premise(ctx.mk_eq_atom(a_lhs, a_rhs), m);

        // build conclusion: ( Length(lhs) == Length(rhs) )
        expr_ref len_lhs(mk_strlen(a_lhs), m);
        SASSERT(len_lhs);
        expr_ref len_rhs(mk_strlen(a_rhs), m);
        SASSERT(len_rhs);
        expr_ref conclusion(ctx.mk_eq_atom(len_lhs, len_rhs), m);

        TRACE("str", tout << "string-eq length-eq axiom: "
              << mk_ismt2_pp(premise, m) << " -> " << mk_ismt2_pp(conclusion, m) << std::endl;);
        assert_implication(premise, conclusion);
    }

    void theory_str::instantiate_axiom_CharAt(enode * e) {
        ast_manager & m = get_manager();
        expr* arg0, *arg1;
        app * expr = e->get_expr();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up CharAt axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);
        VERIFY(u.str.is_at(expr, arg0, arg1));

        TRACE("str", tout << "instantiate CharAt axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("ts0"), m);
        expr_ref ts1(mk_str_var("ts1"), m);
        expr_ref ts2(mk_str_var("ts2"), m);

        expr_ref cond(m.mk_and(
                          m_autil.mk_ge(arg1, mk_int(0)),
                          m_autil.mk_lt(arg1, mk_strlen(arg0))), m);

        expr_ref_vector and_item(m);
        and_item.push_back(ctx.mk_eq_atom(arg0, mk_concat(ts0, mk_concat(ts1, ts2))));
        and_item.push_back(ctx.mk_eq_atom(arg1, mk_strlen(ts0)));
        and_item.push_back(ctx.mk_eq_atom(mk_strlen(ts1), mk_int(1)));

        expr_ref thenBranch(::mk_and(and_item));
        expr_ref elseBranch(ctx.mk_eq_atom(ts1, mk_string("")), m);
        expr_ref axiom(m.mk_ite(cond, thenBranch, elseBranch), m);
        expr_ref reductionVar(ctx.mk_eq_atom(expr, ts1), m);
        expr_ref finalAxiom(m.mk_and(axiom, reductionVar), m);
        ctx.get_rewriter()(finalAxiom);
        assert_axiom(finalAxiom);
    }

    void theory_str::instantiate_axiom_prefixof(enode * e) {
        ast_manager & m = get_manager();

        app * expr = e->get_expr();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up prefixof axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << "instantiate prefixof axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("ts0"), m);
        expr_ref ts1(mk_str_var("ts1"), m);

        expr_ref_vector innerItems(m);
        innerItems.push_back(ctx.mk_eq_atom(expr->get_arg(1), mk_concat(ts0, ts1)));
        innerItems.push_back(ctx.mk_eq_atom(mk_strlen(ts0), mk_strlen(expr->get_arg(0))));
        innerItems.push_back(m.mk_ite(ctx.mk_eq_atom(ts0, expr->get_arg(0)), expr, mk_not(m, expr)));
        expr_ref then1(m.mk_and(innerItems.size(), innerItems.data()), m);
        SASSERT(then1);

        // the top-level condition is Length(arg0) >= Length(arg1)
        expr_ref topLevelCond(
            m_autil.mk_ge(
                m_autil.mk_add(
                    mk_strlen(expr->get_arg(1)), m_autil.mk_mul(mk_int(-1), mk_strlen(expr->get_arg(0)))),
                mk_int(0))
            , m);
        SASSERT(topLevelCond);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        SASSERT(finalAxiom);
        assert_axiom(finalAxiom);
    }

    void theory_str::instantiate_axiom_suffixof(enode * e) {
        ast_manager & m = get_manager();

        app * expr = e->get_expr();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up suffixof axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << "instantiate suffixof axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref ts0(mk_str_var("ts0"), m);
        expr_ref ts1(mk_str_var("ts1"), m);

        expr_ref_vector innerItems(m);
        innerItems.push_back(ctx.mk_eq_atom(expr->get_arg(1), mk_concat(ts0, ts1)));
        innerItems.push_back(ctx.mk_eq_atom(mk_strlen(ts1), mk_strlen(expr->get_arg(0))));
        innerItems.push_back(m.mk_ite(ctx.mk_eq_atom(ts1, expr->get_arg(0)), expr, mk_not(m, expr)));
        expr_ref then1(m.mk_and(innerItems.size(), innerItems.data()), m);
        SASSERT(then1);

        // the top-level condition is Length(arg0) >= Length(arg1)
        expr_ref topLevelCond(
            m_autil.mk_ge(
                m_autil.mk_add(
                    mk_strlen(expr->get_arg(1)), m_autil.mk_mul(mk_int(-1), mk_strlen(expr->get_arg(0)))),
                mk_int(0))
            , m);
        SASSERT(topLevelCond);

        expr_ref finalAxiom(m.mk_ite(topLevelCond, then1, mk_not(m, expr)), m);
        SASSERT(finalAxiom);
        assert_axiom(finalAxiom);
    }

    void theory_str::instantiate_axiom_Contains(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up Contains axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        // quick path, because this is necessary due to rewriter behaviour
        // at minimum it should fix z3str/concat-006.smt2
        zstring haystackStr, needleStr;
        if (u.str.is_string(ex->get_arg(0), haystackStr) && u.str.is_string(ex->get_arg(1), needleStr)) {
            TRACE("str", tout << "eval constant Contains term " << mk_pp(ex, m) << std::endl;);
            if (haystackStr.contains(needleStr)) {
                assert_axiom(ex);
            } else {
                assert_axiom(mk_not(m, ex));
            }
            return;
        }

        { // register Contains()
            expr * str = ex->get_arg(0);
            expr * substr = ex->get_arg(1);
            contains_map.push_back(ex);
            std::pair<expr*, expr*> key = std::pair<expr*, expr*>(str, substr);
            contain_pair_bool_map.insert(str, substr, ex);
            if (!contain_pair_idx_map.contains(str)) {
                contain_pair_idx_map.insert(str, std::set<std::pair<expr*, expr*>>());
            }
            if (!contain_pair_idx_map.contains(substr)) {
                contain_pair_idx_map.insert(substr, std::set<std::pair<expr*, expr*>>());
            }
            contain_pair_idx_map[str].insert(key);
            contain_pair_idx_map[substr].insert(key);
        }

        TRACE("str", tout << "instantiate Contains axiom for " << mk_pp(ex, m) << std::endl;);

        expr_ref ts0(mk_str_var("ts0"), m);
        expr_ref ts1(mk_str_var("ts1"), m);

        expr_ref breakdownAssert(ctx.mk_eq_atom(ex, ctx.mk_eq_atom(ex->get_arg(0), mk_concat(ts0, mk_concat(ex->get_arg(1), ts1)))), m);
        SASSERT(breakdownAssert);
        assert_axiom(breakdownAssert);
    }

    void theory_str::instantiate_axiom_Indexof(enode * e) {
        th_rewriter & rw = ctx.get_rewriter();
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.indexof axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        SASSERT(ex->get_num_args() == 3);

        {
            // Attempt to rewrite to an integer constant. If this succeeds,
            // assert equality with that constant.
            // The rewriter normally takes care of this for terms that are in scope
            // at the beginning of the search.
            // We perform the check here to catch terms that are added during the search.
            expr_ref rwex(ex, m);
            rw(rwex);
            if (m_autil.is_numeral(rwex)) {
                TRACE("str", tout << "constant expression " << mk_pp(ex, m) << " simplifies to " << mk_pp(rwex, m) << std::endl;);
                assert_axiom(ctx.mk_eq_atom(ex, rwex));
                axiomatized_terms.insert(ex);
                return;
            }
        }

        expr * exHaystack = nullptr;
        expr * exNeedle = nullptr;
        expr * exIndex = nullptr;
        u.str.is_index(ex, exHaystack, exNeedle, exIndex);

        // if the third argument is exactly the integer 0, we can use this "simple" indexof;
        // otherwise, we call the "extended" version
        rational startingInteger;
        if (!m_autil.is_numeral(exIndex, startingInteger) || !startingInteger.is_zero()) {
            // "extended" indexof term with prefix
            instantiate_axiom_Indexof_extended(e);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.indexof axiom for " << mk_pp(ex, m) << std::endl;);

        expr_ref x1(mk_str_var("x1"), m);
        expr_ref x2(mk_str_var("x2"), m);

        expr_ref condAst1(mk_contains(exHaystack, exNeedle), m);
        expr_ref condAst2(m.mk_not(ctx.mk_eq_atom(exNeedle, mk_string(""))), m);
        expr_ref condAst(m.mk_and(condAst1, condAst2), m);
        SASSERT(condAst);

        // -----------------------
        // true branch
        expr_ref_vector thenItems(m);
        //  args[0] = x1 . args[1] . x2
        thenItems.push_back(ctx.mk_eq_atom(exHaystack, mk_concat(x1, mk_concat(exNeedle, x2))));
        //  indexAst = |x1|
        thenItems.push_back(ctx.mk_eq_atom(ex, mk_strlen(x1)));
        //     args[0]  = x3 . x4
        //  /\ |x3| = |x1| + |args[1]| - 1
        //  /\ ! contains(x3, args[1])
        expr_ref x3(mk_str_var("x3"), m);
        expr_ref x4(mk_str_var("x4"), m);
        expr_ref tmpLen(m_autil.mk_add(ex, mk_strlen(ex->get_arg(1)), mk_int(-1)), m);
        SASSERT(tmpLen);
        thenItems.push_back(ctx.mk_eq_atom(exHaystack, mk_concat(x3, x4)));
        thenItems.push_back(ctx.mk_eq_atom(mk_strlen(x3), tmpLen));
        thenItems.push_back(mk_not(m, mk_contains(x3, exNeedle)));
        expr_ref thenBranch(mk_and(thenItems), m);
        SASSERT(thenBranch);

        // -----------------------
        // false branch
        expr_ref elseBranch(m.mk_ite(
                ctx.mk_eq_atom(exNeedle, mk_string("")),
                ctx.mk_eq_atom(ex, mk_int(0)),
                ctx.mk_eq_atom(ex, mk_int(-1))
                ), m);
        SASSERT(elseBranch);

        expr_ref breakdownAssert(m.mk_ite(condAst, thenBranch, elseBranch), m);
        assert_axiom_rw(breakdownAssert);

        {
            // heuristic: integrate with str.contains information
            // (but don't introduce it if it isn't already in the instance)
            expr_ref haystack(ex->get_arg(0), m), needle(ex->get_arg(1), m), startIdx(ex->get_arg(2), m);
            expr_ref zeroAst(mk_int(0), m);
            // (H contains N) <==> (H indexof N, 0) >= 0
            expr_ref premise(u.str.mk_contains(haystack, needle), m);
            ctx.internalize(premise, false);
            expr_ref conclusion(m_autil.mk_ge(ex, zeroAst), m);
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, conclusion), m);
            SASSERT(containsAxiom);

            // we can't assert this during init_search as it breaks an invariant if the instance becomes inconsistent
            //m_delayed_axiom_setup_terms.push_back(containsAxiom);
        }
    }

    void theory_str::instantiate_axiom_Indexof_extended(enode * _e) {
        th_rewriter & rw = ctx.get_rewriter();
        ast_manager & m = get_manager();

        app * e = _e->get_expr();
        if (axiomatized_terms.contains(e)) {
            TRACE("str", tout << "already set up extended str.indexof axiom for " << mk_pp(e, m) << std::endl;);
            return;
        }
        SASSERT(e->get_num_args() == 3);
        axiomatized_terms.insert(e);

        TRACE("str", tout << "instantiate extended str.indexof axiom for " << mk_pp(e, m) << std::endl;);

        // str.indexof(H, N, i):
        // i < 0 --> -1
        // i == 0 --> str.indexof(H, N, 0)
        // i >= len(H) --> -1
        // 0 < i < len(H) -->
        //     H = hd ++ tl
        //     len(hd) = i
        //     i + str.indexof(tl, N, 0)

        expr * H = nullptr; // "haystack"
        expr * N = nullptr; // "needle"
        expr * i = nullptr; // start index
        u.str.is_index(e, H, N, i);

        expr_ref minus_one(m_autil.mk_numeral(rational::minus_one(), true), m);
        expr_ref zero(m_autil.mk_numeral(rational::zero(), true), m);
        expr_ref empty_string(mk_string(""), m);

        // case split

        // case 1: i < 0
        {
            expr_ref premise(m_autil.mk_le(i, minus_one), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
            expr_ref ax(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(ax);
        }

        // case 1.1: N == "" and i out of range
        {
            expr_ref premiseNEmpty(ctx.mk_eq_atom(N, empty_string), m);
            // range check
            expr_ref premiseRangeLower(m_autil.mk_ge(i, zero), m);
            expr_ref premiseRangeUpper(m_autil.mk_le(i, mk_strlen(H)), m);
            expr_ref premiseRange(m.mk_and(premiseRangeLower, premiseRangeUpper), m);
            expr_ref premise(m.mk_and(premiseNEmpty, m.mk_not(premiseRange)), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
            expr_ref finalAxiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(finalAxiom);
        }

        // case 1.2: N == "" and i within range
        {
            expr_ref premiseNEmpty(ctx.mk_eq_atom(N, empty_string), m);
            // range check
            expr_ref premiseRangeLower(m_autil.mk_ge(i, zero), m);
            expr_ref premiseRangeUpper(m_autil.mk_le(i, mk_strlen(H)), m);
            expr_ref premiseRange(m.mk_and(premiseRangeLower, premiseRangeUpper), m);
            expr_ref premise(m.mk_and(premiseNEmpty, premiseRange), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, i), m);
            expr_ref finalAxiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(finalAxiom);
        }

        // case 2: i = 0
        {
            expr_ref premise1(ctx.mk_eq_atom(i, zero), m);
            expr_ref premise2(m.mk_not(ctx.mk_eq_atom(N, empty_string)), m);
            expr_ref premise(m.mk_and(premise1, premise2), m);
            // reduction to simpler case
            expr_ref conclusion(ctx.mk_eq_atom(e, mk_indexof(H, N)), m);
            expr_ref ax(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(ax);
        }
        // case 3: i >= len(H)
        {
            expr_ref premise1(m_autil.mk_ge(m_autil.mk_add(i, m_autil.mk_mul(minus_one, mk_strlen(H))), zero), m);
            expr_ref premise2(m.mk_not(ctx.mk_eq_atom(N, empty_string)), m);
            expr_ref premise(m.mk_and(premise1, premise2), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
            expr_ref ax(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(ax);
        }
        // case 3.5: H doesn't contain N
        {
            expr_ref premise(m.mk_not(u.str.mk_contains(H, N)), m);
            expr_ref conclusion(ctx.mk_eq_atom(e, minus_one), m);
            expr_ref ax(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(ax);
        }
        // case 4: 0 < i < len(H), N non-empty, and H contains N
        {
            expr_ref premise1(m_autil.mk_gt(i, zero), m);
            //expr_ref premise2(m_autil.mk_lt(i, mk_strlen(H)), m);
            expr_ref premise2(m.mk_not(m_autil.mk_ge(m_autil.mk_add(i, m_autil.mk_mul(minus_one, mk_strlen(H))), zero)), m);
            expr_ref premise3(u.str.mk_contains(H, N), m);
            expr_ref premise4(m.mk_not(ctx.mk_eq_atom(N, mk_string(""))), m);

            expr_ref_vector premises(m);
            premises.push_back(premise1);
            premises.push_back(premise2);
            premises.push_back(premise3);
            premises.push_back(premise4);
            expr_ref premise(mk_and(premises), m);

            expr_ref hd(mk_str_var("hd"), m);
            expr_ref tl(mk_str_var("tl"), m);

            expr_ref_vector conclusion_terms(m);
            conclusion_terms.push_back(ctx.mk_eq_atom(H, mk_concat(hd, tl)));
            conclusion_terms.push_back(ctx.mk_eq_atom(mk_strlen(hd), i));
            conclusion_terms.push_back(u.str.mk_contains(tl, N));
            conclusion_terms.push_back(ctx.mk_eq_atom(e, m_autil.mk_add(i, mk_indexof(tl, N))));

            expr_ref conclusion(mk_and(conclusion_terms), m);
            expr_ref ax(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(ax);
        }

        {
            // heuristic: integrate with str.contains information
            // (but don't introduce it if it isn't already in the instance)
            // (0 <= i < len(H)) ==> (H contains N) <==> (H indexof N, i) >= 0
            expr_ref precondition1(m_autil.mk_gt(i, minus_one), m);
            //expr_ref precondition2(m_autil.mk_lt(i, mk_strlen(H)), m);
            expr_ref precondition2(m.mk_not(m_autil.mk_ge(m_autil.mk_add(i, m_autil.mk_mul(minus_one, mk_strlen(H))), zero)), m);
            expr_ref precondition3(m.mk_not(ctx.mk_eq_atom(N, mk_string(""))), m);
            expr_ref precondition(m.mk_and(precondition1, precondition2, precondition3), m);
            rw(precondition);

            expr_ref premise(u.str.mk_contains(H, N), m);
            ctx.internalize(premise, false);
            expr_ref conclusion(m_autil.mk_ge(e, zero), m);
            expr_ref containsAxiom(ctx.mk_eq_atom(premise, conclusion), m);
            expr_ref finalAxiom(rewrite_implication(precondition, containsAxiom), m);
            SASSERT(finalAxiom);
            // we can't assert this during init_search as it breaks an invariant if the instance becomes inconsistent
            m_delayed_assertions_todo.push_back(finalAxiom);
        }
    }

    void theory_str::instantiate_axiom_LastIndexof(enode * e) {
        ast_manager & m = get_manager();

        app * expr = e->get_expr();
        if (axiomatized_terms.contains(expr)) {
            TRACE("str", tout << "already set up LastIndexof axiom for " << mk_pp(expr, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(expr);

        TRACE("str", tout << "instantiate LastIndexof axiom for " << mk_pp(expr, m) << std::endl;);

        expr_ref x1(mk_str_var("x1"), m);
        expr_ref x2(mk_str_var("x2"), m);
        expr_ref indexAst(mk_int_var("index"), m);
        expr_ref_vector items(m);

        // args[0] = x1 . args[1] . x2
        expr_ref eq1(ctx.mk_eq_atom(expr->get_arg(0), mk_concat(x1, mk_concat(expr->get_arg(1), x2))), m);
        expr_ref arg0HasArg1(mk_contains(expr->get_arg(0), expr->get_arg(1)), m);  // arg0HasArg1 = Contains(args[0], args[1])
        items.push_back(ctx.mk_eq_atom(arg0HasArg1, eq1));


        expr_ref condAst(arg0HasArg1, m);
        //----------------------------
        // true branch
        expr_ref_vector thenItems(m);
        thenItems.push_back(m_autil.mk_ge(indexAst, mk_int(0)));
        //  args[0] = x1 . args[1] . x2
        //  x1 doesn't contain args[1]
        thenItems.push_back(mk_not(m, mk_contains(x2, expr->get_arg(1))));
        thenItems.push_back(ctx.mk_eq_atom(indexAst, mk_strlen(x1)));

        bool canSkip = false;
        zstring arg1Str;
        if (u.str.is_string(expr->get_arg(1), arg1Str)) {
            if (arg1Str.length() == 1) {
                canSkip = true;
            }
        }

        if (!canSkip) {
            // args[0]  = x3 . x4 /\ |x3| = |x1| + 1 /\ ! contains(x4, args[1])
            expr_ref x3(mk_str_var("x3"), m);
            expr_ref x4(mk_str_var("x4"), m);
            expr_ref tmpLen(m_autil.mk_add(indexAst, mk_int(1)), m);
            thenItems.push_back(ctx.mk_eq_atom(expr->get_arg(0), mk_concat(x3, x4)));
            thenItems.push_back(ctx.mk_eq_atom(mk_strlen(x3), tmpLen));
            thenItems.push_back(mk_not(m, mk_contains(x4, expr->get_arg(1))));
        }
        //----------------------------
        // else branch
        expr_ref_vector elseItems(m);
        elseItems.push_back(ctx.mk_eq_atom(indexAst, mk_int(-1)));

        items.push_back(m.mk_ite(condAst, m.mk_and(thenItems.size(), thenItems.data()), m.mk_and(elseItems.size(), elseItems.data())));

        expr_ref breakdownAssert(m.mk_and(items.size(), items.data()), m);
        SASSERT(breakdownAssert);

        expr_ref reduceToIndex(ctx.mk_eq_atom(expr, indexAst), m);
        SASSERT(reduceToIndex);

        expr_ref finalAxiom(m.mk_and(breakdownAssert, reduceToIndex), m);
        SASSERT(finalAxiom);
        assert_axiom_rw(finalAxiom);
    }

    void theory_str::instantiate_axiom_Substr(enode * _e) {
        ast_manager & m = get_manager();
        expr* s = nullptr;
        expr* i = nullptr;
        expr* l = nullptr;

        app * e = _e->get_expr();
        if (axiomatized_terms.contains(e)) {
            TRACE("str", tout << "already set up Substr axiom for " << mk_pp(e, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(e);

        TRACE("str", tout << "instantiate Substr axiom for " << mk_pp(e, m) << std::endl;);

        VERIFY(u.str.is_extract(e, s, i, l));

        // e = substr(s, i, l)
        expr_ref x(mk_str_var("substrPre"), m);
        expr_ref ls(mk_strlen(s), m);
        expr_ref lx(mk_strlen(x), m);
        expr_ref le(mk_strlen(e), m);
        expr_ref ls_minus_i_l(m_autil.mk_sub(m_autil.mk_sub(ls, i), l), m);
        expr_ref y(mk_str_var("substrPost"), m);
        expr_ref xe(mk_concat(x, e), m);
        expr_ref xey(mk_concat(xe, y), m);
        expr_ref zero(mk_int(0), m);

        expr_ref i_ge_0(m_autil.mk_ge(i, zero), m);
        expr_ref i_le_ls(m_autil.mk_le(m_autil.mk_sub(i, ls), zero), m);
        expr_ref ls_le_i(m_autil.mk_le(m_autil.mk_sub(ls, i), zero), m);
        expr_ref ls_ge_li(m_autil.mk_ge(ls_minus_i_l, zero), m);
        expr_ref l_ge_0(m_autil.mk_ge(l, zero), m);
        expr_ref l_le_0(m_autil.mk_le(l, zero), m);
        expr_ref ls_le_0(m_autil.mk_le(ls, zero), m);
        expr_ref le_is_0(ctx.mk_eq_atom(le, zero), m);

        // 0 <= i & i <= |s| & 0 <= l => xey = s
        {
            expr_ref clause(m.mk_or(~i_ge_0, ~i_le_ls, ~l_ge_0, ctx.mk_eq_atom(xey, s)), m);
            assert_axiom_rw(clause);
        }
        // 0 <= i & i <= |s| => |x| = i
        {
            expr_ref clause(m.mk_or(~i_ge_0, ~i_le_ls, ctx.mk_eq_atom(lx, i)), m);
            assert_axiom_rw(clause);
        }
        // 0 <= i & i <= |s| & l >= 0 & |s| >= l + i => |e| = l
        {
            expr_ref_vector terms(m);
            terms.push_back(~i_ge_0);
            terms.push_back(~i_le_ls);
            terms.push_back(~l_ge_0);
            terms.push_back(~ls_ge_li);
            terms.push_back(ctx.mk_eq_atom(le, l));
            expr_ref clause(mk_or(terms), m);
            assert_axiom_rw(clause);
        }
        // 0 <= i & i <= |s| & |s| < l + i => |e| = |s| - i
        {
            expr_ref_vector terms(m);
            terms.push_back(~i_ge_0);
            terms.push_back(~i_le_ls);
            terms.push_back(~l_ge_0);
            terms.push_back(ls_ge_li);
            terms.push_back(ctx.mk_eq_atom(le, m_autil.mk_sub(ls, i)));
            expr_ref clause(mk_or(terms), m);
            assert_axiom_rw(clause);
        }
        // i < 0 => |e| = 0
        {
            expr_ref clause(m.mk_or(i_ge_0,   le_is_0), m);
            assert_axiom_rw(clause);
        }
        // |s| <= i => |e| = 0
        {
            expr_ref clause(m.mk_or(~ls_le_i, le_is_0), m);
            assert_axiom_rw(clause);
        }
        // |s| <= 0 => |e| = 0
        {
            expr_ref clause(m.mk_or(~ls_le_0, le_is_0), m);
            assert_axiom_rw(clause);
        }
        // l <= 0 => |e| = 0
        {
            expr_ref clause(m.mk_or(~l_le_0,  le_is_0), m);
            assert_axiom_rw(clause);
        }
        // |e| = 0 & i >= 0 & |s| > i & |s| > 0 => l <= 0
        {
            expr_ref_vector terms(m);
            terms.push_back(~le_is_0);
            terms.push_back(~i_ge_0);
            terms.push_back(ls_le_i);
            terms.push_back(ls_le_0);
            terms.push_back(l_le_0);
            expr_ref clause(mk_or(terms), m);
            assert_axiom_rw(clause);
        }

        // Auxiliary axioms

        // |e| <= |s|
        {
            expr_ref axiom(m_autil.mk_le(le, ls), m);
            assert_axiom_rw(axiom);
        }

        // l >= 0 => |e| <= len
        {
            expr_ref premise(m_autil.mk_ge(l, zero), m);
            expr_ref conclusion(m_autil.mk_le(le, l), m);
            expr_ref axiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(axiom);
        }
    }

    //  (str.replace s t t') is the string obtained by replacing the first occurrence
    //  of t in s, if any, by t'. Note that if t is empty, the result is to prepend
    //  t' to s; also, if t does not occur in s then the result is s.
    void theory_str::instantiate_axiom_Replace(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up Replace axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate Replace axiom for " << mk_pp(ex, m) << std::endl;);

        expr_ref x1(mk_str_var("x1"), m);
        expr_ref x2(mk_str_var("x2"), m);
        expr_ref i1(mk_int_var("i1"), m);
        expr_ref result(mk_str_var("result"), m);

        expr * replaceS = nullptr;
        expr * replaceT = nullptr;
        expr * replaceTPrime = nullptr;
        VERIFY(u.str.is_replace(ex, replaceS, replaceT, replaceTPrime));

        // t empty => result = (str.++ t' s)
        expr_ref emptySrcAst(ctx.mk_eq_atom(replaceT, mk_string("")), m);
        expr_ref prependTPrimeToS(ctx.mk_eq_atom(result, mk_concat(replaceTPrime, replaceS)), m);

        // condAst = Contains(args[0], args[1])
        expr_ref condAst(mk_contains(ex->get_arg(0), ex->get_arg(1)), m);
        // -----------------------
        // true branch
        expr_ref_vector thenItems(m);
        //  args[0] = x1 . args[1] . x2
        thenItems.push_back(ctx.mk_eq_atom(ex->get_arg(0), mk_concat(x1, mk_concat(ex->get_arg(1), x2))));
        //  i1 = |x1|
        thenItems.push_back(ctx.mk_eq_atom(i1, mk_strlen(x1)));
        //  args[0]  = x3 . x4 /\ |x3| = |x1| + |args[1]| - 1 /\ ! contains(x3, args[1])
        expr_ref x3(mk_str_var("x3"), m);
        expr_ref x4(mk_str_var("x4"), m);
        expr_ref tmpLen(m_autil.mk_add(i1, mk_strlen(ex->get_arg(1)), mk_int(-1)), m);
        thenItems.push_back(ctx.mk_eq_atom(ex->get_arg(0), mk_concat(x3, x4)));
        thenItems.push_back(ctx.mk_eq_atom(mk_strlen(x3), tmpLen));
        thenItems.push_back(mk_not(m, mk_contains(x3, ex->get_arg(1))));
        thenItems.push_back(ctx.mk_eq_atom(result, mk_concat(x1, mk_concat(ex->get_arg(2), x2))));
        // -----------------------
        // false branch
        expr_ref elseBranch(ctx.mk_eq_atom(result, ex->get_arg(0)), m);

        expr_ref breakdownAssert(m.mk_ite(emptySrcAst, prependTPrimeToS,
                m.mk_ite(condAst, mk_and(thenItems), elseBranch)), m);
        expr_ref breakdownAssert_rw(breakdownAssert, m);
        assert_axiom_rw(breakdownAssert_rw);

        expr_ref reduceToResult(ctx.mk_eq_atom(ex, result), m);
        expr_ref reduceToResult_rw(reduceToResult, m);
        assert_axiom_rw(reduceToResult_rw);
    }

    void theory_str::instantiate_axiom_str_to_int(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.to-int axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.to-int axiom for " << mk_pp(ex, m) << std::endl;);

        // let expr = (str.to-int S)
        // axiom 1: expr >= -1
        // axiom 2: expr = 0 <==> S in "0+"
        // axiom 3: expr >= 1 ==> S in "0*[1-9][0-9]*"

        // expr * S = ex->get_arg(0);
        {
            expr_ref axiom1(m_autil.mk_ge(ex, m_autil.mk_numeral(rational::minus_one(), true)), m);
            SASSERT(axiom1);
            assert_axiom_rw(axiom1);
        }
# if 0
        {
            expr_ref lhs(ctx.mk_eq_atom(ex, m_autil.mk_numeral(rational::zero(), true)), m);
            expr_ref re_zeroes(u.re.mk_plus(u.re.mk_to_re(mk_string("0"))), m);
            expr_ref rhs(mk_RegexIn(S, re_zeroes), m);
            expr_ref axiom2(ctx.mk_eq_atom(lhs, rhs), m);
            SASSERT(axiom2);
            assert_axiom_rw(axiom2);
        }

        {
            expr_ref premise(m_autil.mk_ge(ex, m_autil.mk_numeral(rational::one(), true)), m);
            //expr_ref re_positiveInteger(u.re.mk_concat(
            //        u.re.mk_range(mk_string("1"), mk_string("9")),
            //        u.re.mk_star(u.re.mk_range(mk_string("0"), mk_string("9")))), m);
            expr_ref re_subterm(u.re.mk_concat(u.re.mk_range(mk_string("1"), mk_string("9")),
                u.re.mk_star(u.re.mk_range(mk_string("0"), mk_string("9")))), m);
            expr_ref re_integer(u.re.mk_concat(u.re.mk_star(mk_string("0")), re_subterm), m);
            expr_ref conclusion(mk_RegexIn(S, re_integer), m);
            SASSERT(premise);
            SASSERT(conclusion);
            //assert_implication(premise, conclusion);
            assert_axiom_rw(rewrite_implication(premise, conclusion));
        }
#endif
    }

    void theory_str::instantiate_axiom_int_to_str(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.from-int axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.from-int axiom for " << mk_pp(ex, m) << std::endl;);

        // axiom 1: N < 0 <==> (str.from-int N) = ""
        expr * N = ex->get_arg(0);
        {
            expr_ref axiom1_lhs(mk_not(m, m_autil.mk_ge(N, m_autil.mk_numeral(rational::zero(), true))), m);
            expr_ref axiom1_rhs(ctx.mk_eq_atom(ex, mk_string("")), m);
            expr_ref axiom1(ctx.mk_eq_atom(axiom1_lhs, axiom1_rhs), m);
            SASSERT(axiom1);
            assert_axiom(axiom1);
        }

        // axiom 2: The only (str.from-int N) that starts with a "0" is "0".
        {
            expr_ref zero(mk_string("0"), m);
            // let (the result starts with a "0") be p
            expr_ref starts_with_zero(u.str.mk_prefix(zero, ex), m);
            // let (the result is "0") be q  
            expr_ref is_zero(ctx.mk_eq_atom(ex, zero), m);
            // encoding: the result does NOT start with a "0" (~p) xor the result is "0" (q)
            // ~p xor q == (~p or q) and (p or ~q)
            assert_axiom(m.mk_and(m.mk_or(m.mk_not(starts_with_zero), is_zero), m.mk_or(starts_with_zero, m.mk_not(is_zero))));
        }
    }

    void theory_str::instantiate_axiom_is_digit(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.is_digit axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate str.is_digit axiom for " << mk_pp(ex, m) << std::endl;);
        expr * string_term = nullptr;
        u.str.is_is_digit(ex, string_term);
        SASSERT(string_term);

        expr_ref_vector rhs_terms(m);

        for (unsigned c = 0x30; c <= 0x39; ++c) {
            zstring ch(c);
            expr_ref rhs_term(ctx.mk_eq_atom(string_term, mk_string(ch)), m);
            rhs_terms.push_back(rhs_term);
        }

        expr_ref rhs(mk_or(rhs_terms), m);
        expr_ref axiom(ctx.mk_eq_atom(ex, rhs), m);
        assert_axiom_rw(axiom);
    }
    
    void theory_str::instantiate_axiom_str_from_code(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.from_code axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);
        TRACE("str", tout << "instantiate str.from_code axiom for " << mk_pp(ex, m) << std::endl;);

        expr * arg = nullptr;
        VERIFY(u.str.is_from_code(ex, arg));
        // (str.from_code N) == "" if N is not in the range [0, max_char].
        {
            expr_ref premise(m.mk_or(m_autil.mk_le(arg, mk_int(-1)), m_autil.mk_ge(arg, mk_int(u.max_char() + 1))), m);
            expr_ref conclusion(ctx.mk_eq_atom(ex, mk_string("")), m);
            expr_ref axiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(axiom);
        }
        // len (str.from_code N) == 1 if N is in the range [0, max_char].
        {
            expr_ref premise(m.mk_and(m_autil.mk_ge(arg, mk_int(0)), m_autil.mk_le(arg, mk_int(u.max_char() + 1))), m);
            expr_ref conclusion(ctx.mk_eq_atom(mk_strlen(ex), mk_int(1)), m);
            expr_ref axiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(axiom);
        }
        // If N is in the range [0, max_char], then to_code(from_code(e)) == e.
        {
            expr_ref premise(m.mk_and(m_autil.mk_ge(arg, mk_int(0)), m_autil.mk_le(arg, mk_int(u.max_char() + 1))), m);
            expr_ref conclusion(ctx.mk_eq_atom(u.str.mk_to_code(ex), arg), m);
            expr_ref axiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(axiom);
        }
    }

    void theory_str::instantiate_axiom_str_to_code(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up str.to_code axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);
        TRACE("str", tout << "instantiate str.to_code axiom for " << mk_pp(ex, m) << std::endl;);

        expr * arg = nullptr;
        VERIFY(u.str.is_to_code(ex, arg));
        // (str.to_code S) == -1 if len(S) != 1.
        {
            expr_ref premise(m.mk_not(ctx.mk_eq_atom(mk_strlen(arg), mk_int(1))), m);
            expr_ref conclusion(ctx.mk_eq_atom(ex, mk_int(-1)), m);
            expr_ref axiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(axiom);
        }
        // (str.to_code S) is in [0, max_char] if len(S) == 1.
        {
            expr_ref premise(ctx.mk_eq_atom(mk_strlen(arg), mk_int(1)), m);
            expr_ref conclusion(m.mk_and(m_autil.mk_ge(ex, mk_int(0)), m_autil.mk_le(ex, mk_int(u.max_char()))), m);
            expr_ref axiom(rewrite_implication(premise, conclusion), m);
            assert_axiom_rw(axiom);
        }
    }

    expr * theory_str::mk_RegexIn(expr * str, expr * regexp) {
        app * regexIn = u.re.mk_in_re(str, regexp);
        // immediately force internalization so that axiom setup does not fail
        ctx.internalize(regexIn, false);
        set_up_axioms(regexIn);
        return regexIn;
    }

    void theory_str::instantiate_axiom_RegexIn(enode * e) {
        ast_manager & m = get_manager();

        app * ex = e->get_expr();
        if (axiomatized_terms.contains(ex)) {
            TRACE("str", tout << "already set up RegexIn axiom for " << mk_pp(ex, m) << std::endl;);
            return;
        }
        axiomatized_terms.insert(ex);

        TRACE("str", tout << "instantiate RegexIn axiom for " << mk_pp(ex, m) << std::endl;);

        expr_ref str(ex->get_arg(0), m);

        regex_terms.insert(ex);
        if (!regex_terms_by_string.contains(str)) {
            regex_terms_by_string.insert(str, ptr_vector<expr>());
        }
        regex_terms_by_string[str].push_back(ex);
    }

    void theory_str::attach_new_th_var(enode * n) {
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        TRACE("str", tout << "new theory var: " << mk_ismt2_pp(n->get_expr(), get_manager()) << " := v#" << v << std::endl;);
    }

    void theory_str::reset_eh() {
        TRACE("str", tout << "resetting" << std::endl;);
        m_trail_stack.reset();
        m_library_aware_trail_stack.reset();

        candidate_model.reset();
        m_basicstr_axiom_todo.reset();
        m_concat_axiom_todo.reset();
        pop_scope_eh(ctx.get_scope_level());
    }

    /*
     * Check equality among equivalence class members of LHS and RHS
     * to discover an incorrect LHS == RHS.
     * For example, if we have y2 == "str3"
     * and the equivalence classes are
     * { y2, (Concat ce m2) }
     * { "str3", (Concat abc x2) }
     * then y2 can't be equal to "str3".
     * Then add an assertion: (y2 == (Concat ce m2)) AND ("str3" == (Concat abc x2)) -> (y2 != "str3")
     */
    bool theory_str::new_eq_check(expr * lhs, expr * rhs) {
        ast_manager & m = get_manager();

        // skip this check if we defer consistency checking, as we can do it for every EQC in final check
        if (!opt_DeferEQCConsistencyCheck) {
            check_concat_len_in_eqc(lhs);
            check_concat_len_in_eqc(rhs);
        }

        // Now we iterate over all pairs of terms across both EQCs
        // and check whether we can show that any pair of distinct terms
        // cannot possibly be equal.
        // If that's the case, we assert an axiom to that effect and stop.

        expr * eqc_nn1 = lhs;
        do {
            expr * eqc_nn2 = rhs;
            do {
                TRACE("str", tout << "checking whether " << mk_pp(eqc_nn1, m) << " and " << mk_pp(eqc_nn2, m) << " can be equal" << std::endl;);
                // inconsistency check: value
                if (!can_two_nodes_eq(eqc_nn1, eqc_nn2)) {
                    TRACE("str", tout << "inconsistency detected: " << mk_pp(eqc_nn1, m) << " cannot be equal to " << mk_pp(eqc_nn2, m) << std::endl;);
                    expr_ref to_assert(mk_not(m, m.mk_eq(eqc_nn1, eqc_nn2)), m);
                    assert_axiom(to_assert);
                    // this shouldn't use the integer theory at all, so we don't allow the option of quick-return
                    return false;
                }
                if (!check_length_consistency(eqc_nn1, eqc_nn2)) {
                    TRACE("str", tout << "inconsistency detected: " << mk_pp(eqc_nn1, m) << " and " << mk_pp(eqc_nn2, m) << " have inconsistent lengths" << std::endl;);
                    if (opt_NoQuickReturn_IntegerTheory){
                        TRACE("str", tout << "continuing in new_eq_check() due to opt_NoQuickReturn_IntegerTheory" << std::endl;);
                    } else {
                        return false;
                    }
                }
                eqc_nn2 = get_eqc_next(eqc_nn2);
            } while (eqc_nn2 != rhs);
            eqc_nn1 = get_eqc_next(eqc_nn1);
        } while (eqc_nn1 != lhs);

        if (!contains_map.empty()) {
            check_contain_in_new_eq(lhs, rhs);
        }

        // okay, all checks here passed
        return true;
    }

    // support for user_smt_theory-style EQC handling

    app * theory_str::get_ast(theory_var v) {
        return get_enode(v)->get_expr();
    }

    theory_var theory_str::get_var(expr * n) const {
        if (!is_app(n)) {
            return null_theory_var;
        }
        if (ctx.e_internalized(to_app(n))) {
            enode * e = ctx.get_enode(to_app(n));
            return e->get_th_var(get_id());
        }
        return null_theory_var;
    }

    // simulate Z3_theory_get_eqc_next()
    expr * theory_str::get_eqc_next(expr * n) {
        theory_var v = get_var(n);
        if (v != null_theory_var) {
            theory_var r = m_find.next(v);
            return get_ast(r);
        }
        return n;
    }

    void theory_str::group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts) {
        expr * eqcNode = n;
        do {
            app * ast = to_app(eqcNode);
            if (u.str.is_concat(ast)) {
                expr * simConcat = simplify_concat(ast);
                if (simConcat != ast) {
                    if (u.str.is_concat(to_app(simConcat))) {
                        concats.insert(simConcat);
                    } else {
                        if (u.str.is_string(simConcat)) {
                            consts.insert(simConcat);
                        } else {
                            vars.insert(simConcat);
                        }
                    }
                } else {
                    concats.insert(simConcat);
                }
            } else if (u.str.is_string(ast)) {
                consts.insert(ast);
            } else {
                vars.insert(ast);
            }
            eqcNode = get_eqc_next(eqcNode);
        } while (eqcNode != n);
    }

    void theory_str::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        if (!u.str.is_concat(a_node)) {
            nodeList.push_back(node);
            return;
        } else {
            SASSERT(a_node->get_num_args() == 2);
            expr * leftArg = a_node->get_arg(0);
            expr * rightArg = a_node->get_arg(1);
            get_nodes_in_concat(leftArg, nodeList);
            get_nodes_in_concat(rightArg, nodeList);
        }
    }

    // previously Concat() in strTheory.cpp
    // Evaluates the concatenation (n1 . n2) with respect to
    // the current equivalence classes of n1 and n2.
    // Returns a constant string expression representing this concatenation
    // if one can be determined, or nullptr if this is not possible.
    expr * theory_str::eval_concat(expr * n1, expr * n2) {
        bool n1HasEqcValue = false;
        bool n2HasEqcValue = false;
        expr * v1 = get_eqc_value(n1, n1HasEqcValue);
        expr * v2 = get_eqc_value(n2, n2HasEqcValue);
        if (n1HasEqcValue && n2HasEqcValue) {
            zstring n1_str, n2_str;
            u.str.is_string(v1, n1_str);
            u.str.is_string(v2, n2_str);
            zstring result = n1_str + n2_str;
            return mk_string(result);
        } else if (n1HasEqcValue && !n2HasEqcValue) {
            zstring v1_str;
            u.str.is_string(v1, v1_str);
            if (v1_str.empty()) {
                return n2;
            }
        } else if (n2HasEqcValue && !n1HasEqcValue) {
            zstring v2_str;
            u.str.is_string(v2, v2_str);
            if (v2_str.empty()) {
                return n1;
            }
        }
        // give up
        return nullptr;
    }

    // trace code helper
    inline std::string rational_to_string_if_exists(const rational & x, bool x_exists) {
        if (x_exists) {
            return x.to_string();
        } else {
            return "?";
        }
    }

    /*
     * The inputs:
     *    ~ nn: non const node
     *    ~ eq_str: the equivalent constant string of nn
     *  Iterate the parent of all eqc nodes of nn, looking for:
     *    ~ concat node
     *  to see whether some concat nodes can be simplified.
     */
    void theory_str::simplify_parent(expr * nn, expr * eq_str) {
        ast_manager & m = get_manager();

        TRACE("str", tout << "simplifying parents of " << mk_ismt2_pp(nn, m)
              << " with respect to " << mk_ismt2_pp(eq_str, m) << std::endl;);

        ctx.internalize(nn, false);

        zstring eq_strValue;
        u.str.is_string(eq_str, eq_strValue);
        expr * n_eqNode = nn;
        do {
            enode * n_eq_enode = ctx.get_enode(n_eqNode);
            TRACE("str", tout << "considering all parents of " << mk_ismt2_pp(n_eqNode, m) << std::endl
                  << "associated n_eq_enode has " << n_eq_enode->get_num_parents() << " parents" << std::endl;);

            // the goal of this next bit is to avoid dereferencing a bogus e_parent in the following loop.
            // what I imagine is causing this bug is that, for example, we examine some parent, we add an axiom that involves it,
            // and the parent_it iterator becomes invalidated, because we indirectly modified the container that we're iterating over.

            enode_vector current_parents;
            for (auto &parent: n_eq_enode->get_parents()) {
                current_parents.insert(parent);
            }

            for (auto &e_parent : current_parents) {
                SASSERT(e_parent != nullptr);

                app * a_parent = e_parent->get_expr();
                TRACE("str", tout << "considering parent " << mk_ismt2_pp(a_parent, m) << std::endl;);

                if (u.str.is_concat(a_parent)) {
                    expr * arg0 = a_parent->get_arg(0);
                    expr * arg1 = a_parent->get_arg(1);

                    rational parentLen;
                    bool parentLen_exists = get_len_value(a_parent, parentLen);

                    if (arg0 == n_eq_enode->get_expr()) {
                        rational arg0Len, arg1Len;
                        bool arg0Len_exists = get_len_value(eq_str, arg0Len);
                        bool arg1Len_exists = get_len_value(arg1, arg1Len);

                        TRACE("str",
                              tout << "simplify_parent #1:" << std::endl
                              << "* parent = " << mk_ismt2_pp(a_parent, m) << std::endl
                              << "* |parent| = " << rational_to_string_if_exists(parentLen, parentLen_exists) << std::endl
                              << "* |arg0| = " << rational_to_string_if_exists(arg0Len, arg0Len_exists) << std::endl
                              << "* |arg1| = " << rational_to_string_if_exists(arg1Len, arg1Len_exists) << std::endl;
                              ); (void)arg0Len_exists;

                        if (parentLen_exists && !arg1Len_exists) {
                            TRACE("str", tout << "make up len for arg1" << std::endl;);
                            expr_ref implyL11(m.mk_and(ctx.mk_eq_atom(mk_strlen(a_parent), mk_int(parentLen)),
                                                       ctx.mk_eq_atom(mk_strlen(arg0), mk_int(arg0Len))), m);
                            rational makeUpLenArg1 = parentLen - arg0Len;
                            if (makeUpLenArg1.is_nonneg()) {
                                expr_ref implyR11(ctx.mk_eq_atom(mk_strlen(arg1), mk_int(makeUpLenArg1)), m);
                                assert_implication(implyL11, implyR11);
                            } else {
                                expr_ref neg(mk_not(m, implyL11), m);
                                assert_axiom(neg);
                            }
                        }

                        // (Concat n_eqNode arg1) /\ arg1 has eq const

                        expr * concatResult = eval_concat(eq_str, arg1);
                        if (concatResult != nullptr) {
                            bool arg1HasEqcValue = false;
                            expr * arg1Value = get_eqc_value(arg1, arg1HasEqcValue);
                            expr_ref implyL(m);
                            if (arg1 != arg1Value) {
                                expr_ref eq_ast1(m);
                                eq_ast1 = ctx.mk_eq_atom(n_eqNode, eq_str);
                                SASSERT(eq_ast1);

                                expr_ref eq_ast2(m);
                                eq_ast2 = ctx.mk_eq_atom(arg1, arg1Value);
                                SASSERT(eq_ast2);
                                implyL = m.mk_and(eq_ast1, eq_ast2);
                            } else {
                                implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                            }


                            if (!in_same_eqc(a_parent, concatResult)) {
                                expr_ref implyR(m);
                                implyR = ctx.mk_eq_atom(a_parent, concatResult);
                                SASSERT(implyR);

                                assert_implication(implyL, implyR);
                            }
                        } else if (u.str.is_concat(to_app(n_eqNode))) {
                            expr_ref simpleConcat(m);
                            simpleConcat = mk_concat(eq_str, arg1);
                            if (!in_same_eqc(a_parent, simpleConcat)) {
                                expr_ref implyL(m);
                                implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                                SASSERT(implyL);

                                expr_ref implyR(m);
                                implyR = ctx.mk_eq_atom(a_parent, simpleConcat);
                                SASSERT(implyR);
                                assert_implication(implyL, implyR);
                            }
                        }
                    } // if (arg0 == n_eq_enode->get_expr())

                    if (arg1 == n_eq_enode->get_expr()) {
                        rational arg0Len, arg1Len;
                        bool arg0Len_exists = get_len_value(arg0, arg0Len);
                        bool arg1Len_exists = get_len_value(eq_str, arg1Len);

                        TRACE("str",
                              tout << "simplify_parent #2:" << std::endl
                              << "* parent = " << mk_ismt2_pp(a_parent, m) << std::endl
                              << "* |parent| = " << rational_to_string_if_exists(parentLen, parentLen_exists) << std::endl
                              << "* |arg0| = " << rational_to_string_if_exists(arg0Len, arg0Len_exists) << std::endl
                              << "* |arg1| = " << rational_to_string_if_exists(arg1Len, arg1Len_exists) << std::endl;
                              ); (void)arg1Len_exists;

                        if (parentLen_exists && !arg0Len_exists) {
                            TRACE("str", tout << "make up len for arg0" << std::endl;);
                            expr_ref implyL11(m.mk_and(ctx.mk_eq_atom(mk_strlen(a_parent), mk_int(parentLen)),
                                                       ctx.mk_eq_atom(mk_strlen(arg1), mk_int(arg1Len))), m);
                            rational makeUpLenArg0 = parentLen - arg1Len;
                            if (makeUpLenArg0.is_nonneg()) {
                                expr_ref implyR11(ctx.mk_eq_atom(mk_strlen(arg0), mk_int(makeUpLenArg0)), m);
                                assert_implication(implyL11, implyR11);
                            } else {
                                expr_ref neg(mk_not(m, implyL11), m);
                                assert_axiom(neg);
                            }
                        }

                        // (Concat arg0 n_eqNode) /\ arg0 has eq const

                        expr * concatResult = eval_concat(arg0, eq_str);
                        if (concatResult != nullptr) {
                            bool arg0HasEqcValue = false;
                            expr * arg0Value = get_eqc_value(arg0, arg0HasEqcValue);
                            expr_ref implyL(m);
                            if (arg0 != arg0Value) {
                                expr_ref eq_ast1(m);
                                eq_ast1 = ctx.mk_eq_atom(n_eqNode, eq_str);
                                SASSERT(eq_ast1);
                                expr_ref eq_ast2(m);
                                eq_ast2 = ctx.mk_eq_atom(arg0, arg0Value);
                                SASSERT(eq_ast2);

                                implyL = m.mk_and(eq_ast1, eq_ast2);
                            } else {
                                implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                            }

                            if (!in_same_eqc(a_parent, concatResult)) {
                                expr_ref implyR(m);
                                implyR = ctx.mk_eq_atom(a_parent, concatResult);
                                SASSERT(implyR);

                                assert_implication(implyL, implyR);
                            }
                        } else if (u.str.is_concat(to_app(n_eqNode))) {
                            expr_ref simpleConcat(m);
                            simpleConcat = mk_concat(arg0, eq_str);
                            if (!in_same_eqc(a_parent, simpleConcat)) {
                                expr_ref implyL(m);
                                implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                                SASSERT(implyL);

                                expr_ref implyR(m);
                                implyR = ctx.mk_eq_atom(a_parent, simpleConcat);
                                SASSERT(implyR);
                                assert_implication(implyL, implyR);
                            }
                        }
                    } // if (arg1 == n_eq_enode->get_owner


                    //---------------------------------------------------------
                    // Case (2-1) begin: (Concat n_eqNode (Concat str var))
                    if (arg0 == n_eqNode && u.str.is_concat(to_app(arg1))) {
                        app * a_arg1 = to_app(arg1);
                        TRACE("str", tout << "simplify_parent #3" << std::endl;);
                        expr * r_concat_arg0 = a_arg1->get_arg(0);
                        if (u.str.is_string(r_concat_arg0)) {
                            expr * combined_str = eval_concat(eq_str, r_concat_arg0);
                            SASSERT(combined_str);
                            expr * r_concat_arg1 = a_arg1->get_arg(1);
                            expr_ref implyL(m);
                            implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                            expr * simplifiedAst = mk_concat(combined_str, r_concat_arg1);
                            if (!in_same_eqc(a_parent, simplifiedAst)) {
                                expr_ref implyR(m);
                                implyR = ctx.mk_eq_atom(a_parent, simplifiedAst);
                                assert_implication(implyL, implyR);
                            }
                        }
                    }
                    // Case (2-1) end: (Concat n_eqNode (Concat str var))
                    //---------------------------------------------------------


                    //---------------------------------------------------------
                    // Case (2-2) begin: (Concat (Concat var str) n_eqNode)
                    if (u.str.is_concat(to_app(arg0)) && arg1 == n_eqNode) {
                        app * a_arg0 = to_app(arg0);
                        TRACE("str", tout << "simplify_parent #4" << std::endl;);
                        expr * l_concat_arg1 = a_arg0->get_arg(1);
                        if (u.str.is_string(l_concat_arg1)) {
                            expr * combined_str = eval_concat(l_concat_arg1, eq_str);
                            SASSERT(combined_str);
                            expr * l_concat_arg0 = a_arg0->get_arg(0);
                            expr_ref implyL(m);
                            implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                            expr * simplifiedAst = mk_concat(l_concat_arg0, combined_str);
                            if (!in_same_eqc(a_parent, simplifiedAst)) {
                                expr_ref implyR(m);
                                implyR = ctx.mk_eq_atom(a_parent, simplifiedAst);
                                assert_implication(implyL, implyR);
                            }
                        }
                    }
                    // Case (2-2) end: (Concat (Concat var str) n_eqNode)
                    //---------------------------------------------------------

                    // Have to look up one more layer: if the parent of the concat is another concat
                    //-------------------------------------------------
                    // Case (3-1) begin: (Concat (Concat var n_eqNode) str )
                    if (arg1 == n_eqNode) {
                        expr_ref_vector concat_parents(m);
                        for (auto& e_concat_parent : e_parent->get_parents()) {
                            concat_parents.push_back(e_concat_parent->get_expr());
                        }
                        for (auto& _concat_parent : concat_parents) {
                            app* concat_parent = to_app(_concat_parent);
                            if (u.str.is_concat(concat_parent)) {
                                expr * concat_parent_arg0 = concat_parent->get_arg(0);
                                expr * concat_parent_arg1 = concat_parent->get_arg(1);
                                if (concat_parent_arg0 == a_parent && u.str.is_string(concat_parent_arg1)) {
                                    TRACE("str", tout << "simplify_parent #5" << std::endl;);
                                    expr * combinedStr = eval_concat(eq_str, concat_parent_arg1);
                                    SASSERT(combinedStr);
                                    expr_ref implyL(m);
                                    implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                                    expr * simplifiedAst = mk_concat(arg0, combinedStr);
                                    if (!in_same_eqc(concat_parent, simplifiedAst)) {
                                        expr_ref implyR(m);
                                        implyR = ctx.mk_eq_atom(concat_parent, simplifiedAst);
                                        assert_implication(implyL, implyR);
                                    }
                                }
                            }
                        }
                    }
                    // Case (3-1) end: (Concat (Concat var n_eqNode) str )
                    // Case (3-2) begin: (Concat str (Concat n_eqNode var) )
                    if (arg0 == n_eqNode) {
                        expr_ref_vector concat_parents(m);
                        for (auto& e_concat_parent : e_parent->get_parents()) {
                            concat_parents.push_back(e_concat_parent->get_expr());
                        }
                        for (auto& _concat_parent : concat_parents) {
                            app* concat_parent = to_app(_concat_parent);
                            if (u.str.is_concat(concat_parent)) {
                                expr * concat_parent_arg0 = concat_parent->get_arg(0);
                                expr * concat_parent_arg1 = concat_parent->get_arg(1);
                                if (concat_parent_arg1 == a_parent && u.str.is_string(concat_parent_arg0)) {
                                    TRACE("str", tout << "simplify_parent #6" << std::endl;);
                                    expr * combinedStr = eval_concat(concat_parent_arg0, eq_str);
                                    SASSERT(combinedStr);
                                    expr_ref implyL(m);
                                    implyL = ctx.mk_eq_atom(n_eqNode, eq_str);
                                    expr * simplifiedAst = mk_concat(combinedStr, arg1);
                                    if (!in_same_eqc(concat_parent, simplifiedAst)) {
                                        expr_ref implyR(m);
                                        implyR = ctx.mk_eq_atom(concat_parent, simplifiedAst);
                                        assert_implication(implyL, implyR);
                                    }
                                }
                            }
                        }
                    }
                    // Case (3-2) end: (Concat str (Concat n_eqNode var) )
                } // if is_concat(a_parent)
            } // for parent_it : n_eq_enode->begin_parents()


            // check next EQC member
            n_eqNode = get_eqc_next(n_eqNode);
        } while (n_eqNode != nn);
    }

    expr * theory_str::simplify_concat(expr * node) {
        ast_manager & m = get_manager();
        std::map<expr*, expr*> resolvedMap;
        ptr_vector<expr> argVec;
        get_nodes_in_concat(node, argVec);

        for (unsigned i = 0; i < argVec.size(); ++i) {
            bool vArgHasEqcValue = false;
            expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
            if (vArg != argVec[i]) {
                resolvedMap[argVec[i]] = vArg;
            }
        }

        if (resolvedMap.empty()) {
            // no simplification possible
            return node;
        } else {
            expr * resultAst = mk_string("");
            for (unsigned i = 0; i < argVec.size(); ++i) {
                bool vArgHasEqcValue = false;
                expr * vArg = get_eqc_value(argVec[i], vArgHasEqcValue);
                resultAst = mk_concat(resultAst, vArg);
            }
            TRACE("str", tout << mk_ismt2_pp(node, m) << " is simplified to " << mk_ismt2_pp(resultAst, m) << std::endl;);

            if (in_same_eqc(node, resultAst)) {
                TRACE("str", tout << "SKIP: both concats are already in the same equivalence class" << std::endl;);
            } else {
                expr_ref_vector items(m);
                int pos = 0;
                for (auto itor : resolvedMap) {
                    items.push_back(ctx.mk_eq_atom(itor.first, itor.second));
                    pos += 1;
                }
                expr_ref premise(mk_and(items), m);
                expr_ref conclusion(ctx.mk_eq_atom(node, resultAst), m);
                assert_implication(premise, conclusion);
            }
            return resultAst;
        }

    }

    // Modified signature of Z3str2's inferLenConcat().
    // Returns true iff nLen can be inferred by this method
    // (i.e. the equivalent of a len_exists flag in get_len_value()).

    bool theory_str::infer_len_concat(expr * n, rational & nLen) {
        ast_manager & m = get_manager();
        expr * arg0 = to_app(n)->get_arg(0);
        expr * arg1 = to_app(n)->get_arg(1);

        rational arg0_len, arg1_len;
        bool arg0_len_exists = get_len_value(arg0, arg0_len);
        bool arg1_len_exists = get_len_value(arg1, arg1_len);
        rational tmp_len;
        bool nLen_exists = get_len_value(n, tmp_len);

        if (arg0_len_exists && arg1_len_exists && !nLen_exists) {
            expr_ref_vector l_items(m);
            // if (mk_strlen(arg0) != mk_int(arg0_len)) {
            {
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(arg0), mk_int(arg0_len)));
            }

            // if (mk_strlen(arg1) != mk_int(arg1_len)) {
            {
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(arg1), mk_int(arg1_len)));
            }

            expr_ref axl(m.mk_and(l_items.size(), l_items.data()), m);
            rational nnLen = arg0_len + arg1_len;
            expr_ref axr(ctx.mk_eq_atom(mk_strlen(n), mk_int(nnLen)), m);
            TRACE("str", tout << "inferred (Length " << mk_pp(n, m) << ") = " << nnLen << std::endl;);
            assert_implication(axl, axr);
            nLen = nnLen;
            return true;
        } else {
            return false;
        }
    }

    void theory_str::infer_len_concat_arg(expr * n, rational len) {
        if (len.is_neg()) {
            return;
        }

        ast_manager & m = get_manager();

        expr * arg0 = to_app(n)->get_arg(0);
        expr * arg1 = to_app(n)->get_arg(1);
        rational arg0_len, arg1_len;
        bool arg0_len_exists = get_len_value(arg0, arg0_len);
        bool arg1_len_exists = get_len_value(arg1, arg1_len);

        expr_ref_vector l_items(m);
        expr_ref axr(m);
        axr.reset();

        // if (mk_length(t, n) != mk_int(ctx, len)) {
        {
            l_items.push_back(ctx.mk_eq_atom(mk_strlen(n), mk_int(len)));
        }

        if (!arg0_len_exists && arg1_len_exists) {
            //if (mk_length(t, arg1) != mk_int(ctx, arg1_len)) {
            {
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(arg1), mk_int(arg1_len)));
            }
            rational arg0Len = len - arg1_len;
            if (arg0Len.is_nonneg()) {
                axr = ctx.mk_eq_atom(mk_strlen(arg0), mk_int(arg0Len));
            } else {
                // could negate
            }
        } else if (arg0_len_exists && !arg1_len_exists) {
            //if (mk_length(t, arg0) != mk_int(ctx, arg0_len)) {
            {
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(arg0), mk_int(arg0_len)));
            }
            rational arg1Len = len - arg0_len;
            if (arg1Len.is_nonneg()) {
                axr = ctx.mk_eq_atom(mk_strlen(arg1), mk_int(arg1Len));
            } else {
                // could negate
            }
        } else {

        }

        if (axr) {
            expr_ref axl(m.mk_and(l_items.size(), l_items.data()), m);
            assert_implication(axl, axr);
        }
    }

    void theory_str::infer_len_concat_equality(expr * nn1, expr * nn2) {
        rational nnLen;
        bool nnLen_exists = get_len_value(nn1, nnLen);
        if (!nnLen_exists) {
            nnLen_exists = get_len_value(nn2, nnLen);
        }

        // case 1:
        //    Known: a1_arg0 and a1_arg1
        //    Unknown: nn1

        if (u.str.is_concat(to_app(nn1))) {
            rational nn1ConcatLen;
            bool nn1ConcatLen_exists = infer_len_concat(nn1, nn1ConcatLen);
            if (nnLen_exists && nn1ConcatLen_exists) {
                nnLen = nn1ConcatLen;
            }
        }

        // case 2:
        //    Known: a1_arg0 and a1_arg1
        //    Unknown: nn1

        if (u.str.is_concat(to_app(nn2))) {
            rational nn2ConcatLen;
            bool nn2ConcatLen_exists = infer_len_concat(nn2, nn2ConcatLen);
            if (nnLen_exists && nn2ConcatLen_exists) {
                nnLen = nn2ConcatLen;
            }
        }

        if (nnLen_exists) {
            if (u.str.is_concat(to_app(nn1))) {
                infer_len_concat_arg(nn1, nnLen);
            }
            if (u.str.is_concat(to_app(nn2))) {
                infer_len_concat_arg(nn2, nnLen);
            }
        }

        /*
          if (isConcatFunc(t, nn2)) {
          int nn2ConcatLen = inferLenConcat(t, nn2);
          if (nnLen == -1 && nn2ConcatLen != -1)
          nnLen = nn2ConcatLen;
          }

          if (nnLen != -1) {
          if (isConcatFunc(t, nn1)) {
          inferLenConcatArg(t, nn1, nnLen);
          }
          if (isConcatFunc(t, nn2)) {
          inferLenConcatArg(t, nn2, nnLen);
          }
          }
        */
    }

    void theory_str::add_theory_aware_branching_info(expr * term, double priority, lbool phase) {
        ctx.internalize(term, false);
        bool_var v = ctx.get_bool_var(term);
        ctx.add_theory_aware_branching_info(v, priority, phase);
    }

    void theory_str::generate_mutual_exclusion(expr_ref_vector & terms) {
        // pull each literal out of the arrangement disjunction
        literal_vector ls;
        for (expr * e : terms) {
            literal l = ctx.get_literal(e);
            ls.push_back(l);
        }
        ctx.mk_th_case_split(ls.size(), ls.data());
    }

    void theory_str::print_cut_var(expr * node, std::ofstream & xout) {
        ast_manager & m = get_manager();
        xout << "Cut info of " << mk_pp(node, m) << std::endl;
        if (cut_var_map.contains(node)) {
            if (!cut_var_map[node].empty()) {
                xout << "[" << cut_var_map[node].top()->level << "] ";
                for (auto const& kv : cut_var_map[node].top()->vars) {
                    xout << mk_pp(kv.m_key, m) << ", ";
                }
                xout << std::endl;
            }
        }
    }

    /*
     * Handle two equivalent Concats.
     */
    void theory_str::simplify_concat_equality(expr * nn1, expr * nn2) {
        ast_manager & m = get_manager();

        app * a_nn1 = to_app(nn1);
        SASSERT(a_nn1->get_num_args() == 2);
        app * a_nn2 = to_app(nn2);
        SASSERT(a_nn2->get_num_args() == 2);

        expr * a1_arg0 = a_nn1->get_arg(0);
        expr * a1_arg1 = a_nn1->get_arg(1);
        expr * a2_arg0 = a_nn2->get_arg(0);
        expr * a2_arg1 = a_nn2->get_arg(1);

        rational a1_arg0_len, a1_arg1_len, a2_arg0_len, a2_arg1_len;

        bool a1_arg0_len_exists = get_len_value(a1_arg0, a1_arg0_len);
        bool a1_arg1_len_exists = get_len_value(a1_arg1, a1_arg1_len);
        bool a2_arg0_len_exists = get_len_value(a2_arg0, a2_arg0_len);
        bool a2_arg1_len_exists = get_len_value(a2_arg1, a2_arg1_len);

        TRACE("str", tout << "nn1 = " << mk_ismt2_pp(nn1, m) << std::endl
              << "nn2 = " << mk_ismt2_pp(nn2, m) << std::endl;);

        TRACE("str", tout
              << "len(" << mk_pp(a1_arg0, m) << ") = " << (a1_arg0_len_exists ? a1_arg0_len.to_string() : "?") << std::endl
              << "len(" << mk_pp(a1_arg1, m) << ") = " << (a1_arg1_len_exists ? a1_arg1_len.to_string() : "?") << std::endl
              << "len(" << mk_pp(a2_arg0, m) << ") = " << (a2_arg0_len_exists ? a2_arg0_len.to_string() : "?") << std::endl
              << "len(" << mk_pp(a2_arg1, m) << ") = " << (a2_arg1_len_exists ? a2_arg1_len.to_string() : "?") << std::endl
              << std::endl;);

        infer_len_concat_equality(nn1, nn2);

        if (a1_arg0 == a2_arg0) {
            if (!in_same_eqc(a1_arg1, a2_arg1)) {
                expr_ref premise(ctx.mk_eq_atom(nn1, nn2), m);
                expr_ref eq1(ctx.mk_eq_atom(a1_arg1, a2_arg1), m);
                expr_ref eq2(ctx.mk_eq_atom(mk_strlen(a1_arg1), mk_strlen(a2_arg1)), m);
                expr_ref conclusion(m.mk_and(eq1, eq2), m);
                assert_implication(premise, conclusion);
            }
            TRACE("str", tout << "SKIP: a1_arg0 == a2_arg0" << std::endl;);
            return;
        }

        if (a1_arg1 == a2_arg1) {
            if (!in_same_eqc(a1_arg0, a2_arg0)) {
                expr_ref premise(ctx.mk_eq_atom(nn1, nn2), m);
                expr_ref eq1(ctx.mk_eq_atom(a1_arg0, a2_arg0), m);
                expr_ref eq2(ctx.mk_eq_atom(mk_strlen(a1_arg0), mk_strlen(a2_arg0)), m);
                expr_ref conclusion(m.mk_and(eq1, eq2), m);
                assert_implication(premise, conclusion);
            }
            TRACE("str", tout << "SKIP: a1_arg1 == a2_arg1" << std::endl;);
            return;
        }

        // quick path

        if (in_same_eqc(a1_arg0, a2_arg0)) {
            if (in_same_eqc(a1_arg1, a2_arg1)) {
                TRACE("str", tout << "SKIP: a1_arg0 =~ a2_arg0 and a1_arg1 =~ a2_arg1" << std::endl;);
                return;
            } else {
                TRACE("str", tout << "quick path 1-1: a1_arg0 =~ a2_arg0" << std::endl;);
                expr_ref premise(m.mk_and(ctx.mk_eq_atom(nn1, nn2), ctx.mk_eq_atom(a1_arg0, a2_arg0)), m);
                expr_ref conclusion(m.mk_and(ctx.mk_eq_atom(a1_arg1, a2_arg1), ctx.mk_eq_atom(mk_strlen(a1_arg1), mk_strlen(a2_arg1))), m);
                assert_implication(premise, conclusion);
                return;
            }
        } else {
            if (in_same_eqc(a1_arg1, a2_arg1)) {
                TRACE("str", tout << "quick path 1-2: a1_arg1 =~ a2_arg1" << std::endl;);
                expr_ref premise(m.mk_and(ctx.mk_eq_atom(nn1, nn2), ctx.mk_eq_atom(a1_arg1, a2_arg1)), m);
                expr_ref conclusion(m.mk_and(ctx.mk_eq_atom(a1_arg0, a2_arg0), ctx.mk_eq_atom(mk_strlen(a1_arg0), mk_strlen(a2_arg0))), m);
                assert_implication(premise, conclusion);
                return;
            }
        }

        // quick path 2-1
        if (a1_arg0_len_exists && a2_arg0_len_exists && a1_arg0_len == a2_arg0_len) {
            if (!in_same_eqc(a1_arg0, a2_arg0)) {
                TRACE("str", tout << "quick path 2-1: len(nn1.arg0) == len(nn2.arg0)" << std::endl;);
                expr_ref ax_l1(ctx.mk_eq_atom(nn1, nn2), m);
                expr_ref ax_l2(ctx.mk_eq_atom(mk_strlen(a1_arg0), mk_strlen(a2_arg0)), m);
                expr_ref ax_r1(ctx.mk_eq_atom(a1_arg0, a2_arg0), m);
                expr_ref ax_r2(ctx.mk_eq_atom(a1_arg1, a2_arg1), m);

                expr_ref premise(m.mk_and(ax_l1, ax_l2), m);
                expr_ref conclusion(m.mk_and(ax_r1, ax_r2), m);

                assert_implication(premise, conclusion);

                if (opt_NoQuickReturn_IntegerTheory) {
                    TRACE("str", tout << "bypassing quick return from the end of this case" << std::endl;);
                } else {
                    return;
                }
            }
        }

        if (a1_arg1_len_exists && a2_arg1_len_exists && a1_arg1_len == a2_arg1_len) {
            if (!in_same_eqc(a1_arg1, a2_arg1)) {
                TRACE("str", tout << "quick path 2-2: len(nn1.arg1) == len(nn2.arg1)" << std::endl;);
                expr_ref ax_l1(ctx.mk_eq_atom(nn1, nn2), m);
                expr_ref ax_l2(ctx.mk_eq_atom(mk_strlen(a1_arg1), mk_strlen(a2_arg1)), m);
                expr_ref ax_r1(ctx.mk_eq_atom(a1_arg0, a2_arg0), m);
                expr_ref ax_r2(ctx.mk_eq_atom(a1_arg1, a2_arg1), m);

                expr_ref premise(m.mk_and(ax_l1, ax_l2), m);
                expr_ref conclusion(m.mk_and(ax_r1, ax_r2), m);

                assert_implication(premise, conclusion);
                if (opt_NoQuickReturn_IntegerTheory) {
                    TRACE("str", tout << "bypassing quick return from the end of this case" << std::endl;);
                } else {
                    return;
                }
            }
        }

        expr_ref new_nn1(simplify_concat(nn1), m);
        expr_ref new_nn2(simplify_concat(nn2), m);
        app * a_new_nn1 = to_app(new_nn1);
        app * a_new_nn2 = to_app(new_nn2);

        TRACE("str", tout << "new_nn1 = " << mk_ismt2_pp(new_nn1, m) << std::endl
              << "new_nn2 = " << mk_ismt2_pp(new_nn2, m) << std::endl;);

        if (new_nn1 == new_nn2) {
            TRACE("str", tout << "equal concats, return" << std::endl;);
            return;
        }

        if (!can_two_nodes_eq(new_nn1, new_nn2)) {
            expr_ref detected(mk_not(m, ctx.mk_eq_atom(new_nn1, new_nn2)), m);
            TRACE("str", tout << "inconsistency detected: " << mk_ismt2_pp(detected, m) << std::endl;);
            assert_axiom(detected);
            return;
        }

        // check whether new_nn1 and new_nn2 are still concats

        bool n1IsConcat = u.str.is_concat(a_new_nn1);
        bool n2IsConcat = u.str.is_concat(a_new_nn2);
        if (!n1IsConcat && n2IsConcat) {
            TRACE("str", tout << "nn1_new is not a concat" << std::endl;);
            if (u.str.is_string(a_new_nn1)) {
                simplify_parent(new_nn2, new_nn1);
            }
            return;
        } else if (n1IsConcat && !n2IsConcat) {
            TRACE("str", tout << "nn2_new is not a concat" << std::endl;);
            if (u.str.is_string(a_new_nn2)) {
                simplify_parent(new_nn1, new_nn2);
            }
            return;
        } else if (!n1IsConcat && !n2IsConcat) {
            // normally this should never happen, because group_terms_by_eqc() should have pre-simplified
            // as much as possible. however, we make a defensive check here just in case
            TRACE("str", tout << "WARNING: nn1_new and nn2_new both simplify to non-concat terms" << std::endl;);
            return;
        }

        expr * v1_arg0 = a_new_nn1->get_arg(0);
        expr * v1_arg1 = a_new_nn1->get_arg(1);
        expr * v2_arg0 = a_new_nn2->get_arg(0);
        expr * v2_arg1 = a_new_nn2->get_arg(1);

        if (!in_same_eqc(new_nn1, new_nn2) && (nn1 != new_nn1 || nn2 != new_nn2)) {
            int ii4 = 0;
            expr* item[3];
            if (nn1 != new_nn1) {
                item[ii4++] = ctx.mk_eq_atom(nn1, new_nn1);
            }
            if (nn2 != new_nn2) {
                item[ii4++] = ctx.mk_eq_atom(nn2, new_nn2);
            }
            item[ii4++] = ctx.mk_eq_atom(nn1, nn2);
            expr_ref premise(m.mk_and(ii4, item), m);
            expr_ref conclusion(ctx.mk_eq_atom(new_nn1, new_nn2), m);
            assert_implication(premise, conclusion);
        }

        // start to split both concats
        check_and_init_cut_var(v1_arg0);
        check_and_init_cut_var(v1_arg1);
        check_and_init_cut_var(v2_arg0);
        check_and_init_cut_var(v2_arg1);

        //*************************************************************
              // case 1: concat(x, y) = concat(m, n)
              //*************************************************************
                    if (is_concat_eq_type1(new_nn1, new_nn2)) {
                        process_concat_eq_type1(new_nn1, new_nn2);
                        return;
                    }

        //*************************************************************
              // case 2: concat(x, y) = concat(m, "str")
              //*************************************************************
                    if (is_concat_eq_type2(new_nn1, new_nn2)) {
                        process_concat_eq_type2(new_nn1, new_nn2);
                        return;
                    }

        //*************************************************************
              // case 3: concat(x, y) = concat("str", n)
              //*************************************************************
                    if (is_concat_eq_type3(new_nn1, new_nn2)) {
                        process_concat_eq_type3(new_nn1, new_nn2);
                        return;
                    }

        //*************************************************************
              //  case 4: concat("str1", y) = concat("str2", n)
              //*************************************************************
                    if (is_concat_eq_type4(new_nn1, new_nn2)) {
                        process_concat_eq_type4(new_nn1, new_nn2);
                        return;
                    }

        //*************************************************************
              //  case 5: concat(x, "str1") = concat(m, "str2")
              //*************************************************************
                    if (is_concat_eq_type5(new_nn1, new_nn2)) {
                        process_concat_eq_type5(new_nn1, new_nn2);
                        return;
                    }
        //*************************************************************
              //  case 6: concat("str1", y) = concat(m, "str2")
              //*************************************************************
                    if (is_concat_eq_type6(new_nn1, new_nn2)) {
                        process_concat_eq_type6(new_nn1, new_nn2);
                        return;
                    }

    }

    /*
     * Returns true if attempting to process a concat equality between lhs and rhs
     * will result in overlapping variables (false otherwise).
     */
    bool theory_str::will_result_in_overlap(expr * lhs, expr * rhs) {
        ast_manager & m = get_manager();

        expr_ref new_nn1(simplify_concat(lhs), m);
        expr_ref new_nn2(simplify_concat(rhs), m);
        app * a_new_nn1 = to_app(new_nn1);
        app * a_new_nn2 = to_app(new_nn2);

        bool n1IsConcat = u.str.is_concat(a_new_nn1);
        bool n2IsConcat = u.str.is_concat(a_new_nn2);
        if (!n1IsConcat && !n2IsConcat) {
            // we simplified both sides to non-concat expressions...
            return false;
        }

        expr * v1_arg0 = a_new_nn1->get_arg(0);
        expr * v1_arg1 = a_new_nn1->get_arg(1);
        expr * v2_arg0 = a_new_nn2->get_arg(0);
        expr * v2_arg1 = a_new_nn2->get_arg(1);

        TRACE("str", tout << "checking whether " << mk_pp(new_nn1, m) << " and " << mk_pp(new_nn1, m) << " might overlap." << std::endl;);

        check_and_init_cut_var(v1_arg0);
        check_and_init_cut_var(v1_arg1);
        check_and_init_cut_var(v2_arg0);
        check_and_init_cut_var(v2_arg1);

        //*************************************************************
              // case 1: concat(x, y) = concat(m, n)
              //*************************************************************
                    if (is_concat_eq_type1(new_nn1, new_nn2)) {
                        TRACE("str", tout << "Type 1 check." << std::endl;);
                        expr * x = to_app(new_nn1)->get_arg(0);
                        expr * y = to_app(new_nn1)->get_arg(1);
                        expr * m = to_app(new_nn2)->get_arg(0);
                        expr * n = to_app(new_nn2)->get_arg(1);

                        if (has_self_cut(m, y)) {
                            TRACE("str", tout << "Possible overlap found" << std::endl; print_cut_var(m, tout); print_cut_var(y, tout););
                            return true;
                        } else if (has_self_cut(x, n)) {
                            TRACE("str", tout << "Possible overlap found" << std::endl; print_cut_var(x, tout); print_cut_var(n, tout););
                            return true;
                        } else {
                            return false;
                        }
                    }

        //*************************************************************
              // case 2: concat(x, y) = concat(m, "str")
              //*************************************************************
                    if (is_concat_eq_type2(new_nn1, new_nn2)) {

                        expr * y = nullptr;
                        expr * m = nullptr;
                        expr * v1_arg0 = to_app(new_nn1)->get_arg(0);
                        expr * v1_arg1 = to_app(new_nn1)->get_arg(1);
                        expr * v2_arg0 = to_app(new_nn2)->get_arg(0);
                        expr * v2_arg1 = to_app(new_nn2)->get_arg(1);

                        if (u.str.is_string(v1_arg1) && !u.str.is_string(v2_arg1)) {
                            m = v1_arg0;
                            y = v2_arg1;
                        } else {
                            m = v2_arg0;
                            y = v1_arg1;
                        }

                        if (has_self_cut(m, y)) {
                            TRACE("str", tout << "Possible overlap found" << std::endl; print_cut_var(m, tout); print_cut_var(y, tout););
                            return true;
                        } else {
                            return false;
                        }
                    }

        //*************************************************************
              // case 3: concat(x, y) = concat("str", n)
              //*************************************************************
                    if (is_concat_eq_type3(new_nn1, new_nn2)) {
                        expr * v1_arg0 = to_app(new_nn1)->get_arg(0);
                        expr * v1_arg1 = to_app(new_nn1)->get_arg(1);
                        expr * v2_arg0 = to_app(new_nn2)->get_arg(0);
                        expr * v2_arg1 = to_app(new_nn2)->get_arg(1);

                        expr * x = nullptr;
                        expr * n = nullptr;

                        if (u.str.is_string(v1_arg0) && !u.str.is_string(v2_arg0)) {
                            n = v1_arg1;
                            x = v2_arg0;
                        } else {
                            n = v2_arg1;
                            x = v1_arg0;
                        }
                        if (has_self_cut(x, n)) {
                            TRACE("str", tout << "Possible overlap found" << std::endl; print_cut_var(x, tout); print_cut_var(n, tout););
                            return true;
                        } else {
                            return false;
                        }
                    }

        //*************************************************************
              //  case 4: concat("str1", y) = concat("str2", n)
              //*************************************************************
                    if (is_concat_eq_type4(new_nn1, new_nn2)) {
                        // This case can never result in an overlap.
                        return false;
                    }

        //*************************************************************
              //  case 5: concat(x, "str1") = concat(m, "str2")
              //*************************************************************
                    if (is_concat_eq_type5(new_nn1, new_nn2)) {
                        // This case can never result in an overlap.
                        return false;
                    }
        //*************************************************************
              //  case 6: concat("str1", y) = concat(m, "str2")
              //*************************************************************
                    if (is_concat_eq_type6(new_nn1, new_nn2)) {
                        expr * v1_arg0 = to_app(new_nn1)->get_arg(0);
                        expr * v1_arg1 = to_app(new_nn1)->get_arg(1);
                        expr * v2_arg0 = to_app(new_nn2)->get_arg(0);
                        expr * v2_arg1 = to_app(new_nn2)->get_arg(1);

                        expr * y = nullptr;
                        expr * m = nullptr;

                        if (u.str.is_string(v1_arg0)) {
                            y = v1_arg1;
                            m = v2_arg0;
                        } else {
                            y = v2_arg1;
                            m = v1_arg0;
                        }
                        if (has_self_cut(m, y)) {
                            TRACE("str", tout << "Possible overlap found" << std::endl; print_cut_var(m, tout); print_cut_var(y, tout););
                            return true;
                        } else {
                            return false;
                        }
                    }

        TRACE("str", tout << "warning: unrecognized concat case" << std::endl;);
        return false;
    }

    /*************************************************************
     * Type 1: concat(x, y) = concat(m, n)
     *         x, y, m and n all variables
     *************************************************************/
    bool theory_str::is_concat_eq_type1(expr * concatAst1, expr * concatAst2) {
        expr * x = to_app(concatAst1)->get_arg(0);
        expr * y = to_app(concatAst1)->get_arg(1);
        expr * m = to_app(concatAst2)->get_arg(0);
        expr * n = to_app(concatAst2)->get_arg(1);

        if (!u.str.is_string(x) && !u.str.is_string(y) && !u.str.is_string(m) && !u.str.is_string(n)) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::process_concat_eq_type1(expr * concatAst1, expr * concatAst2) {
        ast_manager & mgr = get_manager();

        bool overlapAssumptionUsed = false;

        TRACE("str", tout << "process_concat_eq TYPE 1" << std::endl
              << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
              << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
              );

        if (!u.str.is_concat(to_app(concatAst1))) {
            TRACE("str", tout << "concatAst1 is not a concat function" << std::endl;);
            return;
        }
        if (!u.str.is_concat(to_app(concatAst2))) {
            TRACE("str", tout << "concatAst2 is not a concat function" << std::endl;);
            return;
        }
        expr * x = to_app(concatAst1)->get_arg(0);
        expr * y = to_app(concatAst1)->get_arg(1);
        expr * m = to_app(concatAst2)->get_arg(0);
        expr * n = to_app(concatAst2)->get_arg(1);

        rational x_len, y_len, m_len, n_len;
        bool x_len_exists = get_len_value(x, x_len);
        bool y_len_exists = get_len_value(y, y_len);
        bool m_len_exists = get_len_value(m, m_len);
        bool n_len_exists = get_len_value(n, n_len);

        int splitType = -1;
        if (x_len_exists && m_len_exists) {
            TRACE("str", tout << "length values found: x/m" << std::endl;);
            if (x_len < m_len) {
                splitType = 0;
            } else if (x_len == m_len) {
                splitType = 1;
            } else {
                splitType = 2;
            }
        }

        if (splitType == -1 && y_len_exists && n_len_exists) {
            TRACE("str", tout << "length values found: y/n" << std::endl;);
            if (y_len > n_len) {
                splitType = 0;
            } else if (y_len == n_len) {
                splitType = 1;
            } else {
                splitType = 2;
            }
        }

        TRACE("str", tout
              << "len(x) = " << (x_len_exists ? x_len.to_string() : "?") << std::endl
              << "len(y) = " << (y_len_exists ? y_len.to_string() : "?") << std::endl
              << "len(m) = " << (m_len_exists ? m_len.to_string() : "?") << std::endl
              << "len(n) = " << (n_len_exists ? n_len.to_string() : "?") << std::endl
              << "split type " << splitType << std::endl;
              );

        expr_ref t1(mgr), t2(mgr);
        expr * xorFlag = nullptr;

        std::pair<expr*, expr*> key1(concatAst1, concatAst2);
        std::pair<expr*, expr*> key2(concatAst2, concatAst1);

        // check the entries in this map to make sure they're still in scope
        // before we use them.

        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry1 = varForBreakConcat.find(key1);
        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry2 = varForBreakConcat.find(key2);

        bool entry1InScope;
        if (entry1 == varForBreakConcat.end()) {
            entry1InScope = false;
        } else {
            if (internal_variable_set.find((entry1->second)[0]) == internal_variable_set.end()
                || internal_variable_set.find((entry1->second)[1]) == internal_variable_set.end()
                /*|| internal_variable_set.find((entry1->second)[2]) == internal_variable_set.end() */) {
                entry1InScope = false;
            } else {
                entry1InScope = true;
            }
        }

        bool entry2InScope;
        if (entry2 == varForBreakConcat.end()) {
            entry2InScope = false;
        } else {
            if (internal_variable_set.find((entry2->second)[0]) == internal_variable_set.end()
                || internal_variable_set.find((entry2->second)[1]) == internal_variable_set.end()
                /* || internal_variable_set.find((entry2->second)[2]) == internal_variable_set.end() */) {
                entry2InScope = false;
            } else {
                entry2InScope = true;
            }
        }

        TRACE("str", tout << "entry 1 " << (entry1InScope ? "in scope" : "not in scope") << std::endl
              << "entry 2 " << (entry2InScope ? "in scope" : "not in scope") << std::endl;);

        if (!entry1InScope && !entry2InScope) {
            t1 = mk_nonempty_str_var();
            t2 = mk_nonempty_str_var();
            xorFlag = mk_internal_xor_var();
            check_and_init_cut_var(t1);
            check_and_init_cut_var(t2);
            varForBreakConcat[key1][0] = t1;
            varForBreakConcat[key1][1] = t2;
            varForBreakConcat[key1][2] = xorFlag;
        } else {
            // match found
            if (entry1InScope) {
                t1 = varForBreakConcat[key1][0];
                t2 = varForBreakConcat[key1][1];
                xorFlag = varForBreakConcat[key1][2];
            } else {
                t1 = varForBreakConcat[key2][0];
                t2 = varForBreakConcat[key2][1];
                xorFlag = varForBreakConcat[key2][2];
            }
            refresh_theory_var(t1);
            add_nonempty_constraint(t1);
            refresh_theory_var(t2);
            add_nonempty_constraint(t2);
        }

        // For split types 0 through 2, we can get away with providing
        // fewer split options since more length information is available.
        if (splitType == 0) {
            //--------------------------------------
            // Type 0: M cuts Y.
            //   len(x) < len(m) || len(y) > len(n)
            //--------------------------------------
            expr_ref_vector ax_l_items(mgr);
            expr_ref_vector ax_r_items(mgr);

            ax_l_items.push_back(ctx.mk_eq_atom(concatAst1, concatAst2));

            expr_ref x_t1(mk_concat(x, t1), mgr);
            expr_ref t1_n(mk_concat(t1, n), mgr);

            ax_r_items.push_back(ctx.mk_eq_atom(m, x_t1));
            ax_r_items.push_back(ctx.mk_eq_atom(y, t1_n));

            if (m_len_exists && x_len_exists) {
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_int(x_len)));
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(m), mk_int(m_len)));
                rational m_sub_x = m_len - x_len;
                ax_r_items.push_back(ctx.mk_eq_atom(mk_strlen(t1), mk_int(m_sub_x)));
            } else {
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(y_len)));
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(n), mk_int(n_len)));
                rational y_sub_n = y_len - n_len;
                ax_r_items.push_back(ctx.mk_eq_atom(mk_strlen(t1), mk_int(y_sub_n)));
            }

            expr_ref ax_l(mk_and(ax_l_items), mgr);
            expr_ref ax_r(mk_and(ax_r_items), mgr);

            if (!has_self_cut(m, y)) {
                // Cut Info
                add_cut_info_merge(t1, sLevel, m);
                add_cut_info_merge(t1, sLevel, y);

                if (m_params.m_StrongArrangements) {
                    expr_ref ax_strong(ctx.mk_eq_atom(ax_l, ax_r), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(ax_l, ax_r);
                }
            } else {
                loopDetected = true;
                TRACE("str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
                TRACE("str", {print_cut_var(m, tout); print_cut_var(y, tout);});

                if (!overlapAssumptionUsed) {
                    overlapAssumptionUsed = true;
                    assert_implication(ax_l, m_theoryStrOverlapAssumption_term);
                }
            }
        } else if (splitType == 1) {
            // Type 1:
            //   len(x) = len(m) || len(y) = len(n)
            expr_ref ax_l1(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
            expr_ref ax_l2(mgr.mk_or(ctx.mk_eq_atom(mk_strlen(x), mk_strlen(m)), ctx.mk_eq_atom(mk_strlen(y), mk_strlen(n))), mgr);
            expr_ref ax_l(mgr.mk_and(ax_l1, ax_l2), mgr);
            expr_ref ax_r(mgr.mk_and(ctx.mk_eq_atom(x,m), ctx.mk_eq_atom(y,n)), mgr);
            assert_implication(ax_l, ax_r);
        } else if (splitType == 2) {
            // Type 2: X cuts N.
            //   len(x) > len(m) || len(y) < len(n)
            expr_ref m_t2(mk_concat(m, t2), mgr);
            expr_ref t2_y(mk_concat(t2, y), mgr);

            expr_ref_vector ax_l_items(mgr);
            ax_l_items.push_back(ctx.mk_eq_atom(concatAst1, concatAst2));

            expr_ref_vector ax_r_items(mgr);
            ax_r_items.push_back(ctx.mk_eq_atom(x, m_t2));
            ax_r_items.push_back(ctx.mk_eq_atom(t2_y, n));

            if (m_len_exists && x_len_exists) {
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_int(x_len)));
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(m), mk_int(m_len)));
                rational x_sub_m = x_len - m_len;
                ax_r_items.push_back(ctx.mk_eq_atom(mk_strlen(t2), mk_int(x_sub_m)));
            } else {
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(y_len)));
                ax_l_items.push_back(ctx.mk_eq_atom(mk_strlen(n), mk_int(n_len)));
                rational n_sub_y = n_len - y_len;
                ax_r_items.push_back(ctx.mk_eq_atom(mk_strlen(t2), mk_int(n_sub_y)));
            }

            expr_ref ax_l(mk_and(ax_l_items), mgr);
            expr_ref ax_r(mk_and(ax_r_items), mgr);

            if (!has_self_cut(x, n)) {
                // Cut Info
                add_cut_info_merge(t2, sLevel, x);
                add_cut_info_merge(t2, sLevel, n);

                if (m_params.m_StrongArrangements) {
                    expr_ref ax_strong(ctx.mk_eq_atom(ax_l, ax_r), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(ax_l, ax_r);
                }
            } else {
                loopDetected = true;

                TRACE("str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
                TRACE("str", {print_cut_var(m, tout); print_cut_var(y, tout);});

                if (!overlapAssumptionUsed) {
                    overlapAssumptionUsed = true;
                    assert_implication(ax_l, m_theoryStrOverlapAssumption_term);
                }

            }
        } else if (splitType == -1) {
            // Here we don't really have a choice. We have no length information at all...

            // This vector will eventually contain one term for each possible arrangement we explore.
            expr_ref_vector arrangement_disjunction(mgr);

            // break option 1: m cuts y
            // len(x) < len(m) || len(y) > len(n)
            if (!avoidLoopCut || !has_self_cut(m, y)) {
                expr_ref_vector and_item(mgr);
                // break down option 1-1
                expr_ref x_t1(mk_concat(x, t1), mgr);
                expr_ref t1_n(mk_concat(t1, n), mgr);

                and_item.push_back(ctx.mk_eq_atom(m, x_t1));
                and_item.push_back(ctx.mk_eq_atom(y, t1_n));

                expr_ref x_plus_t1(m_autil.mk_add(mk_strlen(x), mk_strlen(t1)), mgr);
                and_item.push_back(ctx.mk_eq_atom(mk_strlen(m), x_plus_t1));
                // These were crashing the solver because the integer theory
                // expects a constant on the right-hand side.
                // The things we want to assert here are len(m) > len(x) and len(y) > len(n).
                // We rewrite A > B as A-B > 0 and then as not(A-B <= 0),
                // and then, *because we aren't allowed to use subtraction*,
                // as not(A + -1*B <= 0)
                and_item.push_back(
                    mgr.mk_not(m_autil.mk_le(
                                   m_autil.mk_add(mk_strlen(m), m_autil.mk_mul(mk_int(-1), mk_strlen(x))),
                                   mk_int(0))) );
                and_item.push_back(
                    mgr.mk_not(m_autil.mk_le(
                                   m_autil.mk_add(mk_strlen(y),m_autil.mk_mul(mk_int(-1), mk_strlen(n))),
                                   mk_int(0))) );

                expr_ref option1(mk_and(and_item), mgr);
                arrangement_disjunction.push_back(option1);
                add_theory_aware_branching_info(option1, 0.1, l_true);

                add_cut_info_merge(t1, ctx.get_scope_level(), m);
                add_cut_info_merge(t1, ctx.get_scope_level(), y);
            } else {
                loopDetected = true;

                TRACE("str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
                TRACE("str", {print_cut_var(m, tout); print_cut_var(y, tout);});

                if (!overlapAssumptionUsed) {
                    overlapAssumptionUsed = true;
                    arrangement_disjunction.push_back(m_theoryStrOverlapAssumption_term);
                }

            }

            // break option 2:
            // x = m . t2
            // n = t2 . y
            if (!avoidLoopCut || !has_self_cut(x, n)) {
                expr_ref_vector and_item(mgr);
                // break down option 1-2
                expr_ref m_t2(mk_concat(m, t2), mgr);
                expr_ref t2_y(mk_concat(t2, y), mgr);

                and_item.push_back(ctx.mk_eq_atom(x, m_t2));
                and_item.push_back(ctx.mk_eq_atom(n, t2_y));


                expr_ref m_plus_t2(m_autil.mk_add(mk_strlen(m), mk_strlen(t2)), mgr);

                and_item.push_back(ctx.mk_eq_atom(mk_strlen(x), m_plus_t2));
                // want len(x) > len(m) and len(n) > len(y)
                and_item.push_back(
                    mgr.mk_not(m_autil.mk_le(
                                   m_autil.mk_add(mk_strlen(x), m_autil.mk_mul(mk_int(-1), mk_strlen(m))),
                                   mk_int(0))) );
                and_item.push_back(
                    mgr.mk_not(m_autil.mk_le(
                                   m_autil.mk_add(mk_strlen(n), m_autil.mk_mul(mk_int(-1), mk_strlen(y))),
                                   mk_int(0))) );

                expr_ref option2(mk_and(and_item), mgr);
                arrangement_disjunction.push_back(option2);
                add_theory_aware_branching_info(option2, 0.1, l_true);

                add_cut_info_merge(t2, ctx.get_scope_level(), x);
                add_cut_info_merge(t2, ctx.get_scope_level(), n);
            } else {
                loopDetected = true;

                TRACE("str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
                TRACE("str", {print_cut_var(x, tout); print_cut_var(n, tout);});

                if (!overlapAssumptionUsed) {
                    overlapAssumptionUsed = true;
                    arrangement_disjunction.push_back(m_theoryStrOverlapAssumption_term);
                }

            }

            // option 3:
            // x = m, y = n
            if (can_two_nodes_eq(x, m) && can_two_nodes_eq(y, n)) {
                expr_ref_vector and_item(mgr);

                and_item.push_back(ctx.mk_eq_atom(x, m));
                and_item.push_back(ctx.mk_eq_atom(y, n));
                and_item.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_strlen(m)));
                and_item.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_strlen(n)));

                expr_ref option3(mk_and(and_item), mgr);
                arrangement_disjunction.push_back(option3);
                // prioritize this case, it is easier
                add_theory_aware_branching_info(option3, 0.5, l_true);
            }

            if (!arrangement_disjunction.empty()) {
                expr_ref premise(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
                expr_ref conclusion(mk_or(arrangement_disjunction), mgr);
                if (m_params.m_StrongArrangements) {
                    expr_ref ax_strong(ctx.mk_eq_atom(premise, conclusion), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(premise, conclusion);
                }
                // assert mutual exclusion between each branch of the arrangement
                generate_mutual_exclusion(arrangement_disjunction);
            } else {
                TRACE("str", tout << "STOP: no split option found for two EQ concats." << std::endl;);
            }
        } // (splitType == -1)
    }

    /*************************************************************
     * Type 2: concat(x, y) = concat(m, "str")
     *************************************************************/
    bool theory_str::is_concat_eq_type2(expr * concatAst1, expr * concatAst2) {
        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        if ((!u.str.is_string(v1_arg0)) && u.str.is_string(v1_arg1)
            && (!u.str.is_string(v2_arg0)) && (!u.str.is_string(v2_arg1))) {
            return true;
        } else if ((!u.str.is_string(v2_arg0)) && u.str.is_string(v2_arg1)
                   && (!u.str.is_string(v1_arg0)) && (!u.str.is_string(v1_arg1))) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::process_concat_eq_type2(expr * concatAst1, expr * concatAst2) {
        ast_manager & mgr = get_manager();

        bool overlapAssumptionUsed = false;

        TRACE("str", tout << "process_concat_eq TYPE 2" << std::endl
              << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
              << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
              );

        if (!u.str.is_concat(to_app(concatAst1))) {
            TRACE("str", tout << "concatAst1 is not a concat function" << std::endl;);
            return;
        }
        if (!u.str.is_concat(to_app(concatAst2))) {
            TRACE("str", tout << "concatAst2 is not a concat function" << std::endl;);
            return;
        }

        expr * x = nullptr;
        expr * y = nullptr;
        expr * strAst = nullptr;
        expr * m = nullptr;

        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        if (u.str.is_string(v1_arg1) && !u.str.is_string(v2_arg1)) {
            m = v1_arg0;
            strAst = v1_arg1;
            x = v2_arg0;
            y = v2_arg1;
        } else {
            m = v2_arg0;
            strAst = v2_arg1;
            x = v1_arg0;
            y = v1_arg1;
        }

        zstring strValue;
        u.str.is_string(strAst, strValue);

        rational x_len, y_len, m_len, str_len;
        bool x_len_exists = get_len_value(x, x_len);
        bool y_len_exists = get_len_value(y, y_len);
        bool m_len_exists = get_len_value(m, m_len);
        bool str_len_exists = true;
        str_len = rational(strValue.length());

        // setup

        expr * xorFlag = nullptr;
        expr_ref temp1(mgr);
        std::pair<expr*, expr*> key1(concatAst1, concatAst2);
        std::pair<expr*, expr*> key2(concatAst2, concatAst1);

        // check the entries in this map to make sure they're still in scope
        // before we use them.

        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry1 = varForBreakConcat.find(key1);
        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry2 = varForBreakConcat.find(key2);

        // prevent checking scope for the XOR term, as it's always in the same scope as the split var

        bool entry1InScope;
        if (entry1 == varForBreakConcat.end()) {
            entry1InScope = false;
        } else {
            if (internal_variable_set.find((entry1->second)[0]) == internal_variable_set.end()
                /*|| internal_variable_set.find((entry1->second)[1]) == internal_variable_set.end()*/
                ) {
                entry1InScope = false;
            } else {
                entry1InScope = true;
            }
        }

        bool entry2InScope;
        if (entry2 == varForBreakConcat.end()) {
            entry2InScope = false;
        } else {
            if (internal_variable_set.find((entry2->second)[0]) == internal_variable_set.end()
                /*|| internal_variable_set.find((entry2->second)[1]) == internal_variable_set.end()*/
                ) {
                entry2InScope = false;
            } else {
                entry2InScope = true;
            }
        }

        TRACE("str", tout << "entry 1 " << (entry1InScope ? "in scope" : "not in scope") << std::endl
              << "entry 2 " << (entry2InScope ? "in scope" : "not in scope") << std::endl;);


        if (!entry1InScope && !entry2InScope) {
            temp1 = mk_nonempty_str_var();
            xorFlag = mk_internal_xor_var();
            varForBreakConcat[key1][0] = temp1;
            varForBreakConcat[key1][1] = xorFlag;
        } else {
            if (entry1InScope) {
                temp1 = varForBreakConcat[key1][0];
                xorFlag = varForBreakConcat[key1][1];
            } else if (entry2InScope) {
                temp1 = varForBreakConcat[key2][0];
                xorFlag = varForBreakConcat[key2][1];
            }
            refresh_theory_var(temp1);
            add_nonempty_constraint(temp1);
        }

        int splitType = -1;
        if (x_len_exists && m_len_exists) {
            if (x_len < m_len)
                splitType = 0;
            else if (x_len == m_len)
                splitType = 1;
            else
                splitType = 2;
        }
        if (splitType == -1 && y_len_exists && str_len_exists) {
            if (y_len > str_len)
                splitType = 0;
            else if (y_len == str_len)
                splitType = 1;
            else
                splitType = 2;
        }

        TRACE("str", tout << "Split type " << splitType << std::endl;);

        // Provide fewer split options when length information is available.

        if (splitType == 0) {
            // M cuts Y
            //   |  x  |      y     |
            //   |    m   |   str   |
            expr_ref temp1_strAst(mk_concat(temp1, strAst), mgr);
            if (can_two_nodes_eq(y, temp1_strAst)) {
                expr_ref_vector l_items(mgr);
                l_items.push_back(ctx.mk_eq_atom(concatAst1, concatAst2));

                expr_ref_vector r_items(mgr);
                expr_ref x_temp1(mk_concat(x, temp1), mgr);
                r_items.push_back(ctx.mk_eq_atom(m, x_temp1));
                r_items.push_back(ctx.mk_eq_atom(y, temp1_strAst));

                if (x_len_exists && m_len_exists) {
                    l_items.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_int(x_len)));
                    l_items.push_back(ctx.mk_eq_atom(mk_strlen(m), mk_int(m_len)));
                    rational m_sub_x = (m_len - x_len);
                    r_items.push_back(ctx.mk_eq_atom(mk_strlen(temp1), mk_int(m_sub_x)));
                } else {
                    l_items.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(y_len)));
                    l_items.push_back(ctx.mk_eq_atom(mk_strlen(strAst), mk_int(str_len)));
                    rational y_sub_str = (y_len - str_len);
                    r_items.push_back(ctx.mk_eq_atom(mk_strlen(temp1), mk_int(y_sub_str)));
                }

                expr_ref ax_l(mk_and(l_items), mgr);
                expr_ref ax_r(mk_and(r_items), mgr);

                if (!avoidLoopCut || !(has_self_cut(m, y))) {
                    // break down option 2-1
                    add_cut_info_merge(temp1, sLevel, y);
                    add_cut_info_merge(temp1, sLevel, m);

                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom(ax_l, ax_r), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ax_l, ax_r);
                    }
                } else {
                    loopDetected = true;

                    TRACE("str", tout << "AVOID LOOP: SKIP" << std::endl;);
                    TRACE("str", {print_cut_var(m, tout); print_cut_var(y, tout);});

                    if (!overlapAssumptionUsed) {
                        overlapAssumptionUsed = true;
                        assert_implication(ax_l, m_theoryStrOverlapAssumption_term);
                    }

                }
            }
        } else if (splitType == 1) {
            //   |   x   |    y    |
            //   |   m   |   str   |
            expr_ref ax_l1(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
            expr_ref ax_l2(mgr.mk_or(
                               ctx.mk_eq_atom(mk_strlen(x), mk_strlen(m)),
                               ctx.mk_eq_atom(mk_strlen(y), mk_strlen(strAst))), mgr);
            expr_ref ax_l(mgr.mk_and(ax_l1, ax_l2), mgr);
            expr_ref ax_r(mgr.mk_and(ctx.mk_eq_atom(x, m), ctx.mk_eq_atom(y, strAst)), mgr);
            assert_implication(ax_l, ax_r);
        } else if (splitType == 2) {
            // m cut y,
            //    |   x   |  y  |
            //    | m |   str   |
            rational lenDelta;
            expr_ref_vector l_items(mgr);
            l_items.push_back(ctx.mk_eq_atom(concatAst1, concatAst2));
            if (x_len_exists && m_len_exists) {
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_int(x_len)));
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(m), mk_int(m_len)));
                lenDelta = x_len - m_len;
            } else {
                l_items.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(y_len)));
                lenDelta = str_len - y_len;
            }
            TRACE("str",
                  tout
                  << "xLen? " << (x_len_exists ? "yes" : "no") << std::endl
                  << "mLen? " << (m_len_exists ? "yes" : "no") << std::endl
                  << "yLen? " << (y_len_exists ? "yes" : "no") << std::endl
                  << "xLen = " << x_len.to_string() << std::endl
                  << "yLen = " << y_len.to_string() << std::endl
                  << "mLen = " << m_len.to_string() << std::endl
                  << "strLen = " << str_len.to_string() << std::endl
                  << "lenDelta = " << lenDelta.to_string() << std::endl
                  << "strValue = \"" << strValue << "\" (len=" << strValue.length() << ")" << "\n"
                  ;
                  );

            zstring part1Str = strValue.extract(0, lenDelta.get_unsigned());
            zstring part2Str = strValue.extract(lenDelta.get_unsigned(), strValue.length() - lenDelta.get_unsigned());

            expr_ref prefixStr(mk_string(part1Str), mgr);
            expr_ref x_concat(mk_concat(m, prefixStr), mgr);
            expr_ref cropStr(mk_string(part2Str), mgr);

            if (can_two_nodes_eq(x, x_concat) && can_two_nodes_eq(y, cropStr)) {
                expr_ref_vector r_items(mgr);
                r_items.push_back(ctx.mk_eq_atom(x, x_concat));
                r_items.push_back(ctx.mk_eq_atom(y, cropStr));
                expr_ref ax_l(mk_and(l_items), mgr);
                expr_ref ax_r(mk_and(r_items), mgr);

                if (m_params.m_StrongArrangements) {
                    expr_ref ax_strong(ctx.mk_eq_atom(ax_l, ax_r), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(ax_l, ax_r);
                }
            } else {
                // negate! It's impossible to split str with these lengths
                TRACE("str", tout << "CONFLICT: Impossible to split str with these lengths." << std::endl;);
                expr_ref ax_l(mk_and(l_items), mgr);
                assert_axiom(mgr.mk_not(ax_l));
            }
        } else {
            // Split type -1: no idea about the length...
            expr_ref_vector arrangement_disjunction(mgr);

            expr_ref temp1_strAst(mk_concat(temp1, strAst), mgr);

            // m cuts y
            if (can_two_nodes_eq(y, temp1_strAst)) {
                if (!avoidLoopCut || !has_self_cut(m, y)) {
                    // break down option 2-1
                    expr_ref_vector and_item(mgr);

                    expr_ref x_temp1(mk_concat(x, temp1), mgr);
                    and_item.push_back(ctx.mk_eq_atom(m, x_temp1));
                    and_item.push_back(ctx.mk_eq_atom(y, temp1_strAst));

                    and_item.push_back(ctx.mk_eq_atom(mk_strlen(m),
                                                      m_autil.mk_add(mk_strlen(x), mk_strlen(temp1))));

                    expr_ref option1(mk_and(and_item), mgr);
                    arrangement_disjunction.push_back(option1);
                    add_theory_aware_branching_info(option1, 0.1, l_true);
                    add_cut_info_merge(temp1, ctx.get_scope_level(), y);
                    add_cut_info_merge(temp1, ctx.get_scope_level(), m);
                } else {
                    loopDetected = true;
                    TRACE("str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
                    TRACE("str", {print_cut_var(m, tout); print_cut_var(y, tout);});

                    if (!overlapAssumptionUsed) {
                        overlapAssumptionUsed = true;
                        arrangement_disjunction.push_back(m_theoryStrOverlapAssumption_term);
                    }
                }
            }

            for (unsigned int i = 0; i <= strValue.length(); ++i) {
                zstring part1Str = strValue.extract(0, i);
                zstring part2Str = strValue.extract(i, strValue.length() - i);
                expr_ref prefixStr(mk_string(part1Str), mgr);
                expr_ref x_concat(mk_concat(m, prefixStr), mgr);
                expr_ref cropStr(mk_string(part2Str), mgr);
                if (can_two_nodes_eq(x, x_concat) && can_two_nodes_eq(y, cropStr)) {
                    // break down option 2-2
                    expr_ref_vector and_item(mgr);
                    and_item.push_back(ctx.mk_eq_atom(x, x_concat));
                    and_item.push_back(ctx.mk_eq_atom(y, cropStr));
                    and_item.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(part2Str.length())));
                    expr_ref option2(mk_and(and_item), mgr);
                    arrangement_disjunction.push_back(option2);
                    double priority;
                    // prioritize the option where y is equal to the original string
                    if (i == 0) {
                        priority = 0.5;
                    } else {
                        priority = 0.1;
                    }
                    add_theory_aware_branching_info(option2, priority, l_true);
                }
            }

            if (!arrangement_disjunction.empty()) {
                expr_ref implyR(mk_or(arrangement_disjunction), mgr);

                if (m_params.m_StrongArrangements) {
                    expr_ref implyLHS(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
                    expr_ref ax_strong(ctx.mk_eq_atom(implyLHS, implyR), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                }
                generate_mutual_exclusion(arrangement_disjunction);
            } else {
                TRACE("str", tout << "STOP: Should not split two EQ concats." << std::endl;);
            }
        } // (splitType == -1)
    }

    /*************************************************************
     * Type 3: concat(x, y) = concat("str", n)
     *************************************************************/
    bool theory_str::is_concat_eq_type3(expr * concatAst1, expr * concatAst2) {
        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        if (u.str.is_string(v1_arg0) && (!u.str.is_string(v1_arg1))
            && (!u.str.is_string(v2_arg0)) && (!u.str.is_string(v2_arg1))) {
            return true;
        } else if (u.str.is_string(v2_arg0) && (!u.str.is_string(v2_arg1))
                   && (!u.str.is_string(v1_arg0)) && (!u.str.is_string(v1_arg1))) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::process_concat_eq_type3(expr * concatAst1, expr * concatAst2) {
        ast_manager & mgr = get_manager();

        bool overlapAssumptionUsed = false;

        TRACE("str", tout << "process_concat_eq TYPE 3" << std::endl
              << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
              << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
              );

        if (!u.str.is_concat(to_app(concatAst1))) {
            TRACE("str", tout << "concatAst1 is not a concat function" << std::endl;);
            return;
        }
        if (!u.str.is_concat(to_app(concatAst2))) {
            TRACE("str", tout << "concatAst2 is not a concat function" << std::endl;);
            return;
        }

        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        expr * x = nullptr;
        expr * y = nullptr;
        expr * strAst = nullptr;
        expr * n = nullptr;

        if (u.str.is_string(v1_arg0) && !u.str.is_string(v2_arg0)) {
            strAst = v1_arg0;
            n = v1_arg1;
            x = v2_arg0;
            y = v2_arg1;
        } else {
            strAst = v2_arg0;
            n = v2_arg1;
            x = v1_arg0;
            y = v1_arg1;
        }

        zstring strValue;
        u.str.is_string(strAst, strValue);

        rational x_len, y_len, str_len, n_len;
        bool x_len_exists = get_len_value(x, x_len);
        bool y_len_exists = get_len_value(y, y_len);
        str_len = rational((unsigned)(strValue.length()));
        bool n_len_exists = get_len_value(n, n_len);

        expr_ref xorFlag(mgr);
        expr_ref temp1(mgr);
        std::pair<expr*, expr*> key1(concatAst1, concatAst2);
        std::pair<expr*, expr*> key2(concatAst2, concatAst1);

        // check the entries in this map to make sure they're still in scope
        // before we use them.

        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry1 = varForBreakConcat.find(key1);
        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry2 = varForBreakConcat.find(key2);

        bool entry1InScope;
        if (entry1 == varForBreakConcat.end()) {
            entry1InScope = false;
        } else {
            if (internal_variable_set.find((entry1->second)[0]) == internal_variable_set.end()
                /* || internal_variable_set.find((entry1->second)[1]) == internal_variable_set.end() */) {
                entry1InScope = false;
            } else {
                entry1InScope = true;
            }
        }

        bool entry2InScope;
        if (entry2 == varForBreakConcat.end()) {
            entry2InScope = false;
        } else {
            if (internal_variable_set.find((entry2->second)[0]) == internal_variable_set.end()
                /* || internal_variable_set.find((entry2->second)[1]) == internal_variable_set.end() */) {
                entry2InScope = false;
            } else {
                entry2InScope = true;
            }
        }

        TRACE("str", tout << "entry 1 " << (entry1InScope ? "in scope" : "not in scope") << std::endl
              << "entry 2 " << (entry2InScope ? "in scope" : "not in scope") << std::endl;);


        if (!entry1InScope && !entry2InScope) {
            temp1 = mk_nonempty_str_var();
            xorFlag = mk_internal_xor_var();

            varForBreakConcat[key1][0] = temp1;
            varForBreakConcat[key1][1] = xorFlag;
        } else {
            if (entry1InScope) {
                temp1 = varForBreakConcat[key1][0];
                xorFlag = varForBreakConcat[key1][1];
            } else if (varForBreakConcat.find(key2) != varForBreakConcat.end()) {
                temp1 = varForBreakConcat[key2][0];
                xorFlag = varForBreakConcat[key2][1];
            }
            refresh_theory_var(temp1);
            add_nonempty_constraint(temp1);
        }



        int splitType = -1;
        if (x_len_exists) {
            if (x_len < str_len)
                splitType = 0;
            else if (x_len == str_len)
                splitType = 1;
            else
                splitType = 2;
        }
        if (splitType == -1 && y_len_exists && n_len_exists) {
            if (y_len > n_len)
                splitType = 0;
            else if (y_len == n_len)
                splitType = 1;
            else
                splitType = 2;
        }

        TRACE("str", tout << "Split type " << splitType << std::endl;);

        // Provide fewer split options when length information is available.
        if (splitType == 0) {
            //   |   x   |    y     |
            //   |  str     |   n   |
            expr_ref_vector litems(mgr);
            litems.push_back(ctx.mk_eq_atom(concatAst1, concatAst2));
            rational prefixLen;
            if (!x_len_exists) {
                prefixLen = str_len - (y_len - n_len);
                litems.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(y_len)));
                litems.push_back(ctx.mk_eq_atom(mk_strlen(n), mk_int(n_len)));
            } else {
                prefixLen = x_len;
                litems.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_int(x_len)));
            }
            zstring prefixStr = strValue.extract(0, prefixLen.get_unsigned());
            rational str_sub_prefix = str_len - prefixLen;
            zstring suffixStr = strValue.extract(prefixLen.get_unsigned(), str_sub_prefix.get_unsigned());
            expr_ref prefixAst(mk_string(prefixStr), mgr);
            expr_ref suffixAst(mk_string(suffixStr), mgr);
            expr_ref ax_l(mgr.mk_and(litems.size(), litems.data()), mgr);

            expr_ref suf_n_concat(mk_concat(suffixAst, n), mgr);
            if (can_two_nodes_eq(x, prefixAst) && can_two_nodes_eq(y, suf_n_concat)) {
                expr_ref_vector r_items(mgr);
                r_items.push_back(ctx.mk_eq_atom(x, prefixAst));
                r_items.push_back(ctx.mk_eq_atom(y, suf_n_concat));

                if (m_params.m_StrongArrangements) {
                    expr_ref ax_strong(ctx.mk_eq_atom(ax_l, mk_and(r_items)), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(ax_l, mk_and(r_items));
                }
            } else {
                // negate! It's impossible to split str with these lengths
                TRACE("str", tout << "CONFLICT: Impossible to split str with these lengths." << std::endl;);
                assert_axiom(mgr.mk_not(ax_l));
            }
        }
        else if (splitType == 1) {
            expr_ref ax_l1(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
            expr_ref ax_l2(mgr.mk_or(
                               ctx.mk_eq_atom(mk_strlen(x), mk_strlen(strAst)),
                               ctx.mk_eq_atom(mk_strlen(y), mk_strlen(n))), mgr);
            expr_ref ax_l(mgr.mk_and(ax_l1, ax_l2), mgr);
            expr_ref ax_r(mgr.mk_and(ctx.mk_eq_atom(x, strAst), ctx.mk_eq_atom(y, n)), mgr);

            if (m_params.m_StrongArrangements) {
                expr_ref ax_strong(ctx.mk_eq_atom(ax_l, ax_r), mgr);
                assert_axiom(ax_strong);
            } else {
                assert_implication(ax_l, ax_r);
            }
        }
        else if (splitType == 2) {
            //   |   x        |    y     |
            //   |  str   |       n      |
            expr_ref_vector litems(mgr);
            litems.push_back(ctx.mk_eq_atom(concatAst1, concatAst2));
            rational tmpLen;
            if (!x_len_exists) {
                tmpLen = n_len - y_len;
                litems.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_int(y_len)));
                litems.push_back(ctx.mk_eq_atom(mk_strlen(n), mk_int(n_len)));
            } else {
                tmpLen = x_len - str_len;
                litems.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_int(x_len)));
            }
            expr_ref ax_l(mgr.mk_and(litems.size(), litems.data()), mgr);

            expr_ref str_temp1(mk_concat(strAst, temp1), mgr);
            expr_ref temp1_y(mk_concat(temp1, y), mgr);

            if (can_two_nodes_eq(x, str_temp1)) {
                if (!avoidLoopCut || !(has_self_cut(x, n))) {
                    expr_ref_vector r_items(mgr);
                    r_items.push_back(ctx.mk_eq_atom(x, str_temp1));
                    r_items.push_back(ctx.mk_eq_atom(n, temp1_y));
                    r_items.push_back(ctx.mk_eq_atom(mk_strlen(temp1), mk_int(tmpLen)));
                    expr_ref ax_r(mk_and(r_items), mgr);

                    //Cut Info
                    add_cut_info_merge(temp1, sLevel, x);
                    add_cut_info_merge(temp1, sLevel, n);

                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom(ax_l, ax_r), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ax_l, ax_r);
                    }
                } else {
                    loopDetected = true;
                    TRACE("str", tout << "AVOID LOOP: SKIPPED" << std::endl;);
                    TRACE("str", {print_cut_var(x, tout); print_cut_var(n, tout);});

                    if (!overlapAssumptionUsed) {
                        overlapAssumptionUsed = true;
                        assert_implication(ax_l, m_theoryStrOverlapAssumption_term);
                    }
                }
            }
            //    else {
            //      // negate! It's impossible to split str with these lengths
            //      __debugPrint(logFile, "[Conflict] Negate! It's impossible to split str with these lengths @ %d.\n", __LINE__);
            //      addAxiom(t, Z3_mk_not(ctx, ax_l), __LINE__);
            //    }
        }
        else {
            // Split type -1. We know nothing about the length...

            expr_ref_vector arrangement_disjunction(mgr);

            int pos = 1;
            for (unsigned int i = 0; i <= strValue.length(); i++) {
                zstring part1Str = strValue.extract(0, i);
                zstring part2Str = strValue.extract(i, strValue.length() - i);
                expr_ref cropStr(mk_string(part1Str), mgr);
                expr_ref suffixStr(mk_string(part2Str), mgr);
                expr_ref y_concat(mk_concat(suffixStr, n), mgr);

                if (can_two_nodes_eq(x, cropStr) && can_two_nodes_eq(y, y_concat)) {
                    expr_ref_vector and_item(mgr);
                    // break down option 3-1
                    expr_ref x_eq_str(ctx.mk_eq_atom(x, cropStr), mgr);

                    and_item.push_back(x_eq_str); ++pos;
                    and_item.push_back(ctx.mk_eq_atom(y, y_concat));
                    and_item.push_back(ctx.mk_eq_atom(mk_strlen(x), mk_strlen(cropStr))); ++pos;

                    //        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, y_concat)));
                    // adding length constraint for _ = constStr seems slowing things down.

                    expr_ref option1(mk_and(and_item), mgr);
                    ctx.get_rewriter()(option1);
                    arrangement_disjunction.push_back(option1);
                    double priority;
                    if (i == strValue.length()) {
                        priority = 0.5;
                    } else {
                        priority = 0.1;
                    }
                    add_theory_aware_branching_info(option1, priority, l_true);
                }
            }

            expr_ref strAst_temp1(mk_concat(strAst, temp1), mgr);


            //--------------------------------------------------------
            // x cut n
            //--------------------------------------------------------
            if (can_two_nodes_eq(x, strAst_temp1)) {
                if (!avoidLoopCut || !(has_self_cut(x, n))) {
                    // break down option 3-2
                    expr_ref_vector and_item(mgr);

                    expr_ref temp1_y(mk_concat(temp1, y), mgr);
                    and_item.push_back(ctx.mk_eq_atom(x, strAst_temp1)); ++pos;
                    and_item.push_back(ctx.mk_eq_atom(n, temp1_y)); ++pos;

                    and_item.push_back(ctx.mk_eq_atom(mk_strlen(x),
                                                      m_autil.mk_add(mk_strlen(strAst), mk_strlen(temp1)) ) ); ++pos;

                    expr_ref option2(mk_and(and_item), mgr);
                    arrangement_disjunction.push_back(option2);
                    add_theory_aware_branching_info(option2, 0.1, l_true);

                    add_cut_info_merge(temp1, sLevel, x);
                    add_cut_info_merge(temp1, sLevel, n);
                } else {
                    loopDetected = true;
                    TRACE("str", tout << "AVOID LOOP: SKIPPED." << std::endl;);
                    TRACE("str", {print_cut_var(x, tout); print_cut_var(n, tout);});

                    if (!overlapAssumptionUsed) {
                        overlapAssumptionUsed = true;
                        arrangement_disjunction.push_back(m_theoryStrOverlapAssumption_term);
                    }
                }
            }


            if (!arrangement_disjunction.empty()) {
                expr_ref implyR(mk_or(arrangement_disjunction), mgr);

                if (m_params.m_StrongArrangements) {
                    expr_ref ax_lhs(ctx.mk_eq_atom(concatAst1, concatAst2), mgr);
                    expr_ref ax_strong(ctx.mk_eq_atom(ax_lhs, implyR), mgr);
                    assert_axiom_rw(ax_strong);
                } else {
                    assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                }
                generate_mutual_exclusion(arrangement_disjunction);
            } else {
                TRACE("str", tout << "STOP: should not split two eq. concats" << std::endl;);
            }
        }

    }

    /*************************************************************
     * Type 4: concat("str1", y) = concat("str2", n)
     *************************************************************/
    bool theory_str::is_concat_eq_type4(expr * concatAst1, expr * concatAst2) {
        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        if (u.str.is_string(v1_arg0) && (!u.str.is_string(v1_arg1))
            && u.str.is_string(v2_arg0) && (!u.str.is_string(v2_arg1))) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::process_concat_eq_type4(expr * concatAst1, expr * concatAst2) {
        ast_manager & mgr = get_manager();
        TRACE("str", tout << "process_concat_eq TYPE 4" << std::endl
              << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
              << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
              );

        if (!u.str.is_concat(to_app(concatAst1))) {
            TRACE("str", tout << "concatAst1 is not a concat function" << std::endl;);
            return;
        }
        if (!u.str.is_concat(to_app(concatAst2))) {
            TRACE("str", tout << "concatAst2 is not a concat function" << std::endl;);
            return;
        }

        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        expr * str1Ast = v1_arg0;
        expr * y = v1_arg1;
        expr * str2Ast = v2_arg0;
        expr * n = v2_arg1;

        zstring str1Value, str2Value;
        u.str.is_string(str1Ast, str1Value);
        u.str.is_string(str2Ast, str2Value);

        unsigned int str1Len = str1Value.length();
        unsigned int str2Len = str2Value.length();

        int commonLen = (str1Len > str2Len) ? str2Len : str1Len;
        if (str1Value.extract(0, commonLen) != str2Value.extract(0, commonLen)) {
            TRACE("str", tout << "Conflict: " << mk_ismt2_pp(concatAst1, mgr)
                  << " has no common prefix with " << mk_ismt2_pp(concatAst2, mgr) << std::endl;);
            expr_ref toNegate(mgr.mk_not(ctx.mk_eq_atom(concatAst1, concatAst2)), mgr);
            assert_axiom(toNegate);
            return;
        } else {
            if (str1Len > str2Len) {
                zstring deltaStr = str1Value.extract(str2Len, str1Len - str2Len);
                expr_ref tmpAst(mk_concat(mk_string(deltaStr), y), mgr);
                if (!in_same_eqc(tmpAst, n)) {
                    // break down option 4-1
                    expr_ref implyR(ctx.mk_eq_atom(n, tmpAst), mgr);
                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                    }
                }
            } else if (str1Len == str2Len) {
                if (!in_same_eqc(n, y)) {
                    //break down option 4-2
                    expr_ref implyR(ctx.mk_eq_atom(n, y), mgr);

                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                    }
                }
            } else {
                zstring deltaStr = str2Value.extract(str1Len, str2Len - str1Len);
                expr_ref tmpAst(mk_concat(mk_string(deltaStr), n), mgr);
                if (!in_same_eqc(y, tmpAst)) {
                    //break down option 4-3
                    expr_ref implyR(ctx.mk_eq_atom(y, tmpAst), mgr);
                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                    }
                }
            }
        }
    }

    /*************************************************************
     *  case 5: concat(x, "str1") = concat(m, "str2")
     *************************************************************/
    bool theory_str::is_concat_eq_type5(expr * concatAst1, expr * concatAst2) {
        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        if ((!u.str.is_string(v1_arg0)) && u.str.is_string(v1_arg1)
            && (!u.str.is_string(v2_arg0)) && u.str.is_string(v2_arg1)) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::process_concat_eq_type5(expr * concatAst1, expr * concatAst2) {
        ast_manager & mgr = get_manager();
        TRACE("str", tout << "process_concat_eq TYPE 5" << std::endl
              << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
              << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
              );

        if (!u.str.is_concat(to_app(concatAst1))) {
            TRACE("str", tout << "concatAst1 is not a concat function" << std::endl;);
            return;
        }
        if (!u.str.is_concat(to_app(concatAst2))) {
            TRACE("str", tout << "concatAst2 is not a concat function" << std::endl;);
            return;
        }

        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        expr * x = v1_arg0;
        expr * str1Ast = v1_arg1;
        expr * m = v2_arg0;
        expr * str2Ast = v2_arg1;

        zstring str1Value, str2Value;
        u.str.is_string(str1Ast, str1Value);
        u.str.is_string(str2Ast, str2Value);

        unsigned int str1Len = str1Value.length();
        unsigned int str2Len = str2Value.length();

        int cLen = (str1Len > str2Len) ? str2Len : str1Len;
        if (str1Value.extract(str1Len - cLen, cLen) != str2Value.extract(str2Len - cLen, cLen)) {
            TRACE("str", tout << "Conflict: " << mk_ismt2_pp(concatAst1, mgr)
                  << " has no common suffix with " << mk_ismt2_pp(concatAst2, mgr) << std::endl;);
            expr_ref toNegate(mgr.mk_not(ctx.mk_eq_atom(concatAst1, concatAst2)), mgr);
            assert_axiom(toNegate);
            return;
        } else {
            if (str1Len > str2Len) {
                zstring deltaStr = str1Value.extract(0, str1Len - str2Len);
                expr_ref x_deltaStr(mk_concat(x, mk_string(deltaStr)), mgr);
                if (!in_same_eqc(m, x_deltaStr)) {
                    expr_ref implyR(ctx.mk_eq_atom(m, x_deltaStr), mgr);
                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                    }
                }
            } else if (str1Len == str2Len) {
                // test
                if (!in_same_eqc(x, m)) {
                    expr_ref implyR(ctx.mk_eq_atom(x, m), mgr);
                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                    }
                }
            } else {
                zstring deltaStr = str2Value.extract(0, str2Len - str1Len);
                expr_ref m_deltaStr(mk_concat(m, mk_string(deltaStr)), mgr);
                if (!in_same_eqc(x, m_deltaStr)) {
                    expr_ref implyR(ctx.mk_eq_atom(x, m_deltaStr), mgr);
                    if (m_params.m_StrongArrangements) {
                        expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
                        assert_axiom_rw(ax_strong);
                    } else {
                        assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
                    }
                }
            }
        }
    }

    /*************************************************************
     *  case 6: concat("str1", y) = concat(m, "str2")
     *************************************************************/
    bool theory_str::is_concat_eq_type6(expr * concatAst1, expr * concatAst2) {
        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);

        if (u.str.is_string(v1_arg0) && (!u.str.is_string(v1_arg1))
            && (!u.str.is_string(v2_arg0)) && u.str.is_string(v2_arg1)) {
            return true;
        } else if (u.str.is_string(v2_arg0) && (!u.str.is_string(v2_arg1))
                   && (!u.str.is_string(v1_arg0)) && u.str.is_string(v1_arg1)) {
            return true;
        } else {
            return false;
        }
    }

    void theory_str::process_concat_eq_type6(expr * concatAst1, expr * concatAst2) {
        ast_manager & mgr = get_manager();
        TRACE("str", tout << "process_concat_eq TYPE 6" << std::endl
              << "concatAst1 = " << mk_ismt2_pp(concatAst1, mgr) << std::endl
              << "concatAst2 = " << mk_ismt2_pp(concatAst2, mgr) << std::endl;
              );

        if (!u.str.is_concat(to_app(concatAst1))) {
            TRACE("str", tout << "concatAst1 is not a concat function" << std::endl;);
            return;
        }
        if (!u.str.is_concat(to_app(concatAst2))) {
            TRACE("str", tout << "concatAst2 is not a concat function" << std::endl;);
            return;
        }

        expr * v1_arg0 = to_app(concatAst1)->get_arg(0);
        expr * v1_arg1 = to_app(concatAst1)->get_arg(1);
        expr * v2_arg0 = to_app(concatAst2)->get_arg(0);
        expr * v2_arg1 = to_app(concatAst2)->get_arg(1);


        expr * str1Ast = nullptr;
        expr * y = nullptr;
        expr * m = nullptr;
        expr * str2Ast = nullptr;

        if (u.str.is_string(v1_arg0)) {
            str1Ast = v1_arg0;
            y = v1_arg1;
            m = v2_arg0;
            str2Ast = v2_arg1;
        } else {
            str1Ast = v2_arg0;
            y = v2_arg1;
            m = v1_arg0;
            str2Ast = v1_arg1;
        }

        zstring str1Value, str2Value;
        u.str.is_string(str1Ast, str1Value);
        u.str.is_string(str2Ast, str2Value);

        unsigned int str1Len = str1Value.length();
        unsigned int str2Len = str2Value.length();

        //----------------------------------------
        //(a)  |---str1---|----y----|
        //     |--m--|-----str2-----|
        //
        //(b)  |---str1---|----y----|
        //     |-----m----|--str2---|
        //
        //(c)  |---str1---|----y----|
        //     |------m------|-str2-|
        //----------------------------------------

        std::list<unsigned int> overlapLen;
        overlapLen.push_back(0);

        for (unsigned int i = 1; i <= str1Len && i <= str2Len; i++) {
            if (str1Value.extract(str1Len - i, i) == str2Value.extract(0, i))
                overlapLen.push_back(i);
        }

        //----------------------------------------------------------------
        expr_ref commonVar(mgr);
        expr * xorFlag = nullptr;
        std::pair<expr*, expr*> key1(concatAst1, concatAst2);
        std::pair<expr*, expr*> key2(concatAst2, concatAst1);

        // check the entries in this map to make sure they're still in scope
        // before we use them.

        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry1 = varForBreakConcat.find(key1);
        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry2 = varForBreakConcat.find(key2);

        bool entry1InScope;
        if (entry1 == varForBreakConcat.end()) {
            entry1InScope = false;
        } else {
            if (internal_variable_set.find((entry1->second)[0]) == internal_variable_set.end()
                /* || internal_variable_set.find((entry1->second)[1]) == internal_variable_set.end() */) {
                entry1InScope = false;
            } else {
                entry1InScope = true;
            }
        }

        bool entry2InScope;
        if (entry2 == varForBreakConcat.end()) {
            entry2InScope = false;
        } else {
            if (internal_variable_set.find((entry2->second)[0]) == internal_variable_set.end()
                /* || internal_variable_set.find((entry2->second)[1]) == internal_variable_set.end() */) {
                entry2InScope = false;
            } else {
                entry2InScope = true;
            }
        }

        TRACE("str", tout << "entry 1 " << (entry1InScope ? "in scope" : "not in scope") << std::endl
              << "entry 2 " << (entry2InScope ? "in scope" : "not in scope") << std::endl;);

        if (!entry1InScope && !entry2InScope) {
            commonVar = mk_nonempty_str_var();
            xorFlag = mk_internal_xor_var();
            varForBreakConcat[key1][0] = commonVar;
            varForBreakConcat[key1][1] = xorFlag;
        } else {
            if (entry1InScope) {
                commonVar = (entry1->second)[0];
                xorFlag = (entry1->second)[1];
            } else {
                commonVar = (entry2->second)[0];
                xorFlag = (entry2->second)[1];
            }
            refresh_theory_var(commonVar);
            add_nonempty_constraint(commonVar);
        }

        bool overlapAssumptionUsed = false;

        expr_ref_vector arrangement_disjunction(mgr);
        int pos = 1;

        if (!avoidLoopCut || !has_self_cut(m, y)) {
            expr_ref_vector and_item(mgr);

            expr_ref str1_commonVar(mk_concat(str1Ast, commonVar), mgr);
            and_item.push_back(ctx.mk_eq_atom(m, str1_commonVar));
            pos += 1;

            expr_ref commonVar_str2(mk_concat(commonVar, str2Ast), mgr);
            and_item.push_back(ctx.mk_eq_atom(y, commonVar_str2));
            pos += 1;

            and_item.push_back(ctx.mk_eq_atom(mk_strlen(m),
                                              m_autil.mk_add(mk_strlen(str1Ast), mk_strlen(commonVar)) ));
            pos += 1;

            //    addItems[0] = mk_length(t, commonVar);
            //    addItems[1] = mk_length(t, str2Ast);
            //    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), Z3_mk_add(ctx, 2, addItems)));

            expr_ref option1(mk_and(and_item), mgr);
            arrangement_disjunction.push_back(option1);
            add_theory_aware_branching_info(option1, 0.1, l_true);
        } else {
            loopDetected = true;

            TRACE("str", tout << "AVOID LOOP: SKIPPED." << std::endl;);
            TRACE("str", print_cut_var(m, tout); print_cut_var(y, tout););

            // only add the overlap assumption one time
            if (!overlapAssumptionUsed) {
                arrangement_disjunction.push_back(m_theoryStrOverlapAssumption_term);
                overlapAssumptionUsed = true;
            }

        }

        for (unsigned int overLen : overlapLen) {
            zstring prefix = str1Value.extract(0, str1Len - overLen);
            zstring suffix = str2Value.extract(overLen, str2Len - overLen);

            expr_ref_vector and_item(mgr);

            expr_ref prefixAst(mk_string(prefix), mgr);
            expr_ref x_eq_prefix(ctx.mk_eq_atom(m, prefixAst), mgr);
            and_item.push_back(x_eq_prefix);
            pos += 1;

            and_item.push_back(
                ctx.mk_eq_atom(mk_strlen(m), mk_strlen(prefixAst)));
            pos += 1;

            // adding length constraint for _ = constStr seems slowing things down.

            expr_ref suffixAst(mk_string(suffix), mgr);
            expr_ref y_eq_suffix(ctx.mk_eq_atom(y, suffixAst), mgr);
            and_item.push_back(y_eq_suffix);
            pos += 1;

            and_item.push_back(ctx.mk_eq_atom(mk_strlen(y), mk_strlen(suffixAst)));
            pos += 1;

            expr_ref option2(mk_and(and_item), mgr);
            arrangement_disjunction.push_back(option2);
            double priority;
            // prefer the option "str1" = x
            if (prefix == str1Value) {
                priority = 0.5;
            } else {
                priority = 0.1;
            }
            add_theory_aware_branching_info(option2, priority, l_true);
        }

        //  case 6: concat("str1", y) = concat(m, "str2")

        expr_ref implyR(mk_or(arrangement_disjunction), mgr);

        if (m_params.m_StrongArrangements) {
            expr_ref ax_strong(ctx.mk_eq_atom( ctx.mk_eq_atom(concatAst1, concatAst2), implyR ), mgr);
            assert_axiom_rw(ax_strong);
        } else {
            assert_implication(ctx.mk_eq_atom(concatAst1, concatAst2), implyR);
        }
        generate_mutual_exclusion(arrangement_disjunction);
    }

    bool theory_str::get_string_constant_eqc(expr * e, zstring & stringVal) {
        bool exists;
        expr * strExpr = get_eqc_value(e, exists);
        if (!exists) {
            return false;}
        u.str.is_string(strExpr, stringVal);
        return true;
    }
    
    /*
     * Look through the equivalence class of n to find a string constant.
     * Return that constant if it is found, and set hasEqcValue to true.
     * Otherwise, return n, and set hasEqcValue to false.
     */

    expr * theory_str::get_eqc_value(expr * n, bool & hasEqcValue) {
        return z3str2_get_eqc_value(n, hasEqcValue);
    }


    // Simulate the behaviour of get_eqc_value() from Z3str2.
    // We only check m_find for a string constant.

    expr * theory_str::z3str2_get_eqc_value(expr * n , bool & hasEqcValue) {
        theory_var curr = get_var(n);
        if (curr != null_theory_var) {
            curr = m_find.find(curr);
            theory_var first = curr;
            do {
                expr* a = get_ast(curr);
                if (u.str.is_string(a)) {
                    hasEqcValue = true;
                    return a;
                }
                curr = m_find.next(curr);
            } 
            while (curr != first && curr != null_theory_var);
        }
        hasEqcValue = false;
        return n;
    }

    bool theory_str::get_arith_value(expr* e, rational& val) const {
         ast_manager & m = get_manager();
         (void)m;
         if (!ctx.e_internalized(e)) {
             return false;
         }
         // check root of the eqc for an integer constant
         // if an integer constant exists in the eqc, it should be the root
         enode * en_e = ctx.get_enode(e);
         enode * root_e = en_e->get_root();
         if (m_autil.is_numeral(root_e->get_expr(), val) && val.is_int()) {
             TRACE("str", tout << mk_pp(e, get_manager()) << " ~= " << mk_pp(root_e->get_expr(), get_manager()) << std::endl;);
             return true;
         } else {
             TRACE("str", tout << "root of eqc of " << mk_pp(e, get_manager()) << " is not a numeral" << std::endl;);
             return false;
         }

     }

    bool theory_str::lower_bound(expr* _e, rational& lo) {
        if (opt_DisableIntegerTheoryIntegration) {
            TRACE("str", tout << "WARNING: integer theory integration disabled" << std::endl;);
            return false;
        }

        arith_value v(get_manager());
        v.init(&ctx);
        bool strict;
        return v.get_lo_equiv(_e, lo, strict);
    }

    bool theory_str::upper_bound(expr* _e, rational& hi) {
        if (opt_DisableIntegerTheoryIntegration) {
            TRACE("str", tout << "WARNING: integer theory integration disabled" << std::endl;);
            return false;
        }

        arith_value v(get_manager());
        v.init(&ctx);
        bool strict;
        return v.get_up_equiv(_e, hi, strict);
    }

    bool theory_str::get_len_value(expr* e, rational& val) {
        if (opt_DisableIntegerTheoryIntegration) {
            TRACE("str", tout << "WARNING: integer theory integration disabled" << std::endl;);
            return false;
        }

        ast_manager & m = get_manager();

        TRACE("str", tout << "checking len value of " << mk_ismt2_pp(e, m) << std::endl;);

        rational val1;
        expr_ref len(m), len_val(m);
        expr* e1, *e2;
        ptr_vector<expr> todo;
        todo.push_back(e);
        val.reset();
        while (!todo.empty()) {
            expr* c = todo.back();
            todo.pop_back();
            if (u.str.is_concat(to_app(c))) {
                e1 = to_app(c)->get_arg(0);
                e2 = to_app(c)->get_arg(1);
                todo.push_back(e1);
                todo.push_back(e2);
            }
            else if (u.str.is_string(to_app(c))) {
                zstring tmp;
                u.str.is_string(to_app(c), tmp);
                unsigned int sl = tmp.length();
                val += rational(sl);
            }
            else {
                len = mk_strlen(c);

                // debugging
                TRACE("str", {
                        tout << mk_pp(len, m) << ":" << std::endl
                             << (ctx.is_relevant(len.get()) ? "relevant" : "not relevant") << std::endl
                             << (ctx.e_internalized(len) ? "internalized" : "not internalized") << std::endl
                            ;
                        if (ctx.e_internalized(len)) {
                            enode * e_len = ctx.get_enode(len);
                            tout << "has " << e_len->get_num_th_vars() << " theory vars" << std::endl;

                            // eqc debugging
                            {
                                tout << "dump equivalence class of " << mk_pp(len, get_manager()) << std::endl;
                                enode * nNode = ctx.get_enode(len);
                                enode * eqcNode = nNode;
                                do {
                                    app * ast = eqcNode->get_expr();
                                    tout << mk_pp(ast, get_manager()) << std::endl;
                                    eqcNode = eqcNode->get_next();
                                } while (eqcNode != nNode);
                            }
                        }
                    });

                if (ctx.e_internalized(len) && get_arith_value(len, val1)) {
                    val += val1;
                    TRACE("str", tout << "integer theory: subexpression " << mk_ismt2_pp(len, m) << " has length " << val1 << std::endl;);
                }
                else {
                    TRACE("str", tout << "integer theory: subexpression " << mk_ismt2_pp(len, m) << " has no length assignment; bailing out" << std::endl;);
                    return false;
                }
            }
        }

        TRACE("str", tout << "length of " << mk_ismt2_pp(e, m) << " is " << val << std::endl;);
        return val.is_int() && val.is_nonneg();
    }

    /*
     * Decide whether n1 and n2 are already in the same equivalence class.
     * This only checks whether the core considers them to be equal;
     * they may not actually be equal.
     */
    bool theory_str::in_same_eqc(expr * n1, expr * n2) {
        if (n1 == n2) return true;

        // similar to get_eqc_value(), make absolutely sure
        // that we've set this up properly for the context

        if (!ctx.e_internalized(n1)) {
            TRACE("str", tout << "WARNING: expression " << mk_ismt2_pp(n1, get_manager()) << " was not internalized" << std::endl;);
            ctx.internalize(n1, false);
        }
        if (!ctx.e_internalized(n2)) {
            TRACE("str", tout << "WARNING: expression " << mk_ismt2_pp(n2, get_manager()) << " was not internalized" << std::endl;);
            ctx.internalize(n2, false);
        }

        expr * curr = get_eqc_next(n1);
        while (curr != n1) {
            if (curr == n2)
                return true;
            curr = get_eqc_next(curr);
        }
        return false;
    }

    expr * theory_str::collect_eq_nodes(expr * n, expr_ref_vector & eqcSet) {
        expr * constStrNode = nullptr;

        expr * ex = n;
        do {
            if (u.str.is_string(to_app(ex))) {
                constStrNode = ex;
            }
            eqcSet.push_back(ex);

            ex = get_eqc_next(ex);
        } while (ex != n);
        return constStrNode;
    }

    /*
     * Collect constant strings (from left to right) in an AST node.
     */
    void theory_str::get_const_str_asts_in_node(expr * node, expr_ref_vector & astList) {
        if (u.str.is_string(node)) {
            astList.push_back(node);
            //} else if (getNodeType(t, node) == my_Z3_Func) {
        } else if (is_app(node)) {
            app * func_app = to_app(node);
            unsigned int argCount = func_app->get_num_args();
            for (unsigned int i = 0; i < argCount; i++) {
                expr * argAst = func_app->get_arg(i);
                get_const_str_asts_in_node(argAst, astList);
            }
        }
    }

    void theory_str::check_contain_by_eqc_val(expr * varNode, expr * constNode) {
        ast_manager & m = get_manager();

        TRACE("str", tout << "varNode = " << mk_pp(varNode, m) << ", constNode = " << mk_pp(constNode, m) << std::endl;);

        expr_ref_vector litems(m);

        if (contain_pair_idx_map.contains(varNode)) {
            for (auto entry : contain_pair_idx_map[varNode]) {
                expr * strAst = entry.first;
                expr * substrAst = entry.second;

                expr * boolVar = nullptr;
                if (!contain_pair_bool_map.find(strAst, substrAst, boolVar)) {
                    TRACE("str", tout << "warning: no entry for boolVar in contain_pair_bool_map" << std::endl;);
                }

                // we only want to inspect the Contains terms where either of strAst or substrAst
                // are equal to varNode.

                TRACE("t_str_detail", tout << "considering Contains with strAst = " << mk_pp(strAst, m) << ", substrAst = " << mk_pp(substrAst, m) << "..." << std::endl;);

                if (varNode != strAst && varNode != substrAst) {
                    TRACE("str", tout << "varNode not equal to strAst or substrAst, skip" << std::endl;);
                    continue;
                }
                TRACE("str", tout << "varNode matched one of strAst or substrAst. Continuing" << std::endl;);

                // varEqcNode is str
                if (strAst == varNode) {
                    expr_ref implyR(m);
                    litems.reset();

                    if (strAst != constNode) {
                        litems.push_back(ctx.mk_eq_atom(strAst, constNode));
                    }
                    zstring strConst;
                    u.str.is_string(constNode, strConst);
                    bool subStrHasEqcValue = false;
                    expr * substrValue = get_eqc_value(substrAst, subStrHasEqcValue);
                    if (substrValue != substrAst) {
                        litems.push_back(ctx.mk_eq_atom(substrAst, substrValue));
                    }

                    if (subStrHasEqcValue) {
                        // subStr has an eqc constant value
                        zstring subStrConst;
                        u.str.is_string(substrValue, subStrConst);

                        TRACE("t_str_detail", tout << "strConst = " << strConst << ", subStrConst = " << subStrConst << "\n";);

                        if (strConst.contains(subStrConst)) {
                            //implyR = ctx.mk_eq(ctx, boolVar, Z3_mk_true(ctx));
                            implyR = boolVar;
                        } else {
                            //implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
                            implyR = mk_not(m, boolVar);
                        }
                    } else {
                        // ------------------------------------------------------------------------------------------------
                        // subStr doesn't have an eqc constant value
                        // however, subStr equals to some concat(arg_1, arg_2, ..., arg_n)
                        // if arg_j is a constant and is not a part of the strConst, it's sure that the contains is false
                        // ** This check is needed here because the "strConst" and "strAst" may not be in a same eqc yet
                        // ------------------------------------------------------------------------------------------------
                        // collect eqc concat
                        std::set<expr*> eqcConcats;
                        get_concats_in_eqc(substrAst, eqcConcats);
                        for (expr * aConcat : eqcConcats) {
                            expr_ref_vector constList(m);
                            bool counterEgFound = false;
                            get_const_str_asts_in_node(aConcat, constList);
                            for (auto const& cst : constList) {
                                zstring pieceStr;
                                u.str.is_string(cst, pieceStr);
                                if (!strConst.contains(pieceStr)) {
                                    counterEgFound = true;
                                    if (aConcat != substrAst) {
                                        litems.push_back(ctx.mk_eq_atom(substrAst, aConcat));
                                    }
                                    implyR = mk_not(m, boolVar);
                                    break;
                                }
                            }
                            if (counterEgFound) {
                                TRACE("str", tout << "Inconsistency found!" << std::endl;);
                                break;
                            }
                        }
                    }
                    // add assertion
                    if (implyR) {
                        expr_ref implyLHS(mk_and(litems), m);
                        assert_implication(implyLHS, implyR);
                    }
                }
                // varEqcNode is subStr
                else if (substrAst == varNode) {
                    expr_ref implyR(m);
                    litems.reset();

                    if (substrAst != constNode) {
                        litems.push_back(ctx.mk_eq_atom(substrAst, constNode));
                    }
                    bool strHasEqcValue = false;
                    expr * strValue = get_eqc_value(strAst, strHasEqcValue);
                    if (strValue != strAst) {
                        litems.push_back(ctx.mk_eq_atom(strAst, strValue));
                    }

                    if (strHasEqcValue) {
                        zstring strConst, subStrConst;
                        u.str.is_string(strValue, strConst);
                        u.str.is_string(constNode, subStrConst);
                        if (strConst.contains(subStrConst)) {
                            //implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx));
                            implyR = boolVar;
                        } else {
                            // implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
                            implyR = mk_not(m, boolVar);
                        }
                    }

                    // add assertion
                    if (implyR) {
                        expr_ref implyLHS(mk_and(litems), m);
                        assert_implication(implyLHS, implyR);
                    }
                }
            } // for (itor1 : contains_map)
        } // if varNode in contain_pair_idx_map
    }

    void theory_str::check_contain_by_substr(expr * varNode, expr_ref_vector & willEqClass) {
        ast_manager & m = get_manager();
        expr_ref_vector litems(m);

        if (contain_pair_idx_map.contains(varNode)) {
            for (auto entry : contain_pair_idx_map[varNode]) {
                expr * strAst = entry.first;
                expr * substrAst = entry.second;

                expr * boolVar = nullptr;
                if (!contain_pair_bool_map.find(strAst, substrAst, boolVar)) {
                    TRACE("str", tout << "warning: no entry for boolVar in contain_pair_bool_map" << std::endl;);
                }

                // we only want to inspect the Contains terms where either of strAst or substrAst
                // are equal to varNode.

                TRACE("t_str_detail", tout << "considering Contains with strAst = " << mk_pp(strAst, m) << ", substrAst = " << mk_pp(substrAst, m) << "..." << std::endl;);

                if (varNode != strAst && varNode != substrAst) {
                    TRACE("str", tout << "varNode not equal to strAst or substrAst, skip" << std::endl;);
                    continue;
                }
                TRACE("str", tout << "varNode matched one of strAst or substrAst. Continuing" << std::endl;);

                if (substrAst == varNode) {
                    bool strAstHasVal = false;
                    expr * strValue = get_eqc_value(strAst, strAstHasVal);
                    if (strAstHasVal) {
                        TRACE("str", tout << mk_pp(strAst, m) << " has constant eqc value " << mk_pp(strValue, m) << std::endl;);
                        if (strValue != strAst) {
                            litems.push_back(ctx.mk_eq_atom(strAst, strValue));
                        }
                        zstring strConst;
                        u.str.is_string(strValue, strConst);
                        // iterate eqc (also eqc-to-be) of substr
                        for (auto itAst : willEqClass) {
                            bool counterEgFound = false;
                            if (u.str.is_concat(to_app(itAst))) {
                                expr_ref_vector constList(m);
                                // get constant strings in concat
                                app * aConcat = to_app(itAst);
                                get_const_str_asts_in_node(aConcat, constList);
                                for (auto cst : constList) {
                                    zstring pieceStr;
                                    u.str.is_string(cst, pieceStr);
                                    if (!strConst.contains(pieceStr)) {
                                        TRACE("str", tout << "Inconsistency found!" << std::endl;);
                                        counterEgFound = true;
                                        if (aConcat != substrAst) {
                                            litems.push_back(ctx.mk_eq_atom(substrAst, aConcat));
                                        }
                                        expr_ref implyLHS(mk_and(litems), m);
                                        expr_ref implyR(mk_not(m, boolVar), m);
                                        assert_implication(implyLHS, implyR);
                                        break;
                                    }
                                }
                            }
                            if (counterEgFound) {
                                break;
                            }
                        }
                    }
                }
            }
        } // varNode in contain_pair_idx_map
    }

    bool theory_str::in_contain_idx_map(expr * n) {
        return contain_pair_idx_map.contains(n);
    }

    void theory_str::check_contain_by_eq_nodes(expr * n1, expr * n2) {
        ast_manager & m = get_manager();

        if (in_contain_idx_map(n1) && in_contain_idx_map(n2)) {
            for (auto const& key1 : contain_pair_idx_map[n1]) {
                // keysItor1 is on set {<.., n1>, ..., <n1, ...>, ...}
                //std::pair<expr*, expr*> key1 = *keysItor1;
                if (key1.first == n1 && key1.second == n2) {
                    expr_ref implyL(m);
                    expr_ref implyR(contain_pair_bool_map[key1], m);
                    if (n1 != n2) {
                        implyL = ctx.mk_eq_atom(n1, n2);
                        assert_implication(implyL, implyR);
                    } else {
                        assert_axiom(implyR);
                    }
                }

                for (auto const& key2 : contain_pair_idx_map[n2]) {
                    // keysItor2 is on set {<.., n2>, ..., <n2, ...>, ...}
                    //std::pair<expr*, expr*> key2 = *keysItor2;
                    // skip if the pair is eq
                    if (key1 == key2) {
                        continue;
                    }

                    // ***************************
                    // Case 1: Contains(m, ...) /\ Contains(n, ) /\ m = n
                    // ***************************
                    if (key1.first == n1 && key2.first == n2) {
                        expr * subAst1 = key1.second;
                        expr * subAst2 = key2.second;
                        bool subAst1HasValue = false;
                        bool subAst2HasValue = false;
                        expr * subValue1 = get_eqc_value(subAst1, subAst1HasValue);
                        expr * subValue2 = get_eqc_value(subAst2, subAst2HasValue);

                        TRACE("str",
                              tout << "(Contains " << mk_pp(n1, m) << " " << mk_pp(subAst1, m) << ")" << std::endl;
                              tout << "(Contains " << mk_pp(n2, m) << " " << mk_pp(subAst2, m) << ")" << std::endl;
                              if (subAst1 != subValue1) {
                                  tout << mk_pp(subAst1, m) << " = " << mk_pp(subValue1, m) << std::endl;
                              }
                              if (subAst2 != subValue2) {
                                  tout << mk_pp(subAst2, m) << " = " << mk_pp(subValue2, m) << std::endl;
                              }
                              );

                        if (subAst1HasValue && subAst2HasValue) {
                            expr_ref_vector litems1(m);
                            if (n1 != n2) {
                                litems1.push_back(ctx.mk_eq_atom(n1, n2));
                            }
                            if (subValue1 != subAst1) {
                                litems1.push_back(ctx.mk_eq_atom(subAst1, subValue1));
                            }
                            if (subValue2 != subAst2) {
                                litems1.push_back(ctx.mk_eq_atom(subAst2, subValue2));
                            }

                            zstring subConst1, subConst2;
                            u.str.is_string(subValue1, subConst1);
                            u.str.is_string(subValue2, subConst2);
                            expr_ref implyR(m);
                            if (subConst1 == subConst2) {
                                // key1.first = key2.first /\ key1.second = key2.second
                                // ==> (containPairBoolMap[key1] = containPairBoolMap[key2])
                                implyR = ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            } else if (subConst1.contains(subConst2)) {
                                // key1.first = key2.first /\ Contains(key1.second, key2.second)
                                // ==> (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                implyR = rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            } else if (subConst2.contains(subConst1)) {
                                // key1.first = key2.first /\ Contains(key2.second, key1.second)
                                // ==> (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                implyR = rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]);
                            }

                            if (implyR) {
                                if (litems1.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems1), implyR);
                                }
                            }
                        } else {
                            expr_ref_vector subAst1Eqc(m);
                            expr_ref_vector subAst2Eqc(m);
                            collect_eq_nodes(subAst1, subAst1Eqc);
                            collect_eq_nodes(subAst2, subAst2Eqc);

                            if (subAst1Eqc.contains(subAst2)) {
                                // -----------------------------------------------------------
                                // * key1.first = key2.first /\ key1.second = key2.second
                                //   -->  containPairBoolMap[key1] = containPairBoolMap[key2]
                                // -----------------------------------------------------------
                                expr_ref_vector litems2(m);
                                if (n1 != n2) {
                                    litems2.push_back(ctx.mk_eq_atom(n1, n2));
                                }
                                if (subAst1 != subAst2) {
                                    litems2.push_back(ctx.mk_eq_atom(subAst1, subAst2));
                                }
                                expr_ref implyR(ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                if (litems2.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems2), implyR);
                                }
                            } else {
                                // -----------------------------------------------------------
                                // * key1.first = key2.first
                                //   check eqc(key1.second) and eqc(key2.second)
                                // -----------------------------------------------------------
                                for (auto eqSubVar1 : subAst1Eqc) {
                                    for (auto eqSubVar2 : subAst2Eqc) {
                                        // ------------
                                        // key1.first = key2.first /\ containPairBoolMap[<eqc(key1.second), eqc(key2.second)>]
                                        // ==>  (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                        // ------------
                                        {
                                            expr_ref_vector litems3(m);
                                            if (n1 != n2) {
                                                litems3.push_back(ctx.mk_eq_atom(n1, n2));
                                            }

                                            if (eqSubVar1 != subAst1) {
                                                litems3.push_back(ctx.mk_eq_atom(subAst1, eqSubVar1));
                                            }

                                            if (eqSubVar2 != subAst2) {
                                                litems3.push_back(ctx.mk_eq_atom(subAst2, eqSubVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey1 = std::make_pair(eqSubVar1, eqSubVar2);
                                            if (contain_pair_bool_map.contains(tryKey1)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqSubVar1, m) << " " << mk_pp(eqSubVar2, m) << ")" << std::endl;);
                                                litems3.push_back(contain_pair_bool_map[tryKey1]);
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                                assert_implication(mk_and(litems3), implR);
                                            }
                                        }
                                        // ------------
                                        // key1.first = key2.first /\ containPairBoolMap[<eqc(key2.second), eqc(key1.second)>]
                                        // ==>  (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                        // ------------
                                        {
                                            expr_ref_vector litems4(m);
                                            if (n1 != n2) {
                                                litems4.push_back(ctx.mk_eq_atom(n1, n2));
                                            }

                                            if (eqSubVar1 != subAst1) {
                                                litems4.push_back(ctx.mk_eq_atom(subAst1, eqSubVar1));
                                            }

                                            if (eqSubVar2 != subAst2) {
                                                litems4.push_back(ctx.mk_eq_atom(subAst2, eqSubVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey2 = std::make_pair(eqSubVar2, eqSubVar1);
                                            if (contain_pair_bool_map.contains(tryKey2)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqSubVar2, m) << " " << mk_pp(eqSubVar1, m) << ")" << std::endl;);
                                                litems4.push_back(contain_pair_bool_map[tryKey2]);
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]), m);
                                                assert_implication(mk_and(litems4), implR);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // ***************************
                    // Case 2: Contains(..., m) /\ Contains(... , n) /\ m = n
                    // ***************************
                    else if (key1.second == n1 && key2.second == n2) {
                        expr * str1 = key1.first;
                        expr * str2 = key2.first;
                        bool str1HasValue = false;
                        bool str2HasValue = false;
                        expr * strVal1 = get_eqc_value(str1, str1HasValue);
                        expr * strVal2 = get_eqc_value(str2, str2HasValue);

                        TRACE("str",
                              tout << "(Contains " << mk_pp(str1, m) << " " << mk_pp(n1, m) << ")" << std::endl;
                              tout << "(Contains " << mk_pp(str2, m) << " " << mk_pp(n2, m) << ")" << std::endl;
                              if (str1 != strVal1) {
                                  tout << mk_pp(str1, m) << " = " << mk_pp(strVal1, m) << std::endl;
                              }
                              if (str2 != strVal2) {
                                  tout << mk_pp(str2, m) << " = " << mk_pp(strVal2, m) << std::endl;
                              }
                              );

                        if (str1HasValue && str2HasValue) {
                            expr_ref_vector litems1(m);
                            if (n1 != n2) {
                                litems1.push_back(ctx.mk_eq_atom(n1, n2));
                            }
                            if (strVal1 != str1) {
                                litems1.push_back(ctx.mk_eq_atom(str1, strVal1));
                            }
                            if (strVal2 != str2) {
                                litems1.push_back(ctx.mk_eq_atom(str2, strVal2));
                            }

                            zstring const1, const2;
                            u.str.is_string(strVal1, const1);
                            u.str.is_string(strVal2, const2);
                            expr_ref implyR(m);

                            if (const1 == const2) {
                                // key1.second = key2.second /\ key1.first = key2.first
                                // ==> (containPairBoolMap[key1] = containPairBoolMap[key2])
                                implyR = ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            } else if (const1.contains(const2)) {
                                // key1.second = key2.second /\ Contains(key1.first, key2.first)
                                // ==> (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                implyR = rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]);
                            } else if (const2.contains(const1)) {
                                // key1.first = key2.first /\ Contains(key2.first, key1.first)
                                // ==> (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                implyR = rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]);
                            }

                            if (implyR) {
                                if (litems1.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems1), implyR);
                                }
                            }
                        }

                        else {
                            expr_ref_vector str1Eqc(m);
                            expr_ref_vector str2Eqc(m);
                            collect_eq_nodes(str1, str1Eqc);
                            collect_eq_nodes(str2, str2Eqc);

                            if (str1Eqc.contains(str2)) {
                                // -----------------------------------------------------------
                                // * key1.first = key2.first /\ key1.second = key2.second
                                //   -->  containPairBoolMap[key1] = containPairBoolMap[key2]
                                // -----------------------------------------------------------
                                expr_ref_vector litems2(m);
                                if (n1 != n2) {
                                    litems2.push_back(ctx.mk_eq_atom(n1, n2));
                                }
                                if (str1 != str2) {
                                    litems2.push_back(ctx.mk_eq_atom(str1, str2));
                                }
                                expr_ref implyR(ctx.mk_eq_atom(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                if (litems2.empty()) {
                                    assert_axiom(implyR);
                                } else {
                                    assert_implication(mk_and(litems2), implyR);
                                }
                            } else {
                                // -----------------------------------------------------------
                                // * key1.second = key2.second
                                //   check eqc(key1.first) and eqc(key2.first)
                                // -----------------------------------------------------------
                                for (auto const& eqStrVar1 : str1Eqc) {
                                    for (auto const& eqStrVar2 : str2Eqc) {
                                        {
                                            expr_ref_vector litems3(m);
                                            if (n1 != n2) {
                                                litems3.push_back(ctx.mk_eq_atom(n1, n2));
                                            }

                                            if (eqStrVar1 != str1) {
                                                litems3.push_back(ctx.mk_eq_atom(str1, eqStrVar1));
                                            }

                                            if (eqStrVar2 != str2) {
                                                litems3.push_back(ctx.mk_eq_atom(str2, eqStrVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey1 = std::make_pair(eqStrVar1, eqStrVar2);
                                            if (contain_pair_bool_map.contains(tryKey1)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqStrVar1, m) << " " << mk_pp(eqStrVar2, m) << ")" << std::endl;);
                                                litems3.push_back(contain_pair_bool_map[tryKey1]);

                                                // ------------
                                                // key1.second = key2.second /\ containPairBoolMap[<eqc(key1.first), eqc(key2.first)>]
                                                // ==>  (containPairBoolMap[key2] --> containPairBoolMap[key1])
                                                // ------------
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key2], contain_pair_bool_map[key1]), m);
                                                assert_implication(mk_and(litems3), implR);
                                            }
                                        }

                                        {
                                            expr_ref_vector litems4(m);
                                            if (n1 != n2) {
                                                litems4.push_back(ctx.mk_eq_atom(n1, n2));
                                            }
                                            if (eqStrVar1 != str1) {
                                                litems4.push_back(ctx.mk_eq_atom(str1, eqStrVar1));
                                            }
                                            if (eqStrVar2 != str2) {
                                                litems4.push_back(ctx.mk_eq_atom(str2, eqStrVar2));
                                            }
                                            std::pair<expr*, expr*> tryKey2 = std::make_pair(eqStrVar2, eqStrVar1);

                                            if (contain_pair_bool_map.contains(tryKey2)) {
                                                TRACE("str", tout << "(Contains " << mk_pp(eqStrVar2, m) << " " << mk_pp(eqStrVar1, m) << ")" << std::endl;);
                                                litems4.push_back(contain_pair_bool_map[tryKey2]);
                                                // ------------
                                                // key1.first = key2.first /\ containPairBoolMap[<eqc(key2.second), eqc(key1.second)>]
                                                // ==>  (containPairBoolMap[key1] --> containPairBoolMap[key2])
                                                // ------------
                                                expr_ref implR(rewrite_implication(contain_pair_bool_map[key1], contain_pair_bool_map[key2]), m);
                                                assert_implication(mk_and(litems4), implR);
                                            }
                                        }
                                    }
                                }
                            }
                        }

                    }
                }

                if (n1 == n2) {
                    break;
                }
            }
        } // (in_contain_idx_map(n1) && in_contain_idx_map(n2))
    }

    void theory_str::check_contain_in_new_eq(expr * n1, expr * n2) {
        if (contains_map.empty()) {
            return;
        }

        ast_manager & m = get_manager();
        TRACE("str", tout << "consistency check for contains wrt. " << mk_pp(n1, m) << " and " << mk_pp(n2, m) << std::endl;);

        expr_ref_vector willEqClass(m);
        expr * constStrAst_1 = collect_eq_nodes(n1, willEqClass);
        expr * constStrAst_2 = collect_eq_nodes(n2, willEqClass);
        expr * constStrAst = (constStrAst_1 != nullptr) ? constStrAst_1 : constStrAst_2;

        TRACE("str", tout << "eqc of n1 is {";
              for (expr * el : willEqClass) {
                  tout << " " << mk_pp(el, m);
              }
              tout << std::endl;
              if (constStrAst == nullptr) {
                  tout << "constStrAst = NULL" << std::endl;
              } else {
                  tout << "constStrAst = " << mk_pp(constStrAst, m) << std::endl;
              }
              );

        // step 1: we may have constant values for Contains checks now
        if (constStrAst != nullptr) {
            for (auto a : willEqClass) {
                if (a == constStrAst) {
                    continue;
                }
                check_contain_by_eqc_val(a, constStrAst);
            }
        } else {
            // no concrete value to be put in eqc, solely based on context
            // Check here is used to detected the facts as follows:
            //   * known: contains(Z, Y) /\ Z = "abcdefg" /\ Y = M
            //   * new fact: M = concat(..., "jio", ...)
            // Note that in this branch, either M or concat(..., "jio", ...) has a constant value
            // So, only need to check
            //   * "EQC(M) U EQC(concat(..., "jio", ...))" as substr and
            //   * If strAst registered has an eqc constant in the context
            // -------------------------------------------------------------
            for (auto a : willEqClass) {
                check_contain_by_substr(a, willEqClass);
            }
        }

        // ------------------------------------------
        // step 2: check for b1 = contains(x, m), b2 = contains(y, n)
        //         (1) x = y /\ m = n  ==>  b1 = b2
        //         (2) x = y /\ Contains(const(m), const(n))  ==>  (b1 -> b2)
        //         (3) x = y /\ Contains(const(n), const(m))  ==>  (b2 -> b1)
        //         (4) x = y /\ containPairBoolMap[<eqc(m), eqc(n)>]  ==>  (b1 -> b2)
        //         (5) x = y /\ containPairBoolMap[<eqc(n), eqc(m)>]  ==>  (b2 -> b1)
        //         (6) Contains(const(x), const(y)) /\ m = n  ==>  (b2 -> b1)
        //         (7) Contains(const(y), const(x)) /\ m = n  ==>  (b1 -> b2)
        //         (8) containPairBoolMap[<eqc(x), eqc(y)>] /\ m = n  ==>  (b2 -> b1)
        //         (9) containPairBoolMap[<eqc(y), eqc(x)>] /\ m = n  ==>  (b1 -> b2)
        // ------------------------------------------

        for (auto varAst1 : willEqClass) {
            for (auto varAst2 : willEqClass) {
                check_contain_by_eq_nodes(varAst1, varAst2);
            }
        }
    }

    expr * theory_str::dealias_node(expr * node, std::map<expr*, expr*> & varAliasMap, std::map<expr*, expr*> & concatAliasMap) {
        if (variable_set.find(node) != variable_set.end()) {
            return get_alias_index_ast(varAliasMap, node);
        } else if (u.str.is_concat(to_app(node))) {
            return get_alias_index_ast(concatAliasMap, node);
        }
        return node;
    }

    void theory_str::get_grounded_concats(unsigned depth,
                                          expr* node, std::map<expr*, expr*> & varAliasMap,
                                          std::map<expr*, expr*> & concatAliasMap, std::map<expr*, expr*> & varConstMap,
                                          std::map<expr*, expr*> & concatConstMap, std::map<expr*, std::map<expr*, int> > & varEqConcatMap,
                                          std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > & groundedMap) {
        // **************************************************
        // first deAlias the node if it is a var or concat
        // **************************************************
        node = dealias_node(node, varAliasMap, concatAliasMap);

        if (groundedMap.find(node) != groundedMap.end()) {
            return;
        }
        IF_VERBOSE(100, verbose_stream() << "concats " << depth << "\n";
                   if (depth > 100) verbose_stream() << mk_pp(node, get_manager()) << "\n";
                   );

        // haven't computed grounded concats for "node" (de-aliased)
        // ---------------------------------------------------------


        // const strings: node is de-aliased
        if (u.str.is_string(node)) {
            std::vector<expr*> concatNodes;
            concatNodes.push_back(node);
            groundedMap[node][concatNodes].clear();   // no condition
        }
        // Concat functions
        else if (u.str.is_concat(to_app(node))) {
            // if "node" equals to a constant string, thenjust push the constant into the concat vector
            // Again "node" has been de-aliased at the very beginning
            if (concatConstMap.find(node) != concatConstMap.end()) {
                std::vector<expr*> concatNodes;
                concatNodes.push_back(concatConstMap[node]);
                groundedMap[node][concatNodes].clear();
                groundedMap[node][concatNodes].insert(ctx.mk_eq_atom(node, concatConstMap[node]));
            }
            // node doesn't have eq constant value. Process its children.
            else {
                // merge arg0 and arg1
                expr * arg0 = to_app(node)->get_arg(0);
                expr * arg1 = to_app(node)->get_arg(1);
                expr * arg0DeAlias = dealias_node(arg0, varAliasMap, concatAliasMap);
                expr * arg1DeAlias = dealias_node(arg1, varAliasMap, concatAliasMap);
                get_grounded_concats(depth + 1, arg0DeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);
                get_grounded_concats(depth + 1, arg1DeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);

                std::map<std::vector<expr*>, std::set<expr*> >::iterator arg1_grdItor;
                for (auto const &arg0_grdItor : groundedMap[arg0DeAlias]) {
                    for (auto const &arg1_grdItor : groundedMap[arg1DeAlias]) {
                        std::vector<expr*> ndVec;
                        ndVec.insert(ndVec.end(), arg0_grdItor.first.begin(), arg0_grdItor.first.end());
                        size_t arg0VecSize = arg0_grdItor.first.size();
                        size_t arg1VecSize = arg1_grdItor.first.size();
                        if (arg0VecSize > 0 && arg1VecSize > 0 && u.str.is_string(arg0_grdItor.first[arg0VecSize - 1]) && u.str.is_string(arg1_grdItor.first[0])) {
                            ndVec.pop_back();
                            ndVec.push_back(mk_concat(arg0_grdItor.first[arg0VecSize - 1], arg1_grdItor.first[0]));
                            for (size_t i = 1; i < arg1VecSize; i++) {
                                ndVec.push_back(arg1_grdItor.first[i]);
                            }
                        } else {
                            ndVec.insert(ndVec.end(), arg1_grdItor.first.begin(), arg1_grdItor.first.end());
                        }
                        // only insert if we don't know "node = concat(ndVec)" since one set of condition leads to this is enough
                        if (groundedMap[node].find(ndVec) == groundedMap[node].end()) {
                            groundedMap[node][ndVec];
                            if (arg0 != arg0DeAlias) {
                                groundedMap[node][ndVec].insert(ctx.mk_eq_atom(arg0, arg0DeAlias));
                            }
                            groundedMap[node][ndVec].insert(arg0_grdItor.second.begin(), arg0_grdItor.second.end());

                            if (arg1 != arg1DeAlias) {
                                groundedMap[node][ndVec].insert(ctx.mk_eq_atom(arg1, arg1DeAlias));
                            }
                            groundedMap[node][ndVec].insert(arg1_grdItor.second.begin(), arg1_grdItor.second.end());
                        }
                    }
                }
            }
        }
        // string variables
        else if (variable_set.find(node) != variable_set.end()) {
            // deAliasedVar = Constant
            if (varConstMap.find(node) != varConstMap.end()) {
                std::vector<expr*> concatNodes;
                concatNodes.push_back(varConstMap[node]);
                groundedMap[node][concatNodes].clear();
                groundedMap[node][concatNodes].insert(ctx.mk_eq_atom(node, varConstMap[node]));
            }
            // deAliasedVar = someConcat
            else if (varEqConcatMap.find(node) != varEqConcatMap.end()) {
                expr * eqConcat = varEqConcatMap[node].begin()->first;
                expr * deAliasedEqConcat = dealias_node(eqConcat, varAliasMap, concatAliasMap);
                get_grounded_concats(depth + 1, deAliasedEqConcat, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);

                for (auto const &grdItor : groundedMap[deAliasedEqConcat]) {
                    std::vector<expr*> ndVec;
                    ndVec.insert(ndVec.end(), grdItor.first.begin(), grdItor.first.end());
                    // only insert if we don't know "node = concat(ndVec)" since one set of condition leads to this is enough
                    if (groundedMap[node].find(ndVec) == groundedMap[node].end()) {
                        // condition: node = deAliasedEqConcat
                        groundedMap[node][ndVec].insert(ctx.mk_eq_atom(node, deAliasedEqConcat));
                        // appending conditions for "deAliasedEqConcat = CONCAT(ndVec)"
                        groundedMap[node][ndVec].insert(grdItor.second.begin(), grdItor.second.end());
                    }
                }
            }
            // node (has been de-aliased) != constant && node (has been de-aliased) != any concat
            // just push in the deAliasedVar
            else {
                std::vector<expr*> concatNodes;
                concatNodes.push_back(node);
                groundedMap[node][concatNodes];
            }
        }
    }

    void theory_str::print_grounded_concat(expr * node, std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > & groundedMap) {
        TRACE("str", tout << mk_pp(node, get_manager()) << std::endl;);
        if (groundedMap.find(node) != groundedMap.end()) {
            for (auto const &itor : groundedMap[node]) {
                (void) itor;
                TRACE("str",
                      tout << "\t[grounded] ";
                      for (auto const &vIt : itor.first) {
                          tout << mk_pp(vIt, get_manager()) << ", ";
                      }
                      tout << std::endl;
                      tout << "\t[condition] ";
                      for (auto const &sIt : itor.second) {
                          tout << mk_pp(sIt, get_manager()) << ", ";
                      }
                      tout << std::endl;
                      );
            }
        } else {
            TRACE("str", tout << "not found" << std::endl;);
        }
    }

    bool theory_str::is_partial_in_grounded_concat(const std::vector<expr*> & strVec, const std::vector<expr*> & subStrVec) {
        size_t strCnt = strVec.size();
        size_t subStrCnt = subStrVec.size();

        if (strCnt == 0 || subStrCnt == 0) {
            return false;
        }

        // The assumption is that all consecutive constant strings are merged into one node
        if (strCnt < subStrCnt) {
            return false;
        }

        if (subStrCnt == 1) {
            zstring subStrVal;
            if (u.str.is_string(subStrVec[0], subStrVal)) {
                for (size_t i = 0; i < strCnt; i++) {
                    zstring strVal;
                    if (u.str.is_string(strVec[i], strVal)) {
                        if (strVal.contains(subStrVal)) {
                            return true;
                        }
                    }
                }
            } else {
                for (size_t i = 0; i < strCnt; i++) {
                    if (strVec[i] == subStrVec[0]) {
                        return true;
                    }
                }
            }
            return false;
        } else {
            for (size_t i = 0; i <= (strCnt - subStrCnt); i++) {
                // The first node in subStrVect should be
                //   * constant: a suffix of a note in strVec[i]
                //   * variable:
                bool firstNodesOK = true;
                zstring subStrHeadVal;
                if (u.str.is_string(subStrVec[0], subStrHeadVal)) {
                    zstring strHeadVal;
                    if (u.str.is_string(strVec[i], strHeadVal)) {
                        if (strHeadVal.length() >= subStrHeadVal.length()) {
                            zstring suffix = strHeadVal.extract(strHeadVal.length() - subStrHeadVal.length(), subStrHeadVal.length());
                            if (suffix != subStrHeadVal) {
                                firstNodesOK = false;
                            }
                        } else {
                            firstNodesOK = false;
                        }
                    } else {
                        if (subStrVec[0] != strVec[i]) {
                            firstNodesOK = false;
                        }
                    }
                }
                if (!firstNodesOK) {
                    continue;
                }

                // middle nodes
                bool midNodesOK = true;
                for (size_t j = 1; j < subStrCnt - 1; j++) {
                    if (subStrVec[j] != strVec[i + j]) {
                        midNodesOK = false;
                        break;
                    }
                }
                if (!midNodesOK) {
                    continue;
                }

                // tail nodes
                size_t tailIdx = i + subStrCnt - 1;
                zstring subStrTailVal;
                if (u.str.is_string(subStrVec[subStrCnt - 1], subStrTailVal)) {
                    zstring strTailVal;
                    if (u.str.is_string(strVec[tailIdx], strTailVal)) {
                        if (strTailVal.length() >= subStrTailVal.length()) {
                            zstring prefix = strTailVal.extract(0, subStrTailVal.length());
                            if (prefix == subStrTailVal) {
                                return true;
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                    }
                } else {
                    if (subStrVec[subStrCnt - 1] == strVec[tailIdx]) {
                        return true;
                    } else {
                        continue;
                    }
                }
            }
            return false;
        }
    }

    void theory_str::check_subsequence(expr* str, expr* strDeAlias, expr* subStr, expr* subStrDeAlias, expr* boolVar,
                                       std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > & groundedMap) {

        ast_manager & m = get_manager();
        for (auto const &itorStr : groundedMap[strDeAlias]) {
            for (auto const &itorSubStr : groundedMap[subStrDeAlias]) {
                bool contain = is_partial_in_grounded_concat(itorStr.first, itorSubStr.first);
                if (contain) {
                    expr_ref_vector litems(m);
                    if (str != strDeAlias) {
                        litems.push_back(ctx.mk_eq_atom(str, strDeAlias));
                    }
                    if (subStr != subStrDeAlias) {
                        litems.push_back(ctx.mk_eq_atom(subStr, subStrDeAlias));
                    }

                    for (auto const &i1: itorStr.second) {
                        litems.push_back(i1);
                    }
                    for (auto const &i1 : itorSubStr.second) {
                        litems.push_back(i1);
                    }

                    expr_ref implyR(boolVar, m);

                    if (litems.empty()) {
                        assert_axiom(implyR);
                    } else {
                        expr_ref implyL(mk_and(litems), m);
                        assert_implication(implyL, implyR);
                    }

                }
            }
        }
    }

    void theory_str::compute_contains(std::map<expr*, expr*> & varAliasMap,
                                      std::map<expr*, expr*> & concatAliasMap, std::map<expr*, expr*> & varConstMap,
                                      std::map<expr*, expr*> & concatConstMap, std::map<expr*, std::map<expr*, int> > & varEqConcatMap) {
        std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > groundedMap;
        for (auto const& kv : contain_pair_bool_map) {
            expr* containBoolVar = kv.get_value();
            expr* str = kv.get_key1();
            expr* subStr = kv.get_key2();

            expr* strDeAlias = dealias_node(str, varAliasMap, concatAliasMap);
            expr* subStrDeAlias = dealias_node(subStr, varAliasMap, concatAliasMap);

            get_grounded_concats(0, strDeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);
            get_grounded_concats(0, subStrDeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);

            // debugging
            print_grounded_concat(strDeAlias, groundedMap);
            print_grounded_concat(subStrDeAlias, groundedMap);

            check_subsequence(str, strDeAlias, subStr, subStrDeAlias, containBoolVar, groundedMap);
        }
    }

    bool theory_str::can_concat_eq_str(expr * concat, zstring& str) {
        unsigned int strLen = str.length();
        if (u.str.is_concat(to_app(concat))) {
            ptr_vector<expr> args;
            get_nodes_in_concat(concat, args);
            expr * ml_node = args[0];
            expr * mr_node = args[args.size() - 1];

            zstring ml_str;
            if (u.str.is_string(ml_node, ml_str)) {
                unsigned int ml_len = ml_str.length();
                if (ml_len > strLen) {
                    return false;
                }
                unsigned int cLen = ml_len;
                if (ml_str != str.extract(0, cLen)) {
                    return false;
                }
            }

            zstring mr_str;
            if (u.str.is_string(mr_node, mr_str)) {
                unsigned int mr_len = mr_str.length();
                if (mr_len > strLen) {
                    return false;
                }
                unsigned int cLen = mr_len;
                if (mr_str != str.extract(strLen - cLen, cLen)) {
                    return false;
                }
            }

            unsigned int sumLen = 0;
            for (unsigned int i = 0 ; i < args.size() ; i++) {
                expr * oneArg = args[i];
                zstring arg_str;
                if (u.str.is_string(oneArg, arg_str)) {
                    if (!str.contains(arg_str)) {
                        return false;
                    }
                    sumLen += arg_str.length();
                }
            }

            if (sumLen > strLen) {
                return false;
            }
        }
        return true;
    }

    bool theory_str::can_concat_eq_concat(expr * concat1, expr * concat2) {
        if (u.str.is_concat(to_app(concat1)) && u.str.is_concat(to_app(concat2))) {
            {
                // Suppose concat1 = (Concat X Y) and concat2 = (Concat M N).
                expr * concat1_mostL = getMostLeftNodeInConcat(concat1);
                expr * concat2_mostL = getMostLeftNodeInConcat(concat2);
                // if both X and M are constant strings, check whether they have the same prefix
                zstring concat1_mostL_str, concat2_mostL_str;
                if (u.str.is_string(concat1_mostL, concat1_mostL_str) && u.str.is_string(concat2_mostL, concat2_mostL_str)) {
                    unsigned int cLen = std::min(concat1_mostL_str.length(), concat2_mostL_str.length());
                    if (concat1_mostL_str.extract(0, cLen) != concat2_mostL_str.extract(0, cLen)) {
                        return false;
                    }
                }
            }

            {
                // Similarly, if both Y and N are constant strings, check whether they have the same suffix
                expr * concat1_mostR = getMostRightNodeInConcat(concat1);
                expr * concat2_mostR = getMostRightNodeInConcat(concat2);
                zstring concat1_mostR_str, concat2_mostR_str;
                if (u.str.is_string(concat1_mostR, concat1_mostR_str) && u.str.is_string(concat2_mostR, concat2_mostR_str)) {
                    unsigned int cLen = std::min(concat1_mostR_str.length(), concat2_mostR_str.length());
                    if (concat1_mostR_str.extract(concat1_mostR_str.length() - cLen, cLen) !=
                        concat2_mostR_str.extract(concat2_mostR_str.length() - cLen, cLen)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /*
     * Check whether n1 and n2 could be equal.
     * Returns true if n1 could equal n2 (maybe),
     * and false if n1 is definitely not equal to n2 (no).
     */
    bool theory_str::can_two_nodes_eq(expr * n1, expr * n2) {
        app * n1_curr = to_app(n1);
        app * n2_curr = to_app(n2);

        // case 0: n1_curr is const string, n2_curr is const string
        zstring n1_curr_str, n2_curr_str;
        if (u.str.is_string(n1_curr, n1_curr_str) && u.str.is_string(n2_curr, n2_curr_str)) {
            TRACE("str", tout << "checking string constants: n1=" << n1_curr_str << ", n2=" << n2_curr_str << std::endl;);
            if (n1_curr_str == n2_curr_str) {
                // TODO(mtrberzi) potential correction: if n1_curr != n2_curr,
                // assert that these two terms are in fact equal, because they ought to be
                return true;
            } else {
                return false;
            }
        }
        // case 1: n1_curr is concat, n2_curr is const string
        else if (u.str.is_concat(n1_curr) && u.str.is_string(n2_curr)) {
            zstring n2_curr_str;
            u.str.is_string(n2_curr, n2_curr_str);
            if (!can_concat_eq_str(n1_curr, n2_curr_str)) {
                return false;
            }
        }
        // case 2: n2_curr is concat, n1_curr is const string
        else if (u.str.is_concat(n2_curr) && u.str.is_string(n1_curr)) {
            zstring n1_curr_str;
            u.str.is_string(n1_curr, n1_curr_str);
            if (!can_concat_eq_str(n2_curr, n1_curr_str)) {
                return false;
            }
        }
        // case 3: both are concats
        else if (u.str.is_concat(n1_curr) && u.str.is_concat(n2_curr)) {
            if (!can_concat_eq_concat(n1_curr, n2_curr)) {
                return false;
            }
        }

        return true;
    }

    // was checkLength2ConstStr() in Z3str2
    // returns true if everything is OK, or false if inconsistency detected
    // - note that these are different from the semantics in Z3str2
    bool theory_str::check_length_const_string(expr * n1, expr * constStr) {
        ast_manager & mgr = get_manager();

        zstring tmp;
        u.str.is_string(constStr, tmp);
        rational strLen(tmp.length());

        if (u.str.is_concat(to_app(n1))) {
            ptr_vector<expr> args;
            expr_ref_vector items(mgr);

            get_nodes_in_concat(n1, args);

            rational sumLen(0);
            for (unsigned int i = 0; i < args.size(); ++i) {
                rational argLen;
                bool argLen_exists = get_len_value(args[i], argLen);
                if (argLen_exists) {
                    if (!u.str.is_string(args[i])) {
                        items.push_back(ctx.mk_eq_atom(mk_strlen(args[i]), mk_int(argLen)));
                    }
                    TRACE("str", tout << "concat arg: " << mk_pp(args[i], mgr) << " has len = " << argLen.to_string() << std::endl;);
                    sumLen += argLen;
                    if (sumLen > strLen) {
                        items.push_back(ctx.mk_eq_atom(n1, constStr));
                        expr_ref toAssert(mgr.mk_not(mk_and(items)), mgr);
                        TRACE("str", tout << "inconsistent length: concat (len = " << sumLen << ") <==> string constant (len = " << strLen << ")" << std::endl;);
                        assert_axiom(toAssert);
                        return false;
                    }
                }
            }
        } else { // !is_concat(n1)
            rational oLen;
            bool oLen_exists = get_len_value(n1, oLen);
            if (oLen_exists && oLen != strLen) {
                TRACE("str", tout << "inconsistent length: var (len = " << oLen << ") <==> string constant (len = " << strLen << ")" << std::endl;);
                expr_ref l(ctx.mk_eq_atom(n1, constStr), mgr);
                expr_ref r(ctx.mk_eq_atom(mk_strlen(n1), mk_strlen(constStr)), mgr);
                assert_implication(l, r);
                return false;
            }
        }
        rational unused;
        if (get_len_value(n1, unused) == false) {
            expr_ref l(ctx.mk_eq_atom(n1, constStr), mgr);
            expr_ref r(ctx.mk_eq_atom(mk_strlen(n1), mk_strlen(constStr)), mgr);
            assert_implication(l, r);
        }
        return true;
    }

    bool theory_str::check_length_concat_concat(expr * n1, expr * n2) {
        ast_manager & mgr = get_manager();

        ptr_vector<expr> concat1Args;
        ptr_vector<expr> concat2Args;
        get_nodes_in_concat(n1, concat1Args);
        get_nodes_in_concat(n2, concat2Args);

        bool concat1LenFixed = true;
        bool concat2LenFixed = true;

        expr_ref_vector items(mgr);

        rational sum1(0), sum2(0);

        for (unsigned int i = 0; i < concat1Args.size(); ++i) {
            expr * oneArg = concat1Args[i];
            rational argLen;
            bool argLen_exists = get_len_value(oneArg, argLen);
            if (argLen_exists) {
                sum1 += argLen;
                if (!u.str.is_string(oneArg)) {
                    items.push_back(ctx.mk_eq_atom(mk_strlen(oneArg), mk_int(argLen)));
                }
            } else {
                concat1LenFixed = false;
            }
        }

        for (unsigned int i = 0; i < concat2Args.size(); ++i) {
            expr * oneArg = concat2Args[i];
            rational argLen;
            bool argLen_exists = get_len_value(oneArg, argLen);
            if (argLen_exists) {
                sum2 += argLen;
                if (!u.str.is_string(oneArg)) {
                    items.push_back(ctx.mk_eq_atom(mk_strlen(oneArg), mk_int(argLen)));
                }
            } else {
                concat2LenFixed = false;
            }
        }

        items.push_back(ctx.mk_eq_atom(n1, n2));

        bool conflict = false;

        if (concat1LenFixed && concat2LenFixed) {
            if (sum1 != sum2) {
                conflict = true;
            }
        } else if (!concat1LenFixed && concat2LenFixed) {
            if (sum1 > sum2) {
                conflict = true;
            }
        } else if (concat1LenFixed && !concat2LenFixed) {
            if (sum1 < sum2) {
                conflict = true;
            }
        }

        if (conflict) {
            TRACE("str", tout << "inconsistent length detected in concat <==> concat" << std::endl;);
            expr_ref toAssert(mgr.mk_not(mk_and(items)), mgr);
            assert_axiom(toAssert);
            return false;
        }
        return true;
    }

    bool theory_str::check_length_concat_var(expr * concat, expr * var) {
        ast_manager & mgr = get_manager();

        rational varLen;
        bool varLen_exists = get_len_value(var, varLen);
        if (!varLen_exists) {
            return true;
        } else {
            rational sumLen(0);
            ptr_vector<expr> args;
            expr_ref_vector items(mgr);
            get_nodes_in_concat(concat, args);
            for (unsigned int i = 0; i < args.size(); ++i) {
                expr * oneArg = args[i];
                rational argLen;
                bool argLen_exists = get_len_value(oneArg, argLen);
                if (argLen_exists) {
                    if (!u.str.is_string(oneArg) && !argLen.is_zero()) {
                        items.push_back(ctx.mk_eq_atom(mk_strlen(oneArg), mk_int(argLen)));
                    }
                    sumLen += argLen;
                    if (sumLen > varLen) {
                        TRACE("str", tout << "inconsistent length detected in concat <==> var" << std::endl;);
                        items.push_back(ctx.mk_eq_atom(mk_strlen(var), mk_int(varLen)));
                        items.push_back(ctx.mk_eq_atom(concat, var));
                        expr_ref toAssert(mgr.mk_not(mk_and(items)), mgr);
                        assert_axiom(toAssert);
                        return false;
                    }
                }
            }
            return true;
        }
    }

    bool theory_str::check_length_var_var(expr * var1, expr * var2) {
        ast_manager & mgr = get_manager();

        rational var1Len, var2Len;
        bool var1Len_exists = get_len_value(var1, var1Len);
        bool var2Len_exists = get_len_value(var2, var2Len);

        if (var1Len_exists && var2Len_exists && var1Len != var2Len) {
            TRACE("str", tout << "inconsistent length detected in var <==> var" << std::endl;);
            expr_ref_vector items(mgr);
            items.push_back(ctx.mk_eq_atom(mk_strlen(var1), mk_int(var1Len)));
            items.push_back(ctx.mk_eq_atom(mk_strlen(var2), mk_int(var2Len)));
            items.push_back(ctx.mk_eq_atom(var1, var2));
            expr_ref toAssert(mgr.mk_not(mk_and(items)), mgr);
            assert_axiom(toAssert);
            return false;
        }
        return true;
    }

    // returns true if everything is OK, or false if inconsistency detected
    // - note that these are different from the semantics in Z3str2
    bool theory_str::check_length_eq_var_concat(expr * n1, expr * n2) {
        // n1 and n2 are not const string: either variable or concat
        bool n1Concat = u.str.is_concat(to_app(n1));
        bool n2Concat = u.str.is_concat(to_app(n2));
        if (n1Concat && n2Concat) {
            return check_length_concat_concat(n1, n2);
        }
        // n1 is concat, n2 is variable
        else if (n1Concat && (!n2Concat)) {
            return check_length_concat_var(n1, n2);
        }
        // n1 is variable, n2 is concat
        else if ((!n1Concat) && n2Concat) {
            return check_length_concat_var(n2, n1);
        }
        // n1 and n2 are both variables
        else {
            return check_length_var_var(n1, n2);
        }
        return true;
    }

    // returns false if an inconsistency is detected, or true if no inconsistencies were found
    // - note that these are different from the semantics of checkLengConsistency() in Z3str2
    bool theory_str::check_length_consistency(expr * n1, expr * n2) {
        if (u.str.is_string(n1) && u.str.is_string(n2)) {
            // consistency has already been checked in can_two_nodes_eq().
            return true;
        } else if (u.str.is_string(n1) && (!u.str.is_string(n2))) {
            return check_length_const_string(n2, n1);
        } else if (u.str.is_string(n2) && (!u.str.is_string(n1))) {
            return check_length_const_string(n1, n2);
        } else {
            // n1 and n2 are vars or concats
            return check_length_eq_var_concat(n1, n2);
        }
        return true;
    }

    // Modified signature: returns true if nothing was learned, or false if at least one axiom was asserted.
    // (This is used for deferred consistency checking)
    bool theory_str::check_concat_len_in_eqc(expr * concat) {
        bool no_assertions = true;

        expr * eqc_n = concat;
        do {
            if (u.str.is_concat(to_app(eqc_n))) {
                rational unused;
                bool status = infer_len_concat(eqc_n, unused);
                if (status) {
                    no_assertions = false;
                }
            }
            eqc_n = get_eqc_next(eqc_n);
        } while (eqc_n != concat);

        return no_assertions;
    }

    /*
     * strArgmt::solve_concat_eq_str()
     * Solve concatenations of the form:
     *   const == Concat(const, X)
     *   const == Concat(X, const)
     */
    void theory_str::solve_concat_eq_str(expr * concat, expr * str) {
        ast_manager & m = get_manager();

        TRACE("str", tout << mk_ismt2_pp(concat, m) << " == " << mk_ismt2_pp(str, m) << std::endl;);

        zstring const_str;
        if (u.str.is_concat(to_app(concat)) && u.str.is_string(to_app(str), const_str)) {
            app * a_concat = to_app(concat);
            SASSERT(a_concat->get_num_args() == 2);
            expr * a1 = a_concat->get_arg(0);
            expr * a2 = a_concat->get_arg(1);

            if (const_str.empty()) {
                TRACE("str", tout << "quick path: concat == \"\"" << std::endl;);
                // assert the following axiom:
                // ( (Concat a1 a2) == "" ) -> ( (a1 == "") AND (a2 == "") )


                expr_ref premise(ctx.mk_eq_atom(concat, str), m);
                expr_ref c1(ctx.mk_eq_atom(a1, str), m);
                expr_ref c2(ctx.mk_eq_atom(a2, str), m);
                expr_ref conclusion(m.mk_and(c1, c2), m);
                assert_implication(premise, conclusion);

                return;
            }
            bool arg1_has_eqc_value = false;
            bool arg2_has_eqc_value = false;
            expr * arg1 = get_eqc_value(a1, arg1_has_eqc_value);
            expr * arg2 = get_eqc_value(a2, arg2_has_eqc_value);
            expr_ref newConcat(m);
            if (arg1 != a1 || arg2 != a2) {
                TRACE("str", tout << "resolved concat argument(s) to eqc string constants" << std::endl;);
                expr_ref_vector item1(m);
                if (a1 != arg1) {
                    item1.push_back(ctx.mk_eq_atom(a1, arg1));
                }
                if (a2 != arg2) {
                    item1.push_back(ctx.mk_eq_atom(a2, arg2));
                }
                expr_ref implyL1(mk_and(item1), m);
                newConcat = mk_concat(arg1, arg2);
                if (newConcat != str) {
                    expr_ref implyR1(ctx.mk_eq_atom(concat, newConcat), m);
                    assert_implication(implyL1, implyR1);
                }
            } else {
                newConcat = concat;
            }
            if (newConcat == str) {
                return;
            }
            if (!u.str.is_concat(to_app(newConcat))) {
                return;
            }
            if (arg1_has_eqc_value && arg2_has_eqc_value) {
                // Case 1: Concat(const, const) == const
                TRACE("str", tout << "Case 1: Concat(const, const) == const" << std::endl;);
                zstring arg1_str, arg2_str;
                u.str.is_string(arg1, arg1_str);
                u.str.is_string(arg2, arg2_str);

                zstring result_str = arg1_str + arg2_str;
                if (result_str != const_str) {
                    // Inconsistency
                    TRACE("str", tout << "inconsistency detected: \""
                          << arg1_str << "\" + \"" << arg2_str <<
                          "\" != \"" << const_str << "\"" << "\n";);
                    expr_ref equality(ctx.mk_eq_atom(concat, str), m);
                    expr_ref diseq(mk_not(m, equality), m);
                    assert_axiom(diseq);
                    return;
                }
            } else if (!arg1_has_eqc_value && arg2_has_eqc_value) {
                // Case 2: Concat(var, const) == const
                TRACE("str", tout << "Case 2: Concat(var, const) == const" << std::endl;);
                zstring arg2_str;
                u.str.is_string(arg2, arg2_str);
                unsigned int resultStrLen = const_str.length();
                unsigned int arg2StrLen = arg2_str.length();
                if (resultStrLen < arg2StrLen) {
                    // Inconsistency
                    TRACE("str", tout << "inconsistency detected: \""
                          << arg2_str <<
                          "\" is longer than \"" << const_str << "\","
                          << " so cannot be concatenated with anything to form it" << "\n";);
                    expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                    expr_ref diseq(mk_not(m, equality), m);
                    assert_axiom(diseq);
                    return;
                } else {
                    int varStrLen = resultStrLen - arg2StrLen;
                    zstring firstPart = const_str.extract(0, varStrLen);
                    zstring secondPart = const_str.extract(varStrLen, arg2StrLen);
                    if (arg2_str != secondPart) {
                        // Inconsistency
                        TRACE("str", tout << "inconsistency detected: "
                              << "suffix of concatenation result expected \"" << secondPart << "\", "
                              << "actually \"" << arg2_str << "\""
                              << "\n";);
                        expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref diseq(mk_not(m, equality), m);
                        assert_axiom(diseq);
                        return;
                    } else {
                        expr_ref tmpStrConst(mk_string(firstPart), m);
                        expr_ref premise(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref conclusion(ctx.mk_eq_atom(arg1, tmpStrConst), m);
                        assert_implication(premise, conclusion);
                        return;
                    }
                }
            } else if (arg1_has_eqc_value && !arg2_has_eqc_value) {
                // Case 3: Concat(const, var) == const
                TRACE("str", tout << "Case 3: Concat(const, var) == const" << std::endl;);
                zstring arg1_str;
                u.str.is_string(arg1, arg1_str);
                unsigned int resultStrLen = const_str.length();
                unsigned int arg1StrLen = arg1_str.length();
                if (resultStrLen < arg1StrLen) {
                    // Inconsistency
                    TRACE("str", tout << "inconsistency detected: \""
                          << arg1_str <<
                          "\" is longer than \"" << const_str << "\","
                          << " so cannot be concatenated with anything to form it" << "\n";);
                    expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                    expr_ref diseq(m.mk_not(equality), m);
                    assert_axiom(diseq);
                    return;
                } else {
                    int varStrLen = resultStrLen - arg1StrLen;
                    zstring firstPart = const_str.extract(0, arg1StrLen);
                    zstring secondPart = const_str.extract(arg1StrLen, varStrLen);
                    if (arg1_str != firstPart) {
                        // Inconsistency
                        TRACE("str", tout << "inconsistency detected: "
                              << "prefix of concatenation result expected \"" << secondPart << "\", "
                              << "actually \"" << arg1_str << "\""
                              << "\n";);
                        expr_ref equality(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref diseq(m.mk_not(equality), m);
                        assert_axiom(diseq);
                        return;
                    } else {
                        expr_ref tmpStrConst(mk_string(secondPart), m);
                        expr_ref premise(ctx.mk_eq_atom(newConcat, str), m);
                        expr_ref conclusion(ctx.mk_eq_atom(arg2, tmpStrConst), m);
                        assert_implication(premise, conclusion);
                        return;
                    }
                }
            } else {
                // Case 4: Concat(var, var) == const
                TRACE("str", tout << "Case 4: Concat(var, var) == const" << std::endl;);
                if (eval_concat(arg1, arg2) == nullptr) {
                    rational arg1Len, arg2Len;
                    bool arg1Len_exists = get_len_value(arg1, arg1Len);
                    bool arg2Len_exists = get_len_value(arg2, arg2Len);
                    rational concatStrLen((unsigned)const_str.length());
                    if (arg1Len_exists || arg2Len_exists) {
                        expr_ref ax_l1(ctx.mk_eq_atom(concat, str), m);
                        expr_ref ax_l2(m);
                        zstring prefixStr, suffixStr;
                        if (arg1Len_exists) {
                            if (arg1Len.is_neg()) {
                                TRACE("str", tout << "length conflict: arg1Len = " << arg1Len << ", concatStrLen = " << concatStrLen << std::endl;);
                                expr_ref toAssert(m_autil.mk_ge(mk_strlen(arg1), mk_int(0)), m);
                                assert_axiom(toAssert);
                                return;
                            } else if (arg1Len > concatStrLen) {
                                TRACE("str", tout << "length conflict: arg1Len = " << arg1Len << ", concatStrLen = " << concatStrLen << std::endl;);
                                expr_ref ax_r1(m_autil.mk_le(mk_strlen(arg1), mk_int(concatStrLen)), m);
                                assert_implication(ax_l1, ax_r1);
                                return;
                            }

                            prefixStr = const_str.extract(0, arg1Len.get_unsigned());
                            rational concat_minus_arg1 = concatStrLen - arg1Len;
                            suffixStr = const_str.extract(arg1Len.get_unsigned(), concat_minus_arg1.get_unsigned());
                            ax_l2 = ctx.mk_eq_atom(mk_strlen(arg1), mk_int(arg1Len));
                        } else {
                            // arg2's length is available
                            if (arg2Len.is_neg()) {
                                TRACE("str", tout << "length conflict: arg2Len = " << arg2Len << ", concatStrLen = " << concatStrLen << std::endl;);
                                expr_ref toAssert(m_autil.mk_ge(mk_strlen(arg2), mk_int(0)), m);
                                assert_axiom(toAssert);
                                return;
                            } else if (arg2Len > concatStrLen) {
                                TRACE("str", tout << "length conflict: arg2Len = " << arg2Len << ", concatStrLen = " << concatStrLen << std::endl;);
                                expr_ref ax_r1(m_autil.mk_le(mk_strlen(arg2), mk_int(concatStrLen)), m);
                                assert_implication(ax_l1, ax_r1);
                                return;
                            }

                            rational concat_minus_arg2 = concatStrLen - arg2Len;
                            prefixStr = const_str.extract(0, concat_minus_arg2.get_unsigned());
                            suffixStr = const_str.extract(concat_minus_arg2.get_unsigned(), arg2Len.get_unsigned());
                            ax_l2 = ctx.mk_eq_atom(mk_strlen(arg2), mk_int(arg2Len));
                        }
                        // consistency check
                        if (u.str.is_concat(to_app(arg1)) && !can_concat_eq_str(arg1, prefixStr)) {
                            expr_ref ax_r(m.mk_not(ax_l2), m);
                            assert_implication(ax_l1, ax_r);
                            return;
                        }
                        if (u.str.is_concat(to_app(arg2)) && !can_concat_eq_str(arg2, suffixStr)) {
                            expr_ref ax_r(m.mk_not(ax_l2), m);
                            assert_implication(ax_l1, ax_r);
                            return;
                        }
                        expr_ref_vector r_items(m);
                        r_items.push_back(ctx.mk_eq_atom(arg1, mk_string(prefixStr)));
                        r_items.push_back(ctx.mk_eq_atom(arg2, mk_string(suffixStr)));
                        if (!arg1Len_exists) {
                            r_items.push_back(ctx.mk_eq_atom(mk_strlen(arg1), mk_int(prefixStr.length())));
                        }
                        if (!arg2Len_exists) {
                            r_items.push_back(ctx.mk_eq_atom(mk_strlen(arg2), mk_int(suffixStr.length())));
                        }
                        expr_ref lhs(m.mk_and(ax_l1, ax_l2), m);
                        expr_ref rhs(mk_and(r_items), m);
                        assert_implication(lhs, rhs);
                    } else { /* ! (arg1Len != 1 || arg2Len != 1) */
                        expr_ref xorFlag(m);
                        std::pair<expr*, expr*> key1(arg1, arg2);
                        std::pair<expr*, expr*> key2(arg2, arg1);

                        // check the entries in this map to make sure they're still in scope
                        // before we use them.

                        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry1 = varForBreakConcat.find(key1);
                        std::map<std::pair<expr*,expr*>, std::map<int, expr*> >::iterator entry2 = varForBreakConcat.find(key2);

                        bool entry1InScope;
                        if (entry1 == varForBreakConcat.end()) {
                            TRACE("str", tout << "key1 no entry" << std::endl;);
                            entry1InScope = false;
                        } else {
                            // OVERRIDE.
                            entry1InScope = true;
                            TRACE("str", tout << "key1 entry" << std::endl;);
                            /*
                              if (internal_variable_set.find((entry1->second)[0]) == internal_variable_set.end()) {
                              TRACE("str", tout << "key1 entry not in scope" << std::endl;);
                              entry1InScope = false;
                              } else {
                              TRACE("str", tout << "key1 entry in scope" << std::endl;);
                              entry1InScope = true;
                              }
                            */
                        }

                        bool entry2InScope;
                        if (entry2 == varForBreakConcat.end()) {
                            TRACE("str", tout << "key2 no entry" << std::endl;);
                            entry2InScope = false;
                        } else {
                            // OVERRIDE.
                            entry2InScope = true;
                            TRACE("str", tout << "key2 entry" << std::endl;);
                            /*
                              if (internal_variable_set.find((entry2->second)[0]) == internal_variable_set.end()) {
                              TRACE("str", tout << "key2 entry not in scope" << std::endl;);
                              entry2InScope = false;
                              } else {
                              TRACE("str", tout << "key2 entry in scope" << std::endl;);
                              entry2InScope = true;
                              }
                            */
                        }

                        TRACE("str", tout << "entry 1 " << (entry1InScope ? "in scope" : "not in scope") << std::endl
                              << "entry 2 " << (entry2InScope ? "in scope" : "not in scope") << std::endl;);

                        if (!entry1InScope && !entry2InScope) {
                            xorFlag = mk_internal_xor_var();
                            varForBreakConcat[key1][0] = xorFlag;
                        } else if (entry1InScope) {
                            xorFlag = varForBreakConcat[key1][0];
                        } else { // entry2InScope
                            xorFlag = varForBreakConcat[key2][0];
                        }

                        int concatStrLen = const_str.length();
                        int and_count = 1;

                        expr_ref_vector arrangement_disjunction(m);

                        for (int i = 0; i < concatStrLen + 1; ++i) {
                            expr_ref_vector and_items(m);
                            zstring prefixStr = const_str.extract(0, i);
                            zstring suffixStr = const_str.extract(i, concatStrLen - i);
                            // skip invalid options
                            if (u.str.is_concat(to_app(arg1)) && !can_concat_eq_str(arg1, prefixStr)) {
                                continue;
                            }
                            if (u.str.is_concat(to_app(arg2)) && !can_concat_eq_str(arg2, suffixStr)) {
                                continue;
                            }

                            expr_ref prefixAst(mk_string(prefixStr), m);
                            expr_ref arg1_eq (ctx.mk_eq_atom(arg1, prefixAst), m);
                            and_items.push_back(arg1_eq);
                            and_count += 1;

                            expr_ref suffixAst(mk_string(suffixStr), m);
                            expr_ref arg2_eq (ctx.mk_eq_atom(arg2, suffixAst), m);
                            and_items.push_back(arg2_eq);
                            and_count += 1;

                            arrangement_disjunction.push_back(mk_and(and_items));
                        }

                        expr_ref implyL(ctx.mk_eq_atom(concat, str), m);
                        expr_ref implyR1(m);
                        if (arrangement_disjunction.empty()) {
                            // negate
                            expr_ref concat_eq_str(ctx.mk_eq_atom(concat, str), m);
                            expr_ref negate_ast(m.mk_not(concat_eq_str), m);
                            assert_axiom(negate_ast);
                        } else {
                            implyR1 = mk_or(arrangement_disjunction);
                            if (m_params.m_StrongArrangements) {
                                expr_ref ax_strong(ctx.mk_eq_atom(implyL, implyR1), m);
                                assert_axiom(ax_strong);
                            } else {
                                assert_implication(implyL, implyR1);
                            }
                            generate_mutual_exclusion(arrangement_disjunction);
                        }
                    } /* (arg1Len != 1 || arg2Len != 1) */
                } /* if (Concat(arg1, arg2) == nullptr) */
            }
        }
    }

    void theory_str::handle_equality(expr * lhs, expr * rhs) {
        // both terms must be of sort String
        sort * lhs_sort = lhs->get_sort();
        sort * rhs_sort = rhs->get_sort();
        sort * str_sort = u.str.mk_string_sort();

        // Pick up new terms added during the search (e.g. recursive function expansion).
        if (!existing_toplevel_exprs.contains(lhs)) {
            existing_toplevel_exprs.insert(lhs);
            set_up_axioms(lhs);
            propagate();
        }
        if (!existing_toplevel_exprs.contains(rhs)) {
            existing_toplevel_exprs.insert(rhs);
            set_up_axioms(rhs);
            propagate();
        }

        if (lhs_sort != str_sort || rhs_sort != str_sort) {
            TRACE("str", tout << "skip equality: not String sort" << std::endl;);
            return;
        }

        if (u.str.is_concat(to_app(lhs)) && u.str.is_concat(to_app(rhs))) {
            bool nn1HasEqcValue = false;
            bool nn2HasEqcValue = false;
            expr * nn1_value = get_eqc_value(lhs, nn1HasEqcValue);
            expr * nn2_value = get_eqc_value(rhs, nn2HasEqcValue);
            if (nn1HasEqcValue && !nn2HasEqcValue) {
                simplify_parent(rhs, nn1_value);
            }
            if (!nn1HasEqcValue && nn2HasEqcValue) {
                simplify_parent(lhs, nn2_value);
            }

            expr * nn1_arg0 = to_app(lhs)->get_arg(0);
            expr * nn1_arg1 = to_app(lhs)->get_arg(1);
            expr * nn2_arg0 = to_app(rhs)->get_arg(0);
            expr * nn2_arg1 = to_app(rhs)->get_arg(1);
            if (nn1_arg0 == nn2_arg0 && in_same_eqc(nn1_arg1, nn2_arg1)) {
                TRACE("str", tout << "skip: lhs arg0 == rhs arg0" << std::endl;);
                return;
            }

            if (nn1_arg1 == nn2_arg1 && in_same_eqc(nn1_arg0, nn2_arg0)) {
                TRACE("str", tout << "skip: lhs arg1 == rhs arg1" << std::endl;);
                return;
            }
        }

        if (opt_DeferEQCConsistencyCheck) {
            TRACE("str", tout << "opt_DeferEQCConsistencyCheck is set; deferring new_eq_check call" << std::endl;);
        } else {
            // newEqCheck() -- check consistency wrt. existing equivalence classes
            if (!new_eq_check(lhs, rhs)) {
                return;
            }
        }

        // BEGIN new_eq_handler() in strTheory

        check_eqc_empty_string(lhs, rhs);
        instantiate_str_eq_length_axiom(ctx.get_enode(lhs), ctx.get_enode(rhs));

        // group terms by equivalence class (groupNodeInEqc())

        std::set<expr*> eqc_concat_lhs;
        std::set<expr*> eqc_var_lhs;
        std::set<expr*> eqc_const_lhs;
        group_terms_by_eqc(lhs, eqc_concat_lhs, eqc_var_lhs, eqc_const_lhs);

        std::set<expr*> eqc_concat_rhs;
        std::set<expr*> eqc_var_rhs;
        std::set<expr*> eqc_const_rhs;
        group_terms_by_eqc(rhs, eqc_concat_rhs, eqc_var_rhs, eqc_const_rhs);

        TRACE("str",
              tout << "lhs eqc:" << std::endl;
              tout << "Concats:" << std::endl;
              for (auto const &ex : eqc_concat_lhs) {
                  tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
              }
              tout << "Variables:" << std::endl;
              for (auto const &ex : eqc_var_lhs) {
                  tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
              }
              tout << "Constants:" << std::endl;
              for (auto const &ex : eqc_const_lhs) {
                  tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
              }

              tout << "rhs eqc:" << std::endl;
              tout << "Concats:" << std::endl;
              for (auto const &ex : eqc_concat_rhs) {
                  tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
              }
              tout << "Variables:" << std::endl;
              for (auto const &ex : eqc_var_rhs) {
                  tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
              }
              tout << "Constants:" << std::endl;
              for (auto const &ex : eqc_const_rhs) {
                  tout << mk_ismt2_pp(ex, get_manager()) << std::endl;
              }
              );

        // step 1: Concat == Concat
        check_eqc_concat_concat(eqc_concat_lhs, eqc_concat_rhs);

        // step 2: Concat == Constant

        if (!eqc_const_lhs.empty()) {
            expr * conStr = *(eqc_const_lhs.begin());
            for (auto const &itor2 : eqc_concat_rhs) {
                solve_concat_eq_str(itor2, conStr);
            }
        } else if (!eqc_const_rhs.empty()) {
            expr* conStr = *(eqc_const_rhs.begin());
            for (auto const &itor1 : eqc_concat_lhs) {
                solve_concat_eq_str(itor1, conStr);
            }
        }

        // simplify parents wrt. the equivalence class of both sides
        bool nn1HasEqcValue = false;
        bool nn2HasEqcValue = false;
        // we want the Z3str2 eqc check here...
        expr * nn1_value = z3str2_get_eqc_value(lhs, nn1HasEqcValue);
        expr * nn2_value = z3str2_get_eqc_value(rhs, nn2HasEqcValue);
        if (nn1HasEqcValue && !nn2HasEqcValue) {
            simplify_parent(rhs, nn1_value);
        }

        if (!nn1HasEqcValue && nn2HasEqcValue) {
            simplify_parent(lhs, nn2_value);
        }
    }

    // Check that a string's length can be 0 iff it is the empty string.
    void theory_str::check_eqc_empty_string(expr * lhs, expr * rhs) {
        ast_manager & m = get_manager();

        rational nn1Len, nn2Len;
        bool nn1Len_exists = get_len_value(lhs, nn1Len);
        bool nn2Len_exists = get_len_value(rhs, nn2Len);
        expr_ref emptyStr(mk_string(""), m);

        if (nn1Len_exists && nn1Len.is_zero()) {
            if (!in_same_eqc(lhs, emptyStr) && rhs != emptyStr) {
                expr_ref eql(ctx.mk_eq_atom(mk_strlen(lhs), mk_int(0)), m);
                expr_ref eqr(ctx.mk_eq_atom(lhs, emptyStr), m);
                expr_ref toAssert(ctx.mk_eq_atom(eql, eqr), m);
                assert_axiom(toAssert);
            }
        }

        if (nn2Len_exists && nn2Len.is_zero()) {
            if (!in_same_eqc(rhs, emptyStr) && lhs != emptyStr) {
                expr_ref eql(ctx.mk_eq_atom(mk_strlen(rhs), mk_int(0)), m);
                expr_ref eqr(ctx.mk_eq_atom(rhs, emptyStr), m);
                expr_ref toAssert(ctx.mk_eq_atom(eql, eqr), m);
                assert_axiom(toAssert);
            }
        }
    }

    void theory_str::check_eqc_concat_concat(std::set<expr*> & eqc_concat_lhs, std::set<expr*> & eqc_concat_rhs) {
        ast_manager & m = get_manager();
        (void)m;

        int hasCommon = 0;
        if (!eqc_concat_lhs.empty() && !eqc_concat_rhs.empty()) {
            for (auto const &itor1 : eqc_concat_lhs) {
                if (eqc_concat_rhs.find(itor1) != eqc_concat_rhs.end()) {
                    hasCommon = 1;
                    break;
                }
            }
            for (auto const &itor2 : eqc_concat_rhs) {
                if (eqc_concat_lhs.find(itor2) != eqc_concat_lhs.end()) {
                    hasCommon = 1;
                    break;
                }
            }
            if (hasCommon == 0) {
                if (opt_ConcatOverlapAvoid) {
                    bool found = false;
                    // check each pair and take the first ones that won't immediately overlap
                    for (auto const &concat_lhs : eqc_concat_lhs) {
                        if (found) {
                            break;
                        }
                        for (auto const &concat_rhs : eqc_concat_rhs) {
                            if (will_result_in_overlap(concat_lhs, concat_rhs)) {
                                TRACE("str", tout << "Concats " << mk_pp(concat_lhs, m) << " and "
                                        << mk_pp(concat_rhs, m) << " will result in overlap; skipping." << std::endl;);
                            } else {
                                TRACE("str", tout << "Concats " << mk_pp(concat_lhs, m) << " and "
                                        << mk_pp(concat_rhs, m) << " won't overlap. Simplifying here." << std::endl;);
                                simplify_concat_equality(concat_lhs, concat_rhs);
                                found = true;
                                break;
                            }
                        }
                    }
                    if (!found) {
                        TRACE("str", tout << "All pairs of concats expected to overlap, falling back." << std::endl;);
                        simplify_concat_equality(*(eqc_concat_lhs.begin()), *(eqc_concat_rhs.begin()));
                    }
                } else {
                    // default behaviour
                    simplify_concat_equality(*(eqc_concat_lhs.begin()), *(eqc_concat_rhs.begin()));
                }
            }
        }
    }

    bool theory_str::is_var(expr * e) const {
        ast_manager & m = get_manager();
        sort * ex_sort = e->get_sort();
        sort * str_sort = u.str.mk_string_sort();
        // non-string-sort terms cannot be string variables
        if (ex_sort != str_sort) return false;
        // string constants cannot be variables
        if (u.str.is_string(e)) return false;
        if (u.str.is_concat(e) || u.str.is_at(e) || u.str.is_extract(e) || u.str.is_replace(e) || u.str.is_itos(e) || u.str.is_from_code(e))
            return false;
        if (m.is_ite(e))
            return false;
        return true;
    }

    void theory_str::set_up_axioms(expr * ex) {
        ast_manager & m = get_manager();

        // workaround for #3756:
        // the map existing_toplevel_exprs is never cleared on backtracking.
        // to ensure the expressions are valid we persist validity of the
        // expression throughout the lifetime of theory_str
        m_trail.push_back(ex);

        sort * ex_sort = ex->get_sort();
        sort * str_sort = u.str.mk_string_sort();
        sort * bool_sort = m.mk_bool_sort();

        family_id m_arith_fid = m.mk_family_id("arith");
        sort * int_sort = m.mk_sort(m_arith_fid, INT_SORT);

        // reject unhandled expressions
        if (u.str.is_replace_all(ex) || u.str.is_replace_re(ex) || u.str.is_replace_re_all(ex)) {
            TRACE("str", tout << "ERROR: Z3str3 has encountered an unsupported operator. Aborting." << std::endl;);
            m.raise_exception("Z3str3 encountered an unsupported operator.");
        }

        if (ex_sort == str_sort) {
            TRACE("str", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) <<
                  ": expr is of sort String" << std::endl;);
            // set up basic string axioms
            enode * n = ctx.get_enode(ex);
            SASSERT(n);
            m_basicstr_axiom_todo.push_back(n);
            TRACE("str", tout << "add " << mk_pp(ex, m) << " to m_basicstr_axiom_todo" << std::endl;);


            if (is_app(ex)) {
                app * ap = to_app(ex);
                if (u.str.is_concat(ap)) {
                    // if ex is a concat, set up concat axioms later
                    m_concat_axiom_todo.push_back(n);
                    // we also want to check whether we can eval this concat,
                    // in case the rewriter did not totally finish with this term
                    m_concat_eval_todo.push_back(n);
                } else if (u.str.is_at(ap) || u.str.is_extract(ap) || u.str.is_replace(ap)) {
                    m_library_aware_axiom_todo.push_back(n);
                    m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                } else if (u.str.is_itos(ap)) {
                    TRACE("str", tout << "found string-integer conversion term: " << mk_pp(ex, get_manager()) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                    m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                } else if (u.str.is_from_code(ap)) {
                    TRACE("str", tout << "found string-codepoint conversion term: " << mk_pp(ex, get_manager()) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                    m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                } else if (is_var(ex)) {
                    // if ex is a variable, add it to our list of variables
                    TRACE("str", tout << "tracking variable " << mk_ismt2_pp(ap, get_manager()) << std::endl;);
                    variable_set.insert(ex);
                    ctx.mark_as_relevant(ex);
                    // this might help??
                    theory_var v = mk_var(n);
                    TRACE("str", tout << "variable " << mk_ismt2_pp(ap, get_manager()) << " is #" << v << std::endl;);
                    (void)v;
                }
            }
        } else if (ex_sort == bool_sort && !is_quantifier(ex)) {
            TRACE("str", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) <<
                  ": expr is of sort Bool" << std::endl;);
            // set up axioms for boolean terms

            ensure_enode(ex);
            if (ctx.e_internalized(ex)) {
                enode * n = ctx.get_enode(ex);
                SASSERT(n);

                if (is_app(ex)) {
                    app * ap = to_app(ex);
                    if (u.str.is_prefix(ap) || u.str.is_suffix(ap) || u.str.is_contains(ap) || u.str.is_in_re(ap) || u.str.is_is_digit(ap)) {
                        m_library_aware_axiom_todo.push_back(n);
                        m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                    }
                }
            } else {
                TRACE("str", tout << "WARNING: Bool term " << mk_ismt2_pp(ex, get_manager()) << " not internalized. Delaying axiom setup to prevent a crash." << std::endl;);
                ENSURE(!search_started); // infinite loop prevention
                m_delayed_axiom_setup_terms.push_back(ex);
                return;
            }
        } else if (ex_sort == int_sort) {
            TRACE("str", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) <<
                  ": expr is of sort Int" << std::endl;);
            // set up axioms for integer terms
            enode * n = ensure_enode(ex);
            SASSERT(n);

            if (is_app(ex)) {
                app * ap = to_app(ex);
                if (u.str.is_index(ap)) {
                    m_library_aware_axiom_todo.push_back(n);
                    m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                } else if (u.str.is_stoi(ap)) {
                    TRACE("str", tout << "found string-integer conversion term: " << mk_pp(ex, get_manager()) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                    m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                } else if (u.str.is_to_code(ex)) {
                    TRACE("str", tout << "found string-codepoint conversion term: " << mk_pp(ex, get_manager()) << std::endl;);
                    string_int_conversion_terms.push_back(ap);
                    m_library_aware_axiom_todo.push_back(n);
                    m_library_aware_trail_stack.push(push_back_trail<enode*, false>(m_library_aware_axiom_todo));
                }
            }
        } else {
            if (u.str.is_non_string_sequence(ex)) {
                TRACE("str", tout << "ERROR: Z3str3 does not support non-string sequence terms. Aborting." << std::endl;);
                m.raise_exception("Z3str3 does not support non-string sequence terms.");
            }
            TRACE("str", tout << "setting up axioms for " << mk_ismt2_pp(ex, get_manager()) <<
                  ": expr is of wrong sort, ignoring" << std::endl;);
        }

        // if expr is an application, recursively inspect all arguments
        if (is_app(ex)) {
            app * term = to_app(ex);
            unsigned num_args = term->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                set_up_axioms(term->get_arg(i));
            }
        }
    }

    void theory_str::add_theory_assumptions(expr_ref_vector & assumptions) {
        TRACE("str", tout << "add overlap assumption for theory_str" << std::endl;);
        const char* strOverlap = "!!TheoryStrOverlapAssumption!!";
        sort * s = get_manager().mk_bool_sort();
        m_theoryStrOverlapAssumption_term = expr_ref(mk_fresh_const(strOverlap, s), get_manager());
        assumptions.push_back(get_manager().mk_not(m_theoryStrOverlapAssumption_term));
    }

    lbool theory_str::validate_unsat_core(expr_ref_vector & unsat_core) {
        app * target_term = to_app(get_manager().mk_not(m_theoryStrOverlapAssumption_term));
        ctx.internalize(target_term, false);
        enode* e1 = ctx.get_enode(target_term);
        for (unsigned i = 0; i < unsat_core.size(); ++i) {
            app * core_term = to_app(unsat_core.get(i));
            // not sure if this is the correct way to compare terms in this context
            if (!ctx.e_internalized(core_term)) continue;
            enode *e2 = ctx.get_enode(core_term);
            if (e1 == e2) {
                TRACE("str", tout << "overlap detected in unsat core, changing UNSAT to UNKNOWN" << std::endl;);
                return l_undef;
            }
        }

        return l_false;
    }

    void theory_str::init_search_eh() {

        reset_internal_data_structures();

        TRACE("str",
              tout << "dumping all asserted formulas:" << std::endl;
              unsigned nFormulas = ctx.get_num_asserted_formulas();
              for (unsigned i = 0; i < nFormulas; ++i) {
                  expr * ex = ctx.get_asserted_formula(i);
                  tout << mk_pp(ex, get_manager()) << (ctx.is_relevant(ex) ? " (rel)" : " (NOT REL)") << std::endl;
              }
              );

        TRACE("str",
            expr_ref_vector formulas(get_manager());
            ctx.get_assignments(formulas);
            tout << "dumping all formulas:" << std::endl;
            for (auto const &ex : formulas) {
                tout << mk_pp(ex, get_manager()) << (ctx.is_relevant(ex) ? "" : " (NOT REL)") << std::endl;
            }
        );
        /*
         * Recursive descent through all asserted formulas to set up axioms.
         * Note that this is just the input structure and not necessarily things
         * that we know to be true or false. We're just doing this to see
         * which terms are explicitly mentioned.
         */
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr * ex = ctx.get_asserted_formula(i);
            set_up_axioms(ex);
        }

        TRACE("str", tout << "search started" << std::endl;);
        search_started = true;
    }

    void theory_str::new_eq_eh(theory_var x, theory_var y) {
        //TRACE("str", tout << "new eq: v#" << x << " = v#" << y << std::endl;);
        TRACE("str", tout << "new eq: " << mk_ismt2_pp(get_enode(x)->get_expr(), get_manager()) << " = " <<
              mk_ismt2_pp(get_enode(y)->get_expr(), get_manager()) << std::endl;);
        candidate_model.reset();

        /*
          if (m_find.find(x) == m_find.find(y)) {
          return;
          }
        */
        handle_equality(get_enode(x)->get_expr(), get_enode(y)->get_expr());

        // replicate Z3str2 behaviour: merge eqc **AFTER** handle_equality
        m_find.merge(x, y);
    }

    void theory_str::new_diseq_eh(theory_var x, theory_var y) {
        //TRACE("str", tout << "new diseq: v#" << x << " != v#" << y << std::endl;);
        TRACE("str", tout << "new diseq: " << mk_ismt2_pp(get_enode(x)->get_expr(), get_manager()) << " != " <<
              mk_ismt2_pp(get_enode(y)->get_expr(), get_manager()) << std::endl;);
        candidate_model.reset();
    }

    void theory_str::relevant_eh(app * n) {
        TRACE("str", tout << "relevant: " << mk_ismt2_pp(n, get_manager()) << std::endl;);
    }

    void theory_str::assign_eh(bool_var v, bool is_true) {
        candidate_model.reset();
        expr * e = ctx.bool_var2expr(v);
        TRACE("str", tout << "assert: v" << v << " " << mk_pp(e, get_manager()) << " is_true: " << is_true << std::endl;);
        DEBUG_CODE(
            for (auto * f : existing_toplevel_exprs) {
                SASSERT(f->get_ref_count() > 0);
            });
        if (!existing_toplevel_exprs.contains(e)) {
            existing_toplevel_exprs.insert(e);
            set_up_axioms(e);
            propagate();
        }

        // heuristics
        
        if (u.str.is_prefix(e)) {
            check_consistency_prefix(e, is_true);
        } else if (u.str.is_suffix(e)) {
            check_consistency_suffix(e, is_true);
        } else if (u.str.is_contains(e)) {
            check_consistency_contains(e, is_true);
        }
    }

    // terms like int.to.str cannot start with / end with / contain non-digit characters
    // in the future this could be expanded to regex checks as well
    void theory_str::check_consistency_prefix(expr * e, bool is_true) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr * needle = nullptr;
        expr * haystack = nullptr;

        VERIFY(u.str.is_prefix(e, needle, haystack));
        TRACE("str", tout << "check consistency of prefix predicate: " << mk_pp(needle, m) << " prefixof " << mk_pp(haystack, m) << std::endl;);
        
        zstring needleStringConstant;
        if (get_string_constant_eqc(needle, needleStringConstant)) {
            if (u.str.is_itos(haystack) && is_true) {
                // needle cannot contain non-digit characters
                for (unsigned i = 0; i < needleStringConstant.length(); ++i) {
                    if (! ('0' <= needleStringConstant[i] && needleStringConstant[i] <= '9')) {
                        TRACE("str", tout << "conflict: needle = \"" << needleStringConstant << "\" contains non-digit character, but is a prefix of int-to-string term" << std::endl;);
                        expr_ref premise(ctx.mk_eq_atom(needle, mk_string(needleStringConstant)), m);
                        expr_ref conclusion(m.mk_not(e), m);
                        expr_ref conflict(rewrite_implication(premise, conclusion), m);
                        assert_axiom_rw(conflict);
                        return;
                    }
                }
            }
        }
    }

    void theory_str::check_consistency_suffix(expr * e, bool is_true) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr * needle = nullptr;
        expr * haystack = nullptr;

        VERIFY(u.str.is_suffix(e, needle, haystack));
        TRACE("str", tout << "check consistency of suffix predicate: " << mk_pp(needle, m) << " suffixof " << mk_pp(haystack, m) << std::endl;);
        
        zstring needleStringConstant;
        if (get_string_constant_eqc(needle, needleStringConstant)) {
            if (u.str.is_itos(haystack) && is_true) {
                // needle cannot contain non-digit characters
                for (unsigned i = 0; i < needleStringConstant.length(); ++i) {
                    if (! ('0' <= needleStringConstant[i] && needleStringConstant[i] <= '9')) {
                        TRACE("str", tout << "conflict: needle = \"" << needleStringConstant << "\" contains non-digit character, but is a suffix of int-to-string term" << std::endl;);
                        expr_ref premise(ctx.mk_eq_atom(needle, mk_string(needleStringConstant)), m);
                        expr_ref conclusion(m.mk_not(e), m);
                        expr_ref conflict(rewrite_implication(premise, conclusion), m);
                        assert_axiom_rw(conflict);
                        return;
                    }
                }
            }
        }
    }

    void theory_str::check_consistency_contains(expr * e, bool is_true) {
        context & ctx = get_context();
        ast_manager & m = get_manager();
        expr * needle = nullptr;
        expr * haystack = nullptr;

        VERIFY(u.str.is_contains(e, haystack, needle)); // first string contains second one
        TRACE("str", tout << "check consistency of contains predicate: " << mk_pp(haystack, m) << " contains " << mk_pp(needle, m) << std::endl;);
        
        zstring needleStringConstant;
        if (get_string_constant_eqc(needle, needleStringConstant)) {
            if (u.str.is_itos(haystack) && is_true) {
                // needle cannot contain non-digit characters
                for (unsigned i = 0; i < needleStringConstant.length(); ++i) {
                    if (! ('0' <= needleStringConstant[i] && needleStringConstant[i] <= '9')) {
                        TRACE("str", tout << "conflict: needle = \"" << needleStringConstant << "\" contains non-digit character, but int-to-string term contains it" << std::endl;);
                        expr_ref premise(ctx.mk_eq_atom(needle, mk_string(needleStringConstant)), m);
                        expr_ref conclusion(m.mk_not(e), m);
                        expr_ref conflict(rewrite_implication(premise, conclusion), m);
                        assert_axiom_rw(conflict);
                        return;
                    }
                }
            }
        }
    }

    void theory_str::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
        m_library_aware_trail_stack.push_scope();

        sLevel += 1;
        TRACE("str", tout << "push to " << sLevel << std::endl;);
        TRACE_CODE(if (is_trace_enabled("t_str_dump_assign_on_scope_change")) { dump_assignments(); });
        candidate_model.reset();
    }

    void theory_str::recursive_check_variable_scope(expr * ex) {

        if (is_app(ex)) {
            app * a = to_app(ex);
            if (a->get_num_args() == 0) {
                // we only care about string variables
                sort * s = ex->get_sort();
                sort * string_sort = u.str.mk_string_sort();
                if (s != string_sort) {
                    return;
                }
                // base case: string constant / var
                if (u.str.is_string(a)) {
                    return;
                } else {
                    // assume var
                    if (variable_set.find(ex) == variable_set.end()
                        && internal_variable_set.find(ex) == internal_variable_set.end()) {
                        TRACE("str", tout << "WARNING: possible reference to out-of-scope variable " << mk_pp(ex, m) << std::endl;);
                    }
                }
            } else {
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    recursive_check_variable_scope(a->get_arg(i));
                }
            }
        }
    }

    void theory_str::check_variable_scope() {
        if (!opt_CheckVariableScope) {
            return;
        }

        if (!is_trace_enabled("t_str_detail")) {
            return;
        }

        TRACE("str", tout << "checking scopes of variables in the current assignment" << std::endl;);

        ast_manager & m = get_manager();

        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        for (auto const &ex : assignments) {
            recursive_check_variable_scope(ex);
        }
    }

    void theory_str::add_persisted_axiom(expr * a) {
        m_persisted_axioms.push_back(a);
    }

    void theory_str::pop_scope_eh(unsigned num_scopes) {
        sLevel -= num_scopes;
        TRACE("str", tout << "pop " << num_scopes << " to " << sLevel << std::endl;);
        candidate_model.reset();

        m_basicstr_axiom_todo.reset();
        m_concat_axiom_todo.reset();
        m_concat_eval_todo.reset();
        m_delayed_axiom_setup_terms.reset();
        m_delayed_assertions_todo.reset();
        
        TRACE_CODE(if (is_trace_enabled("t_str_dump_assign_on_scope_change")) { dump_assignments(); });

        // list of expr* to remove from cut_var_map
        ptr_vector<expr> cutvarmap_removes;

        for (auto const &varItor : cut_var_map) {
            std::stack<T_cut*> & val = cut_var_map[varItor.m_key];
            while ((!val.empty()) && (val.top()->level != 0) && (val.top()->level >= sLevel)) {
                // TRACE("str", tout << "remove cut info for " << mk_pp(e, get_manager()) << std::endl; print_cut_var(e, tout););
                // T_cut * aCut = val.top();
                val.pop();
                // dealloc(aCut);
            }
            if (val.empty()) {
                cutvarmap_removes.insert(varItor.m_key);
            }
        }

        for (expr* ex : cutvarmap_removes)
            cut_var_map.remove(ex);

        ptr_vector<enode> new_m_basicstr;
        for (enode* e : m_basicstr_axiom_todo) {
            TRACE("str", tout << "consider deleting " << mk_pp(e->get_expr(), get_manager())
                  << ", enode scope level is " << e->get_iscope_lvl()
                  << std::endl;);
            if (e->get_iscope_lvl() <= (unsigned)sLevel) {
                new_m_basicstr.push_back(e);
            }
        }
        m_basicstr_axiom_todo.reset();
        m_basicstr_axiom_todo = new_m_basicstr;

        if (ctx.is_searching()) {
            for (expr * e : m_persisted_axioms) {
                TRACE("str", tout << "persist axiom: " << mk_pp(e, get_manager()) << std::endl;);
                m_persisted_axiom_todo.push_back(e);
            }
        }

        m_trail_stack.pop_scope(num_scopes);
        // m_library_aware_trail_stack owns m_library_aware_todo vector.
        // the vector cannot be reset outside.
        m_library_aware_trail_stack.pop_scope(num_scopes);
        theory::pop_scope_eh(num_scopes);

        //check_variable_scope();
    }

    void theory_str::dump_assignments() {
        TRACE_CODE(
            ast_manager & m = get_manager();
            tout << "dumping all assignments:" << std::endl;
            expr_ref_vector assignments(m);
            ctx.get_assignments(assignments);
            for (auto const &ex : assignments) {
                tout << mk_ismt2_pp(ex, m) << (ctx.is_relevant(ex) ? "" : " (NOT REL)") << std::endl;
            }
        );
    }

    // returns true if needle appears as a subterm anywhere under haystack,
    // or if needle appears in the same EQC as a subterm anywhere under haystack
    bool theory_str::term_appears_as_subterm(expr * needle, expr * haystack) {
        if (in_same_eqc(needle, haystack)) {
            return true;
        }

        if (is_app(haystack)) {
            app * a_haystack = to_app(haystack);
            for (unsigned i = 0; i < a_haystack->get_num_args(); ++i) {
                expr * subterm = a_haystack->get_arg(i);
                if (term_appears_as_subterm(needle, subterm)) {
                    return true;
                }
            }
        }

        // not found
        return false;
    }

    void theory_str::classify_ast_by_type(expr * node, std::map<expr*, int> & varMap,
                                          std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap) {

        // check whether the node is a string variable;
        // testing set membership here bypasses several expensive checks.
        // note that internal variables don't count if they're only length tester / value tester vars.
        if (variable_set.find(node) != variable_set.end()) {
            if (varMap[node] != 1) {
                TRACE("str", tout << "new variable: " << mk_pp(node, get_manager()) << std::endl;);
            }
            varMap[node] = 1;
        }
        // check whether the node is a function that we want to inspect
        else if (is_app(node)) {
            app * aNode = to_app(node);
            if (u.str.is_length(aNode)) {
                // Length
                return;
            } else if (u.str.is_concat(aNode)) {
                expr * arg0 = aNode->get_arg(0);
                expr * arg1 = aNode->get_arg(1);
                bool arg0HasEq = false;
                bool arg1HasEq = false;
                expr * arg0Val = get_eqc_value(arg0, arg0HasEq);
                expr * arg1Val = get_eqc_value(arg1, arg1HasEq);

                int canskip = 0;
                zstring tmp;
                u.str.is_string(arg0Val, tmp);
                if (arg0HasEq && tmp.empty()) {
                    canskip = 1;
                }
                u.str.is_string(arg1Val, tmp);
                if (canskip == 0 && arg1HasEq && tmp.empty()) {
                    canskip = 1;
                }
                if (canskip == 0 && concatMap.find(node) == concatMap.end()) {
                    concatMap[node] = 1;
                }
            }
            // recursively visit all arguments
            for (unsigned i = 0; i < aNode->get_num_args(); ++i) {
                expr * arg = aNode->get_arg(i);
                classify_ast_by_type(arg, varMap, concatMap, unrollMap);
            }
        }
    }

    void theory_str::classify_ast_by_type_in_positive_context(std::map<expr*, int> & varMap,
                                                              std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap) {

        ast_manager & m = get_manager();
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);

        for (auto const &argAst : assignments) {
            // the original code jumped through some hoops to check whether the AST node
            // is a function, then checked whether that function is "interesting".
            // however, the only thing that's considered "interesting" is an equality predicate.
            // so we bypass a huge amount of work by doing the following...

            if (m.is_eq(argAst)) {
                TRACE("str", tout
                      << "eq ast " << mk_pp(argAst, m) << " is between args of sort "
                      << to_app(argAst)->get_arg(0)->get_sort()->get_name()
                      << std::endl;);
                classify_ast_by_type(argAst, varMap, concatMap, unrollMap);
            }
        }
    }

    inline expr * theory_str::get_alias_index_ast(std::map<expr*, expr*> & aliasIndexMap, expr * node) {
        if (aliasIndexMap.find(node) != aliasIndexMap.end())
            return aliasIndexMap[node];
        else
            return node;
    }

    inline expr * theory_str::getMostLeftNodeInConcat(expr * node) {
        app * aNode = to_app(node);
        if (!u.str.is_concat(aNode)) {
            return node;
        } else {
            expr * concatArgL = aNode->get_arg(0);
            return getMostLeftNodeInConcat(concatArgL);
        }
    }

    inline expr * theory_str::getMostRightNodeInConcat(expr * node) {
        app * aNode = to_app(node);
        if (!u.str.is_concat(aNode)) {
            return node;
        } else {
            expr * concatArgR = aNode->get_arg(1);
            return getMostRightNodeInConcat(concatArgR);
        }
    }

    void theory_str::trace_ctx_dep(std::ofstream & tout,
                                   std::map<expr*, expr*> & aliasIndexMap,
                                   std::map<expr*, expr*> & var_eq_constStr_map,
                                   std::map<expr*, std::map<expr*, int> > & var_eq_concat_map,
                                   std::map<expr*, std::map<expr*, int> > & var_eq_unroll_map,
                                   std::map<expr*, expr*> & concat_eq_constStr_map,
                                   std::map<expr*, std::map<expr*, int> > & concat_eq_concat_map) {
#ifdef _TRACE
        ast_manager & mgr = get_manager();
        {
            tout << "(0) alias: variables" << std::endl;
            std::map<expr*, std::map<expr*, int> > aliasSumMap;
            for (auto const &itor0 : aliasIndexMap) {
                aliasSumMap[itor0.second][itor0.first] = 1;
            }
            for (auto const &keyItor : aliasSumMap) {
                tout << "    * ";
                tout << mk_pp(keyItor.first, mgr);
                tout << " : ";
                for (auto const &innerItor : keyItor.second) {
                    tout << mk_pp(innerItor.first, mgr);
                    tout << ", ";
                }
                tout << std::endl;
            }
            tout << std::endl;
        }

        {
            tout << "(1) var = constStr:" << std::endl;
            for (auto const &itor1 : var_eq_constStr_map) {
                tout << "    * ";
                tout << mk_pp(itor1.first, mgr);
                tout << " = ";
                tout << mk_pp(itor1.second, mgr);
                if (!in_same_eqc(itor1.first, itor1.second)) {
                    tout << "   (not true in ctx)";
                }
                tout << std::endl;
            }
            tout << std::endl;
        }

        {
            tout << "(2) var = concat:" << std::endl;
            for (auto const &itor2 : var_eq_concat_map) {
                tout << "    * ";
                tout << mk_pp(itor2.first, mgr);
                tout << " = { ";
                for (auto const &i_itor : itor2.second) {
                    tout << mk_pp(i_itor.first, mgr);
                    tout << ", ";
                }
                tout << std::endl;
            }
            tout << std::endl;
        }

        {
            tout << "(3) var = unrollFunc:" << std::endl;
            for (auto const &itor2 : var_eq_unroll_map) {
                tout << "    * " << mk_pp(itor2.first, mgr) << " = { ";
                for (auto const &i_itor : itor2.second) {
                    tout << mk_pp(i_itor.first, mgr) << ", ";
                }
                tout << " }" << std::endl;
            }
            tout << std::endl;
        }

        {
            tout << "(4) concat = constStr:" << std::endl;
            for (auto const &itor3 : concat_eq_constStr_map) {
                tout << "    * ";
                tout << mk_pp(itor3.first, mgr);
                tout << " = ";
                tout << mk_pp(itor3.second, mgr);
                tout << std::endl;

            }
            tout << std::endl;
        }

        {
            tout << "(5) eq concats:" << std::endl;
            for (auto const &itor4 : concat_eq_concat_map) {
                if (itor4.second.size() > 1) {
                    tout << "    * ";
                    for (auto const &i_itor : itor4.second) {
                        tout << mk_pp(i_itor.first, mgr);
                        tout << " , ";
                    }
                    tout << std::endl;
                }
            }
            tout << std::endl;
        }

#else
        return;
#endif // _TRACE
    }


    /*
     * Dependence analysis from current context assignment
     * - "freeVarMap" contains a set of variables that doesn't constrained by Concats.
     *    But it's possible that it's bounded by unrolls
     *    For the case of
     *    (1) var1 = unroll(r1, t1)
     *        var1 is in the freeVarMap
     *        > should unroll r1 for var1
     *    (2) var1 = unroll(r1, t1) /\ var1 = Concat(var2, var3)
     *        var2, var3 are all in freeVar
     *        > should split the unroll function so that var2 and var3 are bounded by new unrolls
     */
    int theory_str::ctx_dep_analysis(std::map<expr*, int> & strVarMap, std::map<expr*, int> & freeVarMap,
                                      std::map<expr*, std::map<expr*, int> > & var_eq_concat_map) {
        std::map<expr*, int> concatMap;
        std::map<expr*, int> unrollMap;
        std::map<expr*, expr*> aliasIndexMap;
        std::map<expr*, expr*> var_eq_constStr_map;
        std::map<expr*, expr*> concat_eq_constStr_map;
        std::map<expr*, std::map<expr*, int> > var_eq_unroll_map;
        std::map<expr*, std::map<expr*, int> > concat_eq_concat_map;
        std::map<expr*, std::map<expr*, int> > depMap;

        ast_manager & m = get_manager();

        // note that the old API concatenated these assignments into
        // a massive conjunction; we may have the opportunity to avoid that here
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);

        // Step 1: get variables / concat AST appearing in the context
        // the thing we iterate over should just be variable_set - internal_variable_set
        // so we avoid computing the set difference (but this might be slower)
        for (expr* var : variable_set) {
            if (internal_variable_set.find(var) == internal_variable_set.end()) {
                TRACE("str", tout << "new variable: " << mk_pp(var, m) << std::endl;);
                strVarMap[var] = 1;
            }
        }
        classify_ast_by_type_in_positive_context(strVarMap, concatMap, unrollMap);

        // Step 2: collect alias relation
        // e.g. suppose we have the equivalence class {x, y, z};
        // then we set aliasIndexMap[y] = x
        // and aliasIndexMap[z] = x

        std::map<expr*, int>::iterator varItor = strVarMap.begin();
        for (; varItor != strVarMap.end(); ++varItor) {
            if (aliasIndexMap.find(varItor->first) != aliasIndexMap.end()) {
                continue;
            }
            expr * aRoot = nullptr;
            expr * curr = varItor->first;
            do {
                if (variable_set.find(curr) != variable_set.end()) {
                    if (aRoot == nullptr) {
                        aRoot = curr;
                    } else {
                        aliasIndexMap[curr] = aRoot;
                    }
                }
                curr = get_eqc_next(curr);
            } while (curr != varItor->first);
        }

        // Step 3: Collect interested cases

        varItor = strVarMap.begin();
        for (; varItor != strVarMap.end(); ++varItor) {
            expr * deAliasNode = get_alias_index_ast(aliasIndexMap, varItor->first);
            // Case 1: variable = string constant
            // e.g. z = "str1" ::= var_eq_constStr_map[z] = "str1"

            if (var_eq_constStr_map.find(deAliasNode) == var_eq_constStr_map.end()) {
                bool nodeHasEqcValue = false;
                expr * nodeValue = get_eqc_value(deAliasNode, nodeHasEqcValue);
                if (nodeHasEqcValue) {
                    var_eq_constStr_map[deAliasNode] = nodeValue;
                }
            }

            // Case 2: var_eq_concat
            // e.g. z = concat("str1", b) ::= var_eq_concat[z][concat(c, "str2")] = 1
            // var_eq_unroll
            // e.g. z = unroll(...) ::= var_eq_unroll[z][unroll(...)] = 1

            if (var_eq_concat_map.find(deAliasNode) == var_eq_concat_map.end()) {
                expr * curr = get_eqc_next(deAliasNode);
                while (curr != deAliasNode) {
                    app * aCurr = to_app(curr);
                    // collect concat
                    if (u.str.is_concat(aCurr)) {
                        expr * arg0 = aCurr->get_arg(0);
                        expr * arg1 = aCurr->get_arg(1);
                        bool arg0HasEqcValue = false;
                        bool arg1HasEqcValue = false;
                        expr * arg0_value = get_eqc_value(arg0, arg0HasEqcValue);
                        expr * arg1_value = get_eqc_value(arg1, arg1HasEqcValue);

                        bool is_arg0_emptyStr = false;
                        if (arg0HasEqcValue) {
                            zstring strval;
                            u.str.is_string(arg0_value, strval);
                            if (strval.empty()) {
                                is_arg0_emptyStr = true;
                            }
                        }

                        bool is_arg1_emptyStr = false;
                        if (arg1HasEqcValue) {
                            zstring strval;
                            u.str.is_string(arg1_value, strval);
                            if (strval.empty()) {
                                is_arg1_emptyStr = true;
                            }
                        }

                        if (!is_arg0_emptyStr && !is_arg1_emptyStr) {
                            var_eq_concat_map[deAliasNode][curr] = 1;
                        }
                    }

                    curr = get_eqc_next(curr);
                }
            }

        } // for(varItor in strVarMap)

        // --------------------------------------------------
        // * collect aliasing relation among eq concats
        //   e.g EQC={concat1, concat2, concat3}
        //       concats_eq_Index_map[concat2] = concat1
        //       concats_eq_Index_map[concat3] = concat1
        // --------------------------------------------------

        std::map<expr*, expr*> concats_eq_index_map;
        for(auto const &concatItor : concatMap) {
            if (concats_eq_index_map.find(concatItor.first) != concats_eq_index_map.end()) {
                continue;
            }
            expr * aRoot = nullptr;
            expr * curr = concatItor.first;
            do {
                if (u.str.is_concat(to_app(curr))) {
                    if (aRoot == nullptr) {
                        aRoot = curr;
                    } else {
                        concats_eq_index_map[curr] = aRoot;
                    }
                }
                curr = get_eqc_next(curr);
            } while (curr != concatItor.first);
        }

        for(auto const &concatItor : concatMap) {
            expr * deAliasConcat = nullptr;
            if (concats_eq_index_map.find(concatItor.first) != concats_eq_index_map.end()) {
                deAliasConcat = concats_eq_index_map[concatItor.first];
            } else {
                deAliasConcat = concatItor.first;
            }

            // (3) concat_eq_conststr, e.g. concat(a,b) = "str1"
            if (concat_eq_constStr_map.find(deAliasConcat) == concat_eq_constStr_map.end()) {
                bool nodeHasEqcValue = false;
                expr * nodeValue = get_eqc_value(deAliasConcat, nodeHasEqcValue);
                if (nodeHasEqcValue) {
                    concat_eq_constStr_map[deAliasConcat] = nodeValue;
                }
            }

            // (4) concat_eq_concat, e.g.
            // concat(a,b) = concat("str1", c) AND z = concat(a,b) AND z = concat(e,f)
            if (concat_eq_concat_map.find(deAliasConcat) == concat_eq_concat_map.end()) {
                expr * curr = deAliasConcat;
                do {
                    if (u.str.is_concat(to_app(curr))) {
                        // curr cannot be reduced
                        if (concatMap.find(curr) != concatMap.end()) {
                            concat_eq_concat_map[deAliasConcat][curr] = 1;
                        }
                    }
                    curr = get_eqc_next(curr);
                } while (curr != deAliasConcat);
            }
        }

        // print some debugging info
        TRACE("str", trace_ctx_dep(tout, aliasIndexMap, var_eq_constStr_map,
                                   var_eq_concat_map, var_eq_unroll_map,
                                   concat_eq_constStr_map, concat_eq_concat_map););

        /*
        if (!contain_pair_bool_map.empty()) {
            compute_contains(aliasIndexMap, concats_eq_index_map, var_eq_constStr_map, concat_eq_constStr_map, var_eq_concat_map);
        }
        */

        // step 4: dependence analysis

        // (1) var = string constant
        for (auto const &itor : var_eq_constStr_map) {
            expr * var = get_alias_index_ast(aliasIndexMap, itor.first);
            expr * strAst = itor.second;
            depMap[var][strAst] = 1;
        }

        // (2) var = concat
        for (auto const &itor : var_eq_concat_map) {
            expr * var = get_alias_index_ast(aliasIndexMap, itor.first);
            for (auto const &itor1 : itor.second) {
                expr * concat = itor1.first;
                std::map<expr*, int> inVarMap;
                std::map<expr*, int> inConcatMap;
                std::map<expr*, int> inUnrollMap;
                classify_ast_by_type(concat, inVarMap, inConcatMap, inUnrollMap);
                for (auto const &itor2 : inVarMap) {
                    expr * varInConcat = get_alias_index_ast(aliasIndexMap, itor2.first);
                    if (!(depMap[var].find(varInConcat) != depMap[var].end() && depMap[var][varInConcat] == 1)) {
                        depMap[var][varInConcat] = 2;
                    }
                }
            }
        }

        for (auto const &itor : var_eq_unroll_map) {
            expr * var = get_alias_index_ast(aliasIndexMap, itor.first);
            for (auto const &itor1 : itor.second) {
                expr * unrollFunc = itor1.first;
                std::map<expr*, int> inVarMap;
                std::map<expr*, int> inConcatMap;
                std::map<expr*, int> inUnrollMap;
                classify_ast_by_type(unrollFunc, inVarMap, inConcatMap, inUnrollMap);
                for (auto const &itor2 : inVarMap) {
                    expr * varInFunc = get_alias_index_ast(aliasIndexMap, itor2.first);

                    TRACE("str", tout << "var in unroll = " <<
                          mk_ismt2_pp(itor2.first, m) << std::endl
                          << "dealiased var = " << mk_ismt2_pp(varInFunc, m) << std::endl;);

                    // it's possible that we have both (Unroll $$_regVar_0 $$_unr_0) /\ (Unroll abcd $$_unr_0),
                    // while $$_regVar_0 = "abcd"
                    // have to exclude such cases
                    bool varHasValue = false;
                    get_eqc_value(varInFunc, varHasValue);
                    if (varHasValue)
                        continue;

                    if (depMap[var].find(varInFunc) == depMap[var].end()) {
                        depMap[var][varInFunc] = 6;
                    }
                }
            }
        }

        // (3) concat = string constant
        for (auto const &itor : concat_eq_constStr_map) {
            expr * concatAst = itor.first;
            expr * constStr = itor.second;
            std::map<expr*, int> inVarMap;
            std::map<expr*, int> inConcatMap;
            std::map<expr*, int> inUnrollMap;
            classify_ast_by_type(concatAst, inVarMap, inConcatMap, inUnrollMap);
            for (auto const &itor2 : inVarMap) {
                expr * varInConcat = get_alias_index_ast(aliasIndexMap, itor2.first);
                if (!(depMap[varInConcat].find(constStr) != depMap[varInConcat].end() && depMap[varInConcat][constStr] == 1))
                    depMap[varInConcat][constStr] = 3;
            }
        }

        // (4) equivalent concats
        //     - possibility 1 : concat("str", v1) = concat(concat(v2, v3), v4) = concat(v5, v6)
        //         ==> v2, v5 are constrained by "str"
        //     - possibility 2 : concat(v1, "str") = concat(v2, v3) = concat(v4, v5)
        //         ==> v2, v4 are constrained by "str"
        //--------------------------------------------------------------

        std::map<expr*, expr*> mostLeftNodes;
        std::map<expr*, expr*> mostRightNodes;

        std::map<expr*, int> mLIdxMap;
        std::map<int, std::set<expr*> > mLMap;
        std::map<expr*, int> mRIdxMap;
        std::map<int, std::set<expr*> > mRMap;
        std::set<expr*> nSet;

        for (auto const &itor : concat_eq_concat_map) {
            mostLeftNodes.clear();
            mostRightNodes.clear();

            expr * mLConst = nullptr;
            expr * mRConst = nullptr;

            for (auto const &itor1 : itor.second) {
                expr * concatNode = itor1.first;
                expr * mLNode = getMostLeftNodeInConcat(concatNode);
                zstring strval;
                if (u.str.is_string(to_app(mLNode), strval)) {
                    if (mLConst == nullptr && strval.empty()) {
                        mLConst = mLNode;
                    }
                } else {
                    mostLeftNodes[mLNode] = concatNode;
                }

                expr * mRNode = getMostRightNodeInConcat(concatNode);
                if (u.str.is_string(to_app(mRNode), strval)) {
                    if (mRConst == nullptr && strval.empty()) {
                        mRConst = mRNode;
                    }
                } else {
                    mostRightNodes[mRNode] = concatNode;
                }
            }

            if (mLConst != nullptr) {
                // -------------------------------------------------------------------------------------
                // The left most variable in a concat is constrained by a constant string in eqc concat
                // -------------------------------------------------------------------------------------
                // e.g. Concat(x, ...) = Concat("abc", ...)
                // -------------------------------------------------------------------------------------
                for (auto const &itor1 : mostLeftNodes) {
                    expr * deVar = get_alias_index_ast(aliasIndexMap, itor1.first);
                    if (depMap[deVar].find(mLConst) == depMap[deVar].end() || depMap[deVar][mLConst] != 1) {
                        depMap[deVar][mLConst] = 4;
                    }
                }
            }

            {
                // -------------------------------------------------------------------------------------
                // The left most variables in eqc concats are constrained by each other
                // -------------------------------------------------------------------------------------
                // e.g. concat(x, ...) = concat(u, ...) = ...
                //      x and u are constrained by each other
                // -------------------------------------------------------------------------------------
                nSet.clear();
                for (auto const &itl : mostLeftNodes) {
                    bool lfHasEqcValue = false;
                    get_eqc_value(itl.first, lfHasEqcValue);
                    if (lfHasEqcValue)
                        continue;
                    expr * deVar = get_alias_index_ast(aliasIndexMap, itl.first);
                    nSet.insert(deVar);
                }

                if (nSet.size() > 1) {
                    int lId = -1;
                    for (auto const &itor2 : nSet) {
                        if (mLIdxMap.find(itor2) != mLIdxMap.end()) {
                            lId = mLIdxMap[itor2];
                            break;
                        }
                    }
                    if (lId == -1)
                        lId = static_cast<int>(mLMap.size());
                    for (auto const &itor2 : nSet) {
                        bool itorHasEqcValue = false;
                        get_eqc_value(itor2, itorHasEqcValue);
                        if (itorHasEqcValue)
                            continue;
                        mLIdxMap[itor2] = lId;
                        mLMap[lId].insert(itor2);
                    }
                }
            }

            if (mRConst != nullptr) {
                for (auto const &itor1 : mostRightNodes) {
                    expr * deVar = get_alias_index_ast(aliasIndexMap, itor1.first);
                    if (depMap[deVar].find(mRConst) == depMap[deVar].end() || depMap[deVar][mRConst] != 1) {
                        depMap[deVar][mRConst] = 5;
                    }
                }
            }

            {
                nSet.clear();
                for (auto const &itr : mostRightNodes) {
                    expr * deVar = get_alias_index_ast(aliasIndexMap, itr.first);
                    nSet.insert(deVar);
                }
                if (nSet.size() > 1) {
                    int rId = -1;
                    for (auto const &itor2 : nSet) {
                        if (mRIdxMap.find(itor2) != mRIdxMap.end()) {
                            rId = mRIdxMap[itor2];
                            break;
                        }
                    }
                    if (rId == -1)
                        rId = static_cast<int>(mRMap.size());
                    for (auto const &itor2 : nSet) {
                        bool rHasEqcValue = false;
                        get_eqc_value(itor2, rHasEqcValue);
                        if (rHasEqcValue)
                            continue;
                        mRIdxMap[itor2] = rId;
                        mRMap[rId].insert(itor2);
                    }
                }
            }
        }

        // print the dependence map
        TRACE("str",
              tout << "Dependence Map" << std::endl;
              for(auto const &itor : depMap) {
                  tout << mk_pp(itor.first, m);
                  rational nnLen;
                  bool nnLen_exists = get_len_value(itor.first, nnLen);
                  tout << "  [len = " << (nnLen_exists ? nnLen.to_string() : "?") << "] \t-->\t";
                  for (auto const &itor1 : itor.second) {
                      tout << mk_pp(itor1.first, m) << "(" << itor1.second << "), ";
                  }
                  tout << std::endl;
              }
              );

        // step, errr, 5: compute free variables based on the dependence map

        // the case dependence map is empty, every var in VarMap is free
        //---------------------------------------------------------------
        // remove L/R most var in eq concat since they are constrained with each other
        std::map<expr*, std::map<expr*, int> > lrConstrainedMap;
        for (auto const &itor : mLMap) {
            for (std::set<expr*>::iterator it1 = itor.second.begin(); it1 != itor.second.end(); it1++) {
                std::set<expr*>::iterator it2 = it1;
                it2++;
                for (; it2 != itor.second.end(); it2++) {
                    expr * n1 = *it1;
                    expr * n2 = *it2;
                    lrConstrainedMap[n1][n2] = 1;
                    lrConstrainedMap[n2][n1] = 1;
                }
            }
        }
        for (auto const &itor : mRMap) {
            for (std::set<expr*>::iterator it1 = itor.second.begin(); it1 != itor.second.end(); it1++) {
                std::set<expr*>::iterator it2 = it1;
                it2++;
                for (; it2 != itor.second.end(); it2++) {
                    expr * n1 = *it1;
                    expr * n2 = *it2;
                    lrConstrainedMap[n1][n2] = 1;
                    lrConstrainedMap[n2][n1] = 1;
                }
            }
        }

        if (depMap.empty()) {
            for (auto const &itor : strVarMap) {
                expr * var = get_alias_index_ast(aliasIndexMap, itor.first);
                if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
                    freeVarMap[var] = 1;
                } else {
                    int lrConstrained = 0;
                    for (auto const &lrit : freeVarMap) {
                        if (lrConstrainedMap[var].find(lrit.first) != lrConstrainedMap[var].end()) {
                            lrConstrained = 1;
                            break;
                        }
                    }
                    if (lrConstrained == 0) {
                        freeVarMap[var] = 1;
                    }
                }
            }
        } else {
            // if the keys in aliasIndexMap are not contained in keys in depMap, they are free
            // e.g.,  x= y /\ x = z /\ t = "abc"
            //        aliasIndexMap[y]= x, aliasIndexMap[z] = x
            //        depMap        t ~ "abc"(1)
            //        x should be free
            for (auto const &itor2 : strVarMap) {
                if (aliasIndexMap.find(itor2.first) != aliasIndexMap.end()) {
                    expr * var = aliasIndexMap[itor2.first];
                    if (depMap.find(var) == depMap.end()) {
                        if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
                            freeVarMap[var] = 1;
                        } else {
                            int lrConstrained = 0;
                            for (auto const &lrit : freeVarMap) {
                                if (lrConstrainedMap[var].find(lrit.first) != lrConstrainedMap[var].end()) {
                                    lrConstrained = 1;
                                    break;
                                }
                            }
                            if (lrConstrained == 0) {
                                freeVarMap[var] = 1;
                            }
                        }
                    }
                } else if (aliasIndexMap.find(itor2.first) == aliasIndexMap.end()) {
                    // if a variable is not in aliasIndexMap and not in depMap, it's free
                    if (depMap.find(itor2.first) == depMap.end()) {
                        expr * var = itor2.first;
                        if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
                            freeVarMap[var] = 1;
                        } else {
                            int lrConstrained = 0;
                            for (auto const &lrit : freeVarMap) {
                                if (lrConstrainedMap[var].find(lrit.first) != lrConstrainedMap[var].end()) {
                                    lrConstrained = 1;
                                    break;
                                }
                            }
                            if (lrConstrained == 0) {
                                freeVarMap[var] = 1;
                            }
                        }
                    }
                }
            }

            for (auto const &itor : depMap) {
                for (auto const &itor1 : itor.second) {
                    if (variable_set.find(itor1.first) != variable_set.end()) { // expr type = var
                        expr * var = get_alias_index_ast(aliasIndexMap, itor1.first);
                        // if a var is dep on itself and all dependence are type 2, it's a free variable
                        // e.g {y --> x(2), y(2), m --> m(2), n(2)} y,m are free
                        {
                            if (depMap.find(var) == depMap.end()) {
                                if (freeVarMap.find(var) == freeVarMap.end()) {
                                    if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
                                        freeVarMap[var] = 1;
                                    } else {
                                        int lrConstrained = 0;
                                        for (auto const &lrit : freeVarMap) {
                                            if (lrConstrainedMap[var].find(lrit.first) != lrConstrainedMap[var].end()) {
                                                lrConstrained = 1;
                                                break;
                                            }
                                        }
                                        if (lrConstrained == 0) {
                                            freeVarMap[var] = 1;
                                        }
                                    }

                                } else {
                                    freeVarMap[var] = freeVarMap[var] + 1;
                                }
                            }
                        }
                    }
                }
            }
        }

        return 0;
    }

    // Attempts to convert a string to a non-negative integer.
    // Returns true if this can be done in a valid way, placing the converted value in the argument.
    // Otherwise, returns false, if str is empty or contains non-digit characters.
    bool theory_str::string_integer_conversion_valid(zstring str, rational& converted) const {
        // bool valid = true;
        converted = rational::zero();
        rational ten(10);
        if (str.length() == 0) {
            return false;
        } else {
            for (unsigned i = 0; i < str.length(); ++i) {
                if (!('0' <= str[i] && str[i] <= '9')) {
                    return false;
                } else {
                    // accumulate
                    char digit = (int)str[i];
                    std::string sDigit(1, digit);
                    int val = atoi(sDigit.c_str());
                    converted = (ten * converted) + rational(val);
                }
            }
            return true;
        }
    }

    // Check agreement between integer and string theories for the term a = (str.to-int S).
    // Returns true if axioms were added, and false otherwise.
    bool theory_str::finalcheck_str2int(app * a) {
        SASSERT(u.str.is_stoi(a));
        bool axiomAdd = false;
        ast_manager & m = get_manager();

        expr * S = a->get_arg(0);

        // check integer theory
        rational Ival;
        bool Ival_exists = get_arith_value(a, Ival);
        if (Ival_exists) {
            TRACE("str", tout << "integer theory assigns " << mk_pp(a, m) << " = " << Ival.to_string() << std::endl;);
            // if that value is not -1, and we know the length of S, we can assert (str.to.int S) = Ival --> S = "0...(len(S)-len(Ival))...0" ++ "Ival"
            if (!Ival.is_minus_one()) {
                rational Slen;
                if (get_len_value(S, Slen)) {
                    zstring Ival_str(Ival.to_string());
                    if (rational(Ival_str.length()) <= Slen) {
                        zstring padding;
                        for (rational i = rational::zero(); i < Slen - rational(Ival_str.length()); ++i) {
                            padding = padding + zstring("0");
                        }
                        expr_ref premise(ctx.mk_eq_atom(a, m_autil.mk_numeral(Ival, true)), m);
                        expr_ref conclusion(ctx.mk_eq_atom(S, mk_string(padding + Ival_str)), m);
                        expr_ref axiom(rewrite_implication(premise, conclusion), m);
                        if (!string_int_axioms.contains(axiom)) {
                            string_int_axioms.insert(axiom);
                            assert_axiom(axiom);
                            m_trail_stack.push(insert_obj_trail<expr>(string_int_axioms, axiom));
                            axiomAdd = true;
                        }
                    } else {
                        // assigned length is too short for the string value
                        expr_ref premise(ctx.mk_eq_atom(a, mk_int(Ival)), m);
                        expr_ref conclusion(m_autil.mk_ge(mk_strlen(S), mk_int(Slen)), m);
                        assert_axiom_rw(rewrite_implication(premise, conclusion));
                        axiomAdd = true;
                    }
                }
            }
        } else {
            TRACE("str", tout << "integer theory has no assignment for " << mk_pp(a, m) << std::endl;);
            expr_ref is_zero(ctx.mk_eq_atom(a, m_autil.mk_int(0)), m);
            /* literal is_zero_l = */ mk_literal(is_zero);
            axiomAdd = true;
            TRACE("str", ctx.display(tout););
        }

        bool S_hasEqcValue;
        expr * S_str = get_eqc_value(S, S_hasEqcValue);
        if (S_hasEqcValue) {
            zstring str;
            u.str.is_string(S_str, str);
            rational convertedRepresentation(0);
            // TODO this duplicates code a bit, we can simplify the branch on "conclusion" only
            if (string_integer_conversion_valid(str, convertedRepresentation)) {
                expr_ref premise(ctx.mk_eq_atom(S, mk_string(str)), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(convertedRepresentation, true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    m_trail_stack.push(insert_obj_trail<expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            } else {
                expr_ref premise(ctx.mk_eq_atom(S, mk_string(str)), m);
                expr_ref conclusion(ctx.mk_eq_atom(a, m_autil.mk_numeral(rational::minus_one(), true)), m);
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                if (!string_int_axioms.contains(axiom)) {
                    string_int_axioms.insert(axiom);
                    assert_axiom(axiom);
                    m_trail_stack.push(insert_obj_trail<expr>(string_int_axioms, axiom));
                    axiomAdd = true;
                }
            }
        }

        return axiomAdd;
    }

    bool theory_str::finalcheck_int2str(app * a) {
        SASSERT(u.str.is_itos(a));
        bool axiomAdd = false;
        ast_manager & m = get_manager();

        expr * N = a->get_arg(0);

        // check string theory
        bool Sval_expr_exists;
        expr * Sval_expr = get_eqc_value(a, Sval_expr_exists);
        if (Sval_expr_exists) {
            zstring Sval;
            u.str.is_string(Sval_expr, Sval);
            TRACE("str", tout << "string theory assigns " << mk_pp(a, m) << " = \"" << Sval << "\"\n";);
            // empty string --> integer value < 0
            if (Sval.empty()) {
                // ignore this. we should already assert the axiom for what happens when the string is ""
            } else {
                // check for leading zeroes. if the first character is '0', the entire string must be "0"
                char firstChar = (int)Sval[0];
                if (firstChar == '0' && !(Sval == zstring("0"))) {
                    TRACE("str", tout << "str.from-int argument " << Sval << " contains leading zeroes" << std::endl;);
                    expr_ref axiom(m.mk_not(ctx.mk_eq_atom(a, mk_string(Sval))), m);
                    assert_axiom(axiom);
                    return true;
                }
                // nonempty string --> convert to correct integer value, or disallow it
                rational convertedRepresentation(0);
                if (string_integer_conversion_valid(Sval, convertedRepresentation)) {
                    expr_ref premise(ctx.mk_eq_atom(a, mk_string(Sval)), m);
                    expr_ref conclusion(ctx.mk_eq_atom(N, m_autil.mk_numeral(convertedRepresentation, true)), m);
                    expr_ref axiom(rewrite_implication(premise, conclusion), m);
                    if (!string_int_axioms.contains(axiom)) {
                        string_int_axioms.insert(axiom);
                        assert_axiom(axiom);
                        m_trail_stack.push(insert_obj_trail<expr>(string_int_axioms, axiom));
                        axiomAdd = true;
                    }
                } else {
                    expr_ref axiom(m.mk_not(ctx.mk_eq_atom(a, mk_string(Sval))), m);
                    // always assert this axiom because this is a conflict clause
                    assert_axiom(axiom);
                    axiomAdd = true;
                }
            }
        } else {
            TRACE("str", tout << "string theory has no assignment for " << mk_pp(a, m) << std::endl;);
            // see if the integer theory has assigned N yet
            arith_value v(m);
            v.init(&ctx);
            rational Nval;
            if (v.get_value(N, Nval)) {
                expr_ref premise(ctx.mk_eq_atom(N, mk_int(Nval)), m);
                expr_ref conclusion(m);
                if (Nval.is_neg()) {
                    // negative argument -> ""
                    conclusion = expr_ref(ctx.mk_eq_atom(a, mk_string("")), m);
                } else {
                    // non-negative argument -> convert to string of digits
                    zstring Nval_str(Nval.to_string());
                    conclusion = expr_ref(ctx.mk_eq_atom(a, mk_string(Nval_str)), m);
                }
                expr_ref axiom(rewrite_implication(premise, conclusion), m);
                assert_axiom(axiom);
                axiomAdd = true;
            } else {
                TRACE("str", tout << "integer theory has no assignment for " << mk_pp(N, m) << std::endl;);
                expr_ref is_zero(ctx.mk_eq_atom(N, m_autil.mk_int(0)), m);
                /* literal is_zero_l = */ mk_literal(is_zero);
                axiomAdd = true;
                TRACE("str", ctx.display(tout););
            }
        }
        return axiomAdd;
    }

    void theory_str::collect_var_concat(expr * node, std::set<expr*> & varSet, std::set<expr*> & concatSet) {
        if (variable_set.find(node) != variable_set.end()) {
	    varSet.insert(node);
        }
        else if (is_app(node)) {
            app * aNode = to_app(node);
            if (u.str.is_length(aNode)) {
                // Length
                return;
            }
            if (u.str.is_concat(aNode)) {
                if (concatSet.find(node) == concatSet.end()) {
                    concatSet.insert(node);
                }
            }
            // recursively visit all arguments
            for (unsigned i = 0; i < aNode->get_num_args(); ++i) {
                expr * arg = aNode->get_arg(i);
                collect_var_concat(arg, varSet, concatSet);
            }
        }
    }

    bool theory_str::propagate_length_within_eqc(expr * var) {
        bool res = false;
        ast_manager & m = get_manager();

        TRACE("str", tout << "propagate_length_within_eqc: " << mk_ismt2_pp(var, m) << std::endl ;);

        rational varLen;
        if (! get_len_value(var, varLen)) {
            bool hasLen = false;
            expr * nodeWithLen= var;
            do {
                if (get_len_value(nodeWithLen, varLen)) {
                    hasLen = true;
                    break;
                }
                nodeWithLen = get_eqc_next(nodeWithLen);
            } while (nodeWithLen != var);

            if (hasLen) {
                // var = nodeWithLen --> |var| = |nodeWithLen|
                expr_ref_vector l_items(m);
                expr_ref varEqNode(ctx.mk_eq_atom(var, nodeWithLen), m);
                l_items.push_back(varEqNode);

                expr_ref nodeWithLenExpr (mk_strlen(nodeWithLen), m);
                expr_ref varLenExpr (mk_int(varLen), m);
                expr_ref lenEqNum(ctx.mk_eq_atom(nodeWithLenExpr, varLenExpr), m);
                l_items.push_back(lenEqNum);

                expr_ref axl(m.mk_and(l_items.size(), l_items.data()), m);
                expr_ref varLen(mk_strlen(var), m);
                expr_ref axr(ctx.mk_eq_atom(varLen, mk_int(varLen)), m);
                assert_implication(axl, axr);
                TRACE("str", tout <<  mk_ismt2_pp(axl, m) << std::endl << "  --->  " << std::endl <<  mk_ismt2_pp(axr, m););
                res = true;
            }
        }
        return res;
    }

    bool theory_str::propagate_length(std::set<expr*> & varSet, std::set<expr*> & concatSet, std::map<expr*, int> & exprLenMap) {
        ast_manager & m = get_manager();
        expr_ref_vector assignments(m);
        ctx.get_assignments(assignments);
        bool axiomAdded = false;
        // collect all concats in context
        for (auto const &it : assignments) {
            if (! ctx.is_relevant(it)) {
                continue;
            }
            if (m.is_eq(it)) {
                collect_var_concat(it, varSet, concatSet);
            }
        }
        // iterate each concat
        // if a concat doesn't have length info, check if the length of all leaf nodes can be resolved
        for (auto const &concat : concatSet) {
            rational lenValue;
            expr_ref concatlenExpr (mk_strlen(concat), m) ;
            bool allLeafResolved = true;
            if (! get_arith_value(concatlenExpr, lenValue)) {
                // the length of concat is unresolved yet
                if (get_len_value(concat, lenValue)) {
                    // but all leaf nodes have length information
                    TRACE("str", tout << "* length pop-up: " <<  mk_ismt2_pp(concat, m) << "| = " << lenValue << std::endl;);
                    std::set<expr*> leafNodes;
                    get_unique_non_concat_nodes(concat, leafNodes);
                    expr_ref_vector l_items(m);
                    for (auto const &leafIt : leafNodes) {
                        rational leafLenValue;
                        if (get_len_value(leafIt, leafLenValue)) {
                            expr_ref leafItLenExpr (mk_strlen(leafIt), m);
                            expr_ref leafLenValueExpr (mk_int(leafLenValue), m);
                            expr_ref lcExpr (ctx.mk_eq_atom(leafItLenExpr, leafLenValueExpr), m);
                            l_items.push_back(lcExpr);
                        } else {
                            allLeafResolved = false;
                            break;
                        }
                    }
                    if (allLeafResolved) {
                        expr_ref axl(m.mk_and(l_items.size(), l_items.data()), m);
                        expr_ref lenValueExpr (mk_int(lenValue), m);
                        expr_ref axr(ctx.mk_eq_atom(concatlenExpr, lenValueExpr), m);
                        assert_implication(axl, axr);
                        TRACE("str", tout <<  mk_ismt2_pp(axl, m) << std::endl << "  --->  " << std::endl <<  mk_ismt2_pp(axr, m)<< std::endl;);
                        axiomAdded = true;
                    }
                }
            }
        }
        // if no concat length is propagated, check the length of variables.
        if (! axiomAdded) {
            for (auto const &var : varSet) {
                rational lenValue;
                expr_ref varlen (mk_strlen(var), m) ;
                if (! get_arith_value(varlen, lenValue)) {
                    if (propagate_length_within_eqc(var)) {
                        axiomAdded = true;
                    }
                }
            }

        }
        return axiomAdded;
    }

    void theory_str::get_unique_non_concat_nodes(expr * node, std::set<expr*> & argSet) {
        app * a_node = to_app(node);
        if (!u.str.is_concat(a_node)) {
            argSet.insert(node);
            return;
        } else {
            SASSERT(a_node->get_num_args() == 2);
            expr * leftArg = a_node->get_arg(0);
            expr * rightArg = a_node->get_arg(1);
            get_unique_non_concat_nodes(leftArg, argSet);
            get_unique_non_concat_nodes(rightArg, argSet);
        }
    }

    final_check_status theory_str::final_check_eh() {
        ast_manager & m = get_manager();

        //expr_ref_vector assignments(m);
        //ctx.get_assignments(assignments);

        if (opt_VerifyFinalCheckProgress) {
            finalCheckProgressIndicator = false;
        }

        TRACE("str", tout << "final check" << std::endl;);
        TRACE_CODE(if (is_trace_enabled("t_str_dump_assign")) { dump_assignments(); });
        check_variable_scope();

        if (opt_DeferEQCConsistencyCheck) {
            TRACE("str", tout << "performing deferred EQC consistency check" << std::endl;);
            std::set<enode*> eqc_roots;
            for (auto const &e : ctx.enodes()) {
                enode * root = e->get_root();
                eqc_roots.insert(root);
            }

            bool found_inconsistency = false;

            for (auto const &e : eqc_roots) {
                app * a = e->get_expr();
                if (!(a->get_sort() == u.str.mk_string_sort())) {
                    TRACE("str", tout << "EQC root " << mk_pp(a, m) << " not a string term; skipping" << std::endl;);
                } else {
                    TRACE("str", tout << "EQC root " << mk_pp(a, m) << " is a string term. Checking this EQC" << std::endl;);
                    // first call check_concat_len_in_eqc() on each member of the eqc
                    enode * e_it = e;
                    enode * e_root = e_it;
                    do {
                        bool status = check_concat_len_in_eqc(e_it->get_expr());
                        if (!status) {
                            TRACE("str", tout << "concat-len check asserted an axiom on " << mk_pp(e_it->get_expr(), m) << std::endl;);
                            found_inconsistency = true;
                        }
                        e_it = e_it->get_next();
                    } while (e_it != e_root);

                    // now grab any two distinct elements from the EQC and call new_eq_check() on them
                    enode * e1 = e;
                    enode * e2 = e1->get_next();
                    if (e1 != e2) {
                        TRACE("str", tout << "deferred new_eq_check() over EQC of " << mk_pp(e1->get_expr(), m) << " and " << mk_pp(e2->get_expr(), m) << std::endl;);
                        bool result = new_eq_check(e1->get_expr(), e2->get_expr());
                        if (!result) {
                            TRACE("str", tout << "new_eq_check found inconsistencies" << std::endl;);
                            found_inconsistency = true;
                        }
                    }
                }
            }

            if (found_inconsistency) {
                TRACE("str", tout << "Found inconsistency in final check! Returning to search." << std::endl;);
                return FC_CONTINUE;
            } else {
                TRACE("str", tout << "Deferred consistency check passed. Continuing in final check." << std::endl;);
            }
        }

        // run dependence analysis to find free string variables
        std::map<expr*, int> varAppearInAssign;
        std::map<expr*, int> freeVar_map;
        std::map<expr*, std::map<expr*, int> > var_eq_concat_map;
        int conflictInDep = ctx_dep_analysis(varAppearInAssign, freeVar_map, var_eq_concat_map);
        if (conflictInDep == -1) {
            m_stats.m_solved_by = 2;
            return FC_DONE;
        }

        // enhancement: improved backpropagation of string constants into var=concat terms
        bool backpropagation_occurred = false;
        for (auto const &veqc_map_it : var_eq_concat_map) {
            expr * var = veqc_map_it.first;
            for (auto const &concat_map_it : veqc_map_it.second) {
                app * concat = to_app(concat_map_it.first);
                expr * concat_lhs = concat->get_arg(0);
                expr * concat_rhs = concat->get_arg(1);
                // If the concat LHS and RHS both have a string constant in their EQC,
                // but the var does not, then we assert an axiom of the form
                // (lhs = "lhs" AND rhs = "rhs") --> (Concat lhs rhs) = "lhsrhs"
                bool concat_lhs_haseqc, concat_rhs_haseqc, var_haseqc;
                expr * concat_lhs_str = get_eqc_value(concat_lhs, concat_lhs_haseqc);
                expr * concat_rhs_str = get_eqc_value(concat_rhs, concat_rhs_haseqc);
                get_eqc_value(var, var_haseqc);
                if (concat_lhs_haseqc && concat_rhs_haseqc && !var_haseqc) {
                    TRACE("str", tout << "backpropagate into " << mk_pp(var, m) << " = " << mk_pp(concat, m) << std::endl
                          << "LHS ~= " << mk_pp(concat_lhs_str, m) << " RHS ~= " << mk_pp(concat_rhs_str, m) << std::endl;);

                    zstring lhsString, rhsString;
                    u.str.is_string(concat_lhs_str, lhsString);
                    u.str.is_string(concat_rhs_str, rhsString);
                    zstring concatString = lhsString + rhsString;

                    // special handling: don't assert that string constants are equal to themselves
                    expr_ref_vector lhs_terms(m);
                    if (!u.str.is_string(concat_lhs)) {
                        lhs_terms.push_back(ctx.mk_eq_atom(concat_lhs, concat_lhs_str));
                    }

                    if (!u.str.is_string(concat_rhs)) {
                        lhs_terms.push_back(ctx.mk_eq_atom(concat_rhs, concat_rhs_str));

                    }

                    if (lhs_terms.empty()) {
                        // no assumptions on LHS
                        expr_ref rhs(ctx.mk_eq_atom(concat, mk_string(concatString)), m);
                        assert_axiom(rhs);
                    } else {
                        expr_ref lhs(mk_and(lhs_terms), m);
                        expr_ref rhs(ctx.mk_eq_atom(concat, mk_string(concatString)), m);
                        assert_implication(lhs, rhs);
                    }
                    backpropagation_occurred = true;
                }
            }
        }

        if (backpropagation_occurred) {
            TRACE("str", tout << "Resuming search due to axioms added by backpropagation." << std::endl;);
            return FC_CONTINUE;
        }

        // enhancement: improved backpropagation of length information
        {
            std::set<expr*> varSet;
            std::set<expr*> concatSet;
            std::map<expr*, int> exprLenMap;

            bool length_propagation_occurred = propagate_length(varSet, concatSet, exprLenMap);
            if (length_propagation_occurred) {
                TRACE("str", tout << "Resuming search due to axioms added by length propagation." << std::endl;);
                return FC_CONTINUE;
            }
        }

        if (!solve_regex_automata()) {
            TRACE("str", tout << "regex engine requested to give up!" << std::endl;);
            return FC_GIVEUP;
        }

        bool needToAssignFreeVars = false;
        expr_ref_vector free_variables(m);
        std::set<expr*> unused_internal_variables;
        { // Z3str2 free variables check
            for (auto const &itor : varAppearInAssign) {
                if (internal_variable_set.find(itor.first) != internal_variable_set.end()) {
                    // this can be ignored, I think
                    TRACE("str", tout << "free internal variable " << mk_pp(itor.first, m) << " ignored" << std::endl;);
                    continue;
                }
                bool hasEqcValue = false;
                get_eqc_value(itor.first, hasEqcValue);
                if (!hasEqcValue) {
                    TRACE("str", tout << "found free variable " << mk_pp(itor.first, m) << std::endl;);
                    needToAssignFreeVars = true;
                    free_variables.push_back(itor.first);
                    // break;
                } else {
                    // debug
                    // TRACE("str", tout << "variable " << mk_pp(itor->first, m) << " = " << mk_pp(eqcString, m) << std::endl;);
                }
            }
        }
        
        if (!needToAssignFreeVars) {

            // check string-int terms
            bool addedStrIntAxioms = false;
            for (unsigned i = 0; i < string_int_conversion_terms.size(); ++i) {
                app * ex = to_app(string_int_conversion_terms[i].get());
                if (u.str.is_stoi(ex)) {
                    bool axiomAdd = finalcheck_str2int(ex);
                    if (axiomAdd) {
                        addedStrIntAxioms = true;
                    }
                } else if (u.str.is_itos(ex)) {
                    bool axiomAdd = finalcheck_int2str(ex);
                    if (axiomAdd) {
                        addedStrIntAxioms = true;
                    }
                }
            }
            if (addedStrIntAxioms) {
                TRACE("str", tout << "Resuming search due to addition of string-integer conversion axioms." << std::endl;);
                return FC_CONTINUE;
            }

            // We must be be 100% certain that if there are any regex constraints,
            // the string assignment for each variable is consistent with the automaton.
            bool regexOK = true;
            if (!regex_terms.empty()) {
                for (auto& str_in_re : regex_terms) {
                    expr * str = nullptr;
                    expr * re = nullptr;
                    VERIFY(u.str.is_in_re(str_in_re, str, re));
                    lbool current_assignment = ctx.get_assignment(str_in_re);
                    if (current_assignment == l_undef) {
                        continue;
                    }
                    zstring strValue;
                    if (get_string_constant_eqc(str, strValue)) {
                        // try substituting the current assignment and solving the regex
                        expr_ref valueInRe(u.re.mk_in_re(mk_string(strValue), re), m);
                        ctx.get_rewriter()(valueInRe);
                        if (m.is_true(valueInRe)) {
                            if (current_assignment == l_false) {
                                TRACE("str", tout << "regex conflict: " << mk_pp(str, m) << " = \"" << strValue << "\" but must not be in the language " << mk_pp(re, m) << std::endl;);
                                expr_ref conflictClause(m.mk_or(m.mk_not(ctx.mk_eq_atom(str, mk_string(strValue))), str_in_re), m);
                                assert_axiom(conflictClause);
                                add_persisted_axiom(conflictClause);
                                return FC_CONTINUE;
                            }
                        } else if (m.is_false(valueInRe)) {
                            if (current_assignment == l_true) {
                                TRACE("str", tout << "regex conflict: " << mk_pp(str, m) << " = \"" << strValue << "\" but must be in the language " << mk_pp(re, m) << std::endl;);
                                expr_ref conflictClause(m.mk_or(m.mk_not(ctx.mk_eq_atom(str, mk_string(strValue))), m.mk_not(str_in_re)), m);
                                assert_axiom(conflictClause);
                                add_persisted_axiom(conflictClause);
                                return FC_CONTINUE;
                            }
                        } else {
                            // try to keep going, but don't assume the current assignment is right or wrong
                            regexOK = false;
                            break;
                        }
                    } else {
                        regexOK = false;
                        break;
                    }
                } // foreach (str.in.re in regex_terms)
            }
            // we're not done if some variable in a regex membership predicate was unassigned
            if (regexOK) {
                if (unused_internal_variables.empty()) {
                    TRACE("str", tout << "All variables are assigned. Done!" << std::endl;);
                    m_stats.m_solved_by = 2;
                    return FC_DONE;
                } else {
                    TRACE("str", tout << "Assigning decoy values to free internal variables." << std::endl;);
                    for (auto const &var : unused_internal_variables) {
                        expr_ref assignment(m.mk_eq(var, mk_string("**unused**")), m);
                        assert_axiom(assignment);
                    }
                    return FC_CONTINUE;
                }
            }
        }

        CTRACE("str", needToAssignFreeVars,
               tout << "Need to assign values to the following free variables:" << std::endl;
               for (expr* v : free_variables) {
                   tout << mk_ismt2_pp(v, m) << std::endl;
               }
               tout << "freeVar_map has the following entries:" << std::endl;
               for (auto const& kv : freeVar_map) {
                   expr * var = kv.first;
                   tout << mk_ismt2_pp(var, m) << std::endl;
               }
               );

        // Assign free variables

        {
            TRACE("str", tout << "free var map (#" << freeVar_map.size() << "):" << std::endl;
                  for (auto const &freeVarItor1 : freeVar_map) {
                      expr * freeVar = freeVarItor1.first;
                      rational lenValue;
                      bool lenValue_exists = get_len_value(freeVar, lenValue);
                      tout << mk_pp(freeVar, m) << " [depCnt = " << freeVarItor1.second << ", length = "
                           << (lenValue_exists ? lenValue.to_string() : "?")
                           << "]" << std::endl;
                  }
                  );
        }

        {
            // TODO if we're using fixed-length testing, do we care about finding free variables any more?
            // that work might be useless
            TRACE("str", tout << "using fixed-length model construction" << std::endl;);

            arith_value v(get_manager());
            v.init(&ctx);
            final_check_status arith_fc_status = v.final_check();
            if (arith_fc_status != FC_DONE) {
                TRACE("str", tout << "arithmetic solver not done yet, continuing search" << std::endl;);
                return FC_CONTINUE;
            }
            TRACE("str", tout << "arithmetic solver done in final check" << std::endl;);

            expr_ref_vector assignments(m);
            ctx.get_assignments(assignments);

            expr_ref_vector precondition(m);
            expr_ref_vector cex(m);
            lbool model_status = fixed_length_model_construction(assignments, precondition, free_variables, candidate_model, cex);

            if (model_status == l_true) {
                m_stats.m_solved_by = 2;
                return FC_DONE;
            } else if (model_status == l_false) {
                // whatever came back in CEX is the conflict clause.
                // negate its conjunction and assert that
                expr_ref conflict(m.mk_not(mk_and(cex)), m);
                assert_axiom(conflict);
                add_persisted_axiom(conflict);
                return FC_CONTINUE;
            } else { // model_status == l_undef
                TRACE("str", tout << "fixed-length model construction found missing side conditions; continuing search" << std::endl;);
                return FC_CONTINUE;
            }
        }

        if (opt_VerifyFinalCheckProgress && !finalCheckProgressIndicator) {
            TRACE("str", tout << "BUG: no progress in final check, giving up!!" << std::endl;);
            m.raise_exception("no progress in theory_str final check");
        }

        return FC_CONTINUE; // since by this point we've added axioms
    }

    void theory_str::get_concats_in_eqc(expr * n, std::set<expr*> & concats) {

        expr * eqcNode = n;
        do {
            if (u.str.is_concat(to_app(eqcNode))) {
                concats.insert(eqcNode);
            }
            eqcNode = get_eqc_next(eqcNode);
        } while (eqcNode != n);
    }

    void theory_str::get_var_in_eqc(expr * n, std::set<expr*> & varSet) {
        expr * eqcNode = n;
        do {
            if (variable_set.find(eqcNode) != variable_set.end()) {
                varSet.insert(eqcNode);
            }
            eqcNode = get_eqc_next(eqcNode);
        } while (eqcNode != n);
    }

    bool cmpvarnames(expr * lhs, expr * rhs) {
        symbol lhs_name = to_app(lhs)->get_decl()->get_name();
        symbol rhs_name = to_app(rhs)->get_decl()->get_name();
        return lhs_name.str() < rhs_name.str();
    }

    void theory_str::init_model(model_generator & mg) {
        //TRACE("str", tout << "initializing model" << std::endl; display(tout););
        m_factory = alloc(str_value_factory, get_manager(), get_family_id());
        mg.register_factory(m_factory);
    }

    /*
     * Helper function for mk_value().
     * Attempts to resolve the expression 'n' to a string constant.
     * Stronger than get_eqc_value() in that it will perform recursive descent
     * through every subexpression and attempt to resolve those to concrete values as well.
     * Returns the concrete value obtained from this process,
     * guaranteed to satisfy m_strutil.is_string(),
     * if one could be obtained,
     * or else returns NULL if no concrete value was derived.
     */
    app * theory_str::mk_value_helper(app * n) {
        if (u.str.is_string(n)) {
            return n;
        } else if (u.str.is_concat(n)) {
            // recursively call this function on each argument
            SASSERT(n->get_num_args() == 2);
            expr * a0 = n->get_arg(0);
            expr * a1 = n->get_arg(1);

            app * a0_conststr = mk_value_helper(to_app(a0));
            app * a1_conststr = mk_value_helper(to_app(a1));

            if (a0_conststr != nullptr && a1_conststr != nullptr) {
                zstring a0_s, a1_s;
                u.str.is_string(a0_conststr, a0_s);
                u.str.is_string(a1_conststr, a1_s);
                zstring result = a0_s + a1_s;
                return to_app(mk_string(result));
            }
        }

        zstring assignedValue;
        if (candidate_model.find(n, assignedValue)) {
            return to_app(mk_string(assignedValue));
        }

        // fallback path
        // try to find some constant string, anything, in the equivalence class of n
        if (!candidate_model.empty()) {
            zstring val;
            if (candidate_model.find(n, val)) {
                return to_app(mk_string(val));
            }
        }
        bool hasEqc = false;
        expr * n_eqc = get_eqc_value(n, hasEqc);
        if (hasEqc) {
            return to_app(n_eqc);
        } else {
            theory_var curr = get_var(n);
            if (curr != null_theory_var) {
                curr = m_find.find(curr);
                theory_var first = curr;
                do {
                    expr* a = get_ast(curr);
                    zstring val;
                    if (candidate_model.find(a, val)) {
                        return to_app(mk_string(val));
                    }
                    curr = m_find.next(curr);
                }
                while (curr != first && curr != null_theory_var);
            }
            // fail to find
            return nullptr;
        }
    }

    model_value_proc * theory_str::mk_value(enode * n, model_generator & mg) {
        TRACE("str", tout << "mk_value for: " << mk_ismt2_pp(n->get_expr(), get_manager()) <<
              " (sort " << mk_ismt2_pp(n->get_expr()->get_sort(), get_manager()) << ")" << std::endl;);
        ast_manager & m = get_manager();
        app_ref owner(m);
        owner = n->get_expr();

        // If the owner is not internalized, it doesn't have an enode associated.
        SASSERT(ctx.e_internalized(owner));

        app * val = mk_value_helper(owner);
        if (val != nullptr) {
            return alloc(expr_wrapper_proc, val);
        } else {
            TRACE("str", tout << "WARNING: failed to find a concrete value, falling back" << std::endl;);
            std::ostringstream unused;
            unused << "**UNUSED**" << (m_unused_id++);
            return alloc(expr_wrapper_proc, to_app(mk_string(unused.str())));
        }
    }

    void theory_str::finalize_model(model_generator & mg) {}

    void theory_str::display(std::ostream & out) const {
        out << "TODO: theory_str display" << std::endl;
    }

    rational theory_str::get_refine_length(expr* ex, expr_ref_vector& extra_deps){
        ast_manager & m = get_manager();

        TRACE("str_fl", tout << "finding length for " << mk_ismt2_pp(ex, m) << std::endl;);
        if (u.str.is_string(ex)) {
            bool str_exists;
            expr * str = get_eqc_value(ex, str_exists);
            SASSERT(str_exists);
            zstring str_const;
            u.str.is_string(str, str_const);
            return rational(str_const.length());
        } else if (u.str.is_itos(ex)) {
            expr* fromInt = nullptr;
            u.str.is_itos(ex, fromInt);
            
            arith_value v(m);
            v.init(&ctx);
            rational val;
            VERIFY(v.get_value(fromInt, val));

            std::string s = std::to_string(val.get_int32());
            extra_deps.push_back(ctx.mk_eq_atom(fromInt, mk_int(val)));
            return rational((unsigned)s.length());

        } else if (u.str.is_at(ex)) {
            expr* substrBase = nullptr;
            expr* substrPos = nullptr;
            u.str.is_at(ex, substrBase, substrPos);
            arith_value v(m);
            v.init(&ctx);
            rational pos;
            VERIFY(v.get_value(substrPos, pos));

            extra_deps.push_back(ctx.mk_eq_atom(substrPos, mk_int(pos)));
            return rational::one();

        } else if (u.str.is_extract(ex)) {
            expr* substrBase = nullptr;
            expr* substrPos = nullptr;
            expr* substrLen = nullptr;
            u.str.is_extract(ex, substrBase, substrPos, substrLen);
            arith_value v(m);
            v.init(&ctx);
            rational len, pos;
            VERIFY(v.get_value(substrLen, len));
            VERIFY(v.get_value(substrPos, pos));

            extra_deps.push_back(ctx.mk_eq_atom(substrPos, mk_int(pos)));
            return len;

        } else if (u.str.is_replace(ex)) {
            TRACE("str_fl", tout << "replace is like contains---not in conjunctive fragment!" << std::endl;);
            UNREACHABLE();
        }
        //find asserts that it exists
        return fixed_length_used_len_terms.find(ex);
    }

    expr* theory_str::refine(expr* lhs, expr* rhs, rational offset) {
        // TRACE("str", tout << "refine with " << offset.get_unsigned() << std::endl;);
        if (offset >= rational(0)) {
            ++m_stats.m_refine_eq;
            return refine_eq(lhs, rhs, offset.get_unsigned());
        }
        // Let's just giveup if we find ourselves in the disjunctive fragment.
        if (offset == NEQ) { // negative equation
            ++m_stats.m_refine_neq;
            return refine_dis(lhs, rhs);
        }
        if (offset == PFUN) { // function like contains, prefix,...
            SASSERT(rhs == lhs);
            ++m_stats.m_refine_f;
            return refine_function(lhs);
        }
        if (offset == NFUN) { // negated function
            SASSERT(rhs == lhs);
            ++m_stats.m_refine_nf;
            ast_manager & m = get_manager();
            return refine_function(m.mk_not(lhs));
        }
        UNREACHABLE();
        return nullptr;
    }

    expr* theory_str::refine_eq(expr* lhs, expr* rhs, unsigned _offset) {
        TRACE("str_fl", tout << "refine eq " << _offset << std::endl;);
        ast_manager & m = get_manager();

        expr_ref_vector Gamma(m);
        expr_ref_vector Delta(m);

        if (!flatten(lhs, Gamma) || !flatten(rhs, Delta)){
            UNREACHABLE();
        }

        expr_ref_vector extra_deps(m);
        rational offset(_offset);

        // find len(Gamma[:i])
        unsigned left_count = 0;
        rational left_length(0), last_length(0);
        while(left_count < Gamma.size() && left_length <= offset) {
            last_length = get_refine_length(Gamma.get(left_count), extra_deps);
            left_length += last_length;
            left_count++;
        }
        left_count--;
        SASSERT(left_count >= 0 && left_count < Gamma.size());
        left_length -= last_length;

        expr* left_sublen = nullptr;
        for (unsigned i = 0; i < left_count; i++) {
            expr* len;
            if (!u.str.is_string(to_app(Gamma.get(i)))) {
                len =  u.str.mk_length(Gamma.get(i));
            } else {
                rational lenDiff = offset - left_length;
                len = mk_int(lenDiff);
            }
            if (left_sublen == nullptr) {
                left_sublen = len;
            } else {
                left_sublen = m_autil.mk_add(left_sublen, len);
            }
        }
        if (offset - left_length != 0) {
            rational lenDiff = offset - left_length;
            if (left_sublen == nullptr) {
                left_sublen =  mk_int(lenDiff);
            } else {
                left_sublen = m_autil.mk_add(left_sublen, mk_int(lenDiff));
            }
        }
        expr* extra_left_cond = nullptr;
        if (!u.str.is_string(to_app(Gamma.get(left_count)))) {
            rational offsetLen = offset - left_length + 1;
            extra_left_cond = m_autil.mk_ge(u.str.mk_length(Gamma.get(left_count)), mk_int(offsetLen));
        } 

        // find len(Delta[:j])
        unsigned right_count = 0;
        rational right_length(0);
        last_length = 0;
        while(right_count < Delta.size() && right_length <= offset) {
            last_length = get_refine_length(Delta.get(right_count), extra_deps);
            right_length += last_length;
            right_count++;
        }
        right_count--;
        SASSERT(right_count >= 0 && right_count < Delta.size());
        right_length -= last_length;

        expr* right_sublen = nullptr;
        for (unsigned i = 0; i < right_count; i++) {
            expr* len;
            if (!u.str.is_string(to_app(Delta.get(i)))) {
                len =  u.str.mk_length(Delta.get(i));
            } else {
                rational offsetLen = offset - right_length;
                len = mk_int(offsetLen);
            }
            if (right_sublen == nullptr) {
                right_sublen = len;
            } else {
                right_sublen = m_autil.mk_add(right_sublen, len);
            }
        }
        if (offset - right_length != 0) {
            rational offsetLen = offset - right_length;
            if (right_sublen == nullptr) {
                right_sublen =  mk_int(offsetLen);
            } else {
                right_sublen = m_autil.mk_add(right_sublen, mk_int(offsetLen));
            }
        }
        expr* extra_right_cond = nullptr;
        if (!u.str.is_string(to_app(Delta.get(right_count)))) {
            rational offsetLen = offset - right_length + 1;
            extra_right_cond = m_autil.mk_ge(u.str.mk_length(Delta.get(right_count)), mk_int(offsetLen));
        }

        // Offset tells us that Gamma[i+1:]) != Delta[j+1:]
        // so learn that len(Gamma[:i]) != len(Delta[:j])
        expr_ref_vector diseqs(m);
        diseqs.push_back(ctx.mk_eq_atom(lhs, rhs));
        if (left_sublen != right_sublen) { //nullptr actually means zero
            if (left_sublen == nullptr) {
                left_sublen = mk_int(0);
            }
            if (right_sublen == nullptr) {
                right_sublen = mk_int(0);
            }
            // len(Gamma[:i]) == len(Delta[:j])
            expr* sublen_eq = ctx.mk_eq_atom(left_sublen, right_sublen);
            TRACE("str", tout << "sublen_eq " << mk_pp(sublen_eq, m) << std::endl;);
            diseqs.push_back(sublen_eq);
        }
        if (extra_left_cond != nullptr) {
            TRACE("str", tout << "extra_left_cond " << mk_pp(extra_left_cond, m) << std::endl;);
            diseqs.push_back(extra_left_cond);
        }
        if (extra_right_cond != nullptr) {
            TRACE("str", tout << "extra_right_cond " << mk_pp(extra_right_cond, m) << std::endl;);
            diseqs.push_back(extra_right_cond);
        }
        if (extra_deps.size() > 0) {
            diseqs.push_back(m.mk_and(extra_deps.size(), extra_deps.data()));
            TRACE("str", tout << "extra_deps " << mk_pp(diseqs.get(diseqs.size()-1), m) << std::endl;);
        }
        expr* final_diseq = m.mk_and(diseqs.size(), diseqs.data());
        TRACE("str", tout << "learning not " << mk_pp(final_diseq, m) << std::endl;);
        return final_diseq;
    }

    expr* theory_str::refine_dis(expr* lhs, expr* rhs) {
        ast_manager & m = get_manager();
        
        expr_ref lesson(m);
        lesson = m.mk_not(m.mk_eq(lhs, rhs));
        TRACE("str", tout << "learning not " << mk_pp(lesson, m) << std::endl;);
        return lesson;
    }

    expr* theory_str::refine_function(expr* f) {
        //Can we learn something better?
        TRACE("str", tout << "learning not " << mk_pp(f, get_manager()) << std::endl;);
        return f;
    }

    bool theory_str::flatten(expr* ex, expr_ref_vector & flat) {

        sort * ex_sort = ex->get_sort();
        sort * str_sort = u.str.mk_string_sort();

        if (ex_sort == str_sort) {
            if (is_app(ex)) {
                app * ap = to_app(ex);
                if(u.str.is_concat(ap)) {
                    unsigned num_args = ap->get_num_args();
                    bool success = true;
                    for (unsigned i = 0; i < num_args; i++) {
                        success = success && flatten(ap->get_arg(i), flat);
                    }
                    return success;
                } else {
                    flat.push_back(ex);
                    return true;
                }
            }
        }
        TRACE("str", tout << "non string term!" << mk_pp(ex, m) << std::endl;);
        return false;
    }
}; /* namespace smt */
