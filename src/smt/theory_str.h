/*++
  Module Name:

  theory_str.h

  Abstract:

  String Theory Plugin

  Author:

  Murphy Berzish and Yunhui Zheng

  Revision History:

  --*/
#pragma once

#include "util/trail.h"
#include "util/union_find.h"
#include "util/scoped_ptr_vector.h"
#include "util/hashtable.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "model/value_factory.h"
#include "smt/smt_theory.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_arith_value.h"
#include "smt/smt_kernel.h"
#include<set>
#include<stack>
#include<vector>
#include<map>
#include<functional>

namespace smt {

typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
typedef int_hashtable<int_hash, default_eq<int> > integer_set;

class str_value_factory : public value_factory {
    seq_util u;
    symbol_set m_strings;
    std::string delim;
    unsigned m_next;
public:
    str_value_factory(ast_manager & m, family_id fid) :
        value_factory(m, fid),
        u(m), delim("!"), m_next(0) {}
    ~str_value_factory() override {}
    expr * get_some_value(sort * s) override {
        return u.str.mk_string("some value");
    }
    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
        v1 = u.str.mk_string("value 1");
        v2 = u.str.mk_string("value 2");
        return true;
    }
    expr * get_fresh_value(sort * s) override {
        if (u.is_string(s)) {
            while (true) {
                std::ostringstream strm;
                strm << delim << std::hex << (m_next++) << std::dec << delim;
                std::string s(strm.str());
                symbol sym(s);
                if (m_strings.contains(sym)) continue;
                m_strings.insert(sym);
                return u.str.mk_string(s);
            }
        }
        sort* seq = nullptr;
        if (u.is_re(s, seq)) {
            expr* v0 = get_fresh_value(seq);
            return u.re.mk_to_re(v0);
        }
        TRACE("t_str", tout << "unexpected sort in get_fresh_value(): " << mk_pp(s, m_manager) << std::endl;);
        UNREACHABLE(); return nullptr;
    }
    void register_value(expr * n) override { /* Ignore */ }
};

// NSB: added operator[] and contains to obj_pair_hashtable
class theory_str_contain_pair_bool_map_t : public obj_pair_map<expr, expr, expr*> {};

template<typename Ctx>
class binary_search_trail : public trail {
    obj_map<expr, ptr_vector<expr> > & target;
    expr * entry;
public:
    binary_search_trail(obj_map<expr, ptr_vector<expr> > & target, expr * entry) :
        target(target), entry(entry) {}
    ~binary_search_trail() override {}
    void undo() override {
        TRACE("t_str_binary_search", tout << "in binary_search_trail::undo()" << std::endl;);
        if (target.contains(entry)) {
            if (!target[entry].empty()) {
                target[entry].pop_back();
            } else {
                TRACE("t_str_binary_search", tout << "WARNING: attempt to remove length tester from an empty stack" << std::endl;);
            }
        } else {
            TRACE("t_str_binary_search", tout << "WARNING: attempt to access length tester map via invalid key" << std::endl;);
        }
    }
};

class regex_automaton_under_assumptions {
protected:
    expr * re_term;
    eautomaton * aut;
    bool polarity;

    bool assume_lower_bound;
    rational lower_bound;

    bool assume_upper_bound;
    rational upper_bound;
public:
    regex_automaton_under_assumptions() :
        re_term(nullptr), aut(nullptr), polarity(false),
        assume_lower_bound(false), assume_upper_bound(false) {}

    regex_automaton_under_assumptions(expr * re_term, eautomaton * aut, bool polarity) :
        re_term(re_term), aut(aut), polarity(polarity),
        assume_lower_bound(false), assume_upper_bound(false) {}

    void set_lower_bound(rational & lb) {
        lower_bound = lb;
        assume_lower_bound = true;
    }
    void unset_lower_bound() {
        assume_lower_bound = false;
    }

    void set_upper_bound(rational & ub) {
        upper_bound = ub;
        assume_upper_bound = true;
    }
    void unset_upper_bound() {
        assume_upper_bound = false;
    }

    bool get_lower_bound(rational & lb) const {
        if (assume_lower_bound) {
            lb = lower_bound;
            return true;
        } else {
            return false;
        }
    }

    bool get_upper_bound(rational & ub) const {
        if (assume_upper_bound) {
            ub = upper_bound;
            return true;
        } else {
            return false;
        }
    }

    eautomaton * get_automaton() const { return aut; }
    expr * get_regex_term() const { return re_term; }
    bool get_polarity() const { return polarity; }
};

class char_union_find {
    unsigned_vector   m_find;
    unsigned_vector   m_size;
    unsigned_vector   m_next;

    integer_set char_const_set;

    u_map<svector<expr*> > m_justification; // representative -> list of formulas justifying EQC

    void ensure_size(unsigned v) {
        while (v >= get_num_vars()) {
            mk_var();
        }
    }
 public:
    unsigned mk_var() {
        unsigned r = m_find.size();
        m_find.push_back(r);
        m_size.push_back(1);
        m_next.push_back(r);
        return r;
    }
    unsigned get_num_vars() const { return m_find.size(); }
    void mark_as_char_const(unsigned r) {
        char_const_set.insert((int)r);
    }
    bool is_char_const(unsigned r) {
        return char_const_set.contains((int)r);
    }

    unsigned find(unsigned v) const {
        if (v >= get_num_vars()) {
            return v;
        }
        while (true) {
            unsigned new_v = m_find[v];
            if (new_v == v)
                return v;
            v = new_v;
        }
    }

    unsigned next(unsigned v) const {
        if (v >= get_num_vars()) {
            return v;
        }
        return m_next[v];
    }

    bool is_root(unsigned v) const {
        return v >= get_num_vars() || m_find[v] == v;
    }

    svector<expr*> get_justification(unsigned v) {
        unsigned r = find(v);
        svector<expr*> retval;
        if (m_justification.find(r, retval)) {
            return retval;
        } else {
            return svector<expr*>();
        }
    }

    void merge(unsigned v1, unsigned v2, expr * justification) {
        unsigned r1 = find(v1);
        unsigned r2 = find(v2);
        if (r1 == r2)
            return;
        ensure_size(v1);
        ensure_size(v2);
        // swap r1 and r2 if:
        // 1. EQC of r1 is bigger than EQC of r2
        // 2. r1 is a character constant and r2 is not.
        // this maintains the invariant that if a character constant is in an eqc then it is the root of that eqc
        if (m_size[r1] > m_size[r2] || (is_char_const(r1) && !is_char_const(r2))) {
            std::swap(r1, r2);
        }
        m_find[r1] = r2;
        m_size[r2] += m_size[r1];
        std::swap(m_next[r1], m_next[r2]);

        if (m_justification.contains(r1)) {
            // add r1's justifications to r2
            if (!m_justification.contains(r2)) {
                m_justification.insert(r2, m_justification[r1]);
            } else {
                m_justification[r2].append(m_justification[r1]);
            }
            m_justification.remove(r1);
        }
        if (justification != nullptr) {
            if (!m_justification.contains(r2)) {
                m_justification.insert(r2, svector<expr*>());
            }
            m_justification[r2].push_back(justification);
        }
    }

    void reset() {
        m_find.reset();
        m_next.reset();
        m_size.reset();
        char_const_set.reset();
        m_justification.reset();
    }
};

class theory_str : public theory {
    struct T_cut
    {
        int level;
        obj_map<expr, int> vars;

        T_cut() {
            level = -100;
        }
    };

    typedef union_find<theory_str> th_union_find;

    typedef map<rational, expr*, obj_hash<rational>, default_eq<rational> > rational_map;
    struct zstring_hash_proc {
        unsigned operator()(zstring const & s) const {
            auto str = s.encode();
            return string_hash(str.c_str(), static_cast<unsigned>(s.length()), 17);
        }
    };
    typedef map<zstring, expr*, zstring_hash_proc, default_eq<zstring> > string_map;

    struct stats {
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(stats)); }
        unsigned m_refine_eq;
        unsigned m_refine_neq;
        unsigned m_refine_f;
        unsigned m_refine_nf;
        unsigned m_solved_by;
        unsigned m_fixed_length_iterations;
    };

protected:
    theory_str_params const & m_params;

    /*
     * Setting EagerStringConstantLengthAssertions to true allows some methods,
     * in particular internalize_term(), to add
     * length assertions about relevant string constants.
     * Note that currently this should always be set to 'true', or else *no* length assertions
     * will be made about string constants.
     */
    bool opt_EagerStringConstantLengthAssertions;

    /*
     * If VerifyFinalCheckProgress is set to true, continuing after final check is invoked
     * without asserting any new axioms is considered a bug and will throw an exception.
     */
    bool opt_VerifyFinalCheckProgress;

    /*
     * This constant controls how eagerly we expand unrolls in unbounded regex membership tests.
     */
    int opt_LCMUnrollStep;

    /*
     * If NoQuickReturn_IntegerTheory is set to true,
     * integer theory integration checks that assert axioms
     * will not return from the function after asserting their axioms.
     * The default behaviour of Z3str2 is to set this to 'false'. This may be incorrect.
     */
    bool opt_NoQuickReturn_IntegerTheory;

    /*
     * If DisableIntegerTheoryIntegration is set to true,
     * ALL calls to the integer theory integration methods
     * (get_arith_value, get_len_value, lower_bound, upper_bound)
     * will ignore what the arithmetic solver believes about length terms,
     * and will return no information.
     *
     * This reduces performance significantly, but can be useful to enable
     * if it is suspected that string-integer integration, or the arithmetic solver itself,
     * might have a bug.
     *
     * The default behaviour of Z3str2 is to set this to 'false'.
     */
    bool opt_DisableIntegerTheoryIntegration;

    /*
     * If DeferEQCConsistencyCheck is set to true,
     * expensive calls to new_eq_check() will be deferred until final check,
     * at which time the consistency of *all* string equivalence classes will be validated.
     */
    bool opt_DeferEQCConsistencyCheck;

    /*
     * If CheckVariableScope is set to true,
     * pop_scope_eh() and final_check_eh() will run extra checks
     * to determine whether the current assignment
     * contains references to any internal variables that are no longer in scope.
     */
    bool opt_CheckVariableScope;

    /*
     * If ConcatOverlapAvoid is set to true,
     * the check to simplify Concat = Concat in handle_equality() will
     * avoid simplifying wrt. pairs of Concat terms that will immediately
     * result in an overlap. (false = Z3str2 behaviour)
     */
    bool opt_ConcatOverlapAvoid;

    bool search_started;
    arith_util m_autil;
    seq_util u;
    int sLevel;

    bool finalCheckProgressIndicator;

    expr_ref_vector m_trail; // trail for generated terms

    str_value_factory * m_factory;

    re2automaton m_mk_aut;

    // Unique identifier appended to unused variables to ensure that model construction
    // does not introduce equalities when they weren't enforced.
    unsigned m_unused_id;

    // terms we couldn't go through set_up_axioms() with because they weren't internalized
    expr_ref_vector m_delayed_axiom_setup_terms;

    ptr_vector<enode> m_basicstr_axiom_todo;
    ptr_vector<enode> m_concat_axiom_todo;
    ptr_vector<enode> m_string_constant_length_todo;
    ptr_vector<enode> m_concat_eval_todo;
    expr_ref_vector m_delayed_assertions_todo;

    // enode lists for library-aware/high-level string terms (e.g. substr, contains)
    ptr_vector<enode> m_library_aware_axiom_todo;

    // list of axioms that are re-asserted every time the scope is popped
    expr_ref_vector m_persisted_axioms;
    expr_ref_vector m_persisted_axiom_todo;

    // hashtable of all exprs for which we've already set up term-specific axioms --
    // this prevents infinite recursive descent with respect to axioms that
    // include an occurrence of the term for which axioms are being generated
    obj_hashtable<expr> axiomatized_terms;

    // hashtable of all top-level exprs for which set_up_axioms() has been called
    obj_hashtable<expr> existing_toplevel_exprs;

    int tmpStringVarCount;
    int tmpXorVarCount;
    // obj_pair_map<expr, expr, std::map<int, expr*> > varForBreakConcat;
    std::map<std::pair<expr*,expr*>, std::map<int, expr*> > varForBreakConcat;
    bool avoidLoopCut;
    bool loopDetected;
    obj_map<expr, std::stack<T_cut*> > cut_var_map;
    scoped_ptr_vector<T_cut> m_cut_allocs;
    expr_ref m_theoryStrOverlapAssumption_term;

    obj_hashtable<expr> variable_set;
    obj_hashtable<expr> internal_variable_set;
    std::map<int, obj_hashtable<expr> > internal_variable_scope_levels;

    expr_ref_vector contains_map;

    theory_str_contain_pair_bool_map_t contain_pair_bool_map;
    obj_map<expr, std::set<std::pair<expr*, expr*> > > contain_pair_idx_map;

    // regex automata
    scoped_ptr_vector<eautomaton> m_automata;
    ptr_vector<eautomaton> regex_automata;
    obj_hashtable<expr> regex_terms;
    obj_map<expr, ptr_vector<expr> > regex_terms_by_string; // S --> [ (str.in.re S *) ]
    obj_map<expr, svector<regex_automaton_under_assumptions> > regex_automaton_assumptions; // RegEx --> [ aut+assumptions ]
    obj_hashtable<expr> regex_terms_with_path_constraints; // set of string terms which have had path constraints asserted in the current scope
    obj_hashtable<expr> regex_terms_with_length_constraints; // set of regex terms which had had length constraints asserted in the current scope
    obj_map<expr, expr*> regex_term_to_length_constraint; // (str.in.re S R) -> (length constraint over S wrt. R)
    obj_map<expr, ptr_vector<expr> > regex_term_to_extra_length_vars; // extra length vars used in regex_term_to_length_constraint entries

    // keep track of the last lower/upper bound we saw for each string term
    // so we don't perform duplicate work
    obj_map<expr, rational> regex_last_lower_bound;
    obj_map<expr, rational> regex_last_upper_bound;

    // each counter maps a (str.in.re) expression to an integer.
    // use helper functions regex_inc_counter() and regex_get_counter() to access
    obj_map<expr, unsigned> regex_length_attempt_count;
    obj_map<expr, unsigned> regex_fail_count;
    obj_map<expr, unsigned> regex_intersection_fail_count;

    obj_map<expr, ptr_vector<expr> > string_chars; // S --> [S_0, S_1, ...] for character terms S_i

    obj_pair_map<expr, expr, expr*> concat_astNode_map;

    // all (str.to-int) and (int.to-str) terms
    expr_ref_vector string_int_conversion_terms;
    obj_hashtable<expr> string_int_axioms;

    string_map stringConstantCache;
    unsigned long totalCacheAccessCount;
    unsigned long cacheHitCount;
    unsigned long cacheMissCount;

    unsigned m_fresh_id;

    // cache mapping each string S to Length(S)
    obj_map<expr, app*> length_ast_map;

    trail_stack m_trail_stack;
    trail_stack m_library_aware_trail_stack;
    th_union_find m_find;
    theory_var get_var(expr * n) const;
    expr * get_eqc_next(expr * n);
    app * get_ast(theory_var i);

    // fixed length model construction
    expr_ref_vector fixed_length_subterm_trail; // trail for subterms generated *in the subsolver*
    expr_ref_vector fixed_length_assumptions; // cache of boolean terms to assert *into the subsolver*, unsat core is a subset of these
    obj_map<expr, rational> fixed_length_used_len_terms; // constraints used in generating fixed length model
    obj_map<expr, expr_ref_vector* > var_to_char_subterm_map; // maps a var to a list of character terms *in the subsolver*
    obj_map<expr, expr_ref_vector* > uninterpreted_to_char_subterm_map; // maps an "uninterpreted" string term to a list of character terms *in the subsolver*
    obj_map<expr, std::tuple<rational, expr*, expr*>> fixed_length_lesson; //keep track of information for the lesson
    unsigned preprocessing_iteration_count; // number of attempts we've made to solve by preprocessing length information
    obj_map<expr, zstring> candidate_model;
    
    stats m_stats;

protected:
    void reset_internal_data_structures();

    void assert_axiom(expr * e);
    void assert_implication(expr * premise, expr * conclusion);
    expr * rewrite_implication(expr * premise, expr * conclusion);
    // Use the rewriter to simplify an axiom, then assert it.
    void assert_axiom_rw(expr * e);

    expr * mk_string(zstring const& str);
    expr * mk_string(const char * str);

    app * mk_strlen(expr * e);
    expr * mk_concat(expr * n1, expr * n2);
    expr * mk_concat_const_str(expr * n1, expr * n2);
    app * mk_contains(expr * haystack, expr * needle);
    app * mk_indexof(expr * haystack, expr * needle);
    app * mk_fresh_const(char const* name, sort* s);

    literal mk_literal(expr* _e);
    app * mk_int(int n);
    app * mk_int(rational & q);

    void check_and_init_cut_var(expr * node);
    void add_cut_info_one_node(expr * baseNode, int slevel, expr * node);
    void add_cut_info_merge(expr * destNode, int slevel, expr * srcNode);
    bool has_self_cut(expr * n1, expr * n2);

    // for ConcatOverlapAvoid
    bool will_result_in_overlap(expr * lhs, expr * rhs);

    void track_variable_scope(expr * var);
    app * mk_str_var(std::string name);
    app * mk_int_var(std::string name);
    app_ref mk_nonempty_str_var();
    app * mk_internal_xor_var();
    void add_nonempty_constraint(expr * s);

    void instantiate_concat_axiom(enode * cat);
    void try_eval_concat(enode * cat);
    void instantiate_basic_string_axioms(enode * str);
    void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

    // for count abstraction and refinement
    expr* refine(expr* lhs, expr* rhs, rational offset);
    expr* refine_eq(expr* lhs, expr* rhs, unsigned offset);
    expr* refine_dis(expr* lhs, expr* rhs);
    expr* refine_function(expr* f);
    bool flatten(expr* ex, expr_ref_vector & flat);
    rational get_refine_length(expr* ex, expr_ref_vector& extra_deps);

    void instantiate_axiom_CharAt(enode * e);
    void instantiate_axiom_prefixof(enode * e);
    void instantiate_axiom_suffixof(enode * e);
    void instantiate_axiom_Contains(enode * e);
    void instantiate_axiom_Indexof(enode * e);
    void instantiate_axiom_Indexof_extended(enode * e);
    void instantiate_axiom_LastIndexof(enode * e);
    void instantiate_axiom_Substr(enode * e);
    void instantiate_axiom_Replace(enode * e);
    void instantiate_axiom_str_to_int(enode * e);
    void instantiate_axiom_int_to_str(enode * e);
    void instantiate_axiom_is_digit(enode * e);
    void instantiate_axiom_str_to_code(enode * e);
    void instantiate_axiom_str_from_code(enode * e);

    void add_persisted_axiom(expr * a);

    expr * mk_RegexIn(expr * str, expr * regexp);
    void instantiate_axiom_RegexIn(enode * e);

    // regex automata and length-aware regex
    bool solve_regex_automata();
    unsigned estimate_regex_complexity(expr * re);
    unsigned estimate_regex_complexity_under_complement(expr * re);
    unsigned estimate_automata_intersection_difficulty(eautomaton * aut1, eautomaton * aut2);
    bool check_regex_length_linearity(expr * re);
    bool check_regex_length_linearity_helper(expr * re, bool already_star);
    expr_ref infer_all_regex_lengths(expr * lenVar, expr * re, expr_ref_vector & freeVariables);
    void check_subterm_lengths(expr * re, integer_set & lens);
    void find_automaton_initial_bounds(expr * str_in_re, eautomaton * aut);
    bool refine_automaton_lower_bound(eautomaton * aut, rational current_lower_bound, rational & refined_lower_bound);
    bool refine_automaton_upper_bound(eautomaton * aut, rational current_upper_bound, rational & refined_upper_bound);
    expr_ref generate_regex_path_constraints(expr * stringTerm, eautomaton * aut, rational lenVal, expr_ref & characterConstraints);
    void aut_path_add_next(u_map<expr*>& next, expr_ref_vector& trail, unsigned idx, expr* cond);
    expr_ref aut_path_rewrite_constraint(expr * cond, expr * ch_var);
    void regex_inc_counter(obj_map<expr, unsigned> & counter_map, expr * key);
    unsigned regex_get_counter(obj_map<expr, unsigned> & counter_map, expr * key);

    void set_up_axioms(expr * ex);
    void handle_equality(expr * lhs, expr * rhs);

    app * mk_value_helper(app * n);
    expr * get_eqc_value(expr * n, bool & hasEqcValue);
    bool get_string_constant_eqc(expr * n, zstring & stringVal);
    expr * z3str2_get_eqc_value(expr * n , bool & hasEqcValue);
    bool in_same_eqc(expr * n1, expr * n2);
    expr * collect_eq_nodes(expr * n, expr_ref_vector & eqcSet);
    bool is_var(expr * e) const;

    bool get_arith_value(expr* e, rational& val) const;
    bool get_len_value(expr* e, rational& val);
    bool lower_bound(expr* _e, rational& lo);
    bool upper_bound(expr* _e, rational& hi);

    bool can_two_nodes_eq(expr * n1, expr * n2);
    bool can_concat_eq_str(expr * concat, zstring& str);
    bool can_concat_eq_concat(expr * concat1, expr * concat2);
    bool check_concat_len_in_eqc(expr * concat);
    void check_eqc_empty_string(expr * lhs, expr * rhs);
    void check_eqc_concat_concat(std::set<expr*> & eqc_concat_lhs, std::set<expr*> & eqc_concat_rhs);
    bool check_length_consistency(expr * n1, expr * n2);
    bool check_length_const_string(expr * n1, expr * constStr);
    bool check_length_eq_var_concat(expr * n1, expr * n2);
    bool check_length_concat_concat(expr * n1, expr * n2);
    bool check_length_concat_var(expr * concat, expr * var);
    bool check_length_var_var(expr * var1, expr * var2);
    void check_contain_in_new_eq(expr * n1, expr * n2);
    void check_contain_by_eqc_val(expr * varNode, expr * constNode);
    void check_contain_by_substr(expr * varNode, expr_ref_vector & willEqClass);
    void check_contain_by_eq_nodes(expr * n1, expr * n2);
    bool in_contain_idx_map(expr * n);
    void compute_contains(std::map<expr*, expr*> & varAliasMap,
            std::map<expr*, expr*> & concatAliasMap, std::map<expr*, expr *> & varConstMap,
            std::map<expr*, expr*> & concatConstMap, std::map<expr*, std::map<expr*, int> > & varEqConcatMap);
    expr * dealias_node(expr * node, std::map<expr*, expr*> & varAliasMap, std::map<expr*, expr*> & concatAliasMap);
    void get_grounded_concats(unsigned depth,
                              expr* node, std::map<expr*, expr*> & varAliasMap,
                              std::map<expr*, expr*> & concatAliasMap, std::map<expr*, expr*> & varConstMap,
                              std::map<expr*, expr*> & concatConstMap, std::map<expr*, std::map<expr*, int> > & varEqConcatMap,
                              std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > & groundedMap);
    void print_grounded_concat(expr * node, std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > & groundedMap);
    void check_subsequence(expr* str, expr* strDeAlias, expr* subStr, expr* subStrDeAlias, expr* boolVar,
            std::map<expr*, std::map<std::vector<expr*>, std::set<expr*> > > & groundedMap);
    bool is_partial_in_grounded_concat(const std::vector<expr*> & strVec, const std::vector<expr*> & subStrVec);

    void get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
    expr * simplify_concat(expr * node);

    void simplify_parent(expr * nn, expr * eq_str);

    void simplify_concat_equality(expr * lhs, expr * rhs);
    void solve_concat_eq_str(expr * concat, expr * str);

    void infer_len_concat_equality(expr * nn1, expr * nn2);
    bool infer_len_concat(expr * n, rational & nLen);
    void infer_len_concat_arg(expr * n, rational len);

    bool is_concat_eq_type1(expr * concatAst1, expr * concatAst2);
    bool is_concat_eq_type2(expr * concatAst1, expr * concatAst2);
    bool is_concat_eq_type3(expr * concatAst1, expr * concatAst2);
    bool is_concat_eq_type4(expr * concatAst1, expr * concatAst2);
    bool is_concat_eq_type5(expr * concatAst1, expr * concatAst2);
    bool is_concat_eq_type6(expr * concatAst1, expr * concatAst2);

    void process_concat_eq_type1(expr * concatAst1, expr * concatAst2);
    void process_concat_eq_type2(expr * concatAst1, expr * concatAst2);
    void process_concat_eq_type3(expr * concatAst1, expr * concatAst2);
    void process_concat_eq_type4(expr * concatAst1, expr * concatAst2);
    void process_concat_eq_type5(expr * concatAst1, expr * concatAst2);
    void process_concat_eq_type6(expr * concatAst1, expr * concatAst2);

    void print_cut_var(expr * node, std::ofstream & xout);

    void generate_mutual_exclusion(expr_ref_vector & exprs);
    void add_theory_aware_branching_info(expr * term, double priority, lbool phase);

    bool new_eq_check(expr * lhs, expr * rhs);
    void group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts);

    void check_consistency_prefix(expr * e, bool is_true);
    void check_consistency_suffix(expr * e, bool is_true);
    void check_consistency_contains(expr * e, bool is_true);

    int ctx_dep_analysis(std::map<expr*, int> & strVarMap, std::map<expr*, int> & freeVarMap,
            std::map<expr*, std::map<expr*, int> > & var_eq_concat_map);
    void trace_ctx_dep(std::ofstream & tout,
            std::map<expr*, expr*> & aliasIndexMap,
            std::map<expr*, expr*> & var_eq_constStr_map,
            std::map<expr*, std::map<expr*, int> > & var_eq_concat_map,
            std::map<expr*, std::map<expr*, int> > & var_eq_unroll_map,
            std::map<expr*, expr*> & concat_eq_constStr_map,
            std::map<expr*, std::map<expr*, int> > & concat_eq_concat_map);

    bool term_appears_as_subterm(expr * needle, expr * haystack);
    void classify_ast_by_type(expr * node, std::map<expr*, int> & varMap,
            std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap);
    void classify_ast_by_type_in_positive_context(std::map<expr*, int> & varMap,
            std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap);

    expr * get_alias_index_ast(std::map<expr*, expr*> & aliasIndexMap, expr * node);
    expr * getMostLeftNodeInConcat(expr * node);
    expr * getMostRightNodeInConcat(expr * node);
    void get_var_in_eqc(expr * n, std::set<expr*> & varSet);
    void get_concats_in_eqc(expr * n, std::set<expr*> & concats);
    void get_const_str_asts_in_node(expr * node, expr_ref_vector & constList);
    expr * eval_concat(expr * n1, expr * n2);

    bool finalcheck_str2int(app * a);
    bool finalcheck_int2str(app * a);
    bool string_integer_conversion_valid(zstring str, rational& converted) const;

    lbool fixed_length_model_construction(expr_ref_vector formulas, expr_ref_vector &precondition,
            expr_ref_vector& free_variables,
            obj_map<expr, zstring> &model, expr_ref_vector &cex);
    bool fixed_length_reduce_string_term(smt::kernel & subsolver, expr * term, expr_ref_vector & term_chars, expr_ref & cex);
    bool fixed_length_get_len_value(expr * e, rational & val);
    bool fixed_length_reduce_eq(smt::kernel & subsolver, expr_ref lhs, expr_ref rhs, expr_ref & cex);
    bool fixed_length_reduce_diseq(smt::kernel & subsolver, expr_ref lhs, expr_ref rhs, expr_ref & cex);
    bool fixed_length_reduce_contains(smt::kernel & subsolver, expr_ref f, expr_ref & cex);
    bool fixed_length_reduce_negative_contains(smt::kernel & subsolver, expr_ref f, expr_ref & cex);
    bool fixed_length_reduce_prefix(smt::kernel & subsolver, expr_ref f, expr_ref & cex);
    bool fixed_length_reduce_negative_prefix(smt::kernel & subsolver, expr_ref f, expr_ref & cex);
    bool fixed_length_reduce_suffix(smt::kernel & subsolver, expr_ref f, expr_ref & cex);
    bool fixed_length_reduce_negative_suffix(smt::kernel & subsolver, expr_ref f, expr_ref & cex);
    bool fixed_length_reduce_regex_membership(smt::kernel & subsolver, expr_ref f, expr_ref & cex, bool polarity);

    void dump_assignments();

    void check_variable_scope();
    void recursive_check_variable_scope(expr * ex);

    void collect_var_concat(expr * node, std::set<expr*> & varSet, std::set<expr*> & concatSet);
    bool propagate_length(std::set<expr*> & varSet, std::set<expr*> & concatSet, std::map<expr*, int> & exprLenMap);
    void get_unique_non_concat_nodes(expr * node, std::set<expr*> & argSet);
    bool propagate_length_within_eqc(expr * var);


    const rational NEQ = rational(-1); // negative word equation lesson
    const rational PFUN = rational(-2); // positive function lesson
    const rational NFUN = rational(-3); // negative function lesson

    // TESTING
    void refresh_theory_var(expr * e);

public:
    theory_str(context& ctx, ast_manager & m, theory_str_params const & params);
    ~theory_str() override;

    char const * get_name() const override { return "seq"; }
    void init() override;
    void display(std::ostream & out) const override;

    void collect_statistics(::statistics & st) const override;

    bool overlapping_variables_detected() const { return loopDetected; }

    trail_stack& get_trail_stack() { return m_trail_stack; }
    void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2) {}
    void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) { }
    void unmerge_eh(theory_var v1, theory_var v2) {}
protected:
    bool internalize_atom(app * atom, bool gate_ctx) override;
    bool internalize_term(app * term) override;
    virtual enode* ensure_enode(expr* e);
    theory_var mk_var(enode * n) override;

    void new_eq_eh(theory_var, theory_var) override;
    void new_diseq_eh(theory_var, theory_var) override;

    theory* mk_fresh(context* c) override { return alloc(theory_str, *c, c->get_manager(), m_params); }
    void init_search_eh() override;
    void add_theory_assumptions(expr_ref_vector & assumptions) override;
    lbool validate_unsat_core(expr_ref_vector & unsat_core) override;
    void relevant_eh(app * n) override;
    void assign_eh(bool_var v, bool is_true) override;
    void push_scope_eh() override;
    void pop_scope_eh(unsigned num_scopes) override;
    void reset_eh() override;

    bool can_propagate() override;
    void propagate() override;

    final_check_status final_check_eh() override;
    virtual void attach_new_th_var(enode * n);

    void init_model(model_generator & m) override;
    model_value_proc * mk_value(enode * n, model_generator & mg) override;
    void finalize_model(model_generator & mg) override;
};

};

