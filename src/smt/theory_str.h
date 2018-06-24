/*++
  Module Name:

  theory_str.h

  Abstract:

  String Theory Plugin

  Author:

  Murphy Berzish and Yunhui Zheng

  Revision History:

  --*/
#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include "util/trail.h"
#include "util/union_find.h"
#include "util/scoped_ptr_vector.h"
#include "util/hashtable.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_theory.h"
#include "smt/params/theory_str_params.h"
#include "smt/proto_model/value_factory.h"
#include "smt/smt_model_generator.h"
#include<set>
#include<stack>
#include<vector>
#include<map>

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
        return u.str.mk_string(symbol("some value"));
    }
    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
        v1 = u.str.mk_string(symbol("value 1"));
        v2 = u.str.mk_string(symbol("value 2"));
        return true;
    }
    expr * get_fresh_value(sort * s) override {
        if (u.is_string(s)) {
            while (true) {
                std::ostringstream strm;
                strm << delim << std::hex << (m_next++) << std::dec << delim;
                symbol sym(strm.str().c_str());
                if (m_strings.contains(sym)) continue;
                m_strings.insert(sym);
                return u.str.mk_string(sym);
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
class binary_search_trail : public trail<Ctx> {
    obj_map<expr, ptr_vector<expr> > & target;
    expr * entry;
public:
    binary_search_trail(obj_map<expr, ptr_vector<expr> > & target, expr * entry) :
        target(target), entry(entry) {}
    ~binary_search_trail() override {}
    void undo(Ctx & ctx) override {
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


class nfa {
protected:
    bool m_valid;
    unsigned m_next_id;

    unsigned next_id() {
        unsigned retval = m_next_id;
        ++m_next_id;
        return retval;
    }

    unsigned m_start_state;
    unsigned m_end_state;

    std::map<unsigned, std::map<char, unsigned> > transition_map;
    std::map<unsigned, std::set<unsigned> > epsilon_map;

    void make_transition(unsigned start, char symbol, unsigned end) {
        transition_map[start][symbol] = end;
    }

    void make_epsilon_move(unsigned start, unsigned end) {
        epsilon_map[start].insert(end);
    }

    // Convert a regular expression to an e-NFA using Thompson's construction
    void convert_re(expr * e, unsigned & start, unsigned & end, seq_util & u);

public:
    nfa(seq_util & u, expr * e)
: m_valid(true), m_next_id(0), m_start_state(0), m_end_state(0) {
        convert_re(e, m_start_state, m_end_state, u);
    }

    nfa() : m_valid(false), m_next_id(0), m_start_state(0), m_end_state(0) {}

    bool is_valid() const {
        return m_valid;
    }

    void epsilon_closure(unsigned start, std::set<unsigned> & closure);

    bool matches(zstring input);
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
        re_term(NULL), aut(NULL), polarity(false),
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

    virtual ~regex_automaton_under_assumptions() {
        // don't free str_in_re or aut;
        // they are managed separately
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

    typedef trail_stack<theory_str> th_trail_stack;
    typedef union_find<theory_str> th_union_find;

    typedef map<rational, expr*, obj_hash<rational>, default_eq<rational> > rational_map;
    struct zstring_hash_proc {
        unsigned operator()(zstring const & s) const {
            return string_hash(s.encode().c_str(), static_cast<unsigned>(s.length()), 17);
        }
    };
    typedef map<zstring, expr*, zstring_hash_proc, default_eq<zstring> > string_map;

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
    svector<std::pair<enode*,enode*> > m_str_eq_todo;
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

    int tmpStringVarCount;
    int tmpXorVarCount;
    int tmpLenTestVarCount;
    int tmpValTestVarCount;
    // obj_pair_map<expr, expr, std::map<int, expr*> > varForBreakConcat;
    std::map<std::pair<expr*,expr*>, std::map<int, expr*> > varForBreakConcat;
    bool avoidLoopCut;
    bool loopDetected;
    obj_map<expr, std::stack<T_cut*> > cut_var_map;
    scoped_ptr_vector<T_cut> m_cut_allocs;
    expr_ref m_theoryStrOverlapAssumption_term;

    obj_hashtable<expr> variable_set;
    obj_hashtable<expr> internal_variable_set;
    obj_hashtable<expr> regex_variable_set;
    std::map<int, obj_hashtable<expr> > internal_variable_scope_levels;

    obj_hashtable<expr> internal_lenTest_vars;
    obj_hashtable<expr> internal_valTest_vars;
    obj_hashtable<expr> internal_unrollTest_vars;

    obj_hashtable<expr> input_var_in_len;

    obj_map<expr, unsigned int> fvar_len_count_map;
    obj_map<expr, ptr_vector<expr> > fvar_lenTester_map;
    obj_map<expr, expr*> lenTester_fvar_map;


    obj_map<expr, std::map<int, svector<std::pair<int, expr*> > > > fvar_valueTester_map;

    obj_map<expr, expr*> valueTester_fvar_map;

    obj_map<expr, int_vector> val_range_map;

    // This can't be an expr_ref_vector because the constructor is wrong,
    // we would need to modify the allocator so we pass in ast_manager
    obj_map<expr, std::map<std::set<expr*>, ptr_vector<expr> > > unroll_tries_map;
    obj_map<expr, expr*> unroll_var_map;
    obj_pair_map<expr, expr, expr*> concat_eq_unroll_ast_map;

    expr_ref_vector contains_map;

    theory_str_contain_pair_bool_map_t contain_pair_bool_map;
    obj_map<expr, std::set<std::pair<expr*, expr*> > > contain_pair_idx_map;

    // TBD: do a curried map for determinism.
    std::map<std::pair<expr*, zstring>, expr*> regex_in_bool_map;
    obj_map<expr, std::set<zstring> > regex_in_var_reg_str_map;

    // regex automata
    scoped_ptr_vector<eautomaton> m_automata;
    ptr_vector<eautomaton> regex_automata;
    obj_hashtable<expr> regex_terms;
    obj_map<expr, ptr_vector<expr> > regex_terms_by_string; // S --> [ (str.in.re S *) ]
    obj_map<expr, svector<regex_automaton_under_assumptions> > regex_automaton_assumptions; // RegEx --> [ aut+assumptions ]
    obj_map<expr, nfa> regex_nfa_cache; // Regex term --> NFA
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

    svector<char> char_set;
    std::map<char, int>  charSetLookupTable;
    int           charSetSize;

    obj_pair_map<expr, expr, expr*> concat_astNode_map;

    // all (str.to-int) and (int.to-str) terms
    expr_ref_vector string_int_conversion_terms;
    obj_hashtable<expr> string_int_axioms;

    // used when opt_FastLengthTesterCache is true
    rational_map lengthTesterCache;
    // used when opt_FastValueTesterCache is true
    string_map valueTesterCache;

    string_map stringConstantCache;
    unsigned long totalCacheAccessCount;
    unsigned long cacheHitCount;
    unsigned long cacheMissCount;

    unsigned m_fresh_id;

    // cache mapping each string S to Length(S)
    obj_map<expr, app*> length_ast_map;

    th_trail_stack m_trail_stack;
    th_union_find m_find;
    theory_var get_var(expr * n) const;
    expr * get_eqc_next(expr * n);
    app * get_ast(theory_var i);

    // binary search heuristic data
    struct binary_search_info {
        rational lowerBound;
        rational midPoint;
        rational upperBound;
        rational windowSize;

        binary_search_info() : lowerBound(rational::zero()), midPoint(rational::zero()),
                upperBound(rational::zero()), windowSize(rational::zero()) {}
        binary_search_info(rational lower, rational mid, rational upper, rational windowSize) :
            lowerBound(lower), midPoint(mid), upperBound(upper), windowSize(windowSize) {}

        void calculate_midpoint() {
            midPoint = floor(lowerBound + ((upperBound - lowerBound) / rational(2)) );
        }
    };
    // maps a free string var to a stack of active length testers.
    // can use binary_search_trail to record changes to this object
    obj_map<expr, ptr_vector<expr> > binary_search_len_tester_stack;
    // maps a length tester var to the *active* search window
    obj_map<expr, binary_search_info> binary_search_len_tester_info;
    // maps a free string var to the first length tester to be (re)used
    obj_map<expr, expr*> binary_search_starting_len_tester;
    // maps a length tester to the next length tester to be (re)used if the split is "low"
    obj_map<expr, expr*> binary_search_next_var_low;
    // maps a length tester to the next length tester to be (re)used if the split is "high"
    obj_map<expr, expr*> binary_search_next_var_high;

    // finite model finding data
    // maps a finite model tester var to a list of variables that will be tested
    obj_map<expr, ptr_vector<expr> > finite_model_test_varlists;
protected:
    void assert_axiom(expr * e);
    void assert_implication(expr * premise, expr * conclusion);
    expr * rewrite_implication(expr * premise, expr * conclusion);

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
    app * mk_nonempty_str_var();
    app * mk_internal_xor_var();
    expr * mk_internal_valTest_var(expr * node, int len, int vTries);
    app * mk_regex_rep_var();
    app * mk_unroll_bound_var();
    app * mk_unroll_test_var();
    void add_nonempty_constraint(expr * s);

    void instantiate_concat_axiom(enode * cat);
    void try_eval_concat(enode * cat);
    void instantiate_basic_string_axioms(enode * str);
    void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

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

    void add_persisted_axiom(expr * a);

    expr * mk_RegexIn(expr * str, expr * regexp);
    void instantiate_axiom_RegexIn(enode * e);
    app * mk_unroll(expr * n, expr * bound);
    void process_unroll_eq_const_str(expr * unrollFunc, expr * constStr);
    void unroll_str2reg_constStr(expr * unrollFunc, expr * eqConstStr);
    void process_concat_eq_unroll(expr * concat, expr * unroll);

    // regex automata and length-aware regex
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
    expr * z3str2_get_eqc_value(expr * n , bool & hasEqcValue);
    bool in_same_eqc(expr * n1, expr * n2);
    expr * collect_eq_nodes(expr * n, expr_ref_vector & eqcSet);

    bool get_arith_value(expr* e, rational& val) const;
    bool get_len_value(expr* e, rational& val);
    bool lower_bound(expr* _e, rational& lo);
    bool upper_bound(expr* _e, rational& hi);

    bool can_two_nodes_eq(expr * n1, expr * n2);
    bool can_concat_eq_str(expr * concat, zstring& str);
    bool can_concat_eq_concat(expr * concat1, expr * concat2);
    bool check_concat_len_in_eqc(expr * concat);
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

    int ctx_dep_analysis(std::map<expr*, int> & strVarMap, std::map<expr*, int> & freeVarMap,
            std::map<expr*, std::set<expr*> > & unrollGroupMap, std::map<expr*, std::map<expr*, int> > & var_eq_concat_map);
    void trace_ctx_dep(std::ofstream & tout,
            std::map<expr*, expr*> & aliasIndexMap,
            std::map<expr*, expr*> & var_eq_constStr_map,
            std::map<expr*, std::map<expr*, int> > & var_eq_concat_map,
            std::map<expr*, std::map<expr*, int> > & var_eq_unroll_map,
            std::map<expr*, expr*> & concat_eq_constStr_map,
            std::map<expr*, std::map<expr*, int> > & concat_eq_concat_map,
            std::map<expr*, std::set<expr*> > & unrollGroupMap);

    bool term_appears_as_subterm(expr * needle, expr * haystack);
    void classify_ast_by_type(expr * node, std::map<expr*, int> & varMap,
            std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap);
    void classify_ast_by_type_in_positive_context(std::map<expr*, int> & varMap,
            std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap);

    expr * mk_internal_lenTest_var(expr * node, int lTries);
    expr * gen_len_val_options_for_free_var(expr * freeVar, expr * lenTesterInCbEq, zstring lenTesterValue);
    void process_free_var(std::map<expr*, int> & freeVar_map);
    expr * gen_len_test_options(expr * freeVar, expr * indicator, int tries);
    expr * gen_free_var_options(expr * freeVar, expr * len_indicator,
            zstring len_valueStr, expr * valTesterInCbEq, zstring valTesterValueStr);
    expr* gen_val_options(expr * freeVar, expr * len_indicator, expr * val_indicator,
            zstring lenStr, int tries);
    void print_value_tester_list(svector<std::pair<int, expr*> > & testerList);
    bool get_next_val_encode(int_vector & base, int_vector & next);
    zstring gen_val_string(int len, int_vector & encoding);

    // binary search heuristic
    expr * binary_search_length_test(expr * freeVar, expr * previousLenTester, zstring previousLenTesterValue);
    expr_ref binary_search_case_split(expr * freeVar, expr * tester, binary_search_info & bounds, literal_vector & case_split_lits);

    bool free_var_attempt(expr * nn1, expr * nn2);
    void more_len_tests(expr * lenTester, zstring lenTesterValue);
    void more_value_tests(expr * valTester, zstring valTesterValue);

    expr * get_alias_index_ast(std::map<expr*, expr*> & aliasIndexMap, expr * node);
    expr * getMostLeftNodeInConcat(expr * node);
    expr * getMostRightNodeInConcat(expr * node);
    void get_var_in_eqc(expr * n, std::set<expr*> & varSet);
    void get_concats_in_eqc(expr * n, std::set<expr*> & concats);
    void get_const_str_asts_in_node(expr * node, expr_ref_vector & constList);
    expr * eval_concat(expr * n1, expr * n2);

    bool finalcheck_str2int(app * a);
    bool finalcheck_int2str(app * a);

    // strRegex

    void get_eqc_allUnroll(expr * n, expr * &constStr, std::set<expr*> & unrollFuncSet);
    void get_eqc_simpleUnroll(expr * n, expr * &constStr, std::set<expr*> & unrollFuncSet);
    void gen_assign_unroll_reg(std::set<expr*> & unrolls);
    expr * gen_assign_unroll_Str2Reg(expr * n, std::set<expr*> & unrolls);
    expr * gen_unroll_conditional_options(expr * var, std::set<expr*> & unrolls, zstring lcmStr);
    expr * gen_unroll_assign(expr * var, zstring lcmStr, expr * testerVar, int l, int h);
    void reduce_virtual_regex_in(expr * var, expr * regex, expr_ref_vector & items);
    void check_regex_in(expr * nn1, expr * nn2);
    zstring get_std_regex_str(expr * r);

    void dump_assignments();
    void initialize_charset();

    void check_variable_scope();
    void recursive_check_variable_scope(expr * ex);

    void collect_var_concat(expr * node, std::set<expr*> & varSet, std::set<expr*> & concatSet);
    bool propagate_length(std::set<expr*> & varSet, std::set<expr*> & concatSet, std::map<expr*, int> & exprLenMap);
    void get_unique_non_concat_nodes(expr * node, std::set<expr*> & argSet);
    bool propagate_length_within_eqc(expr * var);

    // TESTING
    void refresh_theory_var(expr * e);

    expr_ref set_up_finite_model_test(expr * lhs, expr * rhs);
    void finite_model_test(expr * v, expr * c);

public:
    theory_str(ast_manager & m, theory_str_params const & params);
    ~theory_str() override;

    char const * get_name() const override { return "seq"; }
    void display(std::ostream & out) const override;

    bool overlapping_variables_detected() const { return loopDetected; }

    th_trail_stack& get_trail_stack() { return m_trail_stack; }
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

    theory* mk_fresh(context*) override { return alloc(theory_str, get_manager(), m_params); }
    void init(context * ctx) override;
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

#endif /* _THEORY_STR_H_ */
