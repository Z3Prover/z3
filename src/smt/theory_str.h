/*++
Module Name:

    theory_str.h

Abstract:

    String Theory Plugin

Author:

    Murphy Berzish (mtrberzi) 2015-09-03

Revision History:

--*/
#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include"smt_theory.h"
#include"trail.h"
#include"th_rewriter.h"
#include"value_factory.h"
#include"smt_model_generator.h"
#include"arith_decl_plugin.h"
#include<set>
#include<stack>
#include<vector>
#include"str_rewriter.h"

namespace smt {

    class str_value_factory : public value_factory {
        str_util m_util;
    public:
        str_value_factory(ast_manager & m, family_id fid) :
            value_factory(m, fid),
            m_util(m) {}
        virtual ~str_value_factory() {}
        virtual expr * get_some_value(sort * s) {
            return m_util.mk_string("some value");
        }
        virtual bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
            v1 = m_util.mk_string("value 1");
            v2 = m_util.mk_string("value 2");
            return true;
        }
        virtual expr * get_fresh_value(sort * s) {
            return m_util.mk_fresh_string();
        }
        virtual void register_value(expr * n) { /* Ignore */ }
    };

    // rather than modify obj_pair_map I inherit from it and add my own helper methods
    class theory_str_contain_pair_bool_map_t : public obj_pair_map<expr, expr, expr*> {
    public:
        expr * operator[](std::pair<expr*, expr*> key) const {
            expr * value;
            bool found = this->find(key.first, key.second, value);
            if (found) {
                return value;
            } else {
                TRACE("t_str", tout << "WARNING: lookup miss in contain_pair_bool_map!" << std::endl;);
                return NULL;
            }
        }

        bool contains(std::pair<expr*, expr*> key) const {
            expr * unused;
            return this->find(key.first, key.second, unused);
        }
    };

    class theory_str : public theory {
        struct T_cut
        {
            int level;
            std::map<expr*, int> vars;

            T_cut() {
              level = -100;
            }
        };
    protected:
        // Some options that control how the solver operates.

        /*
         * If AggressiveLengthTesting is true, we manipulate the phase of length tester equalities
         * to prioritize trying concrete length options over choosing the "more" option.
         */
        bool opt_AggressiveLengthTesting;

        /*
         * Similarly, if AggressiveValueTesting is true, we manipulate the phase of value tester equalities
         * to prioritize trying concrete value options over choosing the "more" option.
         */
        bool opt_AggressiveValueTesting;

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
         * (get_value, get_len_value, lower_bound, upper_bound)
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

        bool search_started;
        arith_util m_autil;
        str_util m_strutil;
        int sLevel;

        bool finalCheckProgressIndicator;

        // TODO make sure that all generated expressions are saved into the trail
        expr_ref_vector m_trail; // trail for generated terms

        str_value_factory * m_factory;

        // terms we couldn't go through set_up_axioms() with because they weren't internalized
        expr_ref_vector m_delayed_axiom_setup_terms;

        ptr_vector<enode> m_basicstr_axiom_todo;
        svector<std::pair<enode*,enode*> > m_str_eq_todo;
        ptr_vector<enode> m_concat_axiom_todo;
        ptr_vector<enode> m_string_constant_length_todo;

        // enode lists for term-specific axioms
        // TODO maybe refactor this into a generic "library_aware_axiom_todo" list
        ptr_vector<enode> m_axiom_CharAt_todo;
        ptr_vector<enode> m_axiom_StartsWith_todo;
        ptr_vector<enode> m_axiom_EndsWith_todo;
        ptr_vector<enode> m_axiom_Contains_todo;
        ptr_vector<enode> m_axiom_Indexof_todo;
        ptr_vector<enode> m_axiom_Indexof2_todo;
        ptr_vector<enode> m_axiom_LastIndexof_todo;
        ptr_vector<enode> m_axiom_Substr_todo;
        ptr_vector<enode> m_axiom_Replace_todo;
        ptr_vector<enode> m_axiom_RegexIn_todo;

        // hashtable of all exprs for which we've already set up term-specific axioms --
        // this prevents infinite recursive descent with respect to axioms that
        // include an occurrence of the term for which axioms are being generated
        obj_hashtable<expr> axiomatized_terms;

        int tmpStringVarCount;
        int tmpXorVarCount;
        int tmpLenTestVarCount;
        int tmpValTestVarCount;
        std::map<std::pair<expr*, expr*>, std::map<int, expr*> > varForBreakConcat;

        bool avoidLoopCut;
        bool loopDetected;
        std::map<expr*, std::stack<T_cut *> > cut_var_map;

        std::set<expr*> variable_set;
        std::set<expr*> internal_variable_set;
        std::set<expr*> regex_variable_set;
        std::map<int, std::set<expr*> > internal_variable_scope_levels;

        obj_hashtable<expr> internal_lenTest_vars;
        obj_hashtable<expr> internal_valTest_vars;
        obj_hashtable<expr> internal_unrollTest_vars;

        std::set<expr*> input_var_in_len;

        std::map<expr*, unsigned int> fvar_len_count_map;
        std::map<expr*, ptr_vector<expr> > fvar_lenTester_map;
        std::map<expr*, expr*> lenTester_fvar_map;

        std::map<expr*, std::map<int, svector<std::pair<int, expr*> > > > fvar_valueTester_map;
        std::map<expr*, expr*> valueTester_fvar_map;

        std::map<expr*, int_vector> val_range_map;

        // This can't be an expr_ref_vector because the constructor is wrong,
        // we would need to modify the allocator so we pass in ast_manager
        std::map<expr*, std::map<std::set<expr*>, ptr_vector<expr> > > unroll_tries_map;
        std::map<expr*, expr*> unroll_var_map;
        std::map<std::pair<expr*, expr*>, expr*> concat_eq_unroll_ast_map;

        expr_ref_vector contains_map;

        theory_str_contain_pair_bool_map_t contain_pair_bool_map;
        //obj_map<expr, obj_pair_set<expr, expr> > contain_pair_idx_map;
        // TODO Find a better data structure, this is 100% a hack right now
        std::map<expr*, std::set<std::pair<expr*, expr*> > > contain_pair_idx_map;

        std::map<std::pair<expr*, std::string>, expr*> regex_in_bool_map;
        std::map<expr*, std::set<std::string> > regex_in_var_reg_str_map;

        std::map<expr*, nfa> regex_nfa_cache; // Regex term --> NFA

        char * char_set;
        std::map<char, int> charSetLookupTable;
        int charSetSize;

    protected:
        void assert_axiom(expr * e);
        void assert_implication(expr * premise, expr * conclusion);
        expr * rewrite_implication(expr * premise, expr * conclusion);

        app * mk_strlen(expr * e);
        expr * mk_concat(expr * n1, expr * n2);
        expr * mk_concat_const_str(expr * n1, expr * n2);
        app * mk_contains(expr * haystack, expr * needle);
        app * mk_indexof(expr * haystack, expr * needle);

        literal mk_literal(expr* _e);
        app * mk_int(int n);
        app * mk_int(rational & q);

        void check_and_init_cut_var(expr * node);
        void add_cut_info_one_node(expr * baseNode, int slevel, expr * node);
        void add_cut_info_merge(expr * destNode, int slevel, expr * srcNode);
        bool has_self_cut(expr * n1, expr * n2);

        void track_variable_scope(expr * var);
        app * mk_str_var(std::string name);
        app * mk_int_var(std::string name);
        app * mk_nonempty_str_var();
        app * mk_internal_xor_var();
        expr * mk_internal_valTest_var(expr * node, int len, int vTries);
        app * mk_regex_rep_var();
        app * mk_unroll_bound_var();
        app * mk_unroll_test_var();

        bool is_concat(app const * a) const { return a->is_app_of(get_id(), OP_STRCAT); }
        bool is_concat(enode const * n) const { return is_concat(n->get_owner()); }
        bool is_string(app const * a) const { return a->is_app_of(get_id(), OP_STR); }
        bool is_string(enode const * n) const { return is_string(n->get_owner()); }
        bool is_strlen(app const * a) const { return a->is_app_of(get_id(), OP_STRLEN); }
        bool is_strlen(enode const * n) const { return is_strlen(n->get_owner()); }
        bool is_CharAt(app const * a) const { return a->is_app_of(get_id(), OP_STR_CHARAT); }
        bool is_CharAt(enode const * n) const { return is_CharAt(n->get_owner()); }
        bool is_StartsWith(app const * a) const { return a->is_app_of(get_id(), OP_STR_STARTSWITH); }
        bool is_StartsWith(enode const * n) const { return is_StartsWith(n->get_owner()); }
        bool is_EndsWith(app const * a) const { return a->is_app_of(get_id(), OP_STR_ENDSWITH); }
        bool is_EndsWith(enode const * n) const { return is_EndsWith(n->get_owner()); }
        bool is_Contains(app const * a) const { return a->is_app_of(get_id(), OP_STR_CONTAINS); }
        bool is_Contains(enode const * n) const { return is_Contains(n->get_owner()); }
        bool is_Indexof(app const * a) const { return a->is_app_of(get_id(), OP_STR_INDEXOF); }
        bool is_Indexof(enode const * n) const { return is_Indexof(n->get_owner()); }
        bool is_Indexof2(app const * a) const { return a->is_app_of(get_id(), OP_STR_INDEXOF2); }
        bool is_Indexof2(enode const * n) const { return is_Indexof2(n->get_owner()); }
        bool is_LastIndexof(app const * a) const { return a->is_app_of(get_id(), OP_STR_LASTINDEXOF); }
        bool is_LastIndexof(enode const * n) const { return is_LastIndexof(n->get_owner()); }
        bool is_Substr(app const * a) const { return a->is_app_of(get_id(), OP_STR_SUBSTR); }
        bool is_Substr(enode const * n) const { return is_Substr(n->get_owner()); }
        bool is_Replace(app const * a) const { return a->is_app_of(get_id(), OP_STR_REPLACE); }
        bool is_Replace(enode const * n) const { return is_Replace(n->get_owner()); }

        bool is_RegexIn(app const * a) const { return a->is_app_of(get_id(), OP_RE_REGEXIN); }
        bool is_RegexIn(enode const * n) const { return is_RegexIn(n->get_owner()); }
        bool is_RegexConcat(app const * a) const { return a->is_app_of(get_id(), OP_RE_REGEXCONCAT); }
        bool is_RegexConcat(enode const * n) const { return is_RegexConcat(n->get_owner()); }
        bool is_RegexStar(app const * a) const { return a->is_app_of(get_id(), OP_RE_REGEXSTAR); }
        bool is_RegexStar(enode const * n) const { return is_RegexStar(n->get_owner()); }
        bool is_RegexUnion(app const * a) const { return a->is_app_of(get_id(), OP_RE_REGEXUNION); }
        bool is_RegexUnion(enode const * n) const { return is_RegexUnion(n->get_owner()); }
        bool is_Str2Reg(app const * a) const { return a->is_app_of(get_id(), OP_RE_STR2REGEX); }
		bool is_Str2Reg(enode const * n) const { return is_Str2Reg(n->get_owner()); }
		bool is_Unroll(app const * a) const { return a->is_app_of(get_id(), OP_RE_UNROLL); }
		bool is_Unroll(enode const * n) const { return is_Unroll(n->get_owner()); }

        void instantiate_concat_axiom(enode * cat);
        void instantiate_basic_string_axioms(enode * str);
        void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

        void instantiate_axiom_CharAt(enode * e);
        void instantiate_axiom_StartsWith(enode * e);
        void instantiate_axiom_EndsWith(enode * e);
        void instantiate_axiom_Contains(enode * e);
        void instantiate_axiom_Indexof(enode * e);
        void instantiate_axiom_Indexof2(enode * e);
        void instantiate_axiom_LastIndexof(enode * e);
        void instantiate_axiom_Substr(enode * e);
        void instantiate_axiom_Replace(enode * e);

        expr * mk_RegexIn(expr * str, expr * regexp);
        void instantiate_axiom_RegexIn(enode * e);
        app * mk_unroll(expr * n, expr * bound);

        void process_unroll_eq_const_str(expr * unrollFunc, expr * constStr);
        void unroll_str2reg_constStr(expr * unrollFunc, expr * eqConstStr);
        void process_concat_eq_unroll(expr * concat, expr * unroll);

        void set_up_axioms(expr * ex);
        void handle_equality(expr * lhs, expr * rhs);

        app * mk_value_helper(app * n);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        bool in_same_eqc(expr * n1, expr * n2);
        expr * collect_eq_nodes(expr * n, expr_ref_vector & eqcSet);

        bool get_value(expr* e, rational& val) const;
        bool get_len_value(expr* e, rational& val);
        bool lower_bound(expr* _e, rational& lo);
        bool upper_bound(expr* _e, rational& hi);

        bool can_two_nodes_eq(expr * n1, expr * n2);
        bool can_concat_eq_str(expr * concat, std::string str);
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
        // TODO refactor these methods to use expr_ref_vector instead of std::vector
        void compute_contains(std::map<expr*, expr*> & varAliasMap,
                std::map<expr*, expr*> & concatAliasMap, std::map<expr*, expr *> & varConstMap,
                std::map<expr*, expr*> & concatConstMap, std::map<expr*, std::map<expr*, int> > & varEqConcatMap);
        expr * dealias_node(expr * node, std::map<expr*, expr*> & varAliasMap, std::map<expr*, expr*> & concatAliasMap);
        void get_grounded_concats(expr* node, std::map<expr*, expr*> & varAliasMap,
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

        bool new_eq_check(expr * lhs, expr * rhs);
        void group_terms_by_eqc(expr * n, std::set<expr*> & concats, std::set<expr*> & vars, std::set<expr*> & consts);

        int ctx_dep_analysis(std::map<expr*, int> & strVarMap, std::map<expr*, int> & freeVarMap,
        		std::map<expr*, std::set<expr*> > & unrollGroupMap);
        void trace_ctx_dep(std::ofstream & tout,
                std::map<expr*, expr*> & aliasIndexMap,
                std::map<expr*, expr*> & var_eq_constStr_map,
                std::map<expr*, std::map<expr*, int> > & var_eq_concat_map,
				std::map<expr*, std::map<expr*, int> > & var_eq_unroll_map,
                std::map<expr*, expr*> & concat_eq_constStr_map,
                std::map<expr*, std::map<expr*, int> > & concat_eq_concat_map,
				std::map<expr*, std::set<expr*> > & unrollGroupMap);

        void classify_ast_by_type(expr * node, std::map<expr*, int> & varMap,
        		std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap);
        void classify_ast_by_type_in_positive_context(std::map<expr*, int> & varMap,
        		std::map<expr*, int> & concatMap, std::map<expr*, int> & unrollMap);

        expr * mk_internal_lenTest_var(expr * node, int lTries);
        expr * gen_len_val_options_for_free_var(expr * freeVar, expr * lenTesterInCbEq, std::string lenTesterValue);
        void process_free_var(std::map<expr*, int> & freeVar_map);
        expr * gen_len_test_options(expr * freeVar, expr * indicator, int tries);
        expr * gen_free_var_options(expr * freeVar, expr * len_indicator,
        		std::string len_valueStr, expr * valTesterInCbEq, std::string valTesterValueStr);
        expr * gen_val_options(expr * freeVar, expr * len_indicator, expr * val_indicator,
        		std::string lenStr, int tries);
        void print_value_tester_list(svector<std::pair<int, expr*> > & testerList);
        bool get_next_val_encode(int_vector & base, int_vector & next);
        std::string gen_val_string(int len, int_vector & encoding);

        bool free_var_attempt(expr * nn1, expr * nn2);
        void more_len_tests(expr * lenTester, std::string lenTesterValue);
        void more_value_tests(expr * valTester, std::string valTesterValue);

        expr * get_alias_index_ast(std::map<expr*, expr*> & aliasIndexMap, expr * node);
        expr * getMostLeftNodeInConcat(expr * node);
        expr * getMostRightNodeInConcat(expr * node);
        void get_var_in_eqc(expr * n, std::set<expr*> & varSet);
        void get_concats_in_eqc(expr * n, std::set<expr*> & concats);
        void get_const_str_asts_in_node(expr * node, expr_ref_vector & constList);
        expr * eval_concat(expr * n1, expr * n2);

        // strRegex

        void get_eqc_allUnroll(expr * n, expr * &constStr, std::set<expr*> & unrollFuncSet);
        void get_eqc_simpleUnroll(expr * n, expr * &constStr, std::set<expr*> & unrollFuncSet);
        void gen_assign_unroll_reg(std::set<expr*> & unrolls);
        expr * gen_assign_unroll_Str2Reg(expr * n, std::set<expr*> & unrolls);
        expr * gen_unroll_conditional_options(expr * var, std::set<expr*> & unrolls, std::string lcmStr);
        expr * gen_unroll_assign(expr * var, std::string lcmStr, expr * testerVar, int l, int h);
        void reduce_virtual_regex_in(expr * var, expr * regex, expr_ref_vector & items);
        std::string get_std_regex_str(expr * regex);
        void check_regex_in(expr * nn1, expr * nn2);

        void dump_assignments();
        void initialize_charset();
    public:
        theory_str(ast_manager & m);
        virtual ~theory_str();

        virtual char const * get_name() const { return "strings"; }
        virtual void display(std::ostream & out) const;

        bool overlapping_variables_detected() const { return loopDetected; }
    protected:
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual enode* ensure_enode(expr* e);
        virtual theory_var mk_var(enode * n);

        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);

        virtual theory* mk_fresh(context*) { return alloc(theory_str, get_manager()); }
        virtual void init_search_eh();
        virtual void relevant_eh(app * n);
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void reset_eh();

        virtual bool can_propagate();
        virtual void propagate();

        virtual final_check_status final_check_eh();
        virtual void attach_new_th_var(enode * n);

        virtual void init_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        virtual void finalize_model(model_generator & mg);
    };

};

#endif /* _THEORY_STR_H_ */
