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
            // TODO this may be causing crashes in model gen? investigate
            //return m_util.mk_fresh_string();
            NOT_IMPLEMENTED_YET();
        }
        virtual void register_value(expr * n) { /* Ignore */ }
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
        bool search_started;
        arith_util m_autil;
        str_util m_strutil;

        str_value_factory * m_factory;

        ptr_vector<enode> m_basicstr_axiom_todo;
        svector<std::pair<enode*,enode*> > m_str_eq_todo;
        ptr_vector<enode> m_concat_axiom_todo;

        int tmpStringVarCount;
        int tmpXorVarCount;
        std::map<std::pair<expr*, expr*>, std::map<int, expr*> > varForBreakConcat;

        bool avoidLoopCut;
        bool loopDetected;
        std::map<expr*, std::stack<T_cut *> > cut_var_map;

        std::set<expr*> variable_set;
        std::set<expr*> internal_variable_set;

        std::set<expr*> input_var_in_len;

        std::map<expr*, unsigned int> fvar_len_count_map;
        std::map<expr*, ptr_vector<expr> > fvar_lenTester_map;
        std::map<expr*, expr*> lenTester_fvar_map;

        std::map<expr*, std::map<int, svector<std::pair<int, expr*> > > > fvar_valueTester_map;
        std::map<expr*, expr*> valueTester_fvar_map;

        std::map<expr*, int_vector> val_range_map;

        char * char_set;
        std::map<char, int> charSetLookupTable;
        int charSetSize;

    protected:
        void assert_axiom(expr * e);
        void assert_implication(expr * premise, expr * conclusion);

        app * mk_strlen(expr * e);
        expr * mk_concat(expr * n1, expr * n2);
        expr * mk_concat_const_str(expr * n1, expr * n2);

        app * mk_int(int n);

        void check_and_init_cut_var(expr * node);
        void add_cut_info_one_node(expr * baseNode, int slevel, expr * node);
        void add_cut_info_merge(expr * destNode, int slevel, expr * srcNode);
        bool has_self_cut(expr * n1, expr * n2);

        app * mk_str_var(std::string name);
        app * mk_nonempty_str_var();
        app * mk_internal_xor_var();
        expr * mk_internal_valTest_var(expr * node, int len, int vTries);

        bool is_concat(app const * a) const { return a->is_app_of(get_id(), OP_STRCAT); }
        bool is_concat(enode const * n) const { return is_concat(n->get_owner()); }
        bool is_string(app const * a) const { return a->is_app_of(get_id(), OP_STR); }
        bool is_string(enode const * n) const { return is_string(n->get_owner()); }
        bool is_strlen(app const * a) const { return a->is_app_of(get_id(), OP_STRLEN); }
        bool is_strlen(enode const * n) const { return is_strlen(n->get_owner()); }
        void instantiate_concat_axiom(enode * cat);
        void instantiate_basic_string_axioms(enode * str);
        void instantiate_str_eq_length_axiom(enode * lhs, enode * rhs);

        void set_up_axioms(expr * ex);
        void handle_equality(expr * lhs, expr * rhs);

        app * mk_value_helper(app * n);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        bool in_same_eqc(expr * n1, expr * n2);

        bool can_two_nodes_eq(expr * n1, expr * n2);
        bool can_concat_eq_str(expr * concat, std::string str);
        bool can_concat_eq_concat(expr * concat1, expr * concat2);

        void get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList);
        expr * simplify_concat(expr * node);

        void simplify_parent(expr * nn, expr * eq_str);

        void simplify_concat_equality(expr * lhs, expr * rhs);
        void solve_concat_eq_str(expr * concat, expr * str);

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

        expr * get_alias_index_ast(std::map<expr*, expr*> & aliasIndexMap, expr * node);
        expr * getMostLeftNodeInConcat(expr * node);
        expr * getMostRightNodeInConcat(expr * node);
        void get_var_in_eqc(expr * n, std::set<expr*> & varSet);

        // strRegex

        void get_eqc_allUnroll(expr * n, expr * &constStr, std::set<expr*> & unrollFuncSet);

        void dump_assignments();
        void initialize_charset();
    public:
        theory_str(ast_manager & m);
        virtual ~theory_str();
    protected:
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);

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
        void attach_new_th_var(enode * n);

        virtual void init_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        virtual void finalize_model(model_generator & mg);
    };

};

#endif /* _THEORY_STR_H_ */
