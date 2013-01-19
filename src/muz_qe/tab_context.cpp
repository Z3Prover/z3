/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    tab_context.cpp

Abstract:

    Tabulation/subsumption/cyclic proof context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-01-15

Revision History:

--*/

#include "tab_context.h"
#include "trail.h"
#include "dl_rule_set.h"
#include "dl_context.h"
#include "dl_mk_rule_inliner.h"
#include "smt_kernel.h"
#include "matcher.h"
#include "qe_lite.h"
#include "bool_rewriter.h"

namespace datalog {

#if 0
    // semantic matcher.
    class tab_matcher {
        typedef std::pair<expr *, expr *> expr_pair;
        svector<expr_pair>    m_todo;

    public:
        matcher(ast_manager& m): m(m) {}
        
        bool operator()(expr* pat, expr* term, substitution& s, expr_ref_vector& side_conds) {
            m_todo.reset();
            m_todo.push_back(expr_pair(pat, term));
            while (!m_todo.empty()) {
                expr_pair const& p = m_todo.back();
                pat = p.first;
                term = p.second;
                if (is_var(pat)) {
                    
                }
            }
        }
        
    };
#endif

    // subsumption index structure.
    class tab_index {
        ast_manager&      m;
        rule_manager&     rm;
        context&          m_ctx;
        app_ref_vector    m_preds;
        expr_ref          m_precond;
        rule_ref_vector   m_rules;
        svector<unsigned> m_num_vars;
        matcher           m_matcher;
        substitution      m_subst;
        qe_lite           m_qe;
        uint_set          m_empty_set;
        bool_rewriter     m_rw;
        smt_params        m_fparams;
        smt::kernel       m_solver;
        
    public:
        tab_index(ast_manager& m, rule_manager& rm, context& ctx): 
            m(m),
            rm(rm),
            m_ctx(ctx),
            m_preds(m),
            m_precond(m),
            m_rules(rm),
            m_matcher(m),
            m_subst(m),
            m_qe(m),
            m_rw(m),
            m_solver(m, m_fparams) {}

        void insert(rule* r) {
            m_rules.push_back(r);
            m_num_vars.push_back(1+rm.get_var_counter().get_max_var(*r));
        }

        bool is_subsumed(rule const& r) {            
            setup(r);
            m_solver.push();
            m_solver.assert_expr(m_precond);
            bool found = find_match();
            m_solver.pop(1);
            return found;
        }

    private:
        
        void setup(rule const& r) {
            m_preds.reset();
            expr_ref_vector fmls(m);
            expr_ref_vector vars(m);
            expr_ref fml(m);
            ptr_vector<sort> sorts;
            r.get_vars(sorts);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz  = r.get_tail_size();
            var_subst vs(m, false);
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (!sorts[i]) {
                    sorts[i] = m.mk_bool_sort();
                }
                vars.push_back(m.mk_const(symbol(i), sorts[i]));
            }
            for (unsigned i = 0; i < utsz; ++i) {
                fml = r.get_tail(i);
                vs(fml, vars.size(), vars.c_ptr(), fml);
                m_preds.push_back(to_app(fml));
            }
            for (unsigned i = utsz; i < tsz; ++i) {
                fml = r.get_tail(i);
                vs(fml, vars.size(), vars.c_ptr(), fml);
                fmls.push_back(fml);
            }            
            m_precond = m.mk_and(fmls.size(), fmls.c_ptr());            
        }


        // extract pre_cond => post_cond validation obligation from match.
        bool find_match() {
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                if (match_rule(i)) {
                    return true;
                }
            }
            return false;            
        }
        //
        // check that each predicate in r is matched by some predicate in premise.
        // for now: skip multiple matches within the same rule (incomplete).
        //
        bool match_rule(unsigned rule_index) {
            rule const& r = *m_rules[rule_index];
            unsigned num_vars = m_num_vars[rule_index];
            m_subst.reset();
            m_subst.reserve(2, num_vars);
            
            // IF_VERBOSE(1, r.display(m_ctx, verbose_stream() << "try-match\n"););

            return match_predicates(0, r);
        }

        bool match_predicates(unsigned predicate_index, rule const& r) {
            if (predicate_index == r.get_uninterpreted_tail_size()) {
                return check_substitution(r);
            }
            app* p = r.get_tail(predicate_index);
            for (unsigned i = 0; i < m_preds.size(); ++i) {
                m_subst.push_scope();
                if (m_matcher(p, m_preds[i].get(), m_subst) &&
                    match_predicates(predicate_index + 1, r)) {
                    return true;
                }
                m_subst.pop_scope();
            }
            return false;
        }

        bool check_substitution(rule const& r) {
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz  = r.get_tail_size();
            unsigned deltas[2] = {0, 0};
            expr_ref_vector fmls(m);
            expr_ref q(m), postcond(m);

            for (unsigned i = utsz; i < tsz; ++i) {
                app* p = r.get_tail(i);
                m_subst.apply(2, deltas, expr_offset(p, 0), q);
                fmls.push_back(q);
            }

            m_qe(m_empty_set, false, fmls);
            m_rw.mk_and(fmls.size(), fmls.c_ptr(), postcond);
            if (m.is_false(postcond)) {
                return false;
            }
            if (m.is_true(postcond)) {
                return true;
            }
            if (!is_ground(postcond)) {
                IF_VERBOSE(1, verbose_stream() << "TBD: non-ground\n" << mk_pp(postcond, m) << "\n";);
                return false;
            }
            postcond = m.mk_not(postcond);
            m_solver.push();
            m_solver.assert_expr(postcond);
            lbool is_sat = m_solver.check();
            m_solver.pop(1);
            return is_sat == l_false;
        }
    };

    enum tab_instruction {
        SELECT_RULE,
        SELECT_PREDICATE,
        BACKTRACK,
        SATISFIABLE,
        UNSATISFIABLE,
        CANCEL
    };

    std::ostream& operator<<(std::ostream& out, tab_instruction i) {
        switch(i) {
        case SELECT_RULE:      return out << "select-rule";
        case SELECT_PREDICATE: return out << "select-predicate";
        case BACKTRACK:        return out << "backtrack";
        case SATISFIABLE:      return out << "sat";
        case UNSATISFIABLE:    return out << "unsat";
        case CANCEL:           return out << "cancel";
        }
        return out << "unmatched instruction";
    }



    class tab::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsume;
        };

        class goal {
        public:
            rule_ref m_goal;
//            app_ref  m_head;
//            app_ref_vector m_predicates;
//            expr_ref m_constraint;
            unsigned m_index;
            unsigned m_predicate_index;
            unsigned m_rule_index;

            goal(rule_manager& rm): 
                m_goal(rm), 
//                m_head(m),
//                m_predicates(m),
//                m_constraint(m),
                m_index(0), 
                m_predicate_index(0), 
                m_rule_index(0) {
            }

#if 0
        private:
            void init() {
                m_head = m_goal.get_head();
                unsigned utsz = m_goal->get_uninterpreted_tail_size();
                unsigned tsz  = m_goal->get_tail_size();
                for (unsigned i = 0; i < utsz; ++i) {
                    m_predicates.push_back(m_goal->get_tail(i));
                }
                expr_ref fmls(m);
                for (unsigned i = utsz; i < tsz; ++i) {
                    fmls.push_back(m_goal->get_tail(i));
                }
                bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(), m_constraint);
            }
#endif
        };        

        context&           m_ctx;
        ast_manager&       m;
        rule_manager&      rm;
        tab_index          m_subsumption_index;
        smt_params         m_fparams;
        smt::kernel        m_solver;
        rule_unifier       m_unifier;
        rule_set           m_rules;
        vector<goal>       m_goals;
        goal               m_goal;
        tab_instruction    m_instruction;
        unsigned           m_goal_index;
        volatile bool      m_cancel;
        stats              m_stats;
    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_subsumption_index(m, rm, ctx),
            m_solver(m, m_fparams),
            m_unifier(ctx),
            m_rules(ctx),
            m_goal(rm),
            m_instruction(SELECT_PREDICATE),
            m_cancel(false),
            m_goal_index(0)
        {
            // m_fparams.m_relevancy_lvl = 0;
            m_fparams.m_mbqi = false;
            m_fparams.m_soft_timeout = 1000;
        }

        ~imp() {}        

        lbool query(expr* query) {
            m_ctx.ensure_opened();
            m_rules.reset();
            m_rules.add_rules(m_ctx.get_rules());
            rule_ref_vector query_rules(rm);
            rule_ref goal(rm);
            func_decl_ref query_pred(m);
            rm.mk_query(query, query_pred, query_rules, goal);
            init_goal(goal);
            IF_VERBOSE(1, display_goal(m_goal, verbose_stream()););
            return run();
        }
    
        void cancel() {
            m_cancel = true;
        }
        void cleanup() {
            m_cancel = false;
            m_goals.reset();
        }
        void reset_statistics() {
            m_stats.reset();
        }
        void collect_statistics(statistics& st) const {
            st.update("tab.num_unfold", m_stats.m_num_unfold);
            st.update("tab.num_unfold_fail", m_stats.m_num_no_unfold);
            st.update("tab.num_subsume", m_stats.m_num_subsume);
        }
        void display_certificate(std::ostream& out) const {
            // TBD
        }
        expr_ref get_answer() {
            // TBD
            return expr_ref(0, m);
        }
    private:
    
        void select_predicate() {
            rule_ref& query = m_goal.m_goal;
            unsigned num_predicates = query->get_uninterpreted_tail_size();
            if (num_predicates == 0) {
                m_instruction = UNSATISFIABLE;
                IF_VERBOSE(2, query->display(m_ctx, verbose_stream()); );
            }
            else {
                m_instruction = SELECT_RULE;
                unsigned pi = 0; // TBD replace by better selection function.                
                m_goal.m_predicate_index = pi; 
                m_goal.m_rule_index = 0;
                IF_VERBOSE(2, verbose_stream() << mk_pp(query->get_tail(pi), m) << "\n";);
            }
        }
        
        void apply_rule(rule const& r) {
            rule_ref& query = m_goal.m_goal;
            rule_ref new_query(rm);
            if (m_unifier.unify_rules(*query, m_goal.m_predicate_index, r) &&
                m_unifier.apply(*query, m_goal.m_predicate_index, r, new_query) &&
                l_false != query_is_sat(*new_query.get()) &&
                !query_is_subsumed(*new_query.get())) {
                m_stats.m_num_unfold++;
                m_subsumption_index.insert(query.get());
                m_goals.push_back(m_goal);
                init_goal(new_query);
                IF_VERBOSE(1, 
                           display_premise(m_goals.back(), verbose_stream());
                           display_goal(m_goal, verbose_stream()););
                m_instruction = SELECT_PREDICATE;
            }
            else {
                m_stats.m_num_no_unfold++;
                m_instruction = SELECT_RULE;
            }
        }
        

        void select_rule() {
            
            func_decl* p = m_goal.m_goal->get_decl(m_goal.m_predicate_index);
            rule_vector const& rules = m_rules.get_predicate_rules(p);
            if (rules.size() <= m_goal.m_rule_index) {
                m_instruction = BACKTRACK;
            }
            else {
                apply_rule(*rules[m_goal.m_rule_index++]);
            }
        }

        void backtrack() {
            if (m_goals.empty()) {
                m_instruction = SATISFIABLE;
            }
            else {
                m_goal = m_goals.back();
                m_goals.pop_back();
                m_instruction = SELECT_RULE;
            }
        }

        lbool run() {
            m_instruction = SELECT_PREDICATE;
            while (true) {
                if (m_cancel) {
                    cleanup();
                    return l_undef;
                }
                switch(m_instruction) {
                case SELECT_PREDICATE: 
                    select_predicate(); 
                    break;
                case SELECT_RULE: 
                    select_rule(); 
                    break;
                case BACKTRACK:
                    backtrack();
                    break;
                case SATISFIABLE: 
                    return l_false;
                case UNSATISFIABLE:
                    return l_true;
                case CANCEL:
                    m_cancel = false;
                    return l_undef;
                }
            }
        }    

        lbool query_is_sat(rule const& query) {
            expr_ref_vector fmls(m);
            expr_ref fml(m);
            unsigned utsz = query.get_uninterpreted_tail_size();
            unsigned tsz = query.get_tail_size();
            for (unsigned i = utsz; i < tsz; ++i) {
                fmls.push_back(query.get_tail(i));
            }
            ptr_vector<sort> sorts;
            svector<symbol> names;
            query.get_vars(sorts);
            sorts.reverse();
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (!sorts[i]) {
                    sorts[i] = m.mk_bool_sort();
                }
                names.push_back(symbol(i));
            }
            fml = m.mk_and(fmls.size(), fmls.c_ptr());
            fml = m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), fml);
            m_solver.push();
            m_solver.assert_expr(fml);
            lbool is_sat = m_solver.check();            
            m_solver.pop(1);

            TRACE("dl", tout << is_sat << ":\n" << mk_pp(fml, m) << "\n";);
            
            return is_sat;
        }

        bool query_is_subsumed(rule const& query) {
            return m_subsumption_index.is_subsumed(query);
        }

        void init_goal(rule_ref& new_query) {
            m_goal.m_goal  = new_query;
            m_goal.m_index = m_goal_index++;
            m_goal.m_predicate_index = 0;
            m_goal.m_rule_index = 0;
        }


        void display_premise(goal& p, std::ostream& out) {
            out << "[" << p.m_index << "]: " << p.m_predicate_index << ":" << p.m_rule_index << "\n";
        }
        void display_goal(goal& g, std::ostream& out) {
            out << g.m_index << " ";
            g.m_goal->display(m_ctx, out);
        }
    };

    tab::tab(context& ctx):
        m_imp(alloc(imp, ctx)) {        
    }
    tab::~tab() {
        dealloc(m_imp);
    }    
    lbool tab::query(expr* query) {
        return m_imp->query(query);
    }
    void tab::cancel() {
        m_imp->cancel();
    }
    void tab::cleanup() {
        m_imp->cleanup();
    }
    void tab::reset_statistics() {
        m_imp->reset_statistics();
    }
    void tab::collect_statistics(statistics& st) const {
        m_imp->collect_statistics(st);
    }
    void tab::display_certificate(std::ostream& out) const {
        m_imp->display_certificate(out);
    }
    expr_ref tab::get_answer() {
        return m_imp->get_answer();
    }

};
