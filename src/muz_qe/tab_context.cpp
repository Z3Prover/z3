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

    template<typename Ctx>
    struct restore_rule : trail<Ctx> {
        rule_ref_vector& m_rules;
        rule_ref&        m_rule;
        
        restore_rule(rule_ref_vector& rules, rule_ref& rule): 
            m_rules(rules),
            m_rule(rule) {
            m_rules.push_back(m_rule);
        }
        
        virtual void undo(Ctx & ctx) {
            m_rule = m_rules.back();
            m_rules.pop_back();
        }
    };

    // subsumption index structure.
    class tab_index {
        ast_manager&      m;
        rule_manager&     rm;
        context&          m_ctx;
        app_ref_vector    m_preds;
        expr_ref          m_precond;
        rule_ref_vector   m_rules;
        svector<unsigned> m_num_vars;
        unsigned          m_idx1;
        matcher           m_matcher;
        substitution      m_subst;
        qe_lite           m_qe;
        uint_set          m_empty_set;
        bool_rewriter     m_rw;
        
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
            m_rw(m) {}

        void insert(rule* r) {
            m_rules.push_back(r);
            m_num_vars.push_back(1+rm.get_var_counter().get_max_var(*r));
        }
        
        void setup(rule const& r) {
            m_preds.reset();
            m_idx1 = 0;
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
            IF_VERBOSE(1, r.display(m_ctx, verbose_stream() << "setup-match\n"););
        }

        expr* get_precond() { return m_precond; }

        // extract pre_cond => post_cond validation obligation from match.
        bool next_match(expr_ref& post_cond) {
            for (; m_idx1 < m_rules.size(); ++m_idx1) {
                if (try_match(post_cond)) {
                    ++m_idx1;
                    return true;
                }
            }
            return false;            
        }
    private:
        //
        // check that each predicate in r is matched by some predicate in premise.
        // for now: skip multiple matches within the same rule (incomplete).
        //
        bool try_match(expr_ref& post_cond) {
            rule const& r = *m_rules[m_idx1];
            unsigned num_vars = m_num_vars[m_idx1];
            m_subst.reset();
            m_subst.reserve(2, num_vars);
            unsigned deltas[2] = {0, 0};
            expr_ref_vector fmls(m);
            expr_ref q(m);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz = r.get_tail_size();
            
            // IF_VERBOSE(1, r.display(m_ctx, verbose_stream() << "try-match\n"););

            for (unsigned i = 0; i < utsz; ++i) {
                m_subst.push_scope();
                if (!try_match(r.get_tail(i))) {
                    return false;
                }
            }
            for (unsigned i = utsz; i < tsz; ++i) {
                app* p = r.get_tail(i);
                m_subst.apply(2, deltas, expr_offset(p, 0), q);
                fmls.push_back(q);
            }

            m_qe(m_empty_set, false, fmls);
            m_rw.mk_and(fmls.size(), fmls.c_ptr(), post_cond);
            if (m.is_false(post_cond)) {
                return false;
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "match: " << mk_pp(post_cond, m) << "\n";);
                return true;
            }
        }

        bool try_match(expr* q) {
            for (unsigned i = 0; i < m_preds.size(); ++i) {
                if (m_matcher(q, m_preds[i].get(), m_subst)) {
                    return true;
                }
                else {
                    // undo effect of failed match attempt.
                    m_subst.pop_scope();
                    m_subst.push_scope();
                }
            }
            return false;
        }
    };

    enum tab_instruction {
        SELECT_RULE,
        SELECT_PREDICATE,
        BACKTRACK,
        NEXT_RULE,
        SATISFIABLE,
        UNSATISFIABLE,
        CANCEL
    };

    std::ostream& operator<<(std::ostream& out, tab_instruction i) {
        switch(i) {
        case SELECT_RULE:      return out << "select-rule";
        case SELECT_PREDICATE: return out << "select-predicate";
        case BACKTRACK:        return out << "backtrack";
        case NEXT_RULE:        return out << "next-rule";
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

        context&           m_ctx;
        ast_manager&       m;
        rule_manager&      rm;
        tab_index          m_subsumption_index;
        smt_params         m_fparams;
        smt::kernel        m_solver;
        rule_unifier       m_unifier;
        rule_set           m_rules;
        trail_stack<imp>   m_trail;
        tab_instruction    m_instruction;
        rule_ref           m_query;
        rule_ref_vector    m_query_trail;
        unsigned           m_predicate_index;
        unsigned           m_rule_index;
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
            m_trail(*this),
            m_instruction(SELECT_PREDICATE),
            m_query(rm),
            m_query_trail(rm),
            m_predicate_index(0),
            m_rule_index(0),
            m_cancel(false)
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
            func_decl_ref query_pred(m);
            rm.mk_query(query, query_pred, query_rules, m_query);            
            return run();
        }
    
        void cancel() {
            m_cancel = true;
        }
        void cleanup() {
            m_cancel = false;
            m_trail.reset();
            m_query_trail.reset();
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
            unsigned num_predicates = m_query->get_uninterpreted_tail_size();
            if (num_predicates == 0) {
                m_instruction = UNSATISFIABLE;
                IF_VERBOSE(1, m_query->display(m_ctx, verbose_stream()); );
            }
            else {
                m_instruction = SELECT_RULE;
                m_predicate_index = 0; // TBD replace by better selection function.                
                m_rule_index = 0;
                IF_VERBOSE(1, verbose_stream() << mk_pp(m_query->get_tail(m_predicate_index), m) << "\n";);
            }
        }
        
        void apply_rule(rule const& r) {
            m_rule_index++;
            IF_VERBOSE(1, r.display(m_ctx, verbose_stream()););
            bool can_unify = m_unifier.unify_rules(*m_query, m_predicate_index, r);
            if (can_unify) {
                m_stats.m_num_unfold++;
                m_trail.push_scope();
                m_trail.push(value_trail<imp,unsigned>(m_rule_index));
                m_trail.push(value_trail<imp,unsigned>(m_predicate_index));
                rule_ref new_query(rm);
                bool is_feasible = m_unifier.apply(*m_query, m_predicate_index, r, new_query);
                if (is_feasible) {
                    TRACE("dl", m_query->display(m_ctx, tout););
                    if (l_false == query_is_sat(*new_query.get())) {
                        m_instruction = BACKTRACK;
                    }
                    else if (l_true == query_is_subsumed(*new_query.get())) {
                        m_instruction = BACKTRACK;
                    }
                    else {
                        m_subsumption_index.insert(m_query.get());
                        m_trail.push(restore_rule<imp>(m_query_trail, m_query));
                        m_query = new_query;
                        m_instruction = SELECT_PREDICATE;
                    }
                }
                else {
                    m_instruction = BACKTRACK;
                }
            }
            else {
                m_stats.m_num_no_unfold++;
                m_instruction = SELECT_RULE;
            }
        }

        void select_rule() {
            func_decl* p = m_query->get_decl(m_predicate_index);
            rule_vector const& rules = m_rules.get_predicate_rules(p);
            if (rules.size() <= m_rule_index) {
                m_instruction = BACKTRACK;
            }
            else {
                apply_rule(*rules[m_rule_index]);
            }
        }

        void backtrack() {
            if (m_trail.get_num_scopes() == 0) {
                m_instruction = SATISFIABLE;
            }
            else {
                m_trail.pop_scope(1);
                m_instruction = SELECT_RULE;
            }
        }

        void next_rule() {
            SASSERT(m_trail.get_num_scopes() > 0);
            m_trail.pop_scope(1);
            m_instruction = SELECT_RULE;
        }

        lbool run() {
            m_instruction = SELECT_PREDICATE;
            while (true) {
                IF_VERBOSE(1, verbose_stream() << "run " << m_trail.get_num_scopes() << " " << m_instruction << "\n";);                
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
                case NEXT_RULE: // just use BACTRACK?
                    next_rule();
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

        lbool query_is_subsumed(rule const& query) {
            lbool is_subsumed = l_false;
            m_subsumption_index.setup(query);
            expr_ref postcond(m);
            while (m_subsumption_index.next_match(postcond)) {
                if (is_ground(postcond)) {
                    postcond = m.mk_not(postcond);
                    m_solver.push();
                    m_solver.assert_expr(m_subsumption_index.get_precond());
                    m_solver.assert_expr(postcond);
                    lbool is_sat = m_solver.check();
                    m_solver.pop(1);
                    if (is_sat == l_false) {
                        return l_true;
                    }
                }
                else {
                    IF_VERBOSE(1, verbose_stream() << "non-ground: " << mk_pp(postcond, m) << "\n";);
                }
            }
            return is_subsumed;
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
