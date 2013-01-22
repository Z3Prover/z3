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
#include "qe_lite.h"
#include "bool_rewriter.h"
#include "th_rewriter.h"
#include "datatype_decl_plugin.h"

namespace tb {

    // semantic matcher.
    class matcher {
        typedef std::pair<expr *, expr *> expr_pair;
        ast_manager&          m;
        svector<expr_pair>    m_todo;
        datatype_util         m_dt;

        lbool is_eq(expr* _s, expr* _t) {
            if (_s == _t) {
                return l_true;
            }
            if (!is_app(_s) || !is_app(_t)) {
                return l_undef;
            }
            app* s = to_app(_s);
            app* t = to_app(_t);

            if (m.is_value(s) && m.is_value(t)) {
                IF_VERBOSE(2, verbose_stream() << "different:" << mk_pp(s, m) << " " << mk_pp(t, m) << "\n";); 
                return l_false;
            }
            
            if (m_dt.is_constructor(s) && m_dt.is_constructor(t)) {
                if (s->get_decl() == t->get_decl()) {
                    lbool state = l_true;
                    for (unsigned i = 0; i < s->get_num_args(); ++i) {
                        // move is_eq: decompose arguments to constraints.
                        switch (is_eq(s->get_arg(i), t->get_arg(i))) {
                        case l_undef:
                            state = l_undef;
                            break;
                        case l_false:
                            return l_false;
                        default:
                            break;
                        }
                    }
                    return state;
                }
                else {
                    IF_VERBOSE(2, verbose_stream() << "different constructors:" << mk_pp(s, m) << " " << mk_pp(t, m) << "\n";); 
                    return l_false;
                }
            }
            return l_undef;
        }

        bool match_var(var* v, app* t, substitution& s, expr_ref_vector& conds) {
            expr_offset r;
            if (s.find(v, 0, r)) {
                app* p = to_app(r.get_expr());
                switch (is_eq(p, t)) {
                case l_true:
                    break;
                case l_false:
                    return false;
                default:
                    conds.push_back(m.mk_eq(p, t));
                    break;
                }
            }
            else {
                s.insert(v, 0, expr_offset(t, 1));
            }
            return true;
        }

        bool match_app(app* p, app* t, substitution& s, expr_ref_vector& conds) {
            switch(is_eq(p, t)) {
            case l_true:
                return true;
            case l_false:
                return false;
            default:
                conds.push_back(m.mk_eq(p, t));                        
                return true;
            }
        }


    public:
        matcher(ast_manager& m): m(m), m_dt(m) {}
        
        bool operator()(app* pat, app* term, substitution& s, expr_ref_vector& conds) {
            // top-most term to match is a predicate. The predicates should be the same.
            if (pat->get_decl() != term->get_decl() ||
                pat->get_num_args() != term->get_num_args()) {
                return false;
            }
            m_todo.reset();
            for (unsigned i = 0; i < pat->get_num_args(); ++i) {
                m_todo.push_back(expr_pair(pat->get_arg(i), term->get_arg(i)));
            }
            while (!m_todo.empty()) {
                expr_pair const& pr = m_todo.back();
                expr* p  = pr.first;
                expr* t = pr.second;
                m_todo.pop_back();
                if (!is_app(t)) {
                    IF_VERBOSE(2, verbose_stream() << "term is not app\n";);
                    return false;
                }
                else if (is_var(p) && match_var(to_var(p), to_app(t), s, conds)) {
                    continue;
                }
                else if (!is_app(p)) {
                    IF_VERBOSE(2, verbose_stream() << "pattern is not app\n";);
                    return false;
                }
                else if (!match_app(to_app(p), to_app(t), s, conds)) {
                    return false;
                }
            }
            return true;
        }        
    };

    class goal {
        th_rewriter       m_rw;
        datalog::rule_ref m_goal;
        app_ref           m_head;
        app_ref_vector    m_predicates;
        expr_ref          m_constraint;
        unsigned          m_index;
        unsigned          m_num_vars;
        unsigned          m_predicate_index;
        unsigned          m_rule_index;
        unsigned          m_ref;

    public:            
        
        goal(datalog::rule_manager& rm): 
            m_rw(rm.get_manager()),
            m_goal(rm), 
            m_head(rm.get_manager()),
            m_predicates(rm.get_manager()),
            m_constraint(rm.get_manager()),
            m_index(0), 
            m_num_vars(0),
            m_predicate_index(0), 
            m_rule_index(0),
            m_ref(0) {
        }
        
        void set_rule_index(unsigned i)       { m_rule_index = i; }
        unsigned get_rule_index() const       { return m_rule_index; }
        void inc_rule_index()                 { m_rule_index++; }
        unsigned get_predicate_index() const  { return m_predicate_index; }
        void  set_predicate_index(unsigned i) { m_predicate_index = i; }
        unsigned get_num_predicates() const   { return m_predicates.size(); }
        app* get_predicate(unsigned i) const  { return m_predicates[i]; }
        expr* get_constraint() const          { return m_constraint; }
        datalog::rule const& get_rule() const { return *m_goal; }
        unsigned get_num_vars() const         { return m_num_vars; }
        unsigned get_index() const            { return m_index; }
        app* get_head() const                 { return m_head; }

        void init(datalog::rule_ref& g) {
            m_goal  = g;
            m_index = 0;
            m_predicate_index = 0;
            m_rule_index      = 0;
            m_num_vars = 1 + g.get_manager().get_var_counter().get_max_var(*g);
            init();

            // IF_VERBOSE(1, display(verbose_stream()););
        }

        void set_index(unsigned index) {
            m_index = index;
        }
        
        void inc_ref() {
            m_ref++;
        }
        
        void dec_ref() {
            --m_ref;
            if (m_ref == 0) {
                dealloc(this);
            }
        }
        
        void display(std::ostream& out)  const {
            ast_manager& m = m_head.get_manager();
            expr_ref_vector fmls(m);
            expr_ref fml(m);
            for (unsigned i = 0; i < m_predicates.size(); ++i) {
                fmls.push_back(m_predicates[i]);
            }
            fmls.push_back(m_constraint);
            bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(), fml);
            out << mk_pp(fml, m) << "\n";
        }
        
    private:
        // x = t[y], if x does not occur in t[y], then add t[y] to subst.
        
        void init() {
            m_predicates.reset();
            ast_manager& m = m_head.get_manager();
            unsigned delta[1] = { 0 };
            datalog::rule_manager& rm = m_goal.m();
            unsigned num_vars = rm.get_var_counter().get_max_var(*m_goal);
            substitution subst(m);
            subst.reserve(1, num_vars+1);
            expr_ref_vector fmls(m);
            expr_ref tmp(m);
            unsigned utsz = m_goal->get_uninterpreted_tail_size();
            unsigned tsz  = m_goal->get_tail_size();
            for (unsigned i = utsz; i < tsz; ++i) {
                fmls.push_back(m_goal->get_tail(i));
            }
            datalog::flatten_and(fmls);
            for (unsigned i = 0; i < fmls.size(); ++i) {
                expr_ref e(m);
                expr* t, *v;
                subst.apply(1, delta, expr_offset(fmls[i].get(), 0), e);
                m_rw(e);
                fmls[i] = e;
                if (m.is_eq(e, v, t) && (is_var(v) || is_var(t))) {
                    if (!is_var(v)) {
                        std::swap(v, t);
                    }
                    SASSERT(!subst.contains(to_var(v), 0));
                    subst.push_scope();
                    subst.insert(to_var(v)->get_idx(), 0, expr_offset(t, 0));
                    subst.reset_cache();
                    if (subst.acyclic()) {
                        fmls[i] = m.mk_true();
                    }
                    else {
                        subst.pop_scope();
                    }
                }
            }
            bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(),  m_constraint);
            subst.apply(1, delta, expr_offset(m_constraint, 0), m_constraint);
            subst.apply(1, delta, expr_offset(m_goal->get_head(), 0), tmp);
            m_head = to_app(tmp);
            m_rw(m_constraint);
            for (unsigned i = 0; i < utsz; ++i) {
                subst.apply(1, delta, expr_offset(m_goal->get_tail(i), 0), tmp);
                m_predicates.push_back(to_app(tmp));
            }
        }
    };        

    // subsumption index structure.
    class index {
        ast_manager&           m;
        datalog::rule_manager& rm;
        datalog::context&      m_ctx;
        app_ref_vector     m_preds;
        expr_ref           m_precond;
        expr_ref_vector    m_sideconds;
        vector<ref<goal> > m_index;
        matcher            m_matcher;
        substitution       m_subst;
        qe_lite            m_qe;
        uint_set           m_empty_set;
        bool_rewriter      m_rw;
        smt_params         m_fparams;
        smt::kernel        m_solver;
        volatile bool      m_cancel;
        
    public:
        index(datalog::context& ctx): 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_ctx(ctx),
            m_preds(m),
            m_precond(m),
            m_sideconds(m),
            m_matcher(m),
            m_subst(m),
            m_qe(m),
            m_rw(m),
            m_solver(m, m_fparams),
            m_cancel(false) {}

        void insert(ref<goal>& g) {
            m_index.push_back(g);
        }

        bool is_subsumed(goal const& g, unsigned& subsumer) {
            setup(g);
            m_solver.push();
            m_solver.assert_expr(m_precond);
            bool found = find_match(subsumer);
            m_solver.pop(1);
            return found;
        }

        void cancel() {
            m_cancel = true;
            m_solver.cancel();
            m_qe.set_cancel(true);
        }

        void cleanup() {
            m_solver.reset_cancel();
            m_qe.set_cancel(false);
            m_cancel = false;
        }

    private:
        
        void setup(goal const& g) {
            m_preds.reset();
            expr_ref_vector fmls(m);
            expr_ref_vector vars(m);
            expr_ref fml(m);
            ptr_vector<sort> sorts;
            for (unsigned i = 0; i < g.get_num_predicates(); ++i) {
                get_free_vars(g.get_predicate(i), sorts);
            }
            get_free_vars(g.get_constraint(), sorts);
            var_subst vs(m, false);
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (!sorts[i]) {
                    sorts[i] = m.mk_bool_sort();
                }
                vars.push_back(m.mk_const(symbol(i), sorts[i]));
            }
            for (unsigned i = 0; i < g.get_num_predicates(); ++i) {
                vs(g.get_predicate(i), vars.size(), vars.c_ptr(), fml);
                m_preds.push_back(to_app(fml));
            }
            vs(g.get_constraint(), vars.size(), vars.c_ptr(), fml);
            fmls.push_back(fml);
            m_precond = m.mk_and(fmls.size(), fmls.c_ptr());            
            IF_VERBOSE(2, 
                       verbose_stream() << "setup-match: ";
                       for (unsigned i = 0; i < m_preds.size(); ++i) {
                           verbose_stream() << mk_pp(m_preds[i].get(), m) << " ";
                       }
                       verbose_stream() << mk_pp(m_precond, m) << "\n";);
        }


        // extract pre_cond => post_cond validation obligation from match.
        bool find_match(unsigned& subsumer) {
            for (unsigned i = 0; !m_cancel && i < m_index.size(); ++i) {
                if (match_rule(i)) {
                    subsumer = m_index[i]->get_index();
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
            goal const& g = *m_index[rule_index];            
            m_sideconds.reset();
            m_subst.reset();
            m_subst.reserve(2, g.get_num_vars());
            
            IF_VERBOSE(2, g.display(verbose_stream() << "try-match\n"););

            return match_predicates(0, g);
        }


        bool match_predicates(unsigned predicate_index, goal const& g) {
            if (predicate_index == g.get_num_predicates()) {
                return check_substitution(g);
            }

            app* q = g.get_predicate(predicate_index);

            for (unsigned i = 0; !m_cancel && i < m_preds.size(); ++i) {
                app* p = m_preds[i].get();
                m_subst.push_scope();
                unsigned limit = m_sideconds.size();
                IF_VERBOSE(2,
                           for (unsigned j = 0; j < predicate_index; ++j) {
                               verbose_stream() << " ";
                           }
                           verbose_stream() << mk_pp(q, m) << " = " << mk_pp(p, m) << "\n";
                           );
                           

                if (q->get_decl() == p->get_decl() && 
                    m_matcher(q, p, m_subst, m_sideconds) &&
                    match_predicates(predicate_index + 1, g)) {
                    return true;
                }
                m_subst.pop_scope(1);
                m_sideconds.resize(limit);
            }
            return false;
        }

        bool check_substitution(goal const& g) {
            unsigned deltas[2] = {0, 0};
            expr_ref q(m), postcond(m);
            expr_ref_vector fmls(m_sideconds);
            m_subst.reset_cache();

            for (unsigned i = 0; i < fmls.size(); ++i) {
                m_subst.apply(2, deltas, expr_offset(fmls[i].get(), 0), q);
                fmls[i] = q;
            }
            m_subst.apply(2, deltas, expr_offset(g.get_constraint(), 0), q);
            fmls.push_back(q);

            IF_VERBOSE(2,
                       for (unsigned i = 0; i < g.get_num_predicates(); ++i) {
                           verbose_stream() << " ";
                       }
                       q = m.mk_and(fmls.size(), fmls.c_ptr());
                       verbose_stream() << "check: " << mk_pp(q, m) << "\n";);

            m_qe(m_empty_set, false, fmls);
            m_rw.mk_and(fmls.size(), fmls.c_ptr(), postcond);
            if (m.is_false(postcond)) {
                return false;
            }
            if (m.is_true(postcond)) {
                return true;
            }
            if (!is_ground(postcond)) {
                IF_VERBOSE(1, verbose_stream() << "TBD: non-ground\n" 
                           << mk_pp(postcond, m) << "\n";);
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

    // predicate selection strategy.
    class selection {
        datalog::context&  m_ctx;
        ast_manager&       m;
        datalog::rule_manager&      rm;
        datatype_util      dt;
        obj_map<func_decl, unsigned_vector> m_scores;
        unsigned_vector    m_score_values;


    public:
        selection(datalog::context& ctx):
            m_ctx(ctx),
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            dt(m) {
        }

        void init(datalog::rule_set const& rules) {
            m_scores.reset();
            goal g(rm);
            datalog::rule_ref r(rm);
            datalog::rule_set::iterator it  = rules.begin();
            datalog::rule_set::iterator end = rules.end();
            for (; it != end; ++it) {
                r = *it;
                g.init(r);
                app* p = g.get_head();
                unsigned_vector scores;
                score_predicate(p, scores);
                insert_score(p->get_decl(), scores);
            }
        }

        unsigned select(goal const& g) {
            return 0;
#if 0
            unsigned max_score = 0;
            unsigned result = 0;
            unsigned_vector& scores = m_score_values;
            for (unsigned i = 0; i < g.get_num_predicates(); ++i) {
                scores.reset();
                app* p = g.get_predicate(i);
                score_predicate(p, scores);
                unsigned score = compute_score(p->get_decl(), scores);
                if (score > max_score) {
                    max_score = score;
                    result = i;
                }
            }
            return result;
#endif
        }

    private:

        unsigned compute_score(func_decl* f, unsigned_vector const& scores) {
            unsigned_vector f_scores;
            unsigned score = 0;
            if (m_scores.find(f, f_scores)) {
                SASSERT(f_scores.size() == scores.size());
                for (unsigned i = 0; i < scores.size(); ++i) {
                    score += scores[i]*f_scores[i];
                }
            }
            // else there is no rule.
            return score;
        }
        
        void score_predicate(app* p, unsigned_vector& scores) {
            for (unsigned i = 0; i < p->get_num_args(); ++i) {
                scores.push_back(score_argument(p->get_arg(i)));
            }
        }

        unsigned score_argument(expr* arg) {
            if (is_var(arg)) {
                return 0;
            }
            if (m.is_value(arg)) {
                return 3;
            }
            if (is_app(arg) && dt.is_constructor(to_app(arg)->get_decl())) {
                return 2;
            }
            return 1;
        }

        void insert_score(func_decl* f, unsigned_vector const& scores) {
            obj_map<func_decl, unsigned_vector>::obj_map_entry* e;
            e = m_scores.find_core(f);
            if (e) {
                unsigned_vector & old_scores = e->get_data().m_value;
                SASSERT(scores.size() == old_scores.size());
                for (unsigned i = 0; i < scores.size(); ++i) {
                    old_scores[i] += scores[i];
                }
            }
            else {
                m_scores.insert(f, scores);
            }            
        }
    };

    enum instruction {
        SELECT_RULE,
        SELECT_PREDICATE,
        BACKTRACK,
        SATISFIABLE,
        UNSATISFIABLE,
        CANCEL
    };

    std::ostream& operator<<(std::ostream& out, instruction i) {
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
};

namespace datalog {

    class tab::imp {
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
            unsigned m_num_unfold;
            unsigned m_num_no_unfold;
            unsigned m_num_subsumed;
        };

        context&           m_ctx;
        ast_manager&       m;
        rule_manager&      rm;
        tb::index          m_index;
        tb::selection      m_selection;
        smt_params         m_fparams;
        smt::kernel        m_solver;
        rule_unifier       m_unifier;
        rule_set           m_rules;
        vector<ref<tb::goal> > m_goals;
        tb::instruction        m_instruction;
        unsigned           m_goal_index;
        volatile bool      m_cancel;
        stats              m_stats;
    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_index(ctx),
            m_selection(ctx),
            m_solver(m, m_fparams),
            m_unifier(ctx),
            m_rules(ctx),
            m_instruction(tb::SELECT_PREDICATE),
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
            m_selection.init(m_rules);
            rule_ref_vector query_rules(rm);
            rule_ref goal(rm);
            func_decl_ref query_pred(m);
            rm.mk_query(query, query_pred, query_rules, goal);
            init_goal(goal);
            IF_VERBOSE(1, display_goal(*get_goal(), verbose_stream() << "g" << get_goal()->get_index() << " "););
            return run();
        }
    
        void cancel() {
            m_cancel = true;
            m_index.cleanup();
            m_solver.cancel();
        }
        
        void cleanup() {
            m_cancel = false;
            m_goals.reset();
            m_index.cleanup();
            m_solver.reset_cancel();
        }
        void reset_statistics() {
            m_stats.reset();
        }
        void collect_statistics(statistics& st) const {
            st.update("tab.num_unfold", m_stats.m_num_unfold);
            st.update("tab.num_unfold_fail", m_stats.m_num_no_unfold);
            st.update("tab.num_subsumed", m_stats.m_num_subsumed);
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
            tb::goal & g = *get_goal();
            unsigned num_predicates = g.get_num_predicates();
            if (num_predicates == 0) {
                m_instruction = tb::UNSATISFIABLE;
                IF_VERBOSE(2, g.display(verbose_stream()); );
            }
            else {
                m_instruction = tb::SELECT_RULE;
                unsigned pi = m_selection.select(g);
                g.set_predicate_index(pi);
                g.set_rule_index(0);
                IF_VERBOSE(2, verbose_stream() << mk_pp(g.get_predicate(pi), m) << "\n";);
            }
        }
        
        void apply_rule(rule const& r) {
            ref<tb::goal> goal = get_goal();
            rule const& query = goal->get_rule();
            rule_ref new_query(rm);
            if (m_unifier.unify_rules(query, goal->get_predicate_index(), r) &&
                m_unifier.apply(query, goal->get_predicate_index(), r, new_query) &&
                l_false != query_is_sat(*new_query.get())) {
                ref<tb::goal> next_goal = init_goal(new_query);     
                unsigned subsumer = 0;
                IF_VERBOSE(1, 
                           display_rule(*goal, verbose_stream());
                           display_premise(*goal,   
                                           verbose_stream() << "g" << next_goal->get_index() << " ");
                           display_goal(*next_goal, verbose_stream()););
                if (m_index.is_subsumed(*next_goal, subsumer)) {
                    IF_VERBOSE(1, verbose_stream() << "subsumed by g" << subsumer << "\n";);
                    m_stats.m_num_subsumed++;
                    m_goals.pop_back();
                    m_instruction = tb::SELECT_RULE;
                }
                else {
                    m_stats.m_num_unfold++;
                    m_index.insert(next_goal);
                    m_instruction = tb::SELECT_PREDICATE;
                }
            }
            else {
                m_stats.m_num_no_unfold++;
                m_instruction = tb::SELECT_RULE;
            }
        }
        
        void select_rule() {   
            tb::goal& g  = *get_goal();
            unsigned pi  = g.get_predicate_index();
            func_decl* p = g.get_predicate(pi)->get_decl();
            rule_vector const& rules = m_rules.get_predicate_rules(p);
            if (rules.size() <= g.get_rule_index()) {
                m_instruction = tb::BACKTRACK;
            }
            else {
                unsigned index = g.get_rule_index();
                g.inc_rule_index();
                apply_rule(*rules[index]);
            }
        }

        void backtrack() {
            SASSERT(!m_goals.empty());
            m_goals.pop_back();            
            if (m_goals.empty()) {
                m_instruction = tb::SATISFIABLE;
            }
            else {
                m_instruction = tb::SELECT_RULE;
            }
        }

        lbool run() {
            m_instruction = tb::SELECT_PREDICATE;
            while (true) {
                IF_VERBOSE(2, verbose_stream() << m_instruction << "\n";);
                if (m_cancel) {
                    cleanup();
                    return l_undef;
                }
                switch(m_instruction) {
                case tb::SELECT_PREDICATE: 
                    select_predicate(); 
                    break;
                case tb::SELECT_RULE: 
                    select_rule(); 
                    break;
                case tb::BACKTRACK:
                    backtrack();
                    break;
                case tb::SATISFIABLE: 
                    return l_false;
                case tb::UNSATISFIABLE:
                    return l_true;
                case tb::CANCEL:
                    cleanup();
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
            if (!sorts.empty()) {
                fml = m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), fml);
            }
            m_solver.push();
            m_solver.assert_expr(fml);
            lbool is_sat = m_solver.check();            
            m_solver.pop(1);

            TRACE("dl", tout << is_sat << ":\n" << mk_pp(fml, m) << "\n";);
            
            return is_sat;
        }

        ref<tb::goal> init_goal(rule_ref& new_query) {
            ref<tb::goal> goal = alloc(tb::goal, rm);
            goal->init(new_query);
            goal->set_index(m_goal_index++);
            m_goals.push_back(goal);
            return goal;
        }

        ref<tb::goal> get_goal() const { return m_goals.back(); }

        hashtable<rule*, rule_hash_proc, rule_eq_proc> m_displayed_rules;

        void display_rule(tb::goal const& p, std::ostream& out) {
            func_decl* f = p.get_predicate(p.get_predicate_index())->get_decl();
            rule_vector const& rules = m_rules.get_predicate_rules(f);
            rule* r = rules[p.get_rule_index()-1];
            if (!m_displayed_rules.contains(r)) {
                m_displayed_rules.insert(r);
                r->display(m_ctx, out << p.get_rule_index() << ":");
            }
        }

        void display_premise(tb::goal& p, std::ostream& out) {
            func_decl* f = p.get_predicate(p.get_predicate_index())->get_decl();
            out << "{g" << p.get_index() << " " << f->get_name() << " pos: " << p.get_predicate_index() << " rule: " << p.get_rule_index() << "}\n";
        }
        void display_goal(tb::goal& g, std::ostream& out) {
            g.display(out);
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
