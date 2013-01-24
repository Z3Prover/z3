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
#include "for_each_expr.h"

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

    class clause {
        app_ref           m_head;             // head predicate
        app_ref_vector    m_predicates;       // predicates used in goal
        expr_ref          m_constraint;       // side constraint
        unsigned          m_seqno;            // sequence number of goal
        unsigned          m_index;            // index of goal into set of goals
        unsigned          m_num_vars;         // maximal free variable index+1
        unsigned          m_predicate_index;  // selected predicate
        unsigned          m_parent_rule;      // rule used to produce goal
        unsigned          m_parent_index;     // index of parent goal
        unsigned          m_next_rule;        // next rule to expand goal on
        unsigned          m_ref;              // reference count

    public:            
        
        clause(datalog::rule_manager& rm): 
            m_head(rm.get_manager()),
            m_predicates(rm.get_manager()),
            m_constraint(rm.get_manager()),
            m_seqno(0),
            m_index(0), 
            m_num_vars(0),
            m_predicate_index(0), 
            m_next_rule(static_cast<unsigned>(-1)),
            m_parent_rule(0),
            m_parent_index(0),
            m_ref(0) {
        }
        
        void set_seqno(unsigned seqno)        { m_seqno = seqno; }
        unsigned get_seqno() const            { return m_seqno; }
        unsigned get_next_rule() const        { return m_next_rule; }
        void inc_next_rule()                  { m_next_rule++; }
        unsigned get_predicate_index() const  { return m_predicate_index; }
        void  set_predicate_index(unsigned i) { m_predicate_index = i; }
        unsigned get_num_predicates() const   { return m_predicates.size(); }
        app* get_predicate(unsigned i) const  { return m_predicates[i]; }
        expr* get_constraint() const          { return m_constraint; }
        unsigned get_num_vars() const         { return m_num_vars; }
        unsigned get_index() const            { return m_index; }
        void set_index(unsigned index)        { m_index = index; }
        app* get_head() const                 { return m_head; }
        unsigned get_parent_index() const     { return m_parent_index; }
        unsigned get_parent_rule() const      { return m_parent_rule; }
        void set_parent(ref<tb::clause>& parent) { 
            m_parent_index = parent->get_index();
            m_parent_rule  = parent->get_next_rule();
        }        

        expr_ref get_body() const {
            ast_manager& m = get_manager();
            expr_ref_vector fmls(m);
            for (unsigned i = 0; i < m_predicates.size(); ++i) {
                fmls.push_back(m_predicates[i]);
            }
            fmls.push_back(m_constraint);
            datalog::flatten_and(fmls);
            return expr_ref(m.mk_and(fmls.size(), fmls.c_ptr()), m);
        }

        void get_free_vars(ptr_vector<sort>& vars) const {
            ::get_free_vars(m_head, vars);
            for (unsigned i = 0; i < m_predicates.size(); ++i) {
                ::get_free_vars(m_predicates[i], vars);
            }
            ::get_free_vars(m_constraint, vars);
        }

        expr_ref to_formula() const {
            ast_manager& m = get_manager();
            expr_ref body = get_body();
            body = m.mk_implies(body, m_head);
            ptr_vector<sort> vars;
            svector<symbol> names;
            get_free_vars(vars);
            mk_fresh_name fresh;
            fresh.add(body);
            vars.reverse();
            for (unsigned i = 0; i < vars.size(); ++i) {
                names.push_back(fresh.next());
                if (!vars[i]) vars[i] = m.mk_bool_sort();
            }
            vars.reverse();
            if (!vars.empty()) {
                body = m.mk_forall(vars.size(), vars.c_ptr(), names.c_ptr(), body);
            }
            return body;
        }

        void init(app* head, app_ref_vector const& predicates, expr* constraint) {
            m_index = 0;
            m_predicate_index = 0;
            m_next_rule       = static_cast<unsigned>(-1);
            m_head = head;
            m_predicates.reset();
            m_predicates.append(predicates);
            m_constraint = constraint;
            ptr_vector<sort> sorts;
            get_free_vars(sorts);
            m_num_vars = sorts.size();
            reduce_equalities();
        }

        void init(datalog::rule_ref& g) {
            m_index = 0;
            m_predicate_index = 0;
            m_next_rule       = static_cast<unsigned>(-1);
            init_from_rule(g);
            reduce_equalities();
            // IF_VERBOSE(1, display(verbose_stream()););
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

        ast_manager& get_manager() const { return m_head.get_manager(); }

        // Given a rule, initialize fields:
        // - m_num_vars   - number of free variables in rule
        // - m_head       - head predicate
        // - m_predicates - auxiliary predicates in body.
        // - m_constraint - side constraint
        // 
        void init_from_rule(datalog::rule_ref const& r) {
            ast_manager& m = get_manager();
            expr_ref_vector fmls(m);
            unsigned utsz = r->get_uninterpreted_tail_size();
            unsigned tsz  = r->get_tail_size();
            for (unsigned i = utsz; i < tsz; ++i) {
                fmls.push_back(r->get_tail(i));
            }
            m_num_vars = 1 + r.get_manager().get_var_counter().get_max_var(*r);
            m_head = r->get_head();
            m_predicates.reset();
            for (unsigned i = 0; i < utsz; ++i) {
                m_predicates.push_back(r->get_tail(i));
            }            
            bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(),  m_constraint);
        }

        // Simplify a clause by applying equalities as substitutions on predicates.
        // x = t[y], if x does not occur in t[y], then add t[y] to subst.
        void reduce_equalities() {
            ast_manager& m = get_manager();
            th_rewriter       rw(m);
            unsigned delta[1] = { 0 };
            expr_ref_vector fmls(m);
            expr_ref tmp(m);
            substitution subst(m);
            subst.reserve(1, get_num_vars());
            datalog::flatten_and(m_constraint, fmls);
            unsigned num_fmls = fmls.size();
            for (unsigned i = 0; i < num_fmls; ++i) {
                if (get_subst(rw, subst, i, fmls)) {
                    fmls[i] = m.mk_true();
                }
            }    
            subst.apply(1, delta, expr_offset(m_head, 0), tmp);
            m_head = to_app(tmp);
            for (unsigned i = 0; i < m_predicates.size(); ++i) {
                subst.apply(1, delta, expr_offset(m_predicates[i].get(), 0), tmp);
                m_predicates[i] = to_app(tmp);
            }        
            bool_rewriter(m).mk_and(fmls.size(), fmls.c_ptr(),  m_constraint);
            subst.apply(1, delta, expr_offset(m_constraint, 0), m_constraint);
            rw(m_constraint);
        }

        bool get_subst(th_rewriter& rw, substitution& S, unsigned i, expr_ref_vector& fmls) {
            ast_manager& m = get_manager();
            unsigned delta[1] = { 0 };
            expr* f = fmls[i].get();
            expr_ref e(m), tr(m);
            expr* t, *v;
            S.apply(1, delta, expr_offset(f, 0), e);
            rw(e);
            fmls[i] = e;
            if (!m.is_eq(e, v, t)) {
                return false;
            }
            if (!is_var(v)) {
                std::swap(v, t);
            }
            if (!is_var(v)) {
                return false;
            }
            if (!can_be_substituted(m, t)) {
                return false;
            }
            SASSERT(!S.contains(to_var(v), 0));
            S.push_scope();
            S.insert(to_var(v)->get_idx(), 0, expr_offset(t, 0));
            if (!S.acyclic()) {
                S.pop_scope();
                return false;
            }
            fmls[i] = m.mk_true();
            return true;
        }

        struct non_constructor {};

        struct constructor_test {
            ast_manager& m;
            datatype_util dt;
            constructor_test(ast_manager& m): m(m), dt(m) {}
            void operator()(app* e) {
                if (!m.is_value(e) &&
                    !dt.is_constructor(e->get_decl())) {
                    throw non_constructor();
                }
            }
            void operator()(var* v) { }            
            void operator()(quantifier* ) {
                throw non_constructor();
            }
        };

        bool can_be_substituted(ast_manager& m, expr* t) {
            constructor_test p(m);
            try {
                quick_for_each_expr(p, t);
            }
            catch (non_constructor) {
                return false;
            }
            return true;
        }

    };        

    // rules
    class rules {
        typedef obj_map<func_decl, unsigned_vector> map;
        vector<ref<clause> >  m_rules;
        map                 m_index;
    public:

        typedef vector<ref<clause> >::const_iterator iterator;

        iterator begin() const { return m_rules.begin(); }
        iterator end() const { return m_rules.end(); }

        void init(datalog::rule_set const& rules) {
            m_rules.reset();
            m_index.reset();
            datalog::rule_manager& rm = rules.get_rule_manager();
            datalog::rule_ref r(rm);
            datalog::rule_set::iterator it  = rules.begin();
            datalog::rule_set::iterator end = rules.end();
            for (; it != end; ++it) {
                r = *it;
                ref<clause> g = alloc(clause, rm);
                g->init(r);
                insert(g);
            }
        }

        void insert(ref<clause>& g) {
            unsigned idx = m_rules.size();
            m_rules.push_back(g);
            func_decl* f = g->get_head()->get_decl();
            map::obj_map_entry* e = m_index.insert_if_not_there2(f, unsigned_vector());
            SASSERT(e);
            e->get_data().m_value.push_back(idx);            
        }

        unsigned get_num_rules(func_decl* p) {
            map::obj_map_entry* e = m_index.find_core(p);
            if (p) {
                return e->get_data().get_value().size();
            }
            else {
                return 0;
            }
        }

        ref<clause> get_rule(func_decl* p, unsigned idx) const {
            map::obj_map_entry* e = m_index.find_core(p);
            SASSERT(p);
            unsigned rule_id = e->get_data().get_value()[idx];
            return m_rules[rule_id];
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
        ref<clause>          m_clause;
        vector<ref<clause> > m_index;
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

        void insert(ref<clause>& g) {
            m_index.push_back(g);
        }

        bool is_subsumed(ref<tb::clause>& g, unsigned& subsumer) {
            setup(*g);
            m_clause = g;
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

        void reset() {
            m_index.reset();
        }

    private:
        
        void setup(clause const& g) {
            m_preds.reset();
            expr_ref_vector fmls(m);
            expr_ref_vector vars(m);
            expr_ref fml(m);
            ptr_vector<sort> sorts;
            g.get_free_vars(sorts);
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
                    subsumer = m_index[i]->get_seqno();
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
            clause const& g = *m_index[rule_index];            
            m_sideconds.reset();
            m_subst.reset();
            m_subst.reserve(2, g.get_num_vars());
            
            IF_VERBOSE(2, g.display(verbose_stream() << "try-match\n"););

            return match_predicates(0, g);
        }


        bool match_predicates(unsigned predicate_index, clause const& g) {
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

        bool check_substitution(clause const& g) {
            unsigned deltas[2] = {0, 0};
            expr_ref q(m), postcond(m);
            expr_ref_vector fmls(m_sideconds);
            m_subst.reset_cache();
            
            for (unsigned i = 0; !m_cancel && i < fmls.size(); ++i) {
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
            if (m_cancel) {
                return false;
            }
            if (m.is_false(postcond)) {
                return false;
            }
            if (m.is_true(postcond)) {
                return true;
            }
            if (!is_ground(postcond)) {
                IF_VERBOSE(1, verbose_stream() << "TBD: non-ground\n" 
                           << mk_pp(postcond, m) << "\n";
                           m_clause->display(verbose_stream());
                           verbose_stream() << "\n=>\n";
                           g.display(verbose_stream());
                           verbose_stream() << "\n";);
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
        datatype_util      dt;
        obj_map<func_decl, unsigned_vector> m_scores;
        unsigned_vector    m_score_values;

    public:
        selection(datalog::context& ctx):
            m_ctx(ctx),
            m(ctx.get_manager()),
            dt(m) {
        }

        void init(rules const& rs) {
            m_scores.reset();
            rules::iterator it = rs.begin(), end = rs.end();
            for (; it != end; ++it) {
                ref<clause> g = *it;
                app* p = g->get_head();
                unsigned_vector scores;
                score_predicate(p, scores);
                insert_score(p->get_decl(), scores);
            }            
        }

        unsigned select(clause const& g) {
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

        void reset() {
            m_scores.reset();
            m_score_values.reset();
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

    class unifier {
        ast_manager&          m;
        datalog::context&     m_ctx;
        ::unifier             m_unifier;
        substitution          m_S1;
        substitution          m_S2;
        expr_ref_vector       m_sub1;
        expr_ref_vector       m_sub2;
    public:
        unifier(ast_manager& m, datalog::context& ctx): 
            m(m), 
            m_ctx(ctx), 
            m_unifier(m),
            m_S1(m),
            m_S2(m),
            m_sub1(m), 
            m_sub2(m) {}
        
        bool operator()(ref<clause>& tgt, ref<clause>& src, bool compute_subst, ref<clause>& result) {
            unsigned idx = tgt->get_predicate_index();
            return new_unify(*tgt, *src, compute_subst, result);
        }

        expr_ref_vector get_rule_subst(bool is_tgt) {
            if (is_tgt) {
                return m_sub1;
            }
            else {
                return m_sub2;
            }
        }

        bool new_unify(clause const& tgt, clause const& src, bool compute_subst, ref<clause>& result) {
            
            qe_lite qe(m);
            reset();
            unsigned idx = tgt.get_predicate_index();
            SASSERT(tgt.get_predicate(idx)->get_decl() == src.get_head()->get_decl());
            unsigned var_cnt = std::max(tgt.get_num_vars(), src.get_num_vars());
            m_S1.reserve(2, var_cnt);            
            if (!m_unifier(tgt.get_predicate(idx), src.get_head(), m_S1)) {
                return false;
            }
            app_ref_vector predicates(m);
            expr_ref tmp(m), tmp2(m), constraint(m);
            app_ref head(m);
            result = alloc(clause, m_ctx.get_rule_manager());
            unsigned delta[2] = { 0, var_cnt };
            m_S1.apply(2, delta, expr_offset(tgt.get_head(), 0), tmp);   
            head = to_app(tmp);
            for (unsigned i = 0; i < tgt.get_num_predicates(); ++i) {
                if (i != idx) {
                    m_S1.apply(2, delta, expr_offset(tgt.get_predicate(i), 0), tmp);
                    predicates.push_back(to_app(tmp));
                }
            }
            for (unsigned i = 0; i < src.get_num_predicates(); ++i) {
                m_S1.apply(2, delta, expr_offset(src.get_predicate(i), 1), tmp);
                predicates.push_back(to_app(tmp));
            }
            m_S1.apply(2, delta, expr_offset(tgt.get_constraint(), 0), tmp);
            m_S1.apply(2, delta, expr_offset(src.get_constraint(), 1), tmp2);
            constraint = m.mk_and(tmp, tmp2);            
            ptr_vector<sort> vars;

            // perform trival quantifier-elimination:
            uint_set index_set;
            get_free_vars(head, vars);
            for (unsigned i = 0; i < predicates.size(); ++i) {
                get_free_vars(predicates[i].get(), vars);
            }
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (vars[i]) {
                    index_set.insert(i);
                }
            }
            qe(index_set, false, constraint);
            if (m.is_false(constraint)) {
                return false;
            }
            
            // initialize rule.
            result->init(head, predicates, constraint);
            vars.reset();
            result->get_free_vars(vars);
            m_S2.reserve(1, vars.size());
            bool change = false;
            for (unsigned i = 0, j = 0; i < vars.size(); ++i) {
                if (vars[i]) {
                    if (i != j) {
                        var_ref v(m), w(m);
                        v = m.mk_var(i, vars[i]);
                        w = m.mk_var(j, vars[i]);
                        m_S2.insert(v.get(), 0, expr_offset(w, 0));
                        change = true;
                    }
                    ++j;
                }
            }
            if (change) {
                m_S2.apply(1, delta, expr_offset(result->get_constraint(), 0), constraint);
                for (unsigned i = 0; i < result->get_num_predicates(); ++i) {
                    m_S2.apply(1, delta, expr_offset(result->get_predicate(i), 0), tmp);
                    predicates[i] = to_app(tmp);
                }
                m_S2.apply(1, delta, expr_offset(result->get_head(), 0), tmp);
                head = to_app(tmp);
                result->init(head, predicates, constraint);
            }
            if (compute_subst) {
                extract_subst(delta, tgt, 0);
                extract_subst(delta, src, 1);
            }

            IF_VERBOSE(1, 
                       verbose_stream() << "New unify:\n";
                       result->display(verbose_stream()););

            // init result using head, predicates, constraint
            return true;            
        }
        
        
    private:
        void reset() {
            m_S1.reset();
            m_S2.reset();
            m_sub1.reset();
            m_sub2.reset();
        }

        void extract_subst(unsigned const* delta, clause const& g, unsigned offset) {
            ptr_vector<sort> vars;
            var_ref v(m);
            expr_ref tmp(m);
            g.get_free_vars(vars);
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (vars[i]) {
                    v = m.mk_var(i, vars[i]);
                    m_S1.apply(2, delta, expr_offset(v, offset), tmp);
                    m_S2.apply(1, delta, expr_offset(tmp, 0), tmp);     
                    insert_subst(offset, tmp);
                }
                else {
                    insert_subst(offset, m.mk_true());
                }
            }            
        }
        
        void insert_subst(unsigned offset, expr* e) {
            if (offset == 0) {
                m_sub1.push_back(e);
            }
            else {
                m_sub2.push_back(e);
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

        context&               m_ctx;
        ast_manager&           m;
        rule_manager&          rm;
        tb::index              m_index;
        tb::selection          m_selection;
        smt_params             m_fparams;
        smt::kernel            m_solver;
        mutable tb::unifier    m_unifier;
        tb::rules              m_rules;
        vector<ref<tb::clause> > m_clauses;
        unsigned               m_seqno;
        tb::instruction        m_instruction;
        lbool                  m_status;
        volatile bool          m_cancel;
        stats                  m_stats;
        uint_set               m_displayed_rules;
    public:
        imp(context& ctx):
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_index(ctx),
            m_selection(ctx),
            m_solver(m, m_fparams),
            m_unifier(m, ctx),
            m_rules(),
            m_seqno(0),
            m_instruction(tb::SELECT_PREDICATE),
            m_status(l_undef),
            m_cancel(false)
        {
            // m_fparams.m_relevancy_lvl = 0;
            m_fparams.m_mbqi = false;
            m_fparams.m_soft_timeout = 1000;
        }

        ~imp() {}        

        lbool query(expr* query) {
            m_ctx.ensure_opened();
            m_index.reset();
            m_selection.reset();
            m_displayed_rules.reset();
            m_rules.init(m_ctx.get_rules());
            m_selection.init(m_rules);
            rule_ref_vector query_rules(rm);
            rule_ref clause(rm);
            func_decl_ref query_pred(m);
            rm.mk_query(query, query_pred, query_rules, clause);

            // ensure clause predicate does not take free variables.
            ptr_vector<app> tail;
            svector<bool> is_neg;
            for (unsigned i = 0; i < clause->get_tail_size(); ++i) {
                tail.push_back(clause->get_tail(i));
                is_neg.push_back(clause->is_neg_tail(i));
            }
            app_ref query_app(m);
            query_app = m.mk_const(symbol("query"), m.mk_bool_sort());
            m_ctx.register_predicate(query_app->get_decl());
            clause = rm.mk(query_app, tail.size(), tail.c_ptr(), is_neg.c_ptr()); 
            ref<tb::clause> g = alloc(tb::clause, rm);
            g->init(clause);
            init_clause(g);
            IF_VERBOSE(1, display_clause(*get_clause(), verbose_stream() << "g" << get_clause()->get_seqno() << " "););
            return run();
        }
    
        void cancel() {
            m_cancel = true;
            m_index.cleanup();
            m_solver.cancel();
        }
        
        void cleanup() {
            m_cancel = false;
            m_clauses.reset();
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
            expr_ref ans = get_answer();
            out << mk_pp(ans, m) << "\n";
        }

        expr_ref get_answer() const {
            switch(m_status) {
            case l_undef: 
                UNREACHABLE();
                return expr_ref(m.mk_false(), m);
            case l_true: {
                proof_ref pr = get_proof();
                return expr_ref(pr.get(), m);
            }
            case l_false:
                // NOT_IMPLEMENTED_YET();
                return expr_ref(m.mk_true(), m);
            }
            UNREACHABLE();
            return expr_ref(m.mk_true(), m);
        }
    private:
    
        void select_predicate() {
            tb::clause & g = *get_clause();
            unsigned num_predicates = g.get_num_predicates();
            if (num_predicates == 0) {
                m_instruction = tb::UNSATISFIABLE;
                IF_VERBOSE(2, g.display(verbose_stream()); );
            }
            else {
                m_instruction = tb::SELECT_RULE;
                unsigned pi = m_selection.select(g);
                g.set_predicate_index(pi);
                IF_VERBOSE(2, verbose_stream() << mk_pp(g.get_predicate(pi), m) << "\n";);
            }
        }
        
        void apply_rule(ref<tb::clause>& r) {
            ref<tb::clause> clause = get_clause();
            ref<tb::clause> next_clause;
            if (m_unifier(clause, r, false, next_clause) &&
                l_false != query_is_sat(*next_clause)) {
                init_clause(next_clause);
                unsigned subsumer = 0;
                IF_VERBOSE(1, 
                           display_rule(*clause, verbose_stream());
                           display_premise(*clause,   
                                           verbose_stream() << "g" << next_clause->get_seqno() << " ");
                           display_clause(*next_clause, verbose_stream());
                           );
                if (m_index.is_subsumed(next_clause, subsumer)) {
                    IF_VERBOSE(1, verbose_stream() << "subsumed by g" << subsumer << "\n";);
                    m_stats.m_num_subsumed++;
                    m_clauses.pop_back();
                    m_instruction = tb::SELECT_RULE;
                }
                else {
                    m_stats.m_num_unfold++;
                    next_clause->set_parent(clause);
                    m_index.insert(next_clause);
                    m_instruction = tb::SELECT_PREDICATE;
                }
            }
            else {
                m_stats.m_num_no_unfold++;
                m_instruction = tb::SELECT_RULE;
            }
        }
        
        void select_rule() {   
            tb::clause& g  = *get_clause();
            g.inc_next_rule();
            unsigned pi  = g.get_predicate_index();
            func_decl* p = g.get_predicate(pi)->get_decl();
            unsigned num_rules = m_rules.get_num_rules(p);
            unsigned index = g.get_next_rule();
            if (num_rules <= index) {
                m_instruction = tb::BACKTRACK;
            }
            else {
                ref<tb::clause> rl = m_rules.get_rule(p, index);
                apply_rule(rl);
            }
        }

        void backtrack() {
            SASSERT(!m_clauses.empty());
            m_clauses.pop_back();            
            if (m_clauses.empty()) {
                m_instruction = tb::SATISFIABLE;
            }
            else {
                m_instruction = tb::SELECT_RULE;
            }
        }

        lbool run() {
            m_instruction = tb::SELECT_PREDICATE;
            m_status      = l_undef;
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
                    m_status = l_false;
                    return l_false;
                case tb::UNSATISFIABLE:
                    m_status = l_true;
                    IF_VERBOSE(1, display_certificate(verbose_stream()););
                    return l_true;
                case tb::CANCEL:
                    cleanup();
                    m_status = l_undef;
                    return l_undef;
                }
            }
        }    

        lbool query_is_sat(tb::clause const& g) {
            ptr_vector<sort> sorts;
            svector<symbol> names;
            expr_ref fml = g.get_body();
            get_free_vars(fml, sorts);
            sorts.reverse();
            for (unsigned i = 0; i < sorts.size(); ++i) {
                if (!sorts[i]) {
                    sorts[i] = m.mk_bool_sort();
                }
                names.push_back(symbol(i));
            }
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


        void init_clause(ref<tb::clause>& clause) {
            clause->set_index(m_clauses.size());
            clause->set_seqno(m_seqno++);
            m_clauses.push_back(clause);
        }

        ref<tb::clause> get_clause() const { return m_clauses.back(); }


        void display_rule(tb::clause const& p, std::ostream& out) {
            func_decl* f = p.get_predicate(p.get_predicate_index())->get_decl();
            ref<tb::clause> rl = m_rules.get_rule(f, p.get_next_rule());
            unsigned idx = rl->get_index();
            if (!m_displayed_rules.contains(idx)) {
                m_displayed_rules.insert(idx);
                rl->display(out << p.get_next_rule() << ":");
            }
        }

        void display_premise(tb::clause& p, std::ostream& out) {
            func_decl* f = p.get_predicate(p.get_predicate_index())->get_decl();
            out << "{g" << p.get_seqno() << " " << f->get_name() << " pos: " << p.get_predicate_index() << " rule: " << p.get_next_rule() << "}\n";
        }

        void display_clause(tb::clause& g, std::ostream& out) {
            g.display(out);
        }

        proof_ref get_proof() const {
            scoped_proof sp(m);
            proof_ref pr(m);
            proof_ref_vector prs(m);
            expr_ref_vector subst(m);
            ref<tb::clause> clause = get_clause();
            ref<tb::clause> replayed_clause;
            replace_proof_converter pc(m);

            // clause is a empty clause. 
            // Pretend it is asserted.
            // It gets replaced by premises.
            SASSERT(clause->get_num_predicates() == 0); 
            expr_ref root = clause->to_formula();

            while (0 != clause->get_index()) {         
                SASSERT(clause->get_parent_index() < clause->get_index());       
                unsigned p_index  = clause->get_parent_index();
                unsigned p_rule   = clause->get_parent_rule();
                ref<tb::clause> parent = m_clauses[p_index];
                unsigned pi = parent->get_predicate_index();
                func_decl* pred = parent->get_predicate(pi)->get_decl();
                ref<tb::clause> rl = m_rules.get_rule(pred, p_rule); 
                VERIFY(m_unifier(parent, rl, true, replayed_clause));
                expr_ref_vector s1(m_unifier.get_rule_subst(true));
                expr_ref_vector s2(m_unifier.get_rule_subst(false));
                resolve_rule(pc, *parent, *rl, s1, s2, *clause);
                clause = parent;
                IF_VERBOSE(1000, 
                           verbose_stream() << "substitution\n";
                           for (unsigned i = 0; i < s1.size(); ++i) {
                               verbose_stream() << mk_pp(s1[i].get(), m) << "\n";
                           });
                // apply_subst(subst, s1);
            }
            pc.invert();
            prs.push_back(m.mk_asserted(root));
            pc(m, 1, prs.c_ptr(), pr);
            IF_VERBOSE(1000, 
                       verbose_stream() << "substitution\n";
                       for (unsigned i = 0; i < subst.size(); ++i) {
                           verbose_stream() << mk_pp(subst[i].get(), m) << "\n";
                       });
            return pr;
        }

        void resolve_rule(replace_proof_converter& pc, tb::clause const& r1, tb::clause const& r2, 
                          expr_ref_vector const& s1, expr_ref_vector const& s2, tb::clause const& res) const {
            unsigned idx = r1.get_predicate_index();
            expr_ref fml1 = r1.to_formula();
            expr_ref fml2 = r2.to_formula();
            expr_ref fml3 = res.to_formula();
            vector<expr_ref_vector> substs;
            svector<std::pair<unsigned, unsigned> > positions;
            substs.push_back(s1);
            substs.push_back(s2);            
            scoped_proof _sc(m);
            proof_ref pr(m);
            proof_ref_vector premises(m);
            premises.push_back(m.mk_asserted(fml1));
            premises.push_back(m.mk_asserted(fml2));
            positions.push_back(std::make_pair(idx+1, 0));            
            pr = m.mk_hyper_resolve(2, premises.c_ptr(), fml3, positions, substs);
            pc.insert(pr);
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
