/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_case_split_queue.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-20.

Revision History:

--*/
#include"smt_context.h"
#include"smt_case_split_queue.h"
#include"warning.h"
#include"stopwatch.h"
#include"for_each_expr.h"
#include"ast_pp.h"
#include"map.h"
#include"hashtable.h"

namespace smt {

    typedef map<bool_var, double, int_hash, default_eq<bool_var> > theory_var_priority_map;

    struct bool_var_act_lt {
        svector<double> const & m_activity;
        bool_var_act_lt(svector<double> const & a):m_activity(a) {}
        bool operator()(bool_var v1, bool_var v2) const {
            return m_activity[v1] > m_activity[v2];
        }
    };

    typedef heap<bool_var_act_lt> bool_var_act_queue;

    struct theory_aware_act_lt {
        svector<double> const & m_activity;
        theory_var_priority_map const & m_theory_var_priority;
        theory_aware_act_lt(svector<double> const & act, theory_var_priority_map const & a):m_activity(act),m_theory_var_priority(a) {}
        bool operator()(bool_var v1, bool_var v2) const {
            double p_v1, p_v2;
            if (!m_theory_var_priority.find(v1, p_v1)) {
                p_v1 = 0.0;
            }
            if (!m_theory_var_priority.find(v2, p_v2)) {
                p_v2 = 0.0;
            }
	    // add clause activity
	    p_v1 += m_activity[v1];
	    p_v2 += m_activity[v2];
            return p_v1 > p_v2;
        }
    };

    typedef heap<theory_aware_act_lt> theory_aware_act_queue;

    /**
       \brief Case split queue based on activity and random splits.
    */
    class act_case_split_queue : public case_split_queue {
    protected:
        context &          m_context;
        smt_params &       m_params;  
        bool_var_act_queue m_queue;
    public:
        act_case_split_queue(context & ctx, smt_params & p):
            m_context(ctx),
            m_params(p),
            m_queue(1024, bool_var_act_lt(ctx.get_activity_vector())) {
        }
            
        virtual void activity_increased_eh(bool_var v) {
            if (m_queue.contains(v))
                m_queue.decreased(v);
        }

        virtual void mk_var_eh(bool_var v) {
            m_queue.reserve(v+1);
            m_queue.insert(v);
        }

        virtual void del_var_eh(bool_var v) {
            if (m_queue.contains(v))
                m_queue.erase(v);
        }

        virtual void unassign_var_eh(bool_var v) {
            if (!m_queue.contains(v))
                m_queue.insert(v);
        }

        virtual void relevant_eh(expr * n) {}

        virtual void init_search_eh() {}

        virtual void end_search_eh() {}

        virtual void reset() {
            m_queue.reset();
        }

        virtual void push_scope() {}

        virtual void pop_scope(unsigned num_scopes) {}

        virtual void next_case_split(bool_var & next, lbool & phase) {
            phase = l_undef;
            
            if (m_context.get_random_value() < static_cast<int>(m_params.m_random_var_freq * random_gen::max_value())) {
                next = m_context.get_random_value() % m_context.get_num_b_internalized(); 
                TRACE("random_split", tout << "next: " << next << " get_assignment(next): " << m_context.get_assignment(next) << "\n";);
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }
            
            while (!m_queue.empty()) {
                next = m_queue.erase_min();
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }
            
            next = null_bool_var;
        }

        virtual void display(std::ostream & out) {
            bool first = true;
            bool_var_act_queue::const_iterator it  = m_queue.begin();
            bool_var_act_queue::const_iterator end = m_queue.end();
            for (; it != end ; ++it) {
                unsigned v = *it;
                if (m_context.get_assignment(v) == l_undef) {
                    if (first) {
                        out << "remaining case-splits:\n";
                        first = false;
                    }
                    out << "#" << m_context.bool_var2expr(v)->get_id() << " ";
                }
            }
            if (!first)
                out << "\n";

        }

        virtual ~act_case_split_queue() {};
    };

    /**
       \brief Similar to dact_case_split_queue, but delay case splits
       created during the search.
    */
    class dact_case_split_queue : public act_case_split_queue {
        bool_var_act_queue m_delayed_queue;
    public:
        dact_case_split_queue(context & ctx, smt_params & p):
            act_case_split_queue(ctx, p),
            m_delayed_queue(1024, bool_var_act_lt(ctx.get_activity_vector())) {
        }

        virtual void activity_increased_eh(bool_var v) {
            act_case_split_queue::activity_increased_eh(v);
            if (m_queue.contains(v))
                m_queue.decreased(v);
        }

        virtual void mk_var_eh(bool_var v) {
            m_queue.reserve(v+1);
            m_delayed_queue.reserve(v+1);
            if (m_context.is_searching()) 
                m_delayed_queue.insert(v);
            else
                m_queue.insert(v);
        }

        virtual void del_var_eh(bool_var v) {
            act_case_split_queue::del_var_eh(v);
            if (m_delayed_queue.contains(v))
                m_delayed_queue.erase(v);
        }

        virtual void relevant_eh(expr * n) {}

        virtual void init_search_eh() {}

        virtual void end_search_eh() {}

        virtual void reset() {
            act_case_split_queue::reset();
            m_delayed_queue.reset();
        }

        virtual void push_scope() {}

        virtual void pop_scope(unsigned num_scopes) {}

        virtual void next_case_split(bool_var & next, lbool & phase) {
            act_case_split_queue::next_case_split(next, phase);
            if (next != null_bool_var)
                return;
            
            m_queue.swap(m_delayed_queue);
            SASSERT(m_delayed_queue.empty());
            
            while (!m_queue.empty()) {
                next = m_queue.erase_min();
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }
            
            next = null_bool_var;
        }
    };

    /**
       \brief Case split queue based on activity and random splits.
    */
    class cact_case_split_queue : public act_case_split_queue {
        obj_map<expr, double>  m_cache;
        expr_ref_vector        m_cache_domain;
    public:
        cact_case_split_queue(context & ctx, smt_params & p):
            act_case_split_queue(ctx, p),
            m_cache_domain(ctx.get_manager()) {
        }
            
        virtual void mk_var_eh(bool_var v) {
            expr * n = m_context.bool_var2expr(v);
            double act;
            if (m_cache.find(n, act))
                m_context.set_activity(v, act);
            act_case_split_queue::mk_var_eh(v);
        }
        
        virtual void del_var_eh(bool_var v) {
            if (m_context.is_searching()) {
                double act = m_context.get_activity(v);
                if (act > 0.0) {
                    expr * n = m_context.bool_var2expr(v);
                    m_cache.insert(n, act);
                    m_cache_domain.push_back(n);
                }
            }
            act_case_split_queue::del_var_eh(v);
        }

        virtual void init_search_eh() {
            m_cache.reset();
            m_cache_domain.reset();
        }

        virtual void end_search_eh() {}

        virtual void reset() {
            init_search_eh();
        }
    };

    static bool has_child_assigned_to(context & ctx, app * parent, lbool val, expr * & undef_child, unsigned order) {
        ptr_vector<expr> undef_children;
        bool found_undef  = false;
        unsigned num_args = parent->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg    = parent->get_arg(i);
            lbool arg_val = ctx.get_assignment(arg);
            if (arg_val == val)
                return true;
            if (found_undef && order == 0)
                continue;
            if (arg_val == l_undef) {
                if (order == 1)
                    undef_children.push_back(arg);
                else
                    undef_child = arg;
                found_undef = true;
            }
        }
        if (order == 1) {
            if (undef_children.size() == 0) {
                // a bug?
            } else if (undef_children.size() == 1) {
                undef_child = undef_children[0];
            } else {
                undef_child = undef_children[ctx.get_random_value() % undef_children.size()];
            }
        }
        return false;
    }

    /**
       \brief Case split queue based on relevancy propagation
    */
    class rel_case_split_queue : public case_split_queue {
        struct scope {
            unsigned m_queue_trail;
            unsigned m_head_old;
            unsigned m_queue2_trail;
            unsigned m_head2_old;
        };
        typedef int_hashtable<int_hash, default_eq<int> > bool_var_set;
        context &         m_context;
        smt_params &m_params;  
        ast_manager &     m_manager;
        ptr_vector<expr>  m_queue;
        unsigned          m_head;
        int               m_bs_num_bool_vars; //!< Number of boolean variable before starting to search.
        ptr_vector<expr>  m_queue2;
        unsigned          m_head2;
        svector<scope>    m_scopes;
    public:
        rel_case_split_queue(context & ctx, smt_params & p):
            m_context(ctx),
            m_params(p),
            m_manager(ctx.get_manager()),
            m_head(0),
            m_bs_num_bool_vars(UINT_MAX),
            m_head2(0) {
        }
        
        virtual void activity_increased_eh(bool_var v) {}

        virtual void mk_var_eh(bool_var v) {}

        virtual void del_var_eh(bool_var v) {}

        virtual void unassign_var_eh(bool_var v) {}

        virtual void relevant_eh(expr * n) {
            if (!m_manager.is_bool(n))
                return;
            bool is_or     = m_manager.is_or(n);
            bool intern    = m_context.b_internalized(n);
            if (!intern && !is_or) 
                return;
            bool_var var = null_bool_var;
            if (intern) {
                var = m_context.get_bool_var(n);
                SASSERT(var != null_bool_var);
                bool is_and = m_manager.is_and(n);
                lbool val   = m_context.get_assignment(var);
                if (!(
                      val == l_undef || // n was not assigned yet
                      (is_or && val == l_true) || // need to justify a child
                      (is_and && val == l_false) // need to justify a child
                      ))
                    return;
            }
            if (!intern && m_context.is_searching()) {
                SASSERT(is_or);
                m_queue2.push_back(n);
                return;
            }
            if (var < m_bs_num_bool_vars) 
                m_queue.push_back(n);
            else
                m_queue2.push_back(n);
        }

        virtual void init_search_eh() {
            m_bs_num_bool_vars = m_context.get_num_bool_vars();
        }

        virtual void end_search_eh() {
            m_bs_num_bool_vars = UINT_MAX;
        }

        virtual void reset() {
            m_queue.reset();
            m_head = 0;
            m_queue2.reset();
            m_head2 = 0;
            m_scopes.reset();
        }

        virtual void push_scope() {
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_queue_trail  = m_queue.size();
            s.m_head_old     = m_head;
            s.m_queue2_trail = m_queue2.size();
            s.m_head2_old    = m_head2;
            TRACE("case_split", tout << "head: " << m_head << "\n";);
        }

        virtual void pop_scope(unsigned num_scopes) {
            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl    = m_scopes.size() - num_scopes;
            scope & s           = m_scopes[new_lvl];
            m_queue.shrink(s.m_queue_trail);
            m_head              = s.m_head_old;
            m_queue2.shrink(s.m_queue2_trail);
            m_head2             = s.m_head2_old;
            m_scopes.shrink(new_lvl);
            SASSERT(m_head <= m_queue.size());
            TRACE("case_split", display(tout); tout << "head: " << m_head << "\n";);
        }
        
        void next_case_split_core(ptr_vector<expr> & queue, unsigned & head, bool_var & next, lbool & phase) {
            phase = l_undef;
            unsigned sz = queue.size();
            for (; head < sz; head++) {
                expr * curr = queue[head];
                bool is_or  = m_manager.is_or(curr);
                bool is_and = m_manager.is_and(curr);
                bool intern = m_context.b_internalized(curr);
                SASSERT(intern || is_or);
                lbool val   = l_undef;
                if (intern) {
                    next = m_context.get_bool_var(curr);
                    val  = m_context.get_assignment(next);
                }
                else {
                    SASSERT(is_or); // top level clause
                    val  = l_true;
                }
                if ((is_or && val == l_true) || (is_and && val == l_false)) {
                    expr * undef_child = 0;
                    if (!has_child_assigned_to(m_context, to_app(curr), val, undef_child, m_params.m_rel_case_split_order)) {
                        if (m_manager.has_trace_stream()) {
                            m_manager.trace_stream() << "[decide-and-or] #" << curr->get_id() << " #" << undef_child->get_id() << "\n";
                        }
                        TRACE("case_split", tout << "found AND/OR candidate: #" << curr->get_id() << " #" << undef_child->get_id() << "\n";);
                        literal l = m_context.get_literal(undef_child);
                        next  = l.var();
                        phase = l.sign() ? l_false : l_true;
                        TRACE("case_split", display(tout););
                        return;
                    }
                }
                else if (val == l_undef) {
                    SASSERT(intern && m_context.get_bool_var(curr) == next);
                    TRACE("case_split", tout << "found candidate: #" << curr->get_id() << "\n";);
                    phase = l_undef;
                    TRACE("case_split", display(tout););
                    return;
                }
            }
            next = null_bool_var;
        }

        virtual void next_case_split(bool_var & next, lbool & phase) {
            next_case_split_core(m_queue, m_head, next, phase);
            if (next == null_bool_var)
                next_case_split_core(m_queue2, m_head2, next, phase);
            // Force l_false is next is an equality that is known to be disequal in the logical context.
            if (m_params.m_lookahead_diseq && next != null_bool_var && phase != l_false && m_context.has_enode(next)) {
                enode * n = m_context.bool_var2enode(next);
                if (n->is_eq()) {
                    enode * lhs = n->get_arg(0);
                    enode * rhs = n->get_arg(1);
                    if (m_context.is_ext_diseq(lhs, rhs, 2))
                        phase = l_false;
                }
            }
        }

        void display_core(std::ostream & out, ptr_vector<expr> & queue, unsigned head, unsigned idx) {
            if (queue.empty())
                return;
            unsigned sz = queue.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i == head) 
                    out << "[HEAD" << idx << "]=> ";
                out << "#" << queue[i]->get_id() << " ";
            }
            out << "\n";
        }

        virtual void display(std::ostream & out) {
            if (m_queue.empty() && m_queue2.empty())
                return;
            out << "case-splits:\n";
            display_core(out, m_queue, m_head, 1);
            display_core(out, m_queue2, m_head2, 2);
        }
   };
   
    /**
       \brief Case split queue based on relevancy propagation
    */
    class rel_act_case_split_queue : public case_split_queue {
        struct scope {
            unsigned m_queue_trail;
            unsigned m_head_old;
        };
        typedef int_hashtable<int_hash, default_eq<int> > bool_var_set;
        context &         m_context;
        ast_manager &     m_manager;
        smt_params &m_params;  
        ptr_vector<expr>  m_queue;
        unsigned          m_head;
        int               m_bs_num_bool_vars; //!< Number of boolean variable before starting to search.
        bool_var_act_queue m_delayed_queue;
        svector<scope>    m_scopes;
    public:
        rel_act_case_split_queue(context & ctx, smt_params & p):
            m_context(ctx),
            m_manager(ctx.get_manager()),
            m_params(p),
            m_head(0),
            m_bs_num_bool_vars(UINT_MAX),
            m_delayed_queue(1024, bool_var_act_lt(ctx.get_activity_vector())) {
        }

        virtual void activity_increased_eh(bool_var v) {}

        virtual void mk_var_eh(bool_var v) {
            if (m_context.is_searching()) {
                SASSERT(v >= m_bs_num_bool_vars);
                m_delayed_queue.reserve(v+1);
                m_delayed_queue.insert(v);
            }
        }

        virtual void del_var_eh(bool_var v) {
            if (v >= m_bs_num_bool_vars && m_delayed_queue.contains(v))
                m_delayed_queue.erase(v);
        }

        virtual void unassign_var_eh(bool_var v) {
            if (v < m_bs_num_bool_vars)
                return;
            if (!m_delayed_queue.contains(v))
                m_delayed_queue.insert(v);
        }

        virtual void relevant_eh(expr * n) {
            if (!m_manager.is_bool(n))
                return;
            bool is_or     = m_manager.is_or(n);
            bool intern    = m_context.b_internalized(n);
            if (!intern && !is_or) 
                return;
            bool_var var = null_bool_var;
            if (intern) {
                var = m_context.get_bool_var(n);
                SASSERT(var != null_bool_var);
                bool is_and = m_manager.is_and(n);
                lbool val   = m_context.get_assignment(var);
                if (!(
                      val == l_undef || // n was not assigned yet
                      (is_or && val == l_true) || // need to justify a child
                      (is_and && val == l_false) // need to justify a child
                      ))
                    return;
            }
            if (!intern) {
                if (!m_context.is_searching())
                    m_queue.push_back(n);
                return;
            }
            if (var < m_bs_num_bool_vars)
                m_queue.push_back(n);
        }
        
        virtual void init_search_eh() {
            m_bs_num_bool_vars = m_context.get_num_bool_vars();
        }

        virtual void end_search_eh() {
            m_bs_num_bool_vars = UINT_MAX;
        }

        virtual void reset() {
            m_queue.reset();
            m_head = 0;
            m_delayed_queue.reset();
            m_scopes.reset();
        }

        virtual void push_scope() {
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_queue_trail  = m_queue.size();
            s.m_head_old     = m_head;
            TRACE("case_split", tout << "head: " << m_head << "\n";);
        }

        virtual void pop_scope(unsigned num_scopes) {
            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl    = m_scopes.size() - num_scopes;
            scope & s           = m_scopes[new_lvl];
            m_queue.shrink(s.m_queue_trail);
            m_head              = s.m_head_old;
            m_scopes.shrink(new_lvl);
            SASSERT(m_head <= m_queue.size());
            TRACE("case_split", display(tout); tout << "head: " << m_head << "\n";);
        }

        void next_case_split_core(bool_var & next, lbool & phase) {
            phase = l_undef;
            unsigned sz = m_queue.size();
            for (; m_head < sz; m_head++) {
                expr * curr = m_queue[m_head];
                bool is_or  = m_manager.is_or(curr);
                bool is_and = m_manager.is_and(curr);
                bool intern = m_context.b_internalized(curr);
                SASSERT(intern || is_or);
                lbool val   = l_undef;
                if (intern) {
                    next = m_context.get_bool_var(curr);
                    val  = m_context.get_assignment(next);
                }
                else {
                    SASSERT(is_or); // top level clause
                    val  = l_true;
                }
                if ((is_or && val == l_true) || (is_and && val == l_false)) {
                    expr * undef_child = 0;
                    if (!has_child_assigned_to(m_context, to_app(curr), val, undef_child, m_params.m_rel_case_split_order)) {
                        TRACE("case_split", tout << "found AND/OR candidate: #" << curr->get_id() << " #" << undef_child->get_id() << "\n";);
                        literal l = m_context.get_literal(undef_child);
                        next  = l.var();
                        phase = l.sign() ? l_false : l_true;
                        TRACE("case_split", display(tout););
                        return;
                    }
                }
                else if (val == l_undef) {
                    SASSERT(intern && m_context.get_bool_var(curr) == next);
                    TRACE("case_split", tout << "found candidate: #" << curr->get_id() << "\n";);
                    phase = l_undef;
                    TRACE("case_split", display(tout););
                    return;
                }
            }
            next = null_bool_var;
        }

        virtual void next_case_split(bool_var & next, lbool & phase) {
            if (m_context.get_random_value() < static_cast<int>(0.02 * random_gen::max_value())) {
                next = m_context.get_random_value() % m_context.get_num_b_internalized(); 
                TRACE("random_split", tout << "next: " << next << " get_assignment(next): " << m_context.get_assignment(next) << "\n";);
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }
            
            next_case_split_core(next, phase);
            if (next != null_bool_var)
                return;
            phase = l_undef;
            while (!m_delayed_queue.empty()) {
                next = m_delayed_queue.erase_min();
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }
            next = null_bool_var;
        }

        void display_core(std::ostream & out) {
            if (m_queue.empty())
                return;
            unsigned sz = m_queue.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i == m_head) 
                    out << "[HEAD]=> ";
                out << "#" << m_queue[i]->get_id() << " ";
            }
            out << "\n";
        }

        virtual void display(std::ostream & out) {
            if (m_queue.empty())
                return;
            out << "case-splits:\n";
            display_core(out);
        }
    };


    /**
       \brief Case split queue based on relevancy propagation and generation/goal-similarity
    */
    class rel_goal_case_split_queue : public case_split_queue {
#if 0
#define GOAL_START() m_goal_time.start()
#define GOAL_STOP()  m_goal_time.stop()
#else
#define GOAL_START() do {} while (0)
#define GOAL_STOP()  do {} while (0)
#endif

        struct queue_entry {
            expr *    m_expr;
            unsigned  m_generation;
            int       m_last_decided;

            queue_entry(expr * e, unsigned gen):
                    m_expr(e),
                    m_generation(gen),
                    m_last_decided(-1) {}
        };

        struct generation_lt {
            rel_goal_case_split_queue & m_parent;
            generation_lt(rel_goal_case_split_queue & p):m_parent(p) {}
            bool operator()(int v1, int v2) const {
                unsigned g1 = m_parent.m_queue2[v1].m_generation;
                unsigned g2 = m_parent.m_queue2[v2].m_generation;

                if (g1 == g2)
                    return v1 < v2;
                else
                    return g1 < g2;
            }
        };

        struct scope {
            unsigned m_queue_trail;
            unsigned m_head_old;
            unsigned m_queue2_trail;
            unsigned m_generation;
            expr *   m_goal;
        };

        typedef int_hashtable<int_hash, default_eq<int> > bool_var_set;
        context &            m_context;
        smt_params &   m_params;  
        ast_manager &        m_manager;
        ptr_vector<expr>     m_queue;
        unsigned             m_head;
        int                  m_bs_num_bool_vars; //!< Number of boolean variable before starting to search.
        svector<queue_entry> m_queue2;
        svector<scope>       m_scopes;
        unsigned             m_current_generation;

        // The heap holds indices into m_queue2, i in m_priority_queue2 <==> m_queue2[i].m_last_assigned == -1
        heap<generation_lt>     m_priority_queue2;
        expr                  * m_current_goal;
        stopwatch               m_goal_time;

        static const unsigned start_gen = 0;
        static const unsigned goal_gen_decrement = 100;
        static const unsigned stop_gen = goal_gen_decrement + 1;


    public:
        rel_goal_case_split_queue(context & ctx, smt_params & p):
            m_context(ctx),
            m_params(p),
            m_manager(ctx.get_manager()),
            m_head(0),
            m_bs_num_bool_vars(UINT_MAX),
            m_priority_queue2(0, generation_lt(*this)),
            m_current_goal(0) {
            set_global_generation();
        }
        
        virtual void activity_increased_eh(bool_var v) {}

        virtual void mk_var_eh(bool_var v) {}

        virtual void del_var_eh(bool_var v) {}

        virtual void unassign_var_eh(bool_var v) {}

        virtual void relevant_eh(expr * n) {
            if (get_generation(n) == 0 && m_current_generation != 0)
                set_generation_rec(n, m_current_generation);

            if (!m_manager.is_bool(n))
                return;
            bool is_or     = m_manager.is_or(n);
            bool intern    = m_context.b_internalized(n);
            if (!intern && !is_or) 
                return;
            bool_var var = null_bool_var;
            if (intern) {
                var = m_context.get_bool_var(n);
                SASSERT(var != null_bool_var);
                bool is_and = m_manager.is_and(n);
                lbool val   = m_context.get_assignment(var);
                if (!(
                      val == l_undef || // n was not assigned yet
                      (is_or && val == l_true) || // need to justify a child
                      (is_and && val == l_false) // need to justify a child
                      ))
                    return;
            }
            if (!intern && m_context.is_searching()) {
                SASSERT(is_or);
                add_to_queue2(n);
                return;
            }
            if (var < m_bs_num_bool_vars) 
                m_queue.push_back(n);
            else
                add_to_queue2(n);
        }

        virtual void internalize_instance_eh(expr * e, unsigned gen)
        {
            //lower_generation(e, gen);
        }

        virtual void init_search_eh() {
            m_bs_num_bool_vars = m_context.get_num_bool_vars();
            set_global_generation();
        }

        virtual void end_search_eh() {
            m_bs_num_bool_vars = UINT_MAX;
        }

        virtual void reset() {
            m_queue.reset();
            m_head = 0;
            m_queue2.reset();
            m_scopes.reset();
            m_priority_queue2.reset();
            set_global_generation();
        }

        virtual void push_scope() {
            m_scopes.push_back(scope());
            scope & s = m_scopes.back();
            s.m_queue_trail  = m_queue.size();
            s.m_head_old     = m_head;
            s.m_queue2_trail = m_queue2.size();
            s.m_generation   = m_current_generation;
            s.m_goal         = m_current_goal;
            TRACE("case_split", tout << "head: " << m_head << "\n";);
        }

        virtual void pop_scope(unsigned num_scopes) {
            SASSERT(num_scopes <= m_scopes.size());
            unsigned new_lvl     = m_scopes.size() - num_scopes;
            scope & s            = m_scopes[new_lvl];
            m_queue.shrink(s.m_queue_trail);
            m_head               = s.m_head_old;
            m_current_generation = s.m_generation;
            m_current_goal       = s.m_goal;

            for (unsigned i = s.m_queue2_trail; i < m_queue2.size(); i++) {
                //TRACE("case_split", tout << "ld[" << i << "] = " << m_queue2[i].m_last_decided << " cont " << 
                SASSERT((m_queue2[i].m_last_decided == -1) == m_priority_queue2.contains(i));
                if (m_priority_queue2.contains(i))
                    m_priority_queue2.erase(i);
            }
            
            for (unsigned i = 0; i < s.m_queue2_trail; i++) {
                queue_entry & e = m_queue2[i];

                if (e.m_last_decided > static_cast<int>(new_lvl)) {
                    SASSERT(!m_priority_queue2.contains(i));
                    // Note that the generation might be reset by the pop, and we keep the heap
                    // ordered by the old generation. It's unlikely to affect performance I think.
                    m_priority_queue2.insert(i);
                    e.m_last_decided = -1;
                }
            }
            m_queue2.shrink(s.m_queue2_trail);
            m_scopes.shrink(new_lvl);
            SASSERT(m_head <= m_queue.size());
            TRACE("case_split", display(tout); tout << "head: " << m_head << "\n";);        
        }
        
        void next_case_split_core(expr * curr, bool_var & next, lbool & phase) {
            bool is_or  = m_manager.is_or(curr);
            bool is_and = m_manager.is_and(curr);
            bool intern = m_context.b_internalized(curr);
            SASSERT(intern || is_or);
            lbool val   = l_undef;
            if (intern) {
                next = m_context.get_bool_var(curr);
                val  = m_context.get_assignment(next);
            }
            else {
                SASSERT(is_or); // top level clause
                val  = l_true;
            }
            if ((is_or && val == l_true) || (is_and && val == l_false)) {
                expr * undef_child = 0;
                if (!has_child_assigned_to(m_context, to_app(curr), val, undef_child, m_params.m_rel_case_split_order)) {
                    if (m_manager.has_trace_stream()) {
                        m_manager.trace_stream() << "[decide-and-or] #" << curr->get_id() << " #" << undef_child->get_id() << "\n";
                    }
                    TRACE("case_split", tout << "found AND/OR candidate: #" << curr->get_id() << " #" << undef_child->get_id() << "\n";);
                    literal l = m_context.get_literal(undef_child);
                    next  = l.var();
                    phase = l.sign() ? l_false : l_true;
                    TRACE("case_split", display(tout););
                    return;
                }
            }
            else if (val == l_undef) {
                SASSERT(intern && m_context.get_bool_var(curr) == next);
                TRACE("case_split", tout << "found candidate: #" << curr->get_id() << "\n";);
                phase = l_undef;
                TRACE("case_split", display(tout););
                return;
            }
            next = null_bool_var;
        }

        virtual void next_case_split(bool_var & next, lbool & phase) {
            phase = l_undef;
            next = null_bool_var;

            unsigned sz = m_queue.size();
            for (; m_head < sz; m_head++) {
                expr * curr = m_queue[m_head];
                next_case_split_core(curr, next, phase);
                if (next != null_bool_var)
                    return;
            }

            while (!m_priority_queue2.empty()) {
                unsigned idx = static_cast<unsigned>(m_priority_queue2.erase_min());
                TRACE("case_split", tout << "q " << m_queue2.size() << " idx " << idx << "\n"; );
                SASSERT(idx < m_queue2.size());
                queue_entry & e = m_queue2[idx];
                SASSERT(e.m_last_decided == -1);
                e.m_last_decided = m_scopes.size();

                next_case_split_core(e.m_expr, next, phase);
                
                if (next != null_bool_var) {
                    // Push the last guy back in; the other queue doesn't increment
                    // the m_head in case of return and the code in decide() actually
                    // does the push after calling us
                    m_priority_queue2.insert(idx);
                    e.m_last_decided = -1;
                    return;
                }
            }
        }

        void display_core(std::ostream & out, ptr_vector<expr> & queue, unsigned head, unsigned idx) {
            if (queue.empty())
                return;
            unsigned sz = queue.size();
            for (unsigned i = 0; i < sz; i++) {
                if (i == head) 
                    out << "[HEAD" << idx << "]=> ";
                out << "#" << queue[i]->get_id() << " ";
            }
            out << "\n";
        }

        virtual void display(std::ostream & out) {
            if (m_queue.empty() && m_queue2.empty())
                return;
            out << "case-splits:\n";
            display_core(out, m_queue, m_head, 1);
            //display_core(out, m_queue2, m_head2, 2);
        }

        virtual void assign_lit_eh(literal l) {
            // if (m_current_generation > stop_gen)
            //    m_current_generation--;

            expr * e = m_context.bool_var2expr(l.var());
            if (e == m_current_goal)
                return;
            bool sign = l.sign();
            if ( ((m_manager.is_and(e) && !sign) ||
                  (m_manager.is_or(e) && sign)) &&
                  to_app(e)->get_num_args() == 2) {
                
                expr * lablit = to_app(e)->get_arg(1);
                if (m_manager.is_not(lablit)) {
                    sign = !sign;
                    lablit = to_app(lablit)->get_arg(0);
                }
                if (sign) return;
                if (!m_manager.is_label_lit(lablit))
                    return;

                TRACE("case_split", tout << "Found goal\n" << mk_pp(e, m_manager) << "\n"; );

                set_goal(e);
            }
        }

    private:

        unsigned get_generation(expr * e)
        {
            unsigned maxgen = 0;
            unsigned mingen = (unsigned)-1;
            ptr_vector<expr> stack;

            stack.push_back(e);
            while (!stack.empty()) {
                unsigned gen;
                expr * curr;

                curr = stack.back();
                stack.pop_back();

                if (m_context.e_internalized(curr)) {
                    gen = m_context.get_enode(curr)->get_generation();
                    if (gen > maxgen)
                        maxgen = gen;
                    if (gen < mingen)
                        mingen = gen;
                }
                else if (is_app(curr)) {
                    app * a = to_app(curr);
                    for (unsigned i = 0; i < a->get_num_args(); ++i)
                        stack.push_back(a->get_arg(i));
                }
            }

            return maxgen;
        }

        void add_to_queue2(expr * e)
        {
            int      idx = m_queue2.size();

            GOAL_START();
            m_queue2.push_back(queue_entry(e, get_generation(e)));
            m_priority_queue2.reserve(idx+1);
            m_priority_queue2.insert(idx);
            GOAL_STOP();
        }

        struct set_generation_fn { 
            context & m_context;
            unsigned m_generation;
            set_generation_fn(context & ctx, unsigned gen) : m_context(ctx), m_generation(gen) { }
            void operator()(expr * e) {
                if (m_context.e_internalized(e)) {
                    enode * n = m_context.get_enode(e);
                    n->set_generation(m_context, m_generation);
                }
            }
        };

        void set_generation_rec(expr * e, unsigned gen)
        {
            set_generation_fn proc(m_context, gen);
            for_each_expr(proc, e);
        }

        void lower_generation(expr * e, unsigned gen)
        {
            ptr_vector<expr> stack;

            stack.push_back(e);
            while (!stack.empty()) {
                expr * curr;

                curr = stack.back();
                stack.pop_back();

                if (m_context.e_internalized(curr)) {
                    unsigned curr_gen = m_context.get_enode(curr)->get_generation();
                    if (curr_gen > gen) {
                        // Lower it.
                        set_generation_rec(e, gen);
                        continue; // Don't add children.
                    }
                    else if (curr_gen < gen) {
                        // All the children will be lower as well, don't add them.
                        continue;
                    }
                }

                if (is_app(curr)) {
                    app * a = to_app(curr);
                    for (unsigned i = 0; i < a->get_num_args(); ++i)
                        stack.push_back(a->get_arg(i));
                }
            }
        }

        void set_goal(expr * e)
        {

            if (e == m_current_goal) return;

            GOAL_START();

            m_current_goal = e;

#if 1
            if (m_current_generation >= goal_gen_decrement) {
                set_generation_rec(m_current_goal, m_current_generation - goal_gen_decrement);

                /*
                m_priority_queue2.reset();
                m_priority_queue2.reserve(m_queue2.size());

                for (unsigned i = 0; i < m_queue2.size(); ++i) {
                    queue_entry & e = m_queue2[i];
                    e.m_generation = get_generation(e.m_expr);
                    if (e.m_last_decided == -1)
                        m_priority_queue2.insert(i);
                }
                */
            }
#endif

            GOAL_STOP();

            //std::cout << "goal set, time " << m_goal_time.get_seconds() << "\n";
        }

        void set_global_generation()
        {
            m_current_generation = start_gen;
            m_context.set_global_generation(start_gen);
            if (m_params.m_qi_eager_threshold < start_gen)
                m_params.m_qi_eager_threshold += start_gen;
        }
    };

    class theory_aware_branching_queue : public case_split_queue {
    protected:
        context &          m_context;
        smt_params &       m_params;
        theory_var_priority_map m_theory_var_priority;
        theory_aware_act_queue m_queue;

        int_hashtable<int_hash, default_eq<bool_var> > m_theory_vars;
        map<bool_var, lbool, int_hash, default_eq<bool_var> > m_theory_var_phase;
    public:
        theory_aware_branching_queue(context & ctx, smt_params & p):
            m_context(ctx),
            m_params(p),
            m_theory_var_priority(),
            m_queue(1024, theory_aware_act_lt(ctx.get_activity_vector(), m_theory_var_priority)) {
        }

        virtual void activity_increased_eh(bool_var v) {
            if (m_queue.contains(v))
                m_queue.decreased(v);
        }

        virtual void mk_var_eh(bool_var v) {
            m_queue.reserve(v+1);
            m_queue.insert(v);
        }

        virtual void del_var_eh(bool_var v) {
            if (m_queue.contains(v))
                m_queue.erase(v);
        }

        virtual void unassign_var_eh(bool_var v) {
            if (!m_queue.contains(v))
                m_queue.insert(v);
        }

        virtual void relevant_eh(expr * n) {}

        virtual void init_search_eh() {}

        virtual void end_search_eh() {}

        virtual void reset() {
            m_queue.reset();
        }

        virtual void push_scope() {}

        virtual void pop_scope(unsigned num_scopes) {}

        virtual void next_case_split(bool_var & next, lbool & phase) {
            int threshold = static_cast<int>(m_params.m_random_var_freq * random_gen::max_value());
            SASSERT(threshold >= 0);
            if (m_context.get_random_value() < threshold) {
                SASSERT(m_context.get_num_b_internalized() > 0);
                next = m_context.get_random_value() % m_context.get_num_b_internalized(); 
                TRACE("random_split", tout << "next: " << next << " get_assignment(next): " << m_context.get_assignment(next) << "\n";);
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }

            while (!m_queue.empty()) {
                next = m_queue.erase_min();
                if (m_context.get_assignment(next) == l_undef)
                    return;
            }

            next = null_bool_var;
            if (m_theory_vars.contains(next)) {
                if (!m_theory_var_phase.find(next, phase)) {
                    phase = l_undef;
                }
            }
        }

        virtual void add_theory_aware_branching_info(bool_var v, double priority, lbool phase) {
            TRACE("theory_aware_branching", tout << "Add theory-aware branching information for l#" << v << ": priority=" << priority << std::endl;);
            m_theory_vars.insert(v);
            m_theory_var_phase.insert(v, phase);
            m_theory_var_priority.insert(v, priority);
            if (m_queue.contains(v)) {
                if (priority > 0.0) {
                    m_queue.decreased(v);
                } else {
                    m_queue.increased(v);
                }
            }
            // m_theory_queue.reserve(v+1);
            // m_theory_queue.insert(v);
        }

        virtual void display(std::ostream & out) {
            bool first = true;
            bool_var_act_queue::const_iterator it  = m_queue.begin();
            bool_var_act_queue::const_iterator end = m_queue.end();
            for (; it != end ; ++it) {
                unsigned v = *it;
                if (m_context.get_assignment(v) == l_undef) {
                    if (first) {
                        out << "remaining case-splits:\n";
                        first = false;
                    }
                    out << "#" << m_context.bool_var2expr(v)->get_id() << " ";
                }
            }
            if (!first)
                out << "\n";

        }

        virtual ~theory_aware_branching_queue() {};
    };


    case_split_queue * mk_case_split_queue(context & ctx, smt_params & p) {
        if (p.m_relevancy_lvl < 2 && (p.m_case_split_strategy == CS_RELEVANCY || p.m_case_split_strategy == CS_RELEVANCY_ACTIVITY || 
                p.m_case_split_strategy == CS_RELEVANCY_GOAL)) {
            warning_msg("relevancy must be enabled to use option CASE_SPLIT=3, 4 or 5");
            p.m_case_split_strategy = CS_ACTIVITY;
        }
        if (p.m_auto_config && (p.m_case_split_strategy == CS_RELEVANCY || p.m_case_split_strategy == CS_RELEVANCY_ACTIVITY || 
                p.m_case_split_strategy == CS_RELEVANCY_GOAL)) {
            warning_msg("auto configuration (option AUTO_CONFIG) must be disabled to use option CASE_SPLIT=3, 4 or 5");
            p.m_case_split_strategy = CS_ACTIVITY;
        }
        switch (p.m_case_split_strategy) {
        case CS_ACTIVITY_DELAY_NEW:
            return alloc(dact_case_split_queue, ctx, p);
        case CS_ACTIVITY_WITH_CACHE:
            return alloc(cact_case_split_queue, ctx, p);
        case CS_RELEVANCY:
            return alloc(rel_case_split_queue, ctx, p);
        case CS_RELEVANCY_ACTIVITY:
            return alloc(rel_act_case_split_queue, ctx, p);
        case CS_RELEVANCY_GOAL:
            return alloc(rel_goal_case_split_queue, ctx, p);
        case CS_ACTIVITY_THEORY_AWARE_BRANCHING:
            return alloc(theory_aware_branching_queue, ctx, p);
        default:
            return alloc(act_case_split_queue, ctx, p);
        }
    }

};

