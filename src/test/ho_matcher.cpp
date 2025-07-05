
// preliminary outline of elements in a higher-order matcher

#include "util/trail.h"
#include "util/dlist.h"
#include "util/uint_set.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/array_rewriter.h"
#include "ast/rewriter/var_subst.h"


namespace euf {

    class ho_matcher;

    class work_state {
        enum state {
            init_s,
            project_s,
            app_s, 
            done_s
        };
        state m_state = state::init_s;
        unsigned m_index = 0;
        bool m_in_scope = false;

    public:
        void set_init() {
            m_state = state::init_s;
            m_index = 0;
            m_in_scope = false;
        }
        bool is_init() const { return m_state == state::init_s; }
        bool is_project() const { return m_state == state::project_s; }
        bool is_app() const { return m_state == state::app_s && m_index == 0; }
        bool is_done() const { return m_state == state::done_s; }
        void set_project() { m_state = state::project_s; m_index = 0; }
        void set_app() { m_state = state::app_s; m_index = 0; }
        void set_done() { m_state = state::done_s; }
        void inc_index() { ++m_index; }
        void set_index(unsigned i) { m_index = i; }
        unsigned index() const { return m_index; }
        bool in_scope() const { return m_in_scope; }
        void set_in_scope(bool f = true) { m_in_scope = f; }
    };

    class match_goal : public dll_base<match_goal>, public work_state {
        unsigned base_offset = 0;
        unsigned delta_offset = 0; // offset of term
    public:
        expr_ref pat, t;
        unsigned level = 0; // level backtrack level
       
        void reset() {
            pat.reset();
            t.reset();
            level = 0;
            base_offset = 0;
            delta_offset = 0;
        }

        bool operator==(match_goal const& other) const {
            return pat == other.pat && t == other.t && base_offset == other.base_offset && delta_offset == other.delta_offset;
        }

        bool operator!=(match_goal const& other) const {
            return !(*this == other);
        }

        match_goal(unsigned level, unsigned offset, expr_ref const& pat, expr_ref const& t) noexcept : 
            base_offset(offset), pat(pat), t(t),  level(level)  {}

        unsigned term_offset() const { return base_offset + delta_offset; }
        unsigned pat_offset() const { return base_offset + delta_offset; }

        std::ostream& display(std::ostream& out) const {
            return out << "[" << level << ":" << base_offset + delta_offset << "] " << pat << " ~ " << t << "\n";
        }
    };

    class match_goals {
    protected:
        ast_manager &m;
        ho_matcher& ho;
        
        match_goal* m_expensive = nullptr, *m_cheap = nullptr;
        match_goal* pop(match_goal*& q);
        
    public:
        match_goals(ho_matcher& em, ast_manager &m) : m(m), ho(em) {}
        bool empty() const { return m_cheap == nullptr && m_expensive == nullptr; }
        void reset() { m_cheap = m_expensive = nullptr; }
        void push(unsigned level, unsigned offset, expr_ref const& pat, expr_ref const& t);
        void push(unsigned level, unsigned offset, expr* p, expr* t) { push(level, offset, expr_ref(p, m), expr_ref(t, m)); }
        match_goal* pop();

        std::ostream& display(std::ostream& out) const;

    };

    class ho_subst {
        expr_ref_vector m_subst;
    public:
        ho_subst(ast_manager& m) :
            m_subst(m) {            
        }
        void resize(unsigned n) {
            m_subst.resize(n, nullptr);
        }

        unsigned size() const {
            return m_subst.size();
        }

        void set(unsigned v, expr* t) {
            SASSERT(!m_subst.get(v));
            m_subst[v] = t;
        }

        expr* get(unsigned v) const {
            return m_subst.get(v);
        }

        void unset(unsigned v) {
            SASSERT(m_subst.get(v));
            m_subst[v] = nullptr;
        }

        std::ostream& display(std::ostream& out) const {
            auto& m = m_subst.get_manager();
            for (unsigned i = 0; i < m_subst.size(); ++i) {
                if (m_subst.get(i)) {
                    out << "v" << i << " -> " << mk_pp(m_subst.get(i), m) << "\n";
                }
            }
            return out;
        }
    };

    class unitary_patterns {
        ast_manager& m;
        array_util a;
        vector<expr_ref_vector> m_patterns;
        vector<svector<lbool>>  m_is_unitary;
        svector<std::pair<unsigned, expr*>> m_todo;

        lbool find(unsigned offset, expr* p) const {
            if (offset >= m_is_unitary.size())
                return l_undef;
            if (p->get_id() >= m_is_unitary[offset].size())
                return l_undef;
            return m_is_unitary[offset][p->get_id()];
        }

        void set_unitary(unsigned offset, expr* p, lbool is_unitary) {
            if (offset >= m_is_unitary.size())
                m_is_unitary.resize(offset + 1);
            if (p->get_id() >= m_is_unitary[offset].size())
                m_is_unitary[offset].resize(p->get_id() + 1, l_undef);
            m_is_unitary[offset][p->get_id()] = is_unitary;
        }

    public:
        unitary_patterns(ast_manager& m) : m(m), a(m) {}

        bool is_unitary(unsigned offset, expr* p) const {
            return find(offset, p) == l_true;
        }

        bool is_flex(unsigned offset, expr* e) const {
            bool is_select = false;
            expr* t = e;
            while (a.is_select(t))
                t = to_app(t)->get_arg(0), is_select = true;
            if (is_select && is_var(t) && to_var(t)->get_idx() >= offset) {
                // check if e is a pattern.
                return true;
            }
            return false;
        }

        void add_pattern(expr* p) {
            m_todo.push_back({ 0, p });
            while (!m_todo.empty()) {
                auto [o, p] = m_todo.back();
                if (l_undef != find(o, p)) {
                    m_todo.pop_back();
                    continue;
                }

                // ((M N) K)
                // if M is a meta variable and N, K are not patterns it is non_unitary
                // otherwise we declare it as (locally) unitary. It will be inserted into the "cheap" queue.
                // subterms can be non-unitary.

                if (is_app(p)) {
                    auto a = to_app(p);
                    auto sz = m_todo.size();
                    lbool is_unitary = l_true;
                    for (auto arg : *a) {
                        switch (find(o, arg)) {
                        case l_undef:
                            m_todo.push_back({ o, arg });
                            break;                       
                        default:
                            break;
                        }
                    }
                    if (sz != m_todo.size())
                        continue;
                    if (is_flex(o, p))
                        is_unitary = l_false;
                    set_unitary(o, p, is_unitary);
                    m_todo.pop_back();
                }
                else if (is_var(p)) 
                    set_unitary(o, p, l_true);              
                else {
                    auto q = to_quantifier(p);
                    unsigned nd = q->get_num_decls();
                    auto body = q->get_expr();
                    switch (find(o + nd, body)) {
                    case l_undef:
                        m_todo.push_back({ o + nd, body });
                        break;
                    default:
                        m_todo.pop_back();
                        set_unitary(o, p, l_true);
                        break;
                    }
                }
            }
        }

    };

    struct undo_set : public trail {
        ho_subst& s;
        unsigned v;
        undo_set(ho_subst& s, unsigned v) : s(s), v(v) {}
        void undo() override {
            s.unset(v);
        }
    };

    struct undo_resize : public trail {
        ho_subst& s;
        unsigned old_size;
        undo_resize(ho_subst& s) : s(s), old_size(s.size()) {}
        void undo() override {
            s.resize(old_size);
        }
    };


    template<typename V>
    class update_value : public trail {
        V& lval;
        V  rval;
    public:
        update_value(V& lval, V rval) : lval(lval), rval(rval) {}
        void undo() override {
            lval = rval;
            rval.reset();
        }
    };

    struct remove_dll : public trail {
        match_goal*& m_list;
        match_goal* m_value;
        remove_dll(match_goal*& list, match_goal* value) : m_list(list), m_value(value) {}
        void undo() override {
            dll_base<match_goal>::remove_from(m_list, m_value);
        }
    };

    struct insert_dll : public trail {
        match_goal*& m_list;
        match_goal* m_value;
        insert_dll(match_goal*& list, match_goal* value) : m_list(list), m_value(value) {}
        void undo() override {
            dll_base<match_goal>::push_to_front(m_list, m_value);
        }
    };

    class ho_matcher {
    protected:
        ast_manager &m;
        trail_stack& m_trail;
        ho_subst         m_subst;
        match_goals      m_goals;
        unitary_patterns m_unitary;
        ptr_vector<match_goal> m_backtrack;
        mutable array_rewriter   m_rewriter;
        array_util       m_array;

    	void resume();

        void push_backtrack();

        void backtrack();

        bool consume_work(match_goal& wi);

        expr_ref whnf(expr* e, unsigned offset) const;
        
        bool is_bound_var(expr* v, unsigned offset) const { return is_var(v) && to_var(v)->get_idx() < offset; }

        bool is_meta_var(expr* v, unsigned offset) const { return is_var(v) && to_var(v)->get_idx() >= offset; }

        bool is_closed(expr* v, unsigned scopes, unsigned offset) const;

        void add_binding(var* v, unsigned offset, expr* t);

        expr_ref mk_project(unsigned num_lambdas, unsigned xi, sort* array_sort);

        void bind_lambdas(unsigned j, sort* s, expr_ref& body);

        lbool are_equal(unsigned o1, expr* p, unsigned o2, expr* t) const;

        bool is_pattern(expr* p, unsigned offset, expr* t);

        expr_ref abstract_pattern(expr* p, unsigned offset, expr* t);

        std::function<void(ho_subst&)> m_on_match;

    public:

        ho_matcher(ast_manager& m, trail_stack &trail) : 
            m(m),
            m_subst(m),
            m_trail(trail),
            m_goals(*this, m),
            m_unitary(m),
            m_array(m),
            m_rewriter(m)
        {
        }

        void set_on_match(std::function<void(ho_subst&)>& on_match) { m_on_match = on_match; }

        void operator()(expr *pat, expr *t, unsigned num_vars);

        void operator()(expr* pat, expr* t, unsigned num_bound, unsigned num_vars);

        void reduce(match_goal& wi);

        trail_stack& trail() { return m_trail; }

        std::ostream& display(std::ostream& out) const;

        bool is_cheap(match_goal const& g) const { return m_unitary.is_unitary(g.pat_offset(), g.pat); }

        void add_pattern(expr* p) {
            m_unitary.add_pattern(p);
        }
    };
}



/**
   Ho-matcher performs a tree search over match_goals.
   Let Q be the current set of match_goals
   Let B be the current state of a backtracking stack.
   Each element in Q is a work item. 
   The workflow is as follows:
   elements w of Q are removed and added to B, 
   if processing of w results in a unitary match, it is removed from B and the match_goals are added to Q.

   match_goals in Q can be processed independently on when they are generated.
   If a subgoal of Q fails to match, the algorithm backtracks.
   Backtracking can be tuned by keeping track of dependencies.

   Elements in Q are simplified relative to a current substitution. 
   The level where the current substitution affects simplification determines 
   the persistence level of simplification.
  
   A v1 ignores dependencies and assumes always that side-effects are relative to the current backtracking scope.
   A v2 should address and measure the overhead.

   Elements in Q need to persist relative to changes made within a backtracking scope.
   Every operation on Q should be replayed. 
   Thus, elements removed from Q are re-inserted.

   (pat, offset) (t, offset)
   - a variable is considered bound if it's index is below offset.
   - meta variables are adjusted relative to offset


*/
namespace euf {


    void ho_matcher::operator()(expr* pat, expr* t, unsigned num_vars) {
        (*this)(pat, t, 0, num_vars);
    }

    void ho_matcher::operator()(expr* pat, expr* t, unsigned num_bound, unsigned num_vars) {               
        m_trail.push_scope();
        m_subst.resize(num_vars);
        m_goals.reset();
        m_goals.push(0, num_bound, pat, t); 

        IF_VERBOSE(1, display(verbose_stream()));
        
        while (m.inc()) {
            // Q, B -> Q', B'. Push work on the backtrack stack and new work items
            // e, Bw -> Q', B'. Consume backtrack stack
            if (!m_goals.empty())
                push_backtrack();
            else if (!m_backtrack.empty()) 
                resume();
            else
                break;
        }
        m_trail.pop_scope(1);
        IF_VERBOSE(1, display(verbose_stream() << "ho_matcher: done\n"));
    }

    void ho_matcher::backtrack() {
        SASSERT(!m_backtrack.empty());
        auto wi = m_backtrack.back();
        if (wi->in_scope()) 
            m_trail.pop_scope(1);        
        m_backtrack.pop_back();
    }

    void ho_matcher::resume() {
        while (!m_backtrack.empty()) {
            auto& wi = *m_backtrack.back();
            if (consume_work(wi)) {
                IF_VERBOSE(3, display(verbose_stream() << "ho_matcher::consume_work: " << wi.pat << " =?= " << wi.t << " -> true\n"););
                if (m_goals.empty()) 
                    m_on_match(m_subst);                
                break;
            }
            else {
                IF_VERBOSE(3, display(verbose_stream() << "ho_matcher::consume_work: " << wi.pat << " =?= " << wi.t << " -> false\n"););
                backtrack();
            }
        }
    }

    void ho_matcher::push_backtrack() {
        SASSERT(!m_goals.empty());      
        m_backtrack.push_back(m_goals.pop());
        resume();
    }

    lbool ho_matcher::are_equal(unsigned o1, expr* p, unsigned o2, expr* t) const {
        SASSERT(p->get_sort() == t->get_sort());
        if (o1 == o2 && p == t)
            return l_true;

        if (is_ground(p) && is_ground(t)) 
            return to_lbool(p == t);
        
        if (is_lambda(p) && is_lambda(t)) {
            auto q1 = to_quantifier(p);
            auto q2 = to_quantifier(t);
            SASSERT(q1->get_num_decls() == q2->get_num_decls());
            return are_equal(o1 + q1->get_num_decls(), q1->get_expr(), o2 + q2->get_num_decls(), q2->get_expr());
        }

        if (is_meta_var(p, o1)) {
            auto p1 = m_subst.get(to_var(p)->get_idx() - o1);
            if (p1) 
                return are_equal(0, p1, o2, t);
            return l_undef;
        }

        if (is_meta_var(t, o2)) {
            auto t1 = m_subst.get(to_var(t)->get_idx() - o2);
            if (t1) 
                return are_equal(o1, p, 0, t1);
            return l_undef;
        }       


        if (m_unitary.is_flex(o1, p)) {
            expr_ref h = whnf(p, o1);
            if (h != p)
                return are_equal(o1, h, o2, t);
            return l_undef;
        }
        if (m_unitary.is_flex(o2, t)) {
            expr_ref h = whnf(t, o2);
            if (h != t)
                return are_equal(o1, p, o2, h);
            return l_undef;
        }
        if (m_array.is_select(p))
            return l_undef; // TODO: interleave check with whnf expansion
        
        if (is_app(p) && is_app(t)) {          
            auto a1 = to_app(p);
            auto a2 = to_app(t);
            if (a1->get_decl() != a2->get_decl())
                return l_false;
            if (a1->get_num_args() != a2->get_num_args())
                return l_false;
            for (unsigned i = 0; i < a1->get_num_args(); ++i) {
                auto r = are_equal(o1, a1->get_arg(i), o2, a2->get_arg(i));
                if (r != l_true)
                    return r;
            }
            return l_true;
        }
        if (is_bound_var(p, o1) || is_bound_var(t, o2))
            return to_lbool(p == t);

        return l_undef;
    }

    //
    // reduces (M N)
    // and recurisvely ((M N) K)
    // such that M is not a lambda
    //
    expr_ref ho_matcher::whnf(expr* e, unsigned offset) const {
        expr_ref r(e, m), t(m);
//        verbose_stream() << "ho_matcher::whnf: " << r << "\n";
        if (is_meta_var(r, offset)) {
            auto v = to_var(e);
            auto idx = v->get_idx();
            if (idx >= offset && m_subst.get(idx - offset)) {
                auto e = m_subst.get(idx - offset);
                r = e;
                if (offset > 0) {
                    var_shifter sh(m);
                    sh(e, offset, r);
                }
                return r;
            }
        }
        while (m_array.is_select(r)) {
            app* a = to_app(r);
            auto arg0 = a->get_arg(0);
            //  apply substitution:
            if (is_meta_var(arg0, offset)) {
                auto v = to_var(arg0);
                auto idx = v->get_idx();
                if (idx >= offset && m_subst.get(idx - offset)) {
                    auto e = m_subst.get(idx - offset);
                    if (offset > 0) {
                        var_shifter sh(m);
                        sh(e, offset, r);
                        e = r;
                    }
                    expr_ref_vector args(m);
                    args.push_back(e);
                    for (unsigned i = 1; i < a->get_num_args(); ++i) 
                        args.push_back(a->get_arg(i));
                    
                    r = m.mk_app(a->get_decl(), args.size(), args.data());
  //                  verbose_stream() << "ho_matcher::whnf: " << r << "\n";
                    continue;
                }
            }
            if (m_array.is_select(arg0)) {
                t = whnf(arg0, offset);
                if (t != arg0) {
                    ptr_vector<expr> args(a->get_num_args(), a->get_args());
                    args[0] = t;
                    r = m_array.mk_select(args.size(), args.data());
   //                 verbose_stream() << "ho_matcher::whnf-rec: " << r << "\n";
                    continue;
                }
            }
            // outer beta reduction
            auto st = m_rewriter.mk_app_core(a->get_decl(), a->get_num_args(), a->get_args(), t);
            if (st != BR_FAILED)
                r = t;
            else
                break;
        }
        return r;    
    }

    // We assume that m_rewriter should produce
    // something amounting to weak-head normal form WHNF

    void ho_matcher::reduce(match_goal& wi) {
        while (true) {
            expr_ref r = whnf(wi.pat, wi.pat_offset());
            if (r == wi.pat)
                break;
            IF_VERBOSE(3, verbose_stream() << "ho_matcher::reduce: " << wi.pat << " -> " << r << "\n";);
            wi.pat = r;
        } 

        while (true) {
            expr_ref r = whnf(wi.t, wi.term_offset());
            if (r == wi.t)
                break;
            IF_VERBOSE(3, verbose_stream() << "ho_matcher::reduce: " << wi.t << " -> " << r << "\n";);
            wi.t = r;
        } 
    }

    bool ho_matcher::consume_work(match_goal &wi) {
//        IF_VERBOSE(1, display(verbose_stream() << "ho_matcher::consume_work: " << wi.pat << " =?= " << wi.t << "\n"););

        if (wi.in_scope()) 
            m_trail.pop_scope(1);
        
        wi.set_in_scope();
        m_trail.push_scope();
        
        if (wi.is_done())
            return false;

        reduce(wi);

        auto t = wi.t;
        auto p = wi.pat;

        switch (are_equal(wi.pat_offset(), p, wi.term_offset(), t)) {
        case l_false:
            wi.set_done();
            return false;
        case l_true:
            wi.set_done();
            return true;
        case l_undef:
            break;
        }
        

        // v >= offset
        // v - offset |-> t
        if (is_meta_var(p, wi.pat_offset()) && is_closed(t, 0, wi.term_offset())) {
            auto v = to_var(p);
            auto idx = v->get_idx() - wi.pat_offset();
            SASSERT(!m_subst.get(idx)); // reduce ensures meta variables are not in substitutions
            add_binding(v, wi.pat_offset(), t);
            wi.set_done();
            return true;
        }


        // N = \ x. T => ((shift1 N) x) = T
        if (is_lambda(t) && !is_lambda(p)) {
            auto q = to_quantifier(t);
            auto t_body = q->get_expr();
            auto nd = q->get_num_decls();
            var_shifter vs(m);
            expr_ref r(m);
            vs(p, nd, r);
            expr_ref_vector args(m);
            args.push_back(r);
            for (unsigned i = 0; i < nd; ++i)
                args.push_back(m.mk_var(nd - 1 - i, q->get_decl_sort(i)));
            r = m_array.mk_select(args);
            m_goals.push(wi.level, wi.term_offset() + nd, r, t_body);
            wi.set_done();
            return true;
        }

        // Flex head unitary
        // H(pat) = t

        if (m_array.is_select(p) && m_unitary.is_flex(wi.pat_offset(), p) && is_pattern(p, wi.pat_offset(), t)) {
            auto lam = abstract_pattern(p, wi.pat_offset(), t);
            while (m_array.is_select(p))
                p = to_app(p)->get_arg(0);
            SASSERT(is_meta_var(p, wi.pat_offset()));
            add_binding(to_var(p), wi.pat_offset(), lam);
            wi.set_done();
            return true;
        }       

        // Flex head general case

        if (m_array.is_select(p) && m_unitary.is_flex(wi.pat_offset(), p)) {
            ptr_vector<app> pats;
            auto p1 = p;
            while (m_array.is_select(p1)) {
                pats.push_back(to_app(p1));
                p1 = to_app(p1)->get_arg(0);
            }
            auto v = to_var(p1);
            if (wi.is_init())
                wi.set_project();

            if (wi.is_project()) {
                // v -> \x\y . x_i
                unsigned start = wi.index();
                unsigned i = 0;
                for (auto pa : pats) {
                    for (auto pi : array_select_indices(pa)) {
                        if (start <= i && pi->get_sort() == t->get_sort()) {                            
                            auto eq = are_equal(wi.pat_offset(), pi, wi.term_offset(), t);
                            if (eq == l_false) {
                                ++i;
                                continue;
                            }
                            auto e = mk_project(pats.size(), i, v->get_sort());
                            add_binding(v, wi.pat_offset(), e);
                            if (eq == l_undef)
                                m_goals.push(wi.level, wi.pat_offset(), pi, t);
                            wi.set_index(i + 1);
                            return true;
                        }
                        ++i;
                    }
                }
            }

            SASSERT(!is_lambda(t));            

            if (!is_app(t))
                return false;

            auto ta = to_app(t);

            if (wi.is_project())
                wi.set_app();           

            if (wi.is_app()) {
                unsigned sz = ta->get_num_args();
                if (sz > 0) {
                    wi.inc_index();
                    m_trail.push(undo_resize(m_subst));
                }

                // H (p1) (p2) = f(t1, .., tn)
                // H -> \x1 \x2 f(H1(x1, x2), .., Hn(x1, x2))
                // H1(p1, p2) = t1, .., Hn(p1, p2) = tn
                ptr_vector<sort> domain, pat_domain;
                ptr_vector<expr> pat_args;
                expr_ref_vector args(m), pat_vars(m), bound_args(m);
                vector<symbol> names;
                pat_args.push_back(nullptr);
                pat_vars.push_back(nullptr);
                unsigned num_bound = 0;
                expr_mark seen;
                for (auto pat : pats) {
                    for (auto pi : array_select_indices(pat)) {
                        ++num_bound;
                        domain.push_back(pi->get_sort());
                        names.push_back(symbol(num_bound));
                        if (seen.is_marked(pi))
                            continue;
                        pat_domain.push_back(pi->get_sort());
                        pat_args.push_back(pi); 
                        seen.mark(pi);
                    }
                }

                for (unsigned i = pat_args.size(); i-- > 1; ) {
                    auto pi = pat_args.get(i);
                    pat_vars.push_back(m.mk_var(pat_args.size() - i - 1, pi->get_sort()));
                }                        

                for (auto ti : *ta) {
                    sort* v_sort = m_array.mk_array_sort(pat_domain.size(), pat_domain.data(), ti->get_sort());
                    auto v = m.mk_var(m_subst.size() + wi.pat_offset(), v_sort);
                    auto w = m.mk_var(m_subst.size() + wi.pat_offset() + num_bound, v_sort); // shifted by number of bound
                    m_subst.resize(m_subst.size() + 1);
                    pat_args[0] = v;
                    auto sel = m_array.mk_select(pat_args.size(), pat_args.data());
                    m_goals.push(wi.level, wi.term_offset(), sel, ti);
                    pat_vars[0] = w;
                    sel = m_array.mk_select(pat_vars.size(), pat_vars.data());
                    bound_args.push_back(sel);
                }

                expr_ref lam(m);
                lam = m.mk_app(ta->get_decl(), bound_args.size(), bound_args.data());

                for (unsigned i = pats.size(); i-- > 0; ) {
                    auto pa = pats[i];
                    auto sz = pa->get_num_args() - 1;
                    num_bound -= sz;
                    lam = m.mk_lambda(sz, domain.data() + num_bound, names.data() + num_bound, lam);
                }
                add_binding(v, wi.pat_offset(), lam);
                wi.set_done();
                return true;
            }
            return false;
        }

        wi.set_done();

        // first order match
        if (is_app(t) && is_app(p)) {
            auto ta = to_app(t);
            auto tp = to_app(p);
            if (ta->get_decl() != tp->get_decl())
                return false;
            if (ta->get_num_args() != tp->get_num_args())
                return false;
            for (unsigned i = 0; i < ta->get_num_args(); ++i)
                m_goals.push(wi.level, wi.term_offset(), tp->get_arg(i), ta->get_arg(i));
            return true;
        }               
                        
        //
        // lambda x . p == lambda x . t
        // 
        if (is_quantifier(p) && is_quantifier(t)) {
            auto qp = to_quantifier(p);
            auto qt = to_quantifier(t);
            unsigned pd = qp->get_num_decls();
            unsigned td = qt->get_num_decls();
            if (qp->get_kind() != qt->get_kind())
                return false;
            if (pd != td)
                return false;
            for (unsigned i = 0; i < pd; ++i)
                if (qp->get_decl_sort(i) != qt->get_decl_sort(i))
                    return false;
            m_goals.push(wi.level, wi.term_offset() + td, qp->get_expr(), qt->get_expr());
            return true;
        }

        return false;		       
    }

    // M p1 p2 ... pk
    // where M is a meta-variable and p1, .., pk are distinct bound variables
    // and t does not contain a bound variable not mentioned in p1,..,pk
    // or terms that don't occur in t.
    bool ho_matcher::is_pattern(expr* p, unsigned offset, expr* t) {
        uint_set vars;
        while (m_array.is_select(p)) {
            auto a = to_app(p);
            for (unsigned i = 1; i < a->get_num_args(); ++i) {
                auto arg = a->get_arg(i);
                if (!is_bound_var(arg, offset))
                    return false;
                auto idx = to_var(arg)->get_idx();
                if (vars.contains(idx))
                    return false;
                vars.insert(idx);
            }
            p = a->get_arg(0);
        }
        if (!is_meta_var(p, offset))
            return false;
        // check that every free variable in t is in vars.
        vector<ptr_vector<expr>> btodo;
        btodo.push_back(ptr_vector<expr>());
        btodo[0].push_back(t);
        for (unsigned i = 0; i < btodo.size(); ++i) {
            expr_fast_mark1 visited;
            for (unsigned j = 0; j < btodo[i].size(); ++j) {
                auto t = btodo[i][j];
                if (visited.is_marked(t))
                    continue;
                visited.mark(t);
                
                if (is_app(t)) {
                    auto a = to_app(t);
                    btodo[i].append(a->get_num_args(), a->get_args());
                }
                else if (is_var(t)) {
                    auto idx = to_var(t)->get_idx();
                    if (idx >= i && !vars.contains(idx - i))
                        return false;
                }
                else {
                    quantifier* q = to_quantifier(t);
                    btodo.reserve(i + q->get_num_decls() + 1);
                    btodo[i + q->get_num_decls()].push_back(q->get_expr());
                }
            }
        }

        return true;
    }

    // create a lambda abstraction for the meta variable such that
    // when applied to patterns, the result is t.
    // pre-condition: is_pattern(p, offset, t);
    // H (v1, v2) (v3, v4, v5)
    // lambda x1 x2 . lambda x3 x4 x5. t[v5 -> 0, v4 -> 1, v3 -> 2, v2 -> 3, v1 -> 4] 
    expr_ref ho_matcher::abstract_pattern(expr* p, unsigned offset, expr* t) {
        unsigned num_bound = 0;
        expr* p1 = p;
        ptr_vector<app> pats;
        while (m_array.is_select(p1)) {
            pats.push_back(to_app(p1));
            num_bound += to_app(p1)->get_num_args() - 1;
            p1 = to_app(p1)->get_arg(0);            
        }
        expr_ref_vector pat2bound(m);        
        for (auto a : pats) {
            unsigned sz = a->get_num_args();
            for (unsigned i = 1; i < sz; ++i) {
                auto arg = a->get_arg(i);
                SASSERT(is_bound_var(arg, offset));
                auto idx = to_var(arg)->get_idx();
                pat2bound.reserve(idx + 1);
                pat2bound[idx] = m.mk_var(--num_bound, arg->get_sort());
            }   
            p1 = a->get_arg(0);
        }
        var_subst sub(m, false);
        expr_ref lam = sub(t, pat2bound);
        for (unsigned i = pats.size(), j = 0; i-- > 0; ) {
            vector<symbol> names;
            ptr_vector<sort> sorts;
            for (unsigned k = 1; k < pats[i]->get_num_args(); ++k) {
                names.push_back(symbol(j++));
                sorts.push_back(pats[i]->get_arg(k)->get_sort());
            }
            lam = m.mk_lambda(names.size(), sorts.data(), names.data(), lam);
        }
        return lam;
    }

    //
    // keep track of number of internal scopes and offset to non-capture variables.
    // a variable is captured if it's index is in the interval [scopes, offset[.
    //
    bool ho_matcher::is_closed(expr* v, unsigned scopes, unsigned offset) const {
        if (is_ground(v))
            return true;
        if (is_app(v)) 
            return all_of(*to_app(v), [&](expr* arg) { return is_closed(arg, scopes, offset); });
        if (is_var(v)) 
            return to_var(v)->get_idx() < scopes || to_var(v)->get_idx() >= offset;
        if (is_quantifier(v)) {
            auto q = to_quantifier(v);
            return is_closed(q->get_expr(), scopes + q->get_num_decls(), offset + q->get_num_decls());
        }
        return false;
    }

    // (T1, T2,.., Tn) -> (Tn+1,.., Ti,.., Tm) -> Ti => lambda x1...xn . lambda x_n+1,..x_m . x_i
    expr_ref ho_matcher::mk_project(unsigned num_lambdas, unsigned i, sort* s) {
        SASSERT(num_lambdas > 0);
        SASSERT(m_array.is_array(s));
        unsigned num_binders = 0;
        expr_ref body(m);
        sort* a = s, * var_sort = nullptr;
        unsigned j = i;
        for (unsigned k = 0; k < num_lambdas; ++k) {
            auto arity = get_array_arity(a);
            if (j >= arity)
                j -= arity;
            else if (j < arity && !var_sort)
                var_sort = get_array_domain(a, j);
            num_binders += arity;
            a = get_array_range(a);
        }
        SASSERT(var_sort);
        body = m.mk_var(num_binders - i - 1, var_sort);
        bind_lambdas(num_lambdas, s, body);
        return body;
    }

    void ho_matcher::bind_lambdas(unsigned j, sort* s, expr_ref& body) {
        if (j > 1) 
            bind_lambdas(j - 1, get_array_range(s), body);        
        unsigned sz = get_array_arity(s);
        ptr_vector<sort> decl_sorts;
        vector<symbol> decl_names;
        for (unsigned i = 0; i < sz; ++i) {
            decl_sorts.push_back(get_array_domain(s, i));
            decl_names.push_back(symbol(i));
        }
        body = m.mk_lambda(sz, decl_sorts.data(), decl_names.data(), body);
    }

    void ho_matcher::add_binding(var* v, unsigned offset, expr* t) {
        SASSERT(v->get_idx() >= offset);
        m_subst.set(v->get_idx() - offset, t);
        IF_VERBOSE(1, verbose_stream() << "ho_matcher::add_binding: v" << v->get_idx() - offset << " -> " << mk_pp(t, m) << "\n";);
        m_trail.push(undo_set(m_subst, v->get_idx() - offset));
    }

    std::ostream& ho_matcher::display(std::ostream& out) const {
        m_subst.display(out << "subst\n");
        m_goals.display(out << "goals\n");
        out << "stack\n";
        for (auto const* mi : m_backtrack)
            mi->display(out);       
        return out;
    }

    struct retire_match_goal : public trail {
        match_goal& mg;        
        retire_match_goal(match_goal& mg) : mg(mg) {}
        void undo() override {
            mg.reset();
        }
    };

    void match_goals::push(unsigned level, unsigned offset, expr_ref const& pat, expr_ref const& t) {
        match_goal* wi = new (ho.trail().get_region()) match_goal(level, offset, pat, t);
        ho.trail().push(retire_match_goal(*wi)); // reset on undo
        wi->init(wi);
        if (ho.is_cheap(*wi)) {
            match_goal::push_to_front(m_cheap, wi);
            ho.trail().push(remove_dll(m_cheap, wi));    // remove from cheap
        }
        else {
            ho.reduce(*wi);
            if (ho.is_cheap(*wi)) {
                match_goal::push_to_front(m_cheap, wi);
                ho.trail().push(remove_dll(m_cheap, wi));
            }
            else {
                match_goal::push_to_front(m_expensive, wi);
                ho.trail().push(remove_dll(m_expensive, wi)); // remove from expensive
            }
        }
    }

    match_goal* match_goals::pop() {
        SASSERT(!empty());
        if (m_cheap)
            return pop(m_cheap);
        auto* wi = m_expensive;
        do {
            expr_ref pat(wi->pat), t(wi->t);
            ho.reduce(*wi);
            if (pat == wi->pat && t == wi->t)
                continue;
            if (pat != wi->pat)
                ho.trail().push(update_value(wi->pat, pat));
            if (t != wi->t)
                ho.trail().push(update_value(wi->t, t));
            if (ho.is_cheap(*wi)) {
                dll_base<match_goal>::remove_from(m_expensive, wi);
                match_goal::push_to_front(m_cheap, wi);

                ho.trail().push(insert_dll(m_expensive, wi)); // remove from expensive
                ho.trail().push(remove_dll(m_cheap, wi));
                return pop(m_cheap);
            }
            wi = wi->next();
        } 
        while (wi != m_expensive);
                
        return pop(m_expensive);
    }    

    match_goal* match_goals::pop(match_goal* &ws) {
        SASSERT(ws);
        auto* wi = ws->pop(ws);
        ho.trail().push(insert_dll(ws, wi)); // insert wi into ws   
        wi->set_init();
        return wi;
    }

    std::ostream& match_goals::display(std::ostream& out) const {
        for (auto const& wi : dll_elements(m_cheap))
            wi.display(out << "c ");
        
        for (auto const& wi : dll_elements(m_expensive))
            wi.display(out << "e ");
        
        return out;
    }

    class test_ho_matcher {
        struct plugins {
            plugins(ast_manager& m) {
                reg_decl_plugins(m);
            }
        };
        ast_manager   m;
        plugins       m_plugins;
        trail_stack   m_trail;
        ho_matcher    m_matcher;
        arith_util    m_arith;
        array_util    m_array;
        sort_ref      m_int;
        func_decl_ref m_f;

    public:
        test_ho_matcher() : m_plugins(m), m_matcher(m, m_trail), m_arith(m), m_array(m), m_int(m), m_f(m) {
            m_int = m_arith.mk_int();
            m_f = m.mk_func_decl(symbol("f"), m_int, m_int, m_int);

            std::function<void(ho_subst& s)> on_match = [&](ho_subst& s) {
                s.display(verbose_stream() << "match\n");
            };

            m_matcher.set_on_match(on_match);
        }

        // f(v0, v1) = f(1, 0)
        void test1() {
            expr_ref v0(m.mk_var(0, m_int), m);
            expr_ref v1(m.mk_var(1, m_int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref_vector args(m);
            args.push_back(v0);
            args.push_back(v1);
            expr_ref pat(m.mk_app(m_f, args), m);
            args.reset();
            args.push_back(one);
            args.push_back(zero);
            expr_ref t(m.mk_app(m_f, args), m);
            m_matcher.add_pattern(pat.get());
            IF_VERBOSE(0, verbose_stream() << "test2 " << pat << " ~ " << t << "\n");
            m_matcher(pat, t, 2);
        }

        // f(v0, v0) = f(1, 0)
        // should fail
        void test2() {
            expr_ref v0(m.mk_var(0, m_int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref_vector args(m);
            args.push_back(v0);
            args.push_back(v0);
            expr_ref pat(m.mk_app(m_f, args), m);
            args.reset();
            args.push_back(one);
            args.push_back(zero);
            expr_ref t(m.mk_app(m_f, args), m);
            m_matcher.add_pattern(pat.get());
            IF_VERBOSE(0, verbose_stream() << "test2 " << pat << " ~ " << t << "\n");
            m_matcher(pat, t, 1);
        }

        // v0(1) = 0
        void test3() {
            sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
            expr_ref v0(m.mk_var(0, int2int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref p(m_array.mk_select(v0, one), m);
            m_matcher.add_pattern(p.get());
            IF_VERBOSE(0, verbose_stream() << "test3 " << p << " ~ " << zero << "\n");
            m_matcher(p, zero, 1);
        }

        // v0(1) = 1
        void test4() {
            sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
            expr_ref v0(m.mk_var(0, int2int), m);
            expr_ref one(m_arith.mk_int(1), m);
            expr_ref p(m_array.mk_select(v0, one), m);
            m_matcher.add_pattern(p.get());
            IF_VERBOSE(0, verbose_stream() << "test4 " << p << " ~ " << one << "\n");
            m_matcher(p, one, 1);
        }

        // f(l') + sum l u f 
        void test5() {
            sort_ref int2int(m_array.mk_array_sort(m_int, m_int), m);
            expr_ref F(m.mk_var(0, int2int), m);
            expr_ref L1(m.mk_var(1, m_int), m);
            expr_ref L(m.mk_var(2, m_int), m);
            expr_ref U(m.mk_var(3, m_int), m);
            expr_ref zero(m_arith.mk_int(0), m);
            expr_ref one(m_arith.mk_int(1), m);
            sort* domain[3] = { m_int.get(), m_int.get(), int2int.get() };
            func_decl_ref sum(m.mk_func_decl(symbol("sum"), 3, domain, m_int), m);
            func_decl_ref f(m.mk_func_decl(symbol("f"), m_int, m_int), m);
            expr* args[3] = { L, U, F };
            expr_ref pat(m); 
            expr_ref u(m.mk_const(symbol("u"), m_int), m);
            symbol x("x");
            sort* int_s = m_int.get();
            expr_ref s(m.mk_app(sum.get(), one.get(), u.get(), m.mk_lambda(1, &int_s, &x, m.mk_app(f, m.mk_var(0, m_int)))), m);
            s = m_arith.mk_add(s, m.mk_app(f.get(), zero));


            pat = m_arith.mk_add(m.mk_app(sum, 3, args), m_array.mk_select(F, L1));
            IF_VERBOSE(0, verbose_stream() << "test5a: " << pat << " =?= " << s << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, s, 4);

            pat = m_arith.mk_add(m_array.mk_select(F, L1), m.mk_app(sum, 3, args));
            IF_VERBOSE(0, verbose_stream() << "test5b: " << pat << " =?= " << s << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, s, 4);
        }

        // test patterns
        // H (2, 0) = f(2)
        // G (1) (2, 0) = f(1, 2)
        // G (1) (2, 1) = f(1, 2) // not unitary
        // H (0, 1) = f(2) // fail
        void test6() {
            sort_ref intint2int(m_array.mk_array_sort(m_int, m_int, m_int), m);
            func_decl_ref f1(m.mk_func_decl(symbol("f"), m_int, m_int), m);
            func_decl_ref f2(m.mk_func_decl(symbol("f"), m_int, m_int, m_int), m);
            expr_ref v0(m.mk_var(0, m_int), m);
            expr_ref v1(m.mk_var(1, m_int), m);
            expr_ref v2(m.mk_var(2, m_int), m);
            expr_ref H(m.mk_var(3, intint2int), m);
            expr* args[3] = { H.get(), v2, v0 };
            expr_ref pat(m_array.mk_select(3, args), m);
            expr_ref t(m.mk_app(f1.get(), v2), m);
            IF_VERBOSE(0, verbose_stream() << "test6a: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            expr* args2[3] = { H.get(), v1, v0 };
            pat = m_array.mk_select(3, args2);
            t = m.mk_app(f2.get(), v0, v1);
            IF_VERBOSE(0, verbose_stream() << "test6b: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            sort_ref int2intt(m_array.mk_array_sort(m_int, intint2int), m);
            expr_ref(m.mk_var(3, int2intt), m);
            expr_ref G(m.mk_var(3, int2intt), m);
            pat = m_array.mk_select(G.get(), v1);
            pat = m_array.mk_select(pat.get(), v2, v0);
            t = m.mk_app(f2.get(), v1, v2);
            IF_VERBOSE(0, verbose_stream() << "test6c: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            pat = m_array.mk_select(G, v1);
            pat = m_array.mk_select(pat, v2, v1);
            IF_VERBOSE(0, verbose_stream() << "test6d: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);

            pat = m_array.mk_select(H, v0, v2);
            IF_VERBOSE(0, verbose_stream() << "test6e: " << pat << " =?= " << t << "\n";);
            m_matcher.add_pattern(pat.get());
            m_matcher(pat, t, 3, 1);
        }
    };

}

void tst_ho_matcher() {
    euf::test_ho_matcher tm;
    try {    
        tm.test1();
        tm.test2();
        tm.test3();
        tm.test4();
        tm.test5();
        tm.test6();
    }
    catch (std::exception const& ex) {
        std::cout << ex.what() << "\n";
    }
}