/**++
Copyright (c) Arie Gurfinkel

Module Name:

    qe_term_graph.cpp

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel

Notes:

--*/

#include "util/util.h"
#include "util/uint_set.h"
#include "util/obj_pair_hashtable.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/occurs.h"
#include "model/model_evaluator.h"
#include "qe/mbp/mbp_term_graph.h"

namespace mbp {

    static expr_ref mk_neq(ast_manager &m, expr *e1, expr *e2) {
        expr *t = nullptr;
        // x != !x  == true
        if ((m.is_not(e1, t) && t == e2) || (m.is_not(e2, t) && t == e1))
            return expr_ref(m.mk_true(), m);
        else if (m.are_distinct(e1, e2))
            return expr_ref(m.mk_true(), m);
        return expr_ref(m.mk_not(m.mk_eq(e1, e2)), m);
    }

    namespace {
        struct sort_lt_proc {
            bool operator()(const expr* a, const expr *b) const {
                return a->get_sort()->get_id() < b->get_sort()->get_id();
            }
        };
    }

    namespace is_pure_ns {
        struct found{};
        struct proc {
            is_variable_proc &m_is_var;
            proc(is_variable_proc &is_var) : m_is_var(is_var) {}
            void operator()(var *n) const {if (m_is_var(n)) throw found();}
            void operator()(app const *n) const {if (m_is_var(n)) throw found();}
            void operator()(quantifier *n) const {}
        };
    }

    bool is_pure(is_variable_proc &is_var, expr *e) {
        try {
            is_pure_ns::proc v(is_var);
            quick_for_each_expr(v, e);
        }
        catch (const is_pure_ns::found &) {
            return false;
        }
        return true;
    }

    class term {
        // -- an app represented by this term
        expr_ref m_expr; // NSB: to make usable with exprs
        // -- root of the equivalence class
        term* m_root;
        // -- next element in the equivalence class (cyclic linked list)
        term* m_next;
        // -- eq class size
        unsigned m_class_size;
        // -- general purpose mark
        unsigned m_mark:1;
        // -- general purpose second mark
        unsigned m_mark2:1;
        // -- is an interpreted constant
        unsigned m_interpreted:1;

        // -- terms that contain this term as a child
        ptr_vector<term> m_parents;

        // arguments of term.
        ptr_vector<term> m_children;

    public:
        term(expr_ref const& v, u_map<term*>& app2term) :
            m_expr(v),
            m_root(this),
            m_next(this),
            m_class_size(1),
            m_mark(false),
            m_mark2(false),
            m_interpreted(false) {
            if (!is_app(m_expr)) return;
            for (expr* e : *to_app(m_expr)) {
                term* t = app2term[e->get_id()];
                t->get_root().m_parents.push_back(this);
                m_children.push_back(t);
            }
        }

        ~term() {}

        class parents {
            term const& t;
        public:
            parents(term const& _t):t(_t) {}
            parents(term const* _t):t(*_t) {}
            ptr_vector<term>::const_iterator begin() const { return t.m_parents.begin(); }
            ptr_vector<term>::const_iterator end() const { return t.m_parents.end(); }
        };

        class children {
            term const& t;
        public:
            children(term const& _t):t(_t) {}
            children(term const* _t):t(*_t) {}
            ptr_vector<term>::const_iterator begin() const { return t.m_children.begin(); }
            ptr_vector<term>::const_iterator end() const { return t.m_children.end(); }
        };        

        // Congruence table hash function is based on
        // roots of children and function declaration.

        unsigned get_hash() const {
            unsigned a, b, c;
            a = b = c = get_decl_id();
            for (term * ch : children(this)) {
                a = ch->get_root().get_id();
                mix(a, b, c);
            }
            return c;
        }

        static bool cg_eq(term const * t1, term const * t2) {
            if (t1->get_decl_id() != t2->get_decl_id()) return false;
            if (t1->m_children.size() != t2->m_children.size()) return false;
            for (unsigned i = 0, sz = t1->m_children.size(); i < sz; ++ i) {
                if (t1->m_children[i]->get_root().get_id() != t2->m_children[i]->get_root().get_id()) return false;
            }
            return true;
        }

        unsigned get_id() const { return m_expr->get_id();}

        unsigned get_decl_id() const { return is_app(m_expr) ? to_app(m_expr)->get_decl()->get_id() : m_expr->get_id(); }

        bool is_marked() const {return m_mark;}
        void set_mark(bool v){m_mark = v;}
        bool is_marked2() const {return m_mark2;} // NSB: where is this used?
        void set_mark2(bool v){m_mark2 = v;}      // NSB: where is this used?

        bool is_interpreted() const {return m_interpreted;}
        bool is_theory() const { return !is_app(m_expr) || to_app(m_expr)->get_family_id() != null_family_id; }
        void mark_as_interpreted() {m_interpreted=true;}
        expr* get_expr() const {return m_expr;}
        unsigned get_num_args() const { return is_app(m_expr) ? to_app(m_expr)->get_num_args() : 0; }

        term &get_root() const {return *m_root;}
        bool is_root() const {return m_root == this;}
        void set_root(term &r) {m_root = &r;}
        term &get_next() const {return *m_next;}
        void add_parent(term* p) { m_parents.push_back(p); }

        unsigned get_class_size() const {return m_class_size;}

        void merge_eq_class(term &b) {
            std::swap(this->m_next, b.m_next);
            m_class_size += b.get_class_size();
            // -- reset (useful for debugging)
            b.m_class_size = 0;
        }

        // -- make this term the root of its equivalence class
        void mk_root() {
            if (is_root()) return;

            term *curr = this;
            do {
                if (curr->is_root()) {
                    // found previous root
                    SASSERT(curr != this);
                    m_class_size = curr->get_class_size();
                    curr->m_class_size = 0;
                }
                curr->set_root(*this);
                curr = &curr->get_next();
            }
            while (curr != this);
        }

        std::ostream& display(std::ostream& out) const {
            out << get_id() << ": " << m_expr 
                << (is_root() ? " R" : "") << " - ";
            term const* r = &this->get_next();
            while (r != this) {
                out << r->get_id() << " ";
                r = &r->get_next();
            }
            out << "\n";
            return out;
        }
    };

    static std::ostream& operator<<(std::ostream& out, term const& t) {
        return t.display(out);
    }

    bool term_graph::is_variable_proc::operator()(const expr * e) const {
        if (!is_app(e)) return false;
        const app *a = ::to_app(e);
        TRACE("qe_verbose", tout << a->get_family_id() << " " << m_solved.contains(a->get_decl()) << " " << m_decls.contains(a->get_decl()) << "\n";);
        return
            a->get_family_id() == null_family_id &&
            !m_solved.contains(a->get_decl()) &&
            m_exclude == m_decls.contains(a->get_decl());
    }

    bool term_graph::is_variable_proc::operator()(const term &t) const {
        return (*this)(t.get_expr());
    }

    void term_graph::is_variable_proc::set_decls(const func_decl_ref_vector &decls, bool exclude) {
        reset();
        m_exclude = exclude;
        for (auto *d : decls) m_decls.insert(d);
    }
    void term_graph::is_variable_proc::mark_solved(const expr *e) {
        if ((*this)(e) && is_app(e))
            m_solved.insert(::to_app(e)->get_decl());
    }


    unsigned term_graph::term_hash::operator()(term const* t) const { return t->get_hash(); }

    bool term_graph::term_eq::operator()(term const* a, term const* b) const { return term::cg_eq(a, b); }

    term_graph::term_graph(ast_manager &man) : m(man), m_lits(m), m_pinned(m), m_projector(nullptr) {
        m_plugins.register_plugin(mbp::mk_basic_solve_plugin(m, m_is_var));
        m_plugins.register_plugin(mbp::mk_arith_solve_plugin(m, m_is_var));
    }

    term_graph::~term_graph() {
        dealloc(m_projector);
        reset();
    }

    bool term_graph::is_pure_def(expr *atom, expr*& v) {
        expr *e = nullptr;
        return m.is_eq(atom, v, e) && m_is_var(v) && is_pure(m_is_var, e);
    }

    static family_id get_family_id(ast_manager &m, expr *lit) {
        if (m.is_not(lit, lit))
            return get_family_id(m, lit);

        expr *a = nullptr, *b = nullptr;
        // deal with equality using sort of range
        if (m.is_eq (lit, a, b)) {
            return a->get_sort()->get_family_id();
        }
        // extract family_id of top level app
        else if (is_app(lit)) {
            return to_app(lit)->get_decl()->get_family_id();
        }
        else {
            return null_family_id;
        }
    }
    void term_graph::add_lit(expr *l) {
        expr_ref lit(m);
        expr_ref_vector lits(m);
        lits.push_back(l);
        for (unsigned i = 0; i < lits.size(); ++i) {
            l = lits.get(i);
            family_id fid = get_family_id(m, l);
            mbp::solve_plugin *pin = m_plugins.get_plugin(fid);
            lit = pin ? (*pin)(l) : l;
            if (m.is_and(lit)) {
                lits.append(::to_app(lit)->get_num_args(), ::to_app(lit)->get_args());
            }
            else {
                m_lits.push_back(lit);
                internalize_lit(lit);
            }
        }
    }

    bool term_graph::is_internalized(expr *a) {
        return m_app2term.contains(a->get_id());
    }

    term* term_graph::get_term(expr *a) {
        term *res;
        return m_app2term.find (a->get_id(), res) ? res : nullptr;
    }

    term *term_graph::mk_term(expr *a) {
        expr_ref e(a, m);
        term * t = alloc(term, e, m_app2term);
        if (t->get_num_args() == 0 && m.is_unique_value(a)){
            t->mark_as_interpreted();
        }

        m_terms.push_back(t);
        m_app2term.insert(a->get_id(), t);
        return t;
    }

    term* term_graph::internalize_term(expr *t) {
        term* res = get_term(t);
        if (res) return res;
        ptr_buffer<expr> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            t = todo.back();
            res = get_term(t);
            if (res) {
                todo.pop_back();
                continue;
            }
            unsigned sz = todo.size();
            if (is_app(t)) {
                for (expr * arg : *::to_app(t)) {
                    if (!get_term(arg))
                        todo.push_back(arg);
                }
            }
            if (sz < todo.size()) continue;
            todo.pop_back();
            res = mk_term(t);
        }
        SASSERT(res);
        return res;
    }

    void term_graph::internalize_eq(expr *a1, expr* a2) {
        SASSERT(m_merge.empty());
        merge(*internalize_term(a1), *internalize_term(a2));
        merge_flush();
        SASSERT(m_merge.empty());
    }

    void term_graph::internalize_lit(expr* lit) {
        expr *e1 = nullptr, *e2 = nullptr, *v = nullptr;
        if (m.is_eq (lit, e1, e2)) {
            internalize_eq (e1, e2);
        }
        else {
            internalize_term(lit);
        }
        if (is_pure_def(lit, v)) {
            m_is_var.mark_solved(v);
        }
    }

    void term_graph::merge_flush() {
        while (!m_merge.empty()) {
            term* t1 = m_merge.back().first;
            term* t2 = m_merge.back().second;
            m_merge.pop_back();
            merge(*t1, *t2);
        }
    }

    void term_graph::merge(term &t1, term &t2) {
        term *a = &t1.get_root();
        term *b = &t2.get_root();

        if (a == b) return;

        // -- merge might invalidate term2app cache
        m_term2app.reset();
        m_pinned.reset();

        if (a->get_class_size() > b->get_class_size()) {
            std::swap(a, b);
        }

        // Remove parents of b from the cg table.
        for (term* p : term::parents(b)) {
            if (!p->is_marked()) {
                p->set_mark(true);
                m_cg_table.erase(p);
            }
        }
        // make 'a' be the root of the equivalence class of 'b'
        b->set_root(*a);
        for (term *it = &b->get_next(); it != b; it = &it->get_next()) {
            it->set_root(*a);
        }

        // merge equivalence classes
        a->merge_eq_class(*b);

        // Insert parents of b's old equilvalence class into the cg table
        for (term* p : term::parents(b)) {
            if (p->is_marked()) {
                term* p_old = m_cg_table.insert_if_not_there(p);
                p->set_mark(false);
                a->add_parent(p);
                // propagate new equalities.
                if (p->get_root().get_id() != p_old->get_root().get_id()) {
                    m_merge.push_back(std::make_pair(p, p_old));
                }
            }
        }
        SASSERT(marks_are_clear());
    }

    expr* term_graph::mk_app_core (expr *e) {
        if (is_app(e)) {
            expr_ref_buffer kids(m);
            app* a = ::to_app(e);
            for (expr * arg : *a) {
                kids.push_back (mk_app(arg));
            }
            app* res = m.mk_app(a->get_decl(), a->get_num_args(), kids.data());
            m_pinned.push_back(res);
            return res;
        }
        else {
            return e;
        }
    }

    expr_ref term_graph::mk_app(term const &r) {
        SASSERT(r.is_root());

        if (r.get_num_args() == 0) {
            return expr_ref(r.get_expr(), m);
        }

        expr* res = nullptr;
        if (m_term2app.find(r.get_id(), res)) {
            return expr_ref(res, m);
        }

        res = mk_app_core (r.get_expr());
        m_term2app.insert(r.get_id(), res);
        return expr_ref(res, m);

    }

    expr_ref term_graph::mk_app(expr *a) {
        term *t = get_term(a);
        if (!t)
            return expr_ref(a, m);
        else
            return mk_app(t->get_root());

    }

    void term_graph::mk_equalities(term const &t, expr_ref_vector &out) {
        SASSERT(t.is_root());
        expr_ref rep(mk_app(t), m);
        for (term *it = &t.get_next(); it != &t; it = &it->get_next()) {
            expr* mem = mk_app_core(it->get_expr());
            out.push_back (m.mk_eq (rep, mem));
        }
    }

    void term_graph::mk_all_equalities(term const &t, expr_ref_vector &out) {
        mk_equalities(t, out);

        for (term *it = &t.get_next(); it != &t; it = &it->get_next ()) {
            expr* a1 = mk_app_core (it->get_expr());
            for (term *it2 = &it->get_next(); it2 != &t; it2 = &it2->get_next()) {
                expr* a2 =  mk_app_core(it2->get_expr());
                out.push_back (m.mk_eq (a1, a2));
            }
        }
    }

    void term_graph::reset_marks() {
        for (term * t : m_terms) {
            t->set_mark(false);
        }
    }

    bool term_graph::marks_are_clear() {
        for (term * t : m_terms) {
            if (t->is_marked()) return false;
        }
        return true;
    }

    /// Order of preference for roots of equivalence classes
    /// XXX This should be factored out to let clients control the preference
    bool term_graph::term_lt(term const &t1, term const &t2) {
        // prefer constants over applications
        // prefer uninterpreted constants over values
        // prefer smaller expressions over larger ones
        if (t1.get_num_args() == 0 || t2.get_num_args() == 0) {
            if (t1.get_num_args() == t2.get_num_args()) {
                // t1.get_num_args() == t2.get_num_args() == 0
                if (m.is_value(t1.get_expr()) == m.is_value(t2.get_expr()))
                    return t1.get_id() < t2.get_id();
                return m.is_value(t2.get_expr());
            }
            return t1.get_num_args() < t2.get_num_args();
        }

        unsigned sz1 = get_num_exprs(t1.get_expr());
        unsigned sz2 = get_num_exprs(t2.get_expr());
        return sz1 < sz2;
    }

    void term_graph::pick_root (term &t) {
        term *r = &t;
        for (term *it = &t.get_next(); it != &t; it = &it->get_next()) {
            it->set_mark(true);
            if (term_lt(*it, *r)) { r = it; }
        }

        // -- if found something better, make it the new root
        if (r != &t) {
            r->mk_root();
        }
    }

    /// Choose better roots for equivalence classes
    void term_graph::pick_roots() {
        SASSERT(marks_are_clear());
        for (term* t : m_terms) {
            if (!t->is_marked() && t->is_root())
                pick_root(*t);
        }
        reset_marks();
    }

    void term_graph::display(std::ostream &out) {
        for (term * t : m_terms) {
            out << *t;
        }
    }

    void term_graph::to_lits (expr_ref_vector &lits, bool all_equalities) {
        pick_roots();

        for (expr * a : m_lits) {
            if (is_internalized(a)) {
                lits.push_back (::to_app(mk_app(a)));
            }
        }

        for (term * t : m_terms) {
            if (!t->is_root())
                continue;
            else if (all_equalities)
                mk_all_equalities (*t, lits);
            else
                mk_equalities(*t, lits);
        }
    }

    expr_ref term_graph::to_expr() {
        expr_ref_vector lits(m);
        to_lits(lits);
        return mk_and(lits);
    }

    void term_graph::reset() {
        m_term2app.reset();
        m_pinned.reset();
        m_app2term.reset();
        std::for_each(m_terms.begin(), m_terms.end(), delete_proc<term>());
        m_terms.reset();
        m_lits.reset();
        m_cg_table.reset();
    }

    class term_graph::projector {
        term_graph &m_tg;
        ast_manager &m;
        u_map<expr*> m_term2app;
        u_map<expr*> m_root2rep;

        model_ref m_model;
        expr_ref_vector m_pinned;  // tracks expr in the maps

        expr* mk_pure(term const& t) {
            TRACE("qe", t.display(tout););
            expr* e = nullptr;
            if (find_term2app(t, e)) return e;
            e = t.get_expr();
            if (!is_app(e)) return nullptr;
            app* a = ::to_app(e);
            expr_ref_buffer kids(m);
            for (term* ch : term::children(t)) {
                // prefer a node that resembles current child, 
                // otherwise, pick a root representative, if present.
                if (find_term2app(*ch, e)) {
                    kids.push_back(e);
                }
                else if (m_root2rep.find(ch->get_root().get_id(), e)) {
                    kids.push_back(e);
                }
                else {
                    return nullptr;
                }
                TRACE("qe_verbose", tout << *ch << " -> " << mk_pp(e, m) << "\n";);
            }
            expr* pure = m.mk_app(a->get_decl(), kids.size(), kids.data());
            m_pinned.push_back(pure);
            add_term2app(t, pure);
            return pure;
        }


        bool is_better_rep(expr *t1, expr *t2) {
            if (!t2) return t1 != nullptr;
            return m.is_unique_value(t1) && !m.is_unique_value(t2);
        }

        struct term_depth {
            bool operator()(term const* t1, term const* t2) const {
                return get_depth(t1->get_expr()) < get_depth(t2->get_expr());
            }
        };           


        void solve_core() {
            ptr_vector<term> worklist;
            for (term * t : m_tg.m_terms) {
                // skip pure terms
                if (!in_term2app(*t)) {
                    worklist.push_back(t);
                    t->set_mark(true);
                }
            }
            term_depth td;
            std::sort(worklist.begin(), worklist.end(), td);

            for (unsigned i = 0; i < worklist.size(); ++i) {
                term* t = worklist[i];
                t->set_mark(false);
                if (in_term2app(*t))
                    continue;

                expr* pure = mk_pure(*t);
                if (!pure) 
                    continue;

                add_term2app(*t, pure);
                expr* rep = nullptr;
                // ensure that the root has a representative
                m_root2rep.find(t->get_root().get_id(), rep);

                if (!rep) {
                    m_root2rep.insert(t->get_root().get_id(), pure);
                    for (term * p : term::parents(t->get_root())) {
                        SASSERT(!in_term2app(*p));
                        if (!p->is_marked()) {
                            p->set_mark(true);
                            worklist.push_back(p);
                        }
                    }
                }
            }
            m_tg.reset_marks();
        }

        bool find_app(term &t, expr *&res) {
            return 
                find_term2app(t, res) ||
                m_root2rep.find(t.get_root().get_id(), res);
        }

        bool find_app(expr *lit, expr *&res) {
            term const* t = m_tg.get_term(lit);
            return 
                find_term2app(*t, res) ||
                m_root2rep.find(t->get_root().get_id(), res);
        }

        void mk_lits(expr_ref_vector &res) {
            expr *e = nullptr;
            for (auto *lit : m_tg.m_lits) {
                if (!m.is_eq(lit) && find_app(lit, e))
                    res.push_back(e);
            }
            TRACE("qe", tout << "literals: " << res << "\n";);
        }

        void lits2pure(expr_ref_vector& res) {
            expr *e1 = nullptr, *e2 = nullptr, *p1 = nullptr, *p2 = nullptr;
            for (auto *lit : m_tg.m_lits) {
                if (m.is_eq(lit, e1, e2)) {
                    if (find_app(e1, p1) && find_app(e2, p2)) {
                        if (p1 != p2) 
                            res.push_back(m.mk_eq(p1, p2));
                    }
                    else {
                        TRACE("qe", tout << "skipping " << mk_pp(lit, m) << "\n";);
                    }
                }
                else if (m.is_distinct(lit)) {
                    ptr_buffer<expr> diff;
                    for (expr* arg : *to_app(lit)) {
                        if (find_app(arg, p1)) {
                            diff.push_back(p1);
                        }
                    }
                    if (diff.size() > 1) {
                        res.push_back(m.mk_distinct(diff.size(), diff.data()));
                    }
                    else {
                        TRACE("qe", tout << "skipping " << mk_pp(lit, m) << "\n";);
                    }
                }
                else if (find_app(lit, p1)) {
                    res.push_back(p1);
                }
                else {
                    TRACE("qe", tout << "skipping " << mk_pp(lit, m) << "\n";);
                }
            }
            remove_duplicates(res);
            TRACE("qe", tout << "literals: " << res << "\n";);            
        }

        void remove_duplicates(expr_ref_vector& v) {
            obj_hashtable<expr> seen;
            unsigned j = 0;
            for (expr* e : v) {
                if (!seen.contains(e)) {
                    v[j++] = e;
                    seen.insert(e);
                }
            }
            v.shrink(j);
        }

        vector<ptr_vector<term>> m_decl2terms; // terms that use function f
        ptr_vector<func_decl>    m_decls;
        
        void collect_decl2terms() {
            // Collect the projected function symbols.
            m_decl2terms.reset();
            m_decls.reset();
            for (term *t : m_tg.m_terms) {
                expr* e = t->get_expr();
                if (!is_app(e)) continue;
                if (!is_projected(*t)) continue;
                app* a = to_app(e);
                func_decl* d = a->get_decl();
                if (d->get_arity() == 0) continue;
                unsigned id = d->get_decl_id();
                m_decl2terms.reserve(id+1);
                if (m_decl2terms[id].empty()) m_decls.push_back(d);
                m_decl2terms[id].push_back(t);
            }
        }

        void args_are_distinct(expr_ref_vector& res) {
            //
            // for each projected function that occurs 
            // (may occur) in multiple congruence classes, 
            // produce assertions that non-congruent arguments 
            // are distinct.
            //
            for (func_decl* d : m_decls) {
                unsigned id = d->get_decl_id();
                ptr_vector<term> const& terms = m_decl2terms[id];
                if (terms.size() <= 1) continue;
                unsigned arity = d->get_arity();
                for (unsigned i = 0; i < arity; ++i) {
                    obj_hashtable<expr> roots, root_vals;
                    expr_ref_vector pinned(m);
                    for (term* t : terms) {
                        expr* arg = to_app(t->get_expr())->get_arg(i);
                        term const& root = m_tg.get_term(arg)->get_root();
                        expr* r = root.get_expr();
                        // if a model is given, then use the equivalence class induced 
                        // by the model. Otherwise, use the congruence class.
                        if (m_model) {
                            expr_ref tmp(m);
                            tmp = (*m_model)(r);
                            if (!root_vals.contains(tmp)) {
                                root_vals.insert(tmp);
                                roots.insert(r);
                                pinned.push_back(tmp);
                            }
                        }
                        else {
                            roots.insert(r);
                        }
                    }
                    if (roots.size() > 1) {
                        ptr_buffer<expr> args;
                        for (expr* r : roots) {
                            args.push_back(r);
                        }
                        TRACE("qe", tout << "function: " << d->get_name() << "\n";);
                        res.push_back(m.mk_distinct(args.size(), args.data()));
                    }
                }
            }
        }

        void mk_distinct(expr_ref_vector& res) {
            collect_decl2terms();
            args_are_distinct(res);
            TRACE("qe", tout << res << "\n";);
        }

        void mk_pure_equalities(const term &t, expr_ref_vector &res) {
            SASSERT(t.is_root());
            expr *rep = nullptr;
            if (!m_root2rep.find(t.get_id(), rep)) return;
            obj_hashtable<expr> members;
            members.insert(rep);
            term const * r = &t;
            do {
                expr* member = nullptr;
                if (find_term2app(*r, member) && !members.contains(member)) {
                    res.push_back (m.mk_eq (rep, member));
                    members.insert(member);
                }
                r = &r->get_next();
            }
            while (r != &t);
        }

        bool is_projected(const term &t) {
            return m_tg.m_is_var(t);
        }

        void mk_unpure_equalities(const term &t, expr_ref_vector &res) {
            expr *rep = nullptr;
            if (!m_root2rep.find(t.get_id(), rep)) return;
            obj_hashtable<expr> members;
            members.insert(rep);
            term const * r = &t;
            do {
                expr* member = mk_pure(*r);
                SASSERT(member);
                if (!members.contains(member) &&
                    (!is_projected(*r) || !is_solved_eq(rep, member))) {
                    res.push_back(m.mk_eq(rep, member));
                    members.insert(member);
                }
                r = &r->get_next();
            }
            while (r != &t);
        }

        template<bool pure>
        void mk_equalities(expr_ref_vector &res) {
            for (term *t : m_tg.m_terms) {
                if (!t->is_root()) continue;
                if (!m_root2rep.contains(t->get_id())) continue;
                if (pure)
                    mk_pure_equalities(*t, res);
                else
                    mk_unpure_equalities(*t, res);
            }
            TRACE("qe", tout << "literals: " << res << "\n";);
        }

        void mk_pure_equalities(expr_ref_vector &res) {
            mk_equalities<true>(res);
        }

        void mk_unpure_equalities(expr_ref_vector &res) {
            mk_equalities<false>(res);
        }

        // TBD: generalize for also the case of a (:var n)
        bool is_solved_eq(expr *lhs, expr* rhs) {
            return is_uninterp_const(rhs) && !occurs(rhs, lhs);
        }

        /// Add equalities and disequalities for all pure representatives
        /// based on their equivalence in the model
        void model_complete(expr_ref_vector &res) {
            if (!m_model) return;
            obj_map<expr,expr*> val2rep;
            model_evaluator mev(*m_model);
            for (auto &kv : m_root2rep) {
                expr *rep = kv.m_value;
                expr_ref val(m);
                expr *u = nullptr;
                if (!mev.eval(rep, val)) continue;
                if (val2rep.find(val, u)) {
                    res.push_back(m.mk_eq(u, rep));
                }
                else {
                    val2rep.insert(val, rep);
                }
            }

            // TBD: optimize further based on implied values (e.g.,
            // some literals are forced to be true/false) and based on
            // unique_values (e.g., (x=1 & y=1) does not require
            // (x!=y) to be added
            ptr_buffer<expr> reps;
            for (auto &kv : val2rep) {
                expr *rep = kv.m_value;
                if (!m.is_unique_value(rep))
                reps.push_back(kv.m_value);
            }

            if (reps.size() <= 1) return;

            // -- sort representatives, call mk_distinct on any range
            // -- of the same sort longer than 1
            std::sort(reps.data(), reps.data() + reps.size(), sort_lt_proc());
            unsigned i = 0;
            unsigned sz = reps.size();
            while (i < sz) {
                sort* last_sort = res.get(i)->get_sort();
                unsigned j = i + 1;
                while (j < sz && last_sort == reps.get(j)->get_sort()) {++j;}
                if (j - i == 2) {
                    expr_ref d(m);
                    d = mk_neq(m, reps.get(i), reps.get(i+1));
                    if (!m.is_true(d)) res.push_back(d);
                }
                else if (j - i > 2)
                    res.push_back(m.mk_distinct(j - i, reps.data() + i));
                i = j;
            }
            TRACE("qe", tout << "after distinct: " << res << "\n";);
        }

        std::ostream& display(std::ostream& out) const {
            m_tg.display(out);
            out << "term2app:\n";
            for (auto const& kv : m_term2app) {
                out << kv.m_key << " |-> " << mk_pp(kv.m_value, m) << "\n";
            }
            out << "root2rep:\n";
            for (auto const& kv : m_root2rep) {
                out << kv.m_key << " |-> " << mk_pp(kv.m_value, m) << "\n";
            }
            return out;
        }

    public:
        projector(term_graph &tg) : m_tg(tg), m(m_tg.m), m_pinned(m) {}

        void add_term2app(term const& t, expr* a) {
            m_term2app.insert(t.get_id(), a);
        }

        void del_term2app(term const& t) {
            m_term2app.remove(t.get_id());
        }

        bool find_term2app(term const& t, expr*& r) {
            return m_term2app.find(t.get_id(), r);
        }

        expr* find_term2app(term const& t) {
            expr* r = nullptr;
            find_term2app(t, r);
            return r;
        }

        bool in_term2app(term const& t) {
            return m_term2app.contains(t.get_id());
        }

        void set_model(model &mdl) { m_model = &mdl; }

        void reset() {
            m_tg.reset_marks();
            m_term2app.reset();
            m_root2rep.reset();
            m_pinned.reset();
            m_model.reset();
        }

        expr_ref_vector project() {
            expr_ref_vector res(m);
            purify();
            lits2pure(res);
            mk_distinct(res);
            reset();
            return res;
        }

        expr_ref_vector get_ackerman_disequalities() {
            expr_ref_vector res(m);
            purify();
            lits2pure(res);
            unsigned sz = res.size();
            mk_distinct(res);
            reset();
            unsigned j = 0;
            for (unsigned i = sz; i < res.size(); ++i) {
                res[j++] = res.get(i);
            }
            res.shrink(j);
            return res;
        }

        expr_ref_vector solve() {
            expr_ref_vector res(m);
            purify();
            solve_core();
            mk_lits(res);
            mk_unpure_equalities(res);
            reset();
            return res;
        }

        vector<expr_ref_vector> get_partition(model& mdl, bool include_bool) {
            vector<expr_ref_vector> result;
            expr_ref_vector pinned(m);
            obj_map<expr, unsigned> pid;
            model::scoped_model_completion _smc(mdl, true);
            for (term *t : m_tg.m_terms) {
                expr* a = t->get_expr();
                if (!is_app(a)) continue;
                if (m.is_bool(a) && !include_bool) continue;
                expr_ref val = mdl(a);
                unsigned p = 0;
                // NB. works for simple domains Integers, Rationals, 
                // but not for algebraic numerals.
                if (!pid.find(val, p)) {
                    p = pid.size();
                    pid.insert(val, p);
                    pinned.push_back(val);
                    result.push_back(expr_ref_vector(m));
                }
                result[p].push_back(a);
            }            
            return result;
        }

        expr_ref_vector shared_occurrences(family_id fid) {
            expr_ref_vector result(m);
            for (term *t : m_tg.m_terms) {
                expr* e = t->get_expr();
                if (e->get_sort()->get_family_id() != fid) continue;
                for (term * p : term::parents(t->get_root())) {
                    expr* pe = p->get_expr();
                    if (!is_app(pe)) continue;
                    if (to_app(pe)->get_family_id() == fid) continue;
                    if (to_app(pe)->get_family_id() == m.get_basic_family_id()) continue;
                    result.push_back(e);
                    break;
                }                
            }
            return result;
        }

        void purify() {
            // - propagate representatives up over parents.
            //   use work-list + marking to propagate.
            // - produce equalities over represented classes.
            // - produce other literals over represented classes
            //   (walk disequalities in m_lits and represent
            //   lhs/rhs over decls or excluding decls)

            ptr_vector<term> worklist;
            for (term * t : m_tg.m_terms) {
                worklist.push_back(t);
                t->set_mark(true);
            }
            // traverse worklist in order of depth.
            term_depth td;
            std::sort(worklist.begin(), worklist.end(), td);

            for (unsigned i = 0; i < worklist.size(); ++i) {
                term* t = worklist[i];
                t->set_mark(false);
                if (in_term2app(*t)) 
                    continue;
                if (!t->is_theory() && is_projected(*t))
                    continue;

                expr* pure = mk_pure(*t);
                if (!pure) continue;

                add_term2app(*t, pure);
                TRACE("qe_verbose", tout << "purified " << *t << " " << mk_pp(pure, m) << "\n";);
                expr* rep = nullptr;                // ensure that the root has a representative
                m_root2rep.find(t->get_root().get_id(), rep);

                // update rep with pure if it is better
                if (pure != rep && is_better_rep(pure, rep)) {
                    m_root2rep.insert(t->get_root().get_id(), pure);
                    for (term * p : term::parents(t->get_root())) {
                        del_term2app(*p);
                        if (!p->is_marked()) {
                            p->set_mark(true);
                            worklist.push_back(p);
                        }
                    }
                }
            }

            // Here we could also walk equivalence classes that
            // contain interpreted values by sort and extract
            // disequalities between non-unique value
            // representatives.  these disequalities are implied
            // and can be mined using other means, such as theory
            // aware core minimization
            m_tg.reset_marks();
            TRACE("qe", display(tout << "after purify\n"););
        }

    };

    void term_graph::set_vars(func_decl_ref_vector const& decls, bool exclude) {
        m_is_var.set_decls(decls, exclude);
    }

    expr_ref_vector term_graph::project() {
        // reset solved vars so that they are not considered pure by projector
        m_is_var.reset_solved();
        term_graph::projector p(*this);
        return p.project();
    }

    expr_ref_vector term_graph::project(model &mdl) {
        m_is_var.reset_solved();
        term_graph::projector p(*this);
        p.set_model(mdl);
        return p.project();
    }

    expr_ref_vector term_graph::solve() {
        // reset solved vars so that they are not considered pure by projector
        m_is_var.reset_solved();
        term_graph::projector p(*this);
        return p.solve();
    }

    expr_ref_vector term_graph::get_ackerman_disequalities() {
        m_is_var.reset_solved();
        dealloc(m_projector);
        m_projector = alloc(term_graph::projector, *this);
        return m_projector->get_ackerman_disequalities();
    }

    vector<expr_ref_vector> term_graph::get_partition(model& mdl) {
        dealloc(m_projector);
        m_projector = alloc(term_graph::projector, *this);
        return m_projector->get_partition(mdl, false);
    }

    expr_ref_vector term_graph::shared_occurrences(family_id fid) {
        term_graph::projector p(*this);
        return p.shared_occurrences(fid);        
    }

    void term_graph::add_model_based_terms(model& mdl, expr_ref_vector const& terms) {
        for (expr* t : terms) {
            internalize_term(t);
        }
        m_is_var.reset_solved();
        
        SASSERT(!m_projector);
        m_projector = alloc(term_graph::projector, *this);        

        // retrieve partition of terms
        vector<expr_ref_vector> equivs = m_projector->get_partition(mdl, true);

        // merge term graph on equal terms.
        for (auto const& cs : equivs) {
            term* t0 = get_term(cs[0]);
            for (unsigned i = 1; i < cs.size(); ++i) {
                merge(*t0, *get_term(cs[i]));
            }
        }
        TRACE("qe", 
              for (auto & es : equivs) {
                  tout << "equiv: ";
                  for (expr* t : es) tout << expr_ref(t, m) << " ";
                  tout << "\n";
              }
              display(tout););
        // create representatives for shared/projected variables.
        m_projector->set_model(mdl);
        m_projector->purify();

    }

    expr* term_graph::rep_of(expr* e) {
        SASSERT(m_projector);
        term* t = get_term(e);
        SASSERT(t && "only get representatives");
        return m_projector->find_term2app(*t);
    }
    
    expr_ref_vector term_graph::dcert(model& mdl, expr_ref_vector const& lits) {
        TRACE("qe", tout << "dcert " << lits << "\n";);
        struct pair_t {
            expr* a, *b;
            pair_t(): a(nullptr), b(nullptr) {}
            pair_t(expr* _a, expr* _b):a(_a), b(_b) {
                if (a->get_id() > b->get_id()) std::swap(a, b);
            }
            struct hash {
                unsigned operator()(pair_t const& p) const { return mk_mix(p.a ? p.a->hash() : 0, p.b ? p.b->hash() : 0, 1); }
            };
            struct eq {
                bool operator()(pair_t const& a, pair_t const& b) const { return a.a == b.a && a.b == b.b; }
            };
        };
        hashtable<pair_t, pair_t::hash, pair_t::eq> diseqs;
        expr_ref_vector result(m);        
        add_lits(lits);
        svector<pair_t> todo;

        for (expr* e : lits) {
            expr* ne, *a, *b;
            if (m.is_not(e, ne) && m.is_eq(ne, a, b) && (is_uninterp(a) || is_uninterp(b))) {
                diseqs.insert(pair_t(a, b));
            }
            else if (is_uninterp(e)) {
                diseqs.insert(pair_t(e, m.mk_false()));
            }
            else if (m.is_not(e, ne) && is_uninterp(ne)) {
                diseqs.insert(pair_t(ne, m.mk_true()));
            }           
        }
        for (auto& p : diseqs) todo.push_back(p);

        auto const partitions = get_partition(mdl);
        obj_map<expr, unsigned> term2pid;
        unsigned id = 0;
        for (auto const& vec : partitions) {
            for (expr* e : vec) term2pid.insert(e, id);
            ++id;
        }
        auto partition_of = [&](expr* e) { return partitions[term2pid[e]]; }; 
        auto in_table = [&](expr* a, expr* b) { 
            return diseqs.contains(pair_t(a, b));
        };
        auto same_function = [](expr* a, expr* b) {
            return is_app(a) && is_app(b) && 
            to_app(a)->get_decl() == to_app(b)->get_decl() && to_app(a)->get_family_id() == null_family_id;
        };

        // make sure that diseqs is closed under function applications
        // of uninterpreted functions.
        for (unsigned idx = 0; idx < todo.size(); ++idx) {
            auto p = todo[idx];
            for (expr* t1 : partition_of(p.a)) {
                for (expr* t2 : partition_of(p.b)) {
                    if (same_function(t1, t2)) {
                        unsigned sz = to_app(t1)->get_num_args();
                        bool found = false;
                        pair_t q(t1, t2);
                        for (unsigned i = 0; i < sz; ++i) {
                            expr* arg1 = to_app(t1)->get_arg(i);
                            expr* arg2 = to_app(t2)->get_arg(i);
                            if (mdl(arg1) == mdl(t2)) {
                                continue;
                            }
                            if (in_table(arg1, arg2)) {
                                found = true;
                                break;
                            }
                            q = pair_t(arg1, arg2);
                        }
                        if (!found) {
                            diseqs.insert(q);
                            todo.push_back(q);
                            result.push_back(m.mk_not(m.mk_eq(q.a, q.b)));
                        }
                    }
                }
            }
        }
        for (auto const& terms : partitions) {
            expr* a = nullptr;
            for (expr* b : terms) { 
                if (is_uninterp(b)) { 
                    if (a) 
                        result.push_back(m.mk_eq(a, b));
                    else 
                        a = b;
                }
            }
        }
        TRACE("qe", tout << result << "\n";);
        return result;
    }

}
