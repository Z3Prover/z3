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
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "qe/qe_term_graph.h"

namespace qe {

class term {
    // -- an app represented by this term
    expr* m_app; // NSB: to make usable with exprs
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
    term(expr* a, u_map<term*>& app2term) : 
        m_app(a), 
        m_root(this), 
        m_next(this),
        m_class_size(1), 
        m_mark(false), 
        m_mark2(false),
        m_interpreted(false) {
        if (!is_app(a)) return;
        for (expr* e : *to_app(a)) {
            term* t = app2term[e->get_id()];
            t->m_parents.push_back(this);
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

    struct cg_hash {
        unsigned operator()(term const* t) const { 
            unsigned a, b, c;
            a = b = c = t->get_decl_id(); 
            for (term * ch : children(t)) {
                a = ch->get_root().get_id();
                mix(a, b, c);
            }
            return c;
        }
    };

    struct cg_eq {
        bool operator()(term * t1, term * t2) const {
            if (t1->get_decl_id() != t2->get_decl_id()) return false;
            if (t1->m_children.size() != t2->m_children.size()) return false;
            for (unsigned i = 0, sz = t1->m_children.size(); i < sz; ++ i) {
                if (t1->m_children[i]->get_root().get_id() != t2->m_children[i]->get_root().get_id()) return false;
            }
            return true;
        }
    };

    unsigned get_id() const { return m_app->get_id();}

    unsigned get_decl_id() const { return is_app(m_app) ? to_app(m_app)->get_decl()->get_id() : m_app->get_id(); }

    bool is_marked() const {return m_mark;}
    void set_mark(bool v){m_mark = v;}
    bool is_marked2() const {return m_mark2;} // NSB: where is this used?
    void set_mark2(bool v){m_mark2 = v;}      // NSB: where is this used?

    bool is_interpreted() const {return m_interpreted;}
    void mark_as_interpreted() {m_interpreted=true;}
    expr* get_app() const {return m_app;}
    unsigned get_num_args() const { return is_app(m_app) ? to_app(m_app)->get_num_args() : 0; }

    term &get_root() const {return *m_root;}
    bool is_root() const {return m_root == this;}
    void set_root(term &r) {m_root = &r;}
    term &get_next() const {return *m_next;}

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
};



class arith_term_graph_plugin : public term_graph_plugin {
    term_graph &m_g;
    ast_manager &m;
    arith_util m_arith;

public:
    arith_term_graph_plugin(term_graph &g) :
        term_graph_plugin (g.get_ast_manager().mk_family_id("arith")),
        m_g(g), m(g.get_ast_manager()), m_arith(m) {(void)m_g;}

    virtual ~arith_term_graph_plugin() {}

    bool mk_eq_core (expr *_e1, expr *_e2, app_ref &res) {
        expr *e1, *e2;
        e1 = _e1;
        e2 = _e2;

        if (m_arith.is_zero(e1)) {
            std::swap(e1, e2);
        }
        // y + -1*x == 0  --> y = x
        expr *a0 = 0, *a1 = 0, *x = 0;
        if (m_arith.is_zero(e2) && m_arith.is_add(e1, a0, a1)) {
            if (m_arith.is_times_minus_one(a1, x)) {
                e1 = a0;
                e2 = x;
            }
            else if (m_arith.is_times_minus_one(a0, x)) {
                e1 = a1;
                e2 = x;
            }
        }
        res = m.mk_eq(e1, e2);
        return true;
    }

    app* mk_le_zero(expr *arg) {
        expr *e1, *e2, *e3;
        // XXX currently disabled
        if (m_arith.is_add(arg, e1, e2)) {
            // e1-e2<=0 --> e1<=e2
            if (m_arith.is_times_minus_one(e2, e3)) {
                return m_arith.mk_le(e1, e3);
            }
            // -e1+e2<=0 --> e2<=e1
            else if (m_arith.is_times_minus_one(e1, e3)) {
                return m_arith.mk_le(e2, e3);
            }
        }
        return m_arith.mk_le(arg, mk_zero());
    }

    app* mk_ge_zero(expr *arg) {
        expr *e1, *e2, *e3;
        // XXX currently disabled
        if (m_arith.is_add(arg, e1, e2)) {
            // e1-e2>=0 --> e1>=e2
            if (m_arith.is_times_minus_one(e2, e3)) {
                return m_arith.mk_ge(e1, e3);
            }
            // -e1+e2>=0 --> e2>=e1
            else if (m_arith.is_times_minus_one(e1, e3)) {
                return m_arith.mk_ge(e2, e3);
            }
        }
        return m_arith.mk_ge(arg, mk_zero());
    }

    bool mk_le_core (expr *arg1, expr * arg2, app_ref &result) {
        // t <= -1  ==> t < 0 ==> ! (t >= 0)
        rational n;
        if (m_arith.is_int (arg1) && m_arith.is_minus_one (arg2)) {
            result = m.mk_not (mk_ge_zero (arg1));
            return true;
        }
        else if (m_arith.is_zero(arg2)) {
            result = mk_le_zero(arg1);
            return true;
        }
        else if (m_arith.is_int(arg1) && m_arith.is_numeral(arg2, n) && n < 0) {
            // t <= n ==> t < n + 1 ==> ! (t >= n + 1)
            result = m.mk_not(m_arith.mk_ge(arg1, m_arith.mk_numeral(n+1, true)));
            return true;
        }
        return false;
    }

    expr * mk_zero () {return m_arith.mk_numeral (rational (0), true);}
    bool is_one (expr const * n) const {
        rational val;
        return m_arith.is_numeral (n, val) && val.is_one ();
    }

    bool mk_ge_core (expr * arg1, expr * arg2, app_ref &result) {
        // t >= 1 ==> t > 0 ==> ! (t <= 0)
        rational n;
        if (m_arith.is_int (arg1) && is_one (arg2)) {
            result = m.mk_not (mk_le_zero (arg1));
            return true;
        }
        else if (m_arith.is_zero(arg2)) {
            result = mk_ge_zero(arg1);
            return true;
        }
        else if (m_arith.is_int(arg1) && m_arith.is_numeral(arg2, n) && n > 0) {
            // t >= n ==> t > n - 1 ==> ! (t <= n - 1)
            result = m.mk_not(m_arith.mk_le(arg1, m_arith.mk_numeral(n-1, true)));
            return true;
        }
        return false;
    }

    virtual app_ref process_lit (app *_lit) {
        app *lit = _lit;
        expr *e1, *e2;

        // strip negation
        bool is_neg = m.is_not(lit);
        if (is_neg) {
            lit = to_app(to_app(lit)->get_arg(0));
        }

        app_ref res(m);
        res = lit;
        if (m.is_eq (lit, e1, e2)) {
            mk_eq_core(e1, e2, res);
        }
        else if (m_arith.is_le(lit, e1, e2)) {
            mk_le_core(e1, e2, res);
        }
        else if (m_arith.is_ge(lit, e1, e2)) {
            mk_ge_core(e1, e2, res);
        }

        // restore negation
        if (is_neg) {
            res = m.mk_not(res);
        }

        return res;
    }
};

term_graph::term_graph(ast_manager &man) : m(man), m_lits(m), m_pinned(m) {
    m_plugins.register_plugin (alloc(arith_term_graph_plugin, *this));
}

term_graph::~term_graph() {
    reset();
}

static family_id get_family_id(ast_manager &m, app *lit) {
    family_id fid = null_family_id;

    expr *e1 = nullptr, *e2 = nullptr, *e3 = nullptr;
    // strip negation
    if (!m.is_not (lit, e1)) { e1 = lit; }

    // deal with equality using sort of range
    if (m.is_eq (e1, e2, e3)) {
        fid = get_sort (e2)->get_family_id();
    }
    // extract family_id of top level app
    else {
        fid = to_app(e1)->get_decl()->get_family_id();
    }

    return fid;
}

void term_graph::add_lit(app *l) {
    app_ref lit(m);

    family_id fid = get_family_id (m, l);
    term_graph_plugin *pin = m_plugins.get_plugin(fid);
    if (pin) {
        lit = pin->process_lit(l);
    } else {
        lit = l;
    }
    m_lits.push_back(lit);
    internalize_lit(lit);
}

bool term_graph::is_internalized(app *a) {
    return m_app2term.contains(a->get_id());
}

term* term_graph::get_term(expr *a) {
    term *res;
    return m_app2term.find (a->get_id(), res) ? res : nullptr;
}

term *term_graph::mk_term(expr *a) {
    term * t = alloc(term, a, m_app2term);
    if (t->get_num_args() == 0 && m.is_unique_value(a)){
        t->mark_as_interpreted();
    }

    m_terms.push_back(t);
    m_app2term.insert(a->get_id(), t);
    return t;
}

term *term_graph::internalize_term(expr *t) {
    term *res = get_term(t);

    if (!res) {
        if (is_app(t)) {
            for (expr * arg : *::to_app(t)) {
                internalize_term(arg);
            }
        }
        res = mk_term(t);
    }
    return res;
}

void term_graph::internalize_eq(expr *a1, expr* a2) {
    internalize_term(a1);
    internalize_term(a2);
    merge(get_term(a1)->get_root(), get_term(a2)->get_root());
}

void term_graph::internalize_lit(app* lit) {
    expr *e1 = nullptr, *e2 = nullptr;
    if (m.is_eq (lit, e1, e2)) {        
        internalize_eq (e1, e2);
    }
    else {
        internalize_term(lit);
    }
}

void term_graph::merge (term &t1, term &t2) {
    SASSERT(t1.is_root());
    SASSERT(t2.is_root());

    if (&t1 == &t2) return;

    term *a = &t1;
    term *b = &t2;
    if (a->get_class_size() > b->get_class_size()) {
        std::swap(a, b);
    }

    // make 'a' be the root of the equivalence class of 'b'
    b->set_root(*a);
    for (term *it = &b->get_next(); it != b; it = &it->get_next()) {
        // TBD: remove parents of it from the cg table.
        it->set_root(*a);
    }

    // merge equivalence classes
    a->merge_eq_class(*b);

    // TBD: insert parents of b's old equilvalence class into the cg table
    // and propagate equalities.

    // -- merge might have invalidated term2map cache

    // NSB: ??? what is ownership model of pinned in m_terms?
    m_term2app.reset();
    m_pinned.reset();  
}

expr* term_graph::mk_app_core (expr *e) {
    if (is_app(e)) {
        expr_ref_vector kids(m);   
        app* a = ::to_app(e);
        for (expr * arg : *a) {
            kids.push_back (mk_app(arg));
        }        
        app* res = m.mk_app(a->get_decl(), a->get_num_args(), kids.c_ptr());
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
        return expr_ref(r.get_app(), m);
    }

    expr* res = nullptr;
    if (m_term2app.find(r.get_id(), res)) {
        return expr_ref(res, m);
    }

    res = mk_app_core (r.get_app());
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

void term_graph::mk_equalities(term const &t, app_ref_vector &out) {
    SASSERT(t.is_root());
    expr_ref rep(mk_app(t), m);

    for (term *it = &t.get_next(); it != &t; it = &it->get_next()) {
        expr* mem = mk_app_core(it->get_app());
        out.push_back (m.mk_eq (rep, mem));
    }
}

void term_graph::mk_all_equalities(term const &t, app_ref_vector &out) {
    mk_equalities(t, out);

    for (term *it = &t.get_next(); it != &t; it = &it->get_next ()) {
        expr* a1 = mk_app_core (it->get_app());
        for (term *it2 = &it->get_next(); it2 != &t; it2 = &it2->get_next()) {
            expr* a2 =  mk_app_core(it2->get_app());
            out.push_back (m.mk_eq (a1, a2));
        }
    }
}

void term_graph::reset_marks() {
    for (term * t : m_terms) {
        t->set_mark(false);
    }
}

/// Order of preference for roots of equivalence classes
/// XXX This should be factored out to let clients control the preference
bool term_graph::term_le(term const &t1, term const &t2) {

    // prefer constants over applications
    // prefer uninterpreted constants over values
    // prefer smaller expressions over larger ones
    if (t1.get_num_args() == 0 && t2.get_num_args() > 0) {
        return true;
    }
    if (t1.get_num_args() == t2.get_num_args()) {
        // NSB: how does this possibly define an order?
        return m.is_value(t2.get_app());
    }

    unsigned sz1 = get_num_exprs(t1.get_app());
    unsigned sz2 = get_num_exprs(t1.get_app());
    return sz1 < sz2;
}

void term_graph::pick_root (term &t) {
    term *r = &t;
    for (term *it = &t.get_next(); it != &t; it = &it->get_next()) {
        it->set_mark(true);
        if (term_le(*it, *r)) { r = it; }
    }

    // -- if found something better, make it the new root
    if (r != &t) {
        r->mk_root();
    }
}
/// Choose better roots for equivalence classes
void term_graph::pick_roots() {
    for (term* t : m_terms) {
        if (!t->is_marked() && t->is_root()) 
            pick_root(*t);
    }
    reset_marks();
}

void term_graph::display(std::ostream &out) {
    for (term * t : m_terms) {
        out << mk_pp(t->get_app(), m) << " is root " << t->is_root()
            << " cls sz " << t->get_class_size()
            << " term " << t
            << "\n";
    }
}

void term_graph::to_lits (app_ref_vector &lits, bool all_equalities) {
    pick_roots();

    for (app * a : m_lits) {
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

void term_graph::to_lits (expr_ref_vector &lits, bool all_equalities) {
    app_ref_vector out(m);
    to_lits (out, all_equalities);
    for (app* a : out) {
        lits.push_back(a);
    }
}

app_ref term_graph::to_app() {
    app_ref_vector lits(m);
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
}

expr_ref_vector term_graph::project(func_decl_ref_vector const& decls, bool exclude) {
    obj_hashtable<func_decl> _decls;
    for (func_decl* f : decls) _decls.insert(f);
    // . propagate representatives up over parents.
    //   use work-list + marking to propagate.
    // . produce equalities over represented classes.
    // . produce other literals over represented classes 
    //    (walk disequalities in m_lits and represent lhs/rhs over decls or excluding decls)
    
    expr_ref_vector result(m);
    NOT_IMPLEMENTED_YET();
    return result;
}

}
