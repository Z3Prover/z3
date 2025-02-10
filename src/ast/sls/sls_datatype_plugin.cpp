/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_datatype_plugin.cpp

Abstract:

    Algebraic Datatypes for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-14

Notes:

Eager reduction to EUF:
   is-c(c(t))                for each c(t) in T
   acc_i(c(t_i)) = t_i       for each c(..t_i..) in T
   is-c(t) => t = c(...acc_j(t)..) for each acc_j(t) in T

   sum_i is-c_i(t) = 1
   is-c(t) <=> c = t         for each 0-ary constructor c

   is-c(t) <=> t = c(acc_1(t)..acc_n(t))

   s = acc(...(acc(t)) => s != t   if t is recursive

   or_i t = t_i              if t is a finite sort with terms t_i


   s := acc(t)                  => s < t in P
   a := s = acc(t), a is a unit => s < t in P
   a := s = acc(t), a in Atoms  => (a => s < t) in P

   s << t if there is a path P with conditions L.
   L => s != t   

   This disregards if acc is applied to non-matching constructor.
   In this case we rely on that the interpretation of acc can be
   forced.
   If this is incorrect, include is-c(t) assumptions in path axioms.

   Is P sufficient? Should we just consider all possible paths of depth at most k to be safe?
   Example: 
      C(acc(t)) == C(s)
   triggers equation acc(t) = s, but the equation is implicit, so acc(t) and s are not directly
   connected.
   Even, the axioms extracted from P don't consider transitivity of =.
   So the can-be-equal alias approximation is too strong.
   We therefore add an occurs check during propagation and lazily add missed axioms.


Model-repair based:

1. Initialize uninterpreted datatype nodes to hold arbitrary values.
2. Initialize datatype nodes by induced evaluation.
3. Atomic constraints are of the form for datatype terms
   x = y, x = t, x != y, x != t; s = t, s != t

   violated x = y:  x <- eval(y), y <- eval(x) or x, y <- fresh
   violated x = t:  x <- eval(t), repair t using the shape of x
   violated x != y: x <- fresh, y <- fresh
   violated x != t: x <- fresh, subterm y of t: y <- fresh

   acc(x) = t: eval(x) = c(u, v) acc(c(u,v)) = u -> repair(u = t)
   acc(x) = t: eval(x) does not match acc        -> acc(x) 
   has a fixed interpretation, so repair over t instead, or update interpretation of x

   uses:
    model::get_fresh_value(s)
    model::get_some_value(s)

--*/

#include "ast/sls/sls_datatype_plugin.h"
#include "ast/sls/sls_euf_plugin.h"
#include "ast/ast_pp.h"
#include "params/sls_params.hpp"

namespace sls {
    
    datatype_plugin::datatype_plugin(context& c):
        plugin(c),
        euf(c.euf()),
        g(c.egraph()),
        dt(m),
        m_axioms(m),
        m_values(m),
        m_eval(m) {
        m_fid = dt.get_family_id();
    }
    
    datatype_plugin::~datatype_plugin() {}

    void datatype_plugin::collect_path_axioms() {
        expr* t = nullptr, *z = nullptr;
        for (auto s : ctx.subterms()) {
            if (dt.is_accessor(s, t) && dt.is_recursive(t) && dt.is_recursive(s))
                add_edge(s, t, m.mk_app(dt.get_constructor_is(dt.get_accessor_constructor(to_app(s)->get_decl())), t));
            if (dt.is_constructor(s) && dt.is_recursive(s)) {
                for (auto arg : *to_app(s))
                    add_edge(arg, s, nullptr);
            }
        }
        expr* x = nullptr, *y = nullptr;
        for (sat::bool_var v = 0; v < ctx.num_bool_vars(); ++v) {
            expr* e = ctx.atom(v);
            if (!e)
                continue;
            if (!m.is_eq(e, x, y))
                continue;
            if (!dt.is_recursive(x))
                continue;
            sat::literal lp(v, false), ln(v, true);
            if (dt.is_accessor(x, z) && dt.is_recursive(z)) {
                if (ctx.is_unit(lp))
                    add_edge(y, z, nullptr);
                else if (ctx.is_unit(ln))
                    ;
                else
                    add_edge(y, z, e);                    
            }
            if (dt.is_accessor(y, z) && dt.is_recursive(z)) {
                if (ctx.is_unit(lp))
                    add_edge(x, z, m.mk_app(dt.get_constructor_is(dt.get_accessor_constructor(to_app(y)->get_decl())), z));
                else if (ctx.is_unit(ln))
                    ;
                else
                    add_edge(x, z, e);                    
            }            
        }
        add_path_axioms();
    }

    void datatype_plugin::add_edge(expr* child, expr* parent, expr* cond) {
        m_parents.insert_if_not_there(child, vector<parent_t>()).push_back({parent, expr_ref(cond, m)});
        TRACE("dt", tout << mk_bounded_pp(child, m) << " <- " << mk_bounded_pp(parent, m) << " " << mk_bounded_pp(cond, m) << "\n");
    }

    void datatype_plugin::add_path_axioms() {
        ptr_vector<expr> path;
        sat::literal_vector lits;
        for (auto [child, parents] : m_parents) {
            path.reset();
            lits.reset();
            path.push_back(child);
            add_path_axioms(path, lits, parents);
        }
    }

    void datatype_plugin::add_path_axioms(ptr_vector<expr>& children, sat::literal_vector& lits, vector<parent_t> const& parents) {
        for (auto const& [parent, cond] : parents) {
            if (cond)                    
                lits.push_back(~ctx.mk_literal(cond));
            if (children.contains(parent)) {
                // only assert loop clauses for proper loops
                if (parent == children[0])
                    ctx.add_clause(lits);
                if (cond)                    
                    lits.pop_back();
                continue;
            }
            if (children[0]->get_sort() == parent->get_sort()) {
                lits.push_back(~ctx.mk_literal(m.mk_eq(children[0], parent)));
                TRACE("dt", for (auto lit : lits) tout << (lit.sign() ? "~": "") << mk_pp(ctx.atom(lit.var()), m) << "\n";);
                ctx.add_clause(lits);
                lits.pop_back();
            }
            auto child = children.back();
            if (m_parents.contains(child)) {
                children.push_back(parent);
                auto& parents2 = m_parents[child];
                add_path_axioms(children, lits, parents2);
                children.pop_back();                
            }
            if (cond)                    
                lits.pop_back();
        }
    }

    // collect datatypes sorts
    // for each constructor term c(t) add axioms:
    //  is-c(c(t))
    //  sel_i(c(..t_i..)) = t_i
    //  not is-c'(c(t)) for c' != c
    // for each term t of datatype sort
    //  or_i is-c_i(t)
    //  is_c_i(t) <=> t = c_i(acc_1(t)..acc_n(t))

    void datatype_plugin::add_axioms() {
        expr_ref_vector axioms(m);
        for (auto t : ctx.subterms()) {
            auto s = t->get_sort();
            if (dt.is_datatype(s)) 
                m_dts.insert_if_not_there(s, ptr_vector<expr>()).push_back(t);

            if (!is_app(t))
                continue;
            auto ta = to_app(t);
            auto f = ta->get_decl();
            
            if (dt.is_constructor(t)) {
                auto r = dt.get_constructor_is(f);
                m_axioms.push_back(m.mk_app(r, t));
                auto& acc = *dt.get_constructor_accessors(f);
                for (unsigned i = 0; i < ta->get_num_args(); ++i) {
                    auto ti = ta->get_arg(i);
                    m_axioms.push_back(m.mk_eq(ti, m.mk_app(acc[i], t)));
                }
                auto& cns = *dt.get_datatype_constructors(s);
                for (auto c : cns) {
                    if (c != f) {
                        auto r2 = dt.get_constructor_is(c);
                        m_axioms.push_back(m.mk_not(m.mk_app(r2, t)));
                    }
                }
                continue;
            }

            if (dt.is_recognizer0(f)) {
                auto u = ta->get_arg(0);
                auto c = dt.get_recognizer_constructor(f);
                m_axioms.push_back(m.mk_iff(t, m.mk_app(dt.get_constructor_is(c), u)));
            }
            
            if (dt.is_update_field(t)) {
                NOT_IMPLEMENTED_YET();
            }

            if (dt.is_datatype(s)) {
                auto& cns = *dt.get_datatype_constructors(s);
                expr_ref_vector ors(m);
                for (auto c : cns) {
                    auto r = dt.get_constructor_is(c);
                    ors.push_back(m.mk_app(r, t));
                }
                m_axioms.push_back(m.mk_or(ors));
#if 0
                // expanded lazily
                // EUF already handles enumeration datatype case.
                for (unsigned i = 0; i < cns.size(); ++i) {
                    auto r1 = dt.get_constructor_is(cns[i]);
                    for (unsigned j = i + 1; j < cns.size(); ++j) {
                        auto r2 = dt.get_constructor_is(cns[j]);
                        m_axioms.push_back(m.mk_or(m.mk_not(m.mk_app(r1, t)), m.mk_not(m.mk_app(r2, t))));
                    }
                }
#endif
                for (auto c : cns) {
                    auto r = dt.get_constructor_is(c);
                    auto& acc = *dt.get_constructor_accessors(c);
                    expr_ref_vector args(m);
                    for (auto a : acc)
                        args.push_back(m.mk_app(a, t));
                    m_axioms.push_back(m.mk_iff(m.mk_app(r, t), m.mk_eq(t, m.mk_app(c, args))));
                }
            }
        }
        //collect_path_axioms();

        TRACE("dt", for (auto a : m_axioms) tout << mk_pp(a, m) << "\n";);

        for (auto a : m_axioms)
            ctx.add_constraint(a);
    }

    void datatype_plugin::initialize() {
        sls_params sp(ctx.get_params());
        m_axiomatic_mode = sp.dt_axiomatic();
        if (m_axiomatic_mode)
            add_axioms();
    }

    expr_ref datatype_plugin::get_value(expr* e) {
        if (!dt.is_datatype(e) || !g)
            return expr_ref(m);
        if (m_axiomatic_mode) {

            init_values();
            TRACE("dt", tout << "get value " << mk_bounded_pp(e, m) << " " << m_values.size() << " " << g->find(e)->get_root_id() << "\n";);
            for (auto n : euf::enode_class(g->find(e))) {
                auto id = n->get_id();
                if (m_values.get(id, nullptr))
                    return expr_ref(m_values.get(id), m);
            }
            m_values.reset();
            init_values();
            return expr_ref(m_values.get(g->find(e)->get_root_id()), m);
        }
        return expr_ref(m_eval.get(e->get_id()), m);
    }

    void datatype_plugin::init_values() {
        if (!m_values.empty())
            return;
        TRACE("dt", g->display(tout));
        m_model = alloc(model, m);
        // retrieve e-graph from sls_euf_solver: add bridge in sls_context to share e-graph
        SASSERT(g);
        // build top_sort<euf::enode> similar to dt_solver.cpp
        top_sort<euf::enode> deps;
        for (auto* n : g->nodes())
            if (n->is_root())
                add_dep(n, deps);

        auto trace_assignment = [&](std::ostream& out, euf::enode* n) {
            for (auto sib : euf::enode_class(n))
                out << g->bpp(sib) << " ";
            out << " <- " << mk_bounded_pp(m_values.get(n->get_id()), m) << "\n";
        };
        (void)trace_assignment;
        deps.topological_sort();
        expr_ref_vector args(m);
        euf::enode_vector leaves, worklist;
        obj_map<euf::enode, euf::enode_vector> leaf2root;
        // walk topological sort in order of leaves to roots, attaching values to nodes.
        for (euf::enode* n : deps.top_sorted()) {
            SASSERT(n->is_root());
            unsigned id = n->get_id();
            if (m_values.get(id, nullptr))
                continue;
            expr* e = n->get_expr();
            m_values.reserve(id + 1);
            if (!dt.is_datatype(e))
                continue;
            euf::enode* con = get_constructor(n);
            if (!con) {
                leaves.push_back(n);
                continue;
            }
            auto f = con->get_decl();
            args.reset();
            bool has_null = false;
            for (auto arg : euf::enode_args(con)) {
                if (dt.is_datatype(arg->get_sort())) {
                    auto val_arg = m_values.get(arg->get_root_id(), nullptr);
                    if (!val_arg)
                        has_null = true;
                    leaf2root.insert_if_not_there(arg->get_root(), euf::enode_vector()).push_back(n);
                    args.push_back(val_arg);
                }
                else
                    args.push_back(ctx.get_value(arg->get_expr()));
            }
            if (!has_null) {                
                m_values.setx(id, m.mk_app(f, args));
                m_model->register_value(m_values.get(id));
                TRACE("dt", tout << "Set interpretation "; trace_assignment(tout, n););
            }
        }

        TRACE("dt",
            for (euf::enode* n : deps.top_sorted()) {
                tout << g->bpp(n) << ": ";
                tout << g->bpp(get_constructor(n)) << " :: ";
                auto s = deps.get_dep(n);
                if (s) {
                    tout << " -> ";
                    for (auto t : *s)
                        tout << g->bpp(t) << " ";
                }
                tout << "\n";
            }
        );

        auto process_workitem = [&](euf::enode* n) {
            if (!leaf2root.contains(n))
                return true;
            bool all_processed = true;
            for (auto p : leaf2root[n]) {
                if (m_values.get(p->get_id(), nullptr))
                    continue;
                auto con = get_constructor(p);
                SASSERT(con);
                auto f = con->get_decl();
                args.reset();
                bool has_missing = false;
                for (auto arg : euf::enode_args(con)) {
                    if (dt.is_datatype(arg->get_sort())) {
                        auto arg_val = m_values.get(arg->get_root_id());
                        if (!arg_val)
                            has_missing = true;
                        args.push_back(arg_val);
                    }
                    else
                        args.push_back(ctx.get_value(arg->get_expr()));
                }
                if (has_missing) {
                    all_processed = false;
                    continue;
                }
                worklist.push_back(p);
                SASSERT(all_of(args, [&](expr* e) { return e != nullptr; }));
                m_values.setx(p->get_id(), m.mk_app(f, args));
                TRACE("dt", tout << "Patched interpretation "; trace_assignment(tout, p););
                m_model->register_value(m_values.get(p->get_id()));
            }
            return all_processed;
         };

        auto process_worklist = [&](euf::enode_vector& worklist) {
            unsigned j = 0, sz = worklist.size();
            for (unsigned i = 0; i < worklist.size(); ++i) 
                if (!process_workitem(worklist[i]))
                    worklist[j++] = worklist[i];
            worklist.shrink(j);
            return j < sz;
        };

        // attach fresh values to each leaf, walk up parents to assign them values.
        while (!leaves.empty()) {
            auto n = leaves.back();            
            leaves.pop_back();
            SASSERT(!get_constructor(n));
            auto v = m_model->get_fresh_value(n->get_sort());
            if (!v)
                v = m_model->get_some_value(n->get_sort());
            SASSERT(v);
            unsigned id = n->get_id();
            m_values.setx(id, v);
            TRACE("dt", tout << "Fresh interpretation "; trace_assignment(tout, n););
            worklist.reset();
            worklist.push_back(n);
            while (process_worklist(worklist))
                ;
        }
    }
    
    void datatype_plugin::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!dt.is_datatype(n->get_expr()))
            return;
        euf::enode* con = get_constructor(n);
        TRACE("dt", tout << g->bpp(n) << " con: " << g->bpp(con) << "\n";);
        if (!con)
            dep.insert(n, nullptr);
        else if (con->num_args() == 0)
            dep.insert(n, nullptr);
        else 
            for (euf::enode* arg : euf::enode_args(con))
                dep.add(n, arg->get_root());       
    }

    
    void datatype_plugin::start_propagation() {
        m_values.reset();
        m_model = nullptr;
    }

    euf::enode* datatype_plugin::get_constructor(euf::enode* n) const {
        for (auto sib : euf::enode_class(n))
            if (dt.is_constructor(sib->get_expr()))
                return sib;
        return nullptr;
    }

    bool datatype_plugin::propagate() {       
        enum color_t { white, grey, black };
        svector<color_t> color;
        ptr_vector<euf::enode> stack;
        obj_map<sort, ptr_vector<expr>> sorts;

        auto set_conflict = [&](euf::enode* n) {
            expr_ref_vector diseqs(m);
            while (true) {
                auto n2 = stack.back();
                auto con2 = get_constructor(n2);
                if (n2 != con2)
                    diseqs.push_back(m.mk_not(m.mk_eq(n2->get_expr(), con2->get_expr())));
                if (n2->get_root() == n->get_root()) {
                    if (n != n2)
                        diseqs.push_back(m.mk_not(m.mk_eq(n->get_expr(), n2->get_expr())));
                    break;
                }
                stack.pop_back();
            }
            IF_VERBOSE(1, verbose_stream() << "cycle\n"; for (auto e : diseqs) verbose_stream() << mk_pp(e, m) << "\n";);
            ctx.add_constraint(m.mk_or(diseqs));
            ++m_stats.m_num_occurs;
        };

        for (auto n : g->nodes()) {
            if (!n->is_root())
                continue;
            euf::enode* con = nullptr;
            for (auto sib : euf::enode_class(n)) {
                if (dt.is_constructor(sib->get_expr())) {
                    if (!con) 
                        con = sib;                    
                    if (con && con->get_decl() != sib->get_decl()) {
                        ctx.add_constraint(m.mk_not(m.mk_eq(con->get_expr(), sib->get_expr())));
                        ++m_stats.m_num_occurs;                        
                    }
                }
            }
        }

        for (auto n : g->nodes()) {
            if (!n->is_root())
                continue;
            expr* e = n->get_expr();
            if (!dt.is_datatype(e))
                continue;
            if (!ctx.is_relevant(e))
                continue;
            sort* s = e->get_sort();
            sorts.insert_if_not_there(s, ptr_vector<expr>()).push_back(e);

            auto c = color.get(e->get_id(), white);
            SASSERT(c != grey);
            if (c == black)
                continue;

            // dfs traversal of enodes, starting with n, 
            // with outgoing edges the arguments of con, where con
            // is a node in the same congruence class as n that is a constructor.
            // For every cycle accumulate a conflict.

            stack.push_back(n);
            while (!stack.empty()) {
                n = stack.back();
                unsigned id = n->get_root_id();
                c = color.get(id, white);
                euf::enode* con;

                switch (c) {
                case black:
                    stack.pop_back();
                    break;
                case grey:
                case white: 
                    color.setx(id, grey, white);
                    con = get_constructor(n);
                    if (!con)
                        goto done_with_node;
                    for (auto child : euf::enode_args(con)) {
                        auto c2 = color.get(child->get_root_id(), white);
                        switch (c2) {
                        case black:
                            break;
                        case grey:
                            set_conflict(child);
                            return true;
                        case white:
                            stack.push_back(child);
                            goto node_pushed;
                        }
                    }
                done_with_node:
                    color[id] = black;
                    stack.pop_back();
                node_pushed:
                    break;                
                }
            }                    
        }


        for (auto const& [s, elems] : sorts) {
            auto sz = s->get_num_elements();

            if (!sz.is_finite() || sz.size() >= elems.size())
                continue;
            ctx.add_constraint(m.mk_not(m.mk_distinct((unsigned)sz.size() + 1, elems.data())));                       
        }

        return false;
    }

    bool datatype_plugin::include_func_interp(func_decl* f) const {
        if (!dt.is_accessor(f))
            return false;
        func_decl* con_decl = dt.get_accessor_constructor(f);
        for (euf::enode* app : g->enodes_of(f)) {   
            euf::enode* con = get_constructor(app->get_arg(0));
            if (con && con->get_decl() != con_decl) 
                return true;
        }
        return false; 
    }

    bool datatype_plugin::check_ackerman(func_decl* f) const {
        if (dt.is_accessor(f))
            return true;
        if (dt.is_constructor(f)) {
            for (unsigned i = 0; i < f->get_arity(); ++i) {
                if (f->get_range() != f->get_domain(i))
                    return true;
            }
            return false;
        }
        if (dt.is_is(f))
            return false;
        return true;
    }

    std::ostream& datatype_plugin::display(std::ostream& out) const {
        for (auto a : m_axioms)
            out << mk_bounded_pp(a, m, 3) << "\n";
        return out;
    }
    
    void datatype_plugin::propagate_literal(sat::literal lit) {
        if (m_axiomatic_mode)
            euf.propagate_literal(lit);
        else
            propagate_literal_model_building(lit);
    }

    void datatype_plugin::propagate_literal_model_building(sat::literal lit) {
        if (!ctx.is_true(lit))
            return;
        auto a = ctx.atom(lit.var());
        if (!a || !is_app(a))
            return;
        repair_down(to_app(a));
    }
   
    bool datatype_plugin::is_sat() { return true; }
    
    void datatype_plugin::register_term(expr* e) {    
        expr* t = nullptr;
        if (dt.is_accessor(e, t)) {
            auto f = to_app(e)->get_decl();
            m_occurs.insert_if_not_there(f, expr_set()).insert(e);
            m_eval_accessor.insert_if_not_there(f, obj_map<expr, expr*>());
        }
    }


    bool datatype_plugin::repair_down(app* e) {
        expr* t, * s;
        auto v0 = eval0(e);
        auto v1 = eval1(e);
        if (v0 == v1)
            return true;
        IF_VERBOSE(2, verbose_stream() << "dt-repair-down " << mk_bounded_pp(e, m) << " " << v0 << " <- " << v1 << "\n");
        if (dt.is_constructor(e))
            repair_down_constructor(e, v0, v1);
        else if (dt.is_accessor(e, t))
            repair_down_accessor(e, t, v0);
        else if (dt.is_recognizer(e, t))
            repair_down_recognizer(e, t);
        else if (m.is_eq(e, s, t))
            repair_down_eq(e, s, t);
        else if (m.is_distinct(e))
            repair_down_distinct(e);        
        else {
            UNREACHABLE();
        }
        return false;
    }

    //
    // C(t) <- C(s) then repair t <- s
    // C(t) <- D(s) then fail the repair.
    //
    void datatype_plugin::repair_down_constructor(app* e, expr* v0, expr* v1) {
        SASSERT(dt.is_constructor(v0));
        SASSERT(dt.is_constructor(v1));
        SASSERT(e->get_decl() == to_app(v1)->get_decl());
        if (e->get_decl() == to_app(v0)->get_decl()) {
            for (unsigned i = 0; i < e->get_num_args(); ++i) {
                auto w0 = to_app(v0)->get_arg(i);
                auto w1 = to_app(v1)->get_arg(i);
                if (w0 == w1)
                    continue;
                expr* arg = e->get_arg(i);
                set_eval0(arg, w0);
                ctx.new_value_eh(arg);
            }
        }
    }

    //
    // A_D(t) <- s, val(t) = D(..s'..)      then update val(t) to agree with s
    // A_D(t) <- s, val(t) = C(..)          then set t to D(...s...)
    //            , eval(val(A_D(t))) = s'  then update eval(val(A_D,(t))) to s'
    void datatype_plugin::repair_down_accessor(app* e, expr* t, expr* v0) {
        auto f = e->get_decl();
        auto c = dt.get_accessor_constructor(f);       
        auto val_t = eval0(t);
        SASSERT(dt.is_constructor(val_t));
        expr_ref_vector args(m);
        auto const& accs = *dt.get_constructor_accessors(c);
        unsigned i;
        for (i = 0; i < accs.size(); ++i) {
            if (accs[i] == f)
                break;
        }
        SASSERT(i < accs.size());
        if (to_app(val_t)->get_decl() == c) {
            if (to_app(val_t)->get_arg(i) == v0)
                return;
            args.append(accs.size(), to_app(val_t)->get_args());
            args[i] = v0;
            expr* new_val_t = m.mk_app(c, args);
            set_eval0(t, new_val_t);
            ctx.new_value_eh(t);
            return;
        }
        if (ctx.rand(5) != 0) {
            update_eval_accessor(e, val_t, v0);              
            return;
        }
        for (unsigned j = 0; j < accs.size(); ++j) {
            if (i == j)
                args.push_back(v0);
            else
                args.push_back(m_model->get_some_value(accs[j]->get_range()));
        }
        expr* new_val_t = m.mk_app(c, args);
        set_eval0(t, new_val_t);
        ctx.new_value_eh(t);
    }

    void datatype_plugin::repair_down_recognizer(app* e, expr* t) {
        auto bv = ctx.atom2bool_var(e);
        auto is_true = ctx.is_true(bv);
        auto c = dt.get_recognizer_constructor(e->get_decl());
        auto val_t = eval0(t);
        auto const& cons = *dt.get_datatype_constructors(t->get_sort());

        auto set_to_instance = [&](func_decl* c) {
            auto const& accs = *dt.get_constructor_accessors(c);
            expr_ref_vector args(m);
            for (auto a : accs)
                args.push_back(m_model->get_some_value(a->get_range()));
            set_eval0(t, m.mk_app(c, args));
            ctx.new_value_eh(t);
        };
        auto different_constructor = [&](func_decl* c) {
            unsigned i = 0;
            func_decl* c_new = nullptr;
            for (auto c2 : cons)
                if (c2 != c && ctx.rand(++i) == 0)
                    c_new = c2;
            return c_new;
        };

        SASSERT(dt.is_constructor(val_t));
        if (c == to_app(val_t)->get_decl() && is_true)
            return;
        if (c != to_app(val_t)->get_decl() && !is_true)
            return;
        if (ctx.rand(10) == 0) 
            ctx.flip(bv);
        else if (is_true) 
            set_to_instance(c);
        else if (cons.size() == 1) 
            ctx.flip(bv);
        else 
            set_to_instance(different_constructor(c));
    }

    void datatype_plugin::repair_down_eq(app* e, expr* s, expr* t) {
        auto bv = ctx.atom2bool_var(e);
        auto is_true = ctx.is_true(bv);
        auto vs = eval0(s);
        auto vt = eval0(t);
        if (is_true && vs == vt)
            return;
        if (!is_true && vs != vt)
            return;

        if (is_true) {
            auto coin = ctx.rand(5);
            if (coin <= 1) {
                set_eval0(s, vt);
                ctx.new_value_eh(s);
                return;
            }
            if (coin <= 3) {
                set_eval0(t, vs);
                ctx.new_value_eh(t);
                return;
            }
            if (true) {
                auto new_v = m_model->get_some_value(s->get_sort());
                set_eval0(s, new_v);
                set_eval0(t, new_v);
                ctx.new_value_eh(s);
                ctx.new_value_eh(t);
                return;
            }
        }
        auto coin = ctx.rand(10);
        if (coin <= 4) {
            auto new_v = m_model->get_some_value(s->get_sort());
            set_eval0(s, new_v);
            ctx.new_value_eh(s);
            return;
        }
        if (coin <= 9) {
            auto new_v = m_model->get_some_value(s->get_sort());
            set_eval0(t, new_v);
            ctx.new_value_eh(t);
            return;
        }
    }

    void datatype_plugin::repair_down_distinct(app* e) {
        auto bv = ctx.atom2bool_var(e);
        auto is_true = ctx.is_true(bv);
        unsigned sz = e->get_num_args();
        for (unsigned i = 0; i < sz; ++i) {
            auto val1 = eval0(e->get_arg(i));
            for (unsigned j = i + 1; j < sz; ++j) {
                auto val2 = eval0(e->get_arg(j));
                if (val1 != val2)
                    continue;
                if (!is_true)
                    return;
                if (ctx.rand(2) == 0)
                    std::swap(i, j);
                auto new_v = m_model->get_some_value(e->get_arg(i)->get_sort());
                set_eval0(e->get_arg(i), new_v);
                ctx.new_value_eh(e->get_arg(i));
                return;
            }
        }
        if (is_true)
            return;
        if (sz == 1) {
            ctx.flip(bv);
            return;
        }
        unsigned i = ctx.rand(sz);
        unsigned j = ctx.rand(sz-1);
        if (j == i)
            ++j;
        if (ctx.rand(2) == 0)
            std::swap(i, j);
        set_eval0(e->get_arg(i), eval0(e->get_arg(j)));
    }

    void datatype_plugin::repair_up(app* e) {
        IF_VERBOSE(2, verbose_stream() << "dt-repair-up " << mk_bounded_pp(e, m) << "\n");
        expr* t;
        auto v0 = eval0(e);
        auto v1 = eval1(e);
        if (v0 == v1)
            return;
        if (dt.is_constructor(e)) 
            set_eval0(e, v1);                 
        else if (m.is_bool(e)) 
            ctx.flip(ctx.atom2bool_var(e));
        else if (dt.is_accessor(e, t))
            repair_up_accessor(e, t, v1);
        else {
            UNREACHABLE();
        }
    }

    void datatype_plugin::repair_up_accessor(app* e, expr* t, expr* v1) {
        auto v_t = eval0(t);
        auto f = e->get_decl();
        SASSERT(dt.is_constructor(v_t));
        auto c = dt.get_accessor_constructor(f);
        if (to_app(v_t)->get_decl() != c) 
            update_eval_accessor(e, v_t, v1);
        
        set_eval0(e, v1);       
    }

    expr_ref datatype_plugin::eval1(expr* e) {
        expr* s = nullptr, * t = nullptr;
        if (m.is_eq(e, s, t))
            return expr_ref(m.mk_bool_val(eval0rec(s) == eval0rec(t)), m);
        if (m.is_distinct(e)) {
            expr_ref_vector args(m);
            for (auto arg : *to_app(e))
                args.push_back(eval0(arg));
            bool d = true;
            for (unsigned i = 0; i < args.size(); ++i)
                for (unsigned j = i + 1; i < args.size(); ++j)
                    d &= args.get(i) != args.get(j);
            return expr_ref(m.mk_bool_val(d), m);
        }
        if (dt.is_accessor(e, t)) {
            auto f = to_app(e)->get_decl();
            auto v = eval0rec(t);
            return eval_accessor(f, v);
        }
        if (dt.is_constructor(e)) {
            expr_ref_vector args(m);
            for (auto arg : *to_app(e))
                args.push_back(eval0rec(arg));
            return expr_ref(m.mk_app(to_app(e)->get_decl(), args), m);
        }
        if (dt.is_recognizer(e, t)) {
            auto v = eval0rec(t);
            SASSERT(dt.is_constructor(v));
            auto c = dt.get_recognizer_constructor(to_app(e)->get_decl());
            return expr_ref(m.mk_bool_val(c == to_app(v)->get_decl()), m);
        }
        return eval0(e);
    }

    expr_ref datatype_plugin::eval0rec(expr* e) {
        auto v = m_eval.get(e->get_id(), nullptr);
        if (v)
            return expr_ref(v, m);
        if (!is_app(e) || to_app(e)->get_family_id() != m_fid)
            return ctx.get_value(e);
        auto w = eval1(e);
        m_eval.setx(e->get_id(), w);
        return w;
    }

    expr_ref datatype_plugin::eval_accessor(func_decl* f, expr* t) {
        auto& t2val = m_eval_accessor[f];
        if (!t2val.contains(t)) {
            if (!m_model)
                m_model = alloc(model, m);
            auto val = m_model->get_some_value(f->get_range());
            m.inc_ref(t);
            m.inc_ref(val);
            t2val.insert(t, val);
        }
        return expr_ref(t2val[t], m);
    }

    void datatype_plugin::update_eval_accessor(app* e, expr* t, expr* value) {
        func_decl* f = e->get_decl();
        
        auto& t2val = m_eval_accessor[f];
        expr* old_value = nullptr;
        t2val.find(t, old_value);
        if (old_value == value)
            ;
        else if (old_value) {
            t2val[t] = value;
            m.inc_ref(value);
            m.dec_ref(old_value);
        }
        else {
            m.inc_ref(t);
            m.inc_ref(value);
            t2val.insert(t, value);
        }        

        for (expr* b : m_occurs[f]) {
            if (b == e)
                continue;
            expr* a = nullptr;
            VERIFY(dt.is_accessor(b, a));
            auto v_a = eval0(a);
            if (v_a.get() == t) {
                set_eval0(b, value);
                ctx.new_value_eh(b);
            }
        }
    }

    void datatype_plugin::del_eval_accessor() {
        ptr_vector<expr> kv;
        for (auto& [f, t2val] : m_eval_accessor)
            for (auto& [k, val] : t2val)
                kv.push_back(k), kv.push_back(val);
        for (auto k : kv)
            m.dec_ref(k);
    }

    expr_ref datatype_plugin::eval0(expr* n) {
        if (!dt.is_datatype(n->get_sort()))
            return ctx.get_value(n);
        auto v = m_eval.get(n->get_id(), nullptr);
        if (v)
            return expr_ref(v, m);
        set_eval0(n, m_model->get_some_value(n->get_sort()));
        return expr_ref(m_eval.get(n->get_id()), m);
    }

    void datatype_plugin::set_eval0(expr* e, expr* value) {
        if (dt.is_datatype(e->get_sort()))
            m_eval.setx(e->get_id(), value);
        else
            ctx.set_value(e, value);
    }

    expr_ref datatype_plugin::eval0(euf::enode* n) {
        return eval0(n->get_root()->get_expr());
    }
        
    void datatype_plugin::collect_statistics(statistics& st) const {
        st.update("sls-dt-axioms", m_axioms.size());
        st.update("sls-dt-occurs-conflicts", m_stats.m_num_occurs);
    }
    
    void datatype_plugin::reset_statistics() {}
    
}
