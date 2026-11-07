/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    array_map_coherence.h

Abstract:

    Check finite-support array definitions involving map.

--*/
#pragma once

#include "ast/array_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/lbool.h"
#include "util/scoped_ptr_vector.h"

// A definition gives an array's value outside a finite set of store indices.
// Follow definitions, not just roots, to retain the equalities that justify
// substituting an equivalent array into a store or map.
template <typename Node, typename Internalize, typename Select, typename Propagate>
lbool check_array_map_coherence(ast_manager& m, ptr_vector<Node> const& nodes,
                                Internalize&& internalize, Select&& select, Propagate&& propagate) {
    array_util a(m);
    bool has_map = false, has_const = false;
    for (Node* n : nodes) {
        has_map |= a.is_map(n->get_expr());
        has_const |= a.is_const(n->get_expr());
    }
    if (!has_map || !has_const)
        return l_true;

    struct definition {
        Node* node;
        expr_ref value;
        ptr_vector<definition> args;
        bool has_map;
        definition(Node* n, expr* v, ast_manager& m, bool has_map) :
            node(n), value(v, m), has_map(has_map) {}
    };
    using eq_vector = svector<std::pair<Node*, Node*>>;
    scoped_ptr_vector<definition> definitions;
    obj_map<Node, definition*> values;
    obj_map<Node, ptr_vector<Node>> parents;
    ptr_vector<Node> todo;
    obj_hashtable<Node> processed;
    for (Node* n : nodes) {
        expr* e = n->get_expr();
        if (a.is_const(e))
            todo.push_back(n);
        else if (a.is_store(e))
            parents.insert_if_not_there(n->get_arg(0)->get_root(), ptr_vector<Node>()).push_back(n);
        else if (a.is_map(e))
            for (unsigned i = 0; i < to_app(e)->get_num_args(); ++i)
                parents.insert_if_not_there(n->get_arg(i)->get_root(), ptr_vector<Node>()).push_back(n);
    }

    auto add_eq = [](Node* n1, Node* n2, eq_vector& eqs) {
        if (n1 != n2) {
            SASSERT(n1->get_root() == n2->get_root());
            eqs.push_back({n1, n2});
        }
    };
    auto collect = [&](definition* d1, definition* d2, ptr_vector<Node>& indices, eq_vector& eqs) {
        ptr_vector<definition> pending;
        obj_hashtable<Node> visited;
        pending.push_back(d1);
        pending.push_back(d2);
        for (unsigned i = 0; i < pending.size(); ++i) {
            definition* d = pending[i];
            if (!visited.insert_if_not_there(d->node))
                continue;
            for (unsigned j = 0; j < d->args.size(); ++j) {
                add_eq(d->node->get_arg(j), d->args[j]->node, eqs);
                pending.push_back(d->args[j]);
            }
            if (!a.is_store(d->node->get_expr()))
                continue;
            unsigned arity = get_array_arity(d->node->get_expr()->get_sort());
            Node* old = nullptr;
            for (Node* s : indices) {
                unsigned k = 1;
                for (; k <= arity; ++k)
                    if (s->get_arg(k)->get_root() != d->node->get_arg(k)->get_root())
                        break;
                if (k > arity) {
                    old = s;
                    break;
                }
            }
            if (!old)
                indices.push_back(d->node);
            else
                for (unsigned k = 1; k <= arity; ++k)
                    add_eq(old->get_arg(k), d->node->get_arg(k), eqs);
        }
        add_eq(d1->node, d2->node, eqs);
    };

    th_rewriter rw(m);
    bool has_uninterpreted = false;
    for (unsigned qhead = 0; qhead < todo.size(); ++qhead) {
        if (!m.inc())
            return l_undef;
        Node* n = todo[qhead];
        if (processed.contains(n))
            continue;
        expr* e = n->get_expr();
        ptr_vector<definition> args;
        unsigned num_args = a.is_store(e) ? 1 : a.is_map(e) ? to_app(e)->get_num_args() : 0;
        for (unsigned i = 0; i < num_args; ++i) {
            definition* arg = nullptr;
            if (!values.find(n->get_arg(i)->get_root(), arg))
                break;
            args.push_back(arg);
        }
        if (args.size() != num_args)
            continue;
        processed.insert(n);
        expr_ref value(m);
        bool uses_map = a.is_map(e);
        if (a.is_const(e))
            value = n->get_arg(0)->get_expr();
        else if (a.is_store(e))
            value = args[0]->value;
        else {
            ptr_buffer<expr> values;
            for (definition* arg : args)
                values.push_back(arg->value);
            value = m.mk_app(a.get_map_func_decl(to_app(e)), values.size(), values.data());
            rw(value);
        }
        for (definition* arg : args)
            uses_map |= arg->has_map;
        definition* d = alloc(definition, n, value, m, uses_map);
        d->args.append(args);
        definitions.push_back(d);
        definition* old = nullptr;
        if (!values.find(n->get_root(), old)) {
            values.insert(n->get_root(), d);
            ptr_vector<Node> ps;
            if (parents.find(n->get_root(), ps))
                todo.append(ps);
            continue;
        }
        if ((!d->has_map && !old->has_map) || d->value == old->value)
            continue;

        ptr_vector<Node> indices;
        eq_vector eqs;
        collect(d, old, indices, eqs);
        // Equal arrays must agree on their computed values outside the union
        // of stores, but that union may cover an entire finite domain.
        sort* s = e->get_sort();
        uint64_t domain_size = 1;
        bool exceeds = false, uninterpreted = false;
        for (unsigned i = 0; i < get_array_arity(s); ++i) {
            sort* domain = get_array_domain(s, i);
            if (m.is_uninterp(domain)) {
                uninterpreted = true;
                continue;
            }
            sort_size const& size = domain->get_num_elements();
            if (!size.is_finite() || size.size() > indices.size() ||
                domain_size > indices.size() / size.size()) {
                exceeds = true;
                break;
            }
            domain_size *= size.size();
        }
        if (exceeds || domain_size > indices.size()) {
            bool is_new = false;
            Node* v1 = internalize(d->value, is_new);
            Node* v2 = internalize(old->value, is_new);
            if (v1->get_root() != v2->get_root()) {
                propagate(eqs, v1, v2);
                return l_false;
            }
            if (is_new)
                return l_false;
        }
        else {
            bool is_new = false;
            for (Node* store : indices) {
                ptr_buffer<expr> idx;
                for (unsigned i = 0; i < get_array_arity(s); ++i)
                    idx.push_back(store->get_arg(i + 1)->get_expr());
                is_new |= select(n, idx.size(), idx.data());
            }
            if (is_new)
                return l_false;
            has_uninterpreted |= uninterpreted;
        }
    }
    return has_uninterpreted ? l_undef : l_true;
}
