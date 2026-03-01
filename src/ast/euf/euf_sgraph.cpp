/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    euf_sgraph.cpp

Abstract:

    Sequence/string graph implementation

Author:

    Nikolaj Bjorner (nbjorner) 2025-03-01

--*/

#include "ast/euf/euf_sgraph.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"

namespace euf {

    sgraph::sgraph(ast_manager& m):
        m(m),
        m_seq(m),
        m_exprs(m) {
    }

    sgraph::~sgraph() {
    }

    snode_kind sgraph::classify(expr* e) const {
        if (!is_app(e))
            return snode_kind::s_other;

        if (m_seq.str.is_empty(e))
            return snode_kind::s_empty;

        if (m_seq.str.is_string(e)) {
            zstring s;
            if (m_seq.str.is_string(e, s) && s.empty())
                return snode_kind::s_empty;
            return snode_kind::s_other;
        }

        if (m_seq.str.is_concat(e))
            return snode_kind::s_concat;

        if (m_seq.str.is_unit(e)) {
            expr* ch = to_app(e)->get_arg(0);
            if (m_seq.is_const_char(ch))
                return snode_kind::s_char;
            return snode_kind::s_unit;
        }

        if (m_seq.str.is_power(e))
            return snode_kind::s_power;

        if (m_seq.re.is_star(e))
            return snode_kind::s_star;

        if (m_seq.re.is_loop(e))
            return snode_kind::s_loop;

        if (m_seq.re.is_union(e))
            return snode_kind::s_union;

        if (m_seq.re.is_intersection(e))
            return snode_kind::s_intersect;

        if (m_seq.re.is_complement(e))
            return snode_kind::s_complement;

        if (m_seq.re.is_empty(e))
            return snode_kind::s_fail;

        if (m_seq.re.is_full_char(e))
            return snode_kind::s_full_char;

        if (m_seq.re.is_full_seq(e))
            return snode_kind::s_full_seq;

        if (m_seq.re.is_to_re(e))
            return snode_kind::s_to_re;

        if (m_seq.str.is_in_re(e))
            return snode_kind::s_in_re;

        // uninterpreted constants of string sort are variables
        if (is_uninterp_const(e) && m_seq.is_seq(e->get_sort()))
            return snode_kind::s_var;

        return snode_kind::s_other;
    }

    void sgraph::compute_metadata(snode* n) {
        switch (n->m_kind) {
        case snode_kind::s_empty:
            n->m_ground = true;
            n->m_regex_free = true;
            n->m_nullable = true;
            n->m_level = 0;
            n->m_length = 0;
            break;

        case snode_kind::s_char:
            n->m_ground = true;
            n->m_regex_free = true;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_var:
            n->m_ground = false;
            n->m_regex_free = true;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_unit:
            n->m_ground = n->num_args() > 0 ? n->arg(0)->is_ground() : true;
            n->m_regex_free = true;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_concat: {
            SASSERT(n->num_args() == 2);
            snode* l = n->arg(0);
            snode* r = n->arg(1);
            n->m_ground = l->is_ground() && r->is_ground();
            n->m_regex_free = l->is_regex_free() && r->is_regex_free();
            n->m_nullable = l->is_nullable() && r->is_nullable();
            n->m_level = std::max(l->level(), r->level()) + 1;
            n->m_length = l->length() + r->length();
            ++m_stats.m_num_concat;
            break;
        }

        case snode_kind::s_power: {
            SASSERT(n->num_args() >= 1);
            snode* base = n->arg(0);
            n->m_ground = base->is_ground();
            n->m_regex_free = base->is_regex_free();
            n->m_nullable = base->is_nullable();
            n->m_level = 1;
            n->m_length = 1;
            ++m_stats.m_num_power;
            break;
        }

        case snode_kind::s_star:
            SASSERT(n->num_args() == 1);
            n->m_ground = n->arg(0)->is_ground();
            n->m_regex_free = false;
            n->m_nullable = true;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_loop:
            n->m_ground = n->num_args() > 0 ? n->arg(0)->is_ground() : true;
            n->m_regex_free = false;
            n->m_nullable = false; // depends on lower bound
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_union:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();
            n->m_regex_free = false;
            n->m_nullable = n->arg(0)->is_nullable() || n->arg(1)->is_nullable();
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_intersect:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();
            n->m_regex_free = false;
            n->m_nullable = n->arg(0)->is_nullable() && n->arg(1)->is_nullable();
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_complement:
            SASSERT(n->num_args() == 1);
            n->m_ground = n->arg(0)->is_ground();
            n->m_regex_free = false;
            n->m_nullable = !n->arg(0)->is_nullable();
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_fail:
            n->m_ground = true;
            n->m_regex_free = false;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_full_char:
            n->m_ground = true;
            n->m_regex_free = false;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_full_seq:
            n->m_ground = true;
            n->m_regex_free = false;
            n->m_nullable = true;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_to_re:
            SASSERT(n->num_args() == 1);
            n->m_ground = n->arg(0)->is_ground();
            n->m_regex_free = false;
            n->m_nullable = n->arg(0)->is_nullable();
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_in_re:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();
            n->m_regex_free = false;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        default:
            n->m_ground = true;
            n->m_regex_free = true;
            n->m_nullable = false;
            n->m_level = 1;
            n->m_length = 1;
            break;
        }
    }

    snode* sgraph::mk_snode(expr* e, snode_kind k, unsigned num_args, snode* const* args) {
        unsigned id = m_nodes.size();
        snode* n = snode::mk(m_region, e, k, id, num_args, args);
        compute_metadata(n);
        m_nodes.push_back(n);
        m_exprs.push_back(e);
        if (e) {
            unsigned eid = e->get_id();
            m_expr2snode.reserve(eid + 1, nullptr);
            m_expr2snode[eid] = n;
        }
        ++m_stats.m_num_nodes;
        return n;
    }

    snode* sgraph::mk(expr* e) {
        SASSERT(e);
        snode* n = find(e);
        if (n)
            return n;

        snode_kind k = classify(e);

        if (!is_app(e))
            return mk_snode(e, k, 0, nullptr);

        app* a = to_app(e);
        unsigned arity = a->get_num_args();

        // recursively register children that are sequences or regexes
        snode_vector child_nodes;
        for (unsigned i = 0; i < arity; ++i) {
            expr* ch = a->get_arg(i);
            if (m_seq.is_seq(ch) || m_seq.is_re(ch)) {
                snode* cn = mk(ch);
                child_nodes.push_back(cn);
            }
        }

        return mk_snode(e, k, child_nodes.size(), child_nodes.data());
    }

    snode* sgraph::find(expr* e) const {
        if (!e)
            return nullptr;
        unsigned eid = e->get_id();
        if (eid < m_expr2snode.size())
            return m_expr2snode[eid];
        return nullptr;
    }

    snode* sgraph::mk_empty(sort* s) {
        expr_ref e(m_seq.str.mk_empty(s), m);
        return mk(e);
    }

    snode* sgraph::mk_concat(snode* a, snode* b) {
        SASSERT(a && b);
        if (a->is_empty()) return b;
        if (b->is_empty()) return a;
        expr_ref e(m_seq.str.mk_concat(a->get_expr(), b->get_expr()), m);
        snode* n = find(e);
        if (n) return n;
        snode* args[2] = { a, b };
        return mk_snode(e, snode_kind::s_concat, 2, args);
    }

    snode* sgraph::mk_power(snode* base, snode* exp) {
        SASSERT(base && exp);
        expr_ref e(m_seq.str.mk_power(base->get_expr(), exp->get_expr()), m);
        snode* n = find(e);
        if (n) return n;
        snode* args[2] = { base, exp };
        return mk_snode(e, snode_kind::s_power, 2, args);
    }

    void sgraph::push() {
        m_scopes.push_back(m_nodes.size());
        ++m_num_scopes;
    }

    void sgraph::pop(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        SASSERT(num_scopes <= m_num_scopes);
        unsigned new_lvl = m_num_scopes - num_scopes;
        unsigned old_sz = m_scopes[new_lvl];
        for (unsigned i = m_nodes.size(); i-- > old_sz; ) {
            snode* n = m_nodes[i];
            if (n->get_expr()) {
                unsigned eid = n->get_expr()->get_id();
                if (eid < m_expr2snode.size())
                    m_expr2snode[eid] = nullptr;
            }
        }
        m_nodes.shrink(old_sz);
        m_exprs.shrink(old_sz);
        m_scopes.shrink(new_lvl);
        m_num_scopes = new_lvl;
    }

    std::ostream& sgraph::display(std::ostream& out) const {
        auto kind_str = [](snode_kind k) -> char const* {
            switch (k) {
            case snode_kind::s_empty:      return "empty";
            case snode_kind::s_char:       return "char";
            case snode_kind::s_var:        return "var";
            case snode_kind::s_unit:       return "unit";
            case snode_kind::s_concat:     return "concat";
            case snode_kind::s_power:      return "power";
            case snode_kind::s_star:       return "star";
            case snode_kind::s_loop:       return "loop";
            case snode_kind::s_union:      return "union";
            case snode_kind::s_intersect:  return "intersect";
            case snode_kind::s_complement: return "complement";
            case snode_kind::s_fail:       return "fail";
            case snode_kind::s_full_char:  return "full_char";
            case snode_kind::s_full_seq:   return "full_seq";
            case snode_kind::s_to_re:      return "to_re";
            case snode_kind::s_in_re:      return "in_re";
            case snode_kind::s_other:      return "other";
            }
            return "?";
        };
        for (snode* n : m_nodes) {
            out << "snode[" << n->id() << "] "
                << kind_str(n->kind())
                << " level=" << n->level()
                << " len=" << n->length()
                << " ground=" << n->is_ground()
                << " rfree=" << n->is_regex_free()
                << " nullable=" << n->is_nullable();
            if (n->num_args() > 0) {
                out << " args=(";
                for (unsigned i = 0; i < n->num_args(); ++i) {
                    if (i > 0) out << ", ";
                    out << n->arg(i)->id();
                }
                out << ")";
            }
            if (n->get_expr())
                out << " expr=" << mk_pp(n->get_expr(), m);
            out << "\n";
        }
        return out;
    }

    void sgraph::collect_statistics(statistics& st) const {
        st.update("seq-graph-nodes", m_stats.m_num_nodes);
        st.update("seq-graph-concat", m_stats.m_num_concat);
        st.update("seq-graph-power", m_stats.m_num_power);
    }

}

