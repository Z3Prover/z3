/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_sgraph.cpp

Abstract:

    Sequence/string graph implementation

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01
    Clemens Eisenhofer 2026-03-01

--*/

#include "ast/euf/euf_sgraph.h"
#include "ast/euf/euf_seq_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"

namespace euf {

    sgraph::sgraph(ast_manager& m):
        m(m),
        m_seq(m),
        m_rewriter(m),
        m_egraph(m),
        m_exprs(m),
        m_str_sort(m_seq.str.mk_string_sort(), m) {
        // create seq_plugin and register it with the egraph
        m_egraph.add_plugin(alloc(seq_plugin, m_egraph));
        // register on_make callback so sgraph creates snodes for new enodes
        std::function<void(enode*)> on_make = [this](enode* n) {
            expr* e = n->get_expr();
            if (m_seq.is_seq(e) || m_seq.is_re(e))
                mk(e);
        };
        m_egraph.set_on_make(on_make);
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
            // s^n: nullable follows base, consistent with ZIPT's PowerToken
            // the exponent n is assumed to be a symbolic integer, may or may not be zero
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

        // recursively register children
        // for seq/re children, create classified snodes
        // for other children (e.g. integer exponents), create s_other snodes
        snode_vector child_nodes;
        for (unsigned i = 0; i < arity; ++i) {
            expr* ch = a->get_arg(i);
            snode* cn = mk(ch);
            child_nodes.push_back(cn);
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

    enode* sgraph::mk_enode(expr* e) {
        enode* n = m_egraph.find(e);
        if (n) return n;
        enode_vector args;
        if (is_app(e)) {
            for (expr* arg : *to_app(e)) {
                enode* a = mk_enode(arg);
                args.push_back(a);
            }
        }
        return m_egraph.mk(e, 0, args.size(), args.data());
    }

    void sgraph::push() {
        m_scopes.push_back(m_nodes.size());
        ++m_num_scopes;
        m_egraph.push();
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
        m_egraph.pop(num_scopes);
    }

    snode* sgraph::mk_var(symbol const& name) {
        expr_ref e(m.mk_const(name, m_str_sort), m);
        return mk(e);
    }

    snode* sgraph::mk_char(unsigned ch) {
        expr_ref c(m_seq.str.mk_char(ch), m);
        expr_ref u(m_seq.str.mk_unit(c), m);
        return mk(u);
    }

    snode* sgraph::mk_empty() {
        expr_ref e(m_seq.str.mk_empty(m_str_sort), m);
        return mk(e);
    }

    snode* sgraph::mk_concat(snode* a, snode* b) {
        if (a->is_empty()) return b;
        if (b->is_empty()) return a;
        expr_ref e(m_seq.str.mk_concat(a->get_expr(), b->get_expr()), m);
        return mk(e);
    }

    snode* sgraph::drop_first(snode* n) {
        if (n->is_empty() || n->is_token())
            return mk_empty();
        SASSERT(n->is_concat());
        snode* l = n->arg(0);
        snode* r = n->arg(1);
        if (l->is_token() || l->is_empty())
            return r;
        return mk_concat(drop_first(l), r);
    }

    snode* sgraph::drop_last(snode* n) {
        if (n->is_empty() || n->is_token())
            return mk_empty();
        SASSERT(n->is_concat());
        snode* l = n->arg(0);
        snode* r = n->arg(1);
        if (r->is_token() || r->is_empty())
            return l;
        return mk_concat(l, drop_last(r));
    }

    snode* sgraph::drop_left(snode* n, unsigned count) {
        for (unsigned i = 0; i < count && !n->is_empty(); ++i)
            n = drop_first(n);
        return n;
    }

    snode* sgraph::drop_right(snode* n, unsigned count) {
        for (unsigned i = 0; i < count && !n->is_empty(); ++i)
            n = drop_last(n);
        return n;
    }

    snode* sgraph::subst(snode* n, snode* var, snode* replacement) {
        if (n == var)
            return replacement;
        if (n->is_empty() || n->is_char())
            return n;
        if (n->is_concat())
            return mk_concat(subst(n->arg(0), var, replacement),
                             subst(n->arg(1), var, replacement));
        // for non-concat compound nodes (power, star, etc.), no substitution into children
        return n;
    }

    snode* sgraph::brzozowski_deriv(snode* re, snode* elem) {
        expr* re_expr = re->get_expr();
        expr* elem_expr = elem->get_expr();
        if (!re_expr || !elem_expr)
            return nullptr;
        // unwrap str.unit to get the character expression
        expr* ch = nullptr;
        if (m_seq.str.is_unit(elem_expr, ch))
            elem_expr = ch;
        expr_ref result = m_rewriter.mk_derivative(elem_expr, re_expr);
        if (!result)
            return nullptr;
        return mk(result);
    }

    void sgraph::collect_re_predicates(snode* re, expr_ref_vector& preds) {
        if (!re || !re->get_expr())
            return;
        expr* e = re->get_expr();
        expr* ch = nullptr, *lo = nullptr, *hi = nullptr;
        // leaf regex predicates: character ranges and single characters
        if (m_seq.re.is_range(e, lo, hi)) {
            preds.push_back(e);
            return;
        }
        if (m_seq.re.is_to_re(e))
            return;
        if (m_seq.re.is_full_char(e))
            return;
        if (m_seq.re.is_full_seq(e))
            return;
        if (m_seq.re.is_empty(e))
            return;
        // recurse into compound regex operators
        for (unsigned i = 0; i < re->num_args(); ++i)
            collect_re_predicates(re->arg(i), preds);
    }

    void sgraph::compute_minterms(snode* re, snode_vector& minterms) {
        // extract character predicates from the regex
        expr_ref_vector preds(m);
        collect_re_predicates(re, preds);
        if (preds.empty()) {
            // no predicates means the whole alphabet is one minterm
            // represented by full_char
            expr_ref fc(m_seq.re.mk_full_char(m_str_sort), m);
            minterms.push_back(mk(fc));
            return;
        }
        // generate minterms as conjunctions/negations of predicates
        // for n predicates, there are up to 2^n minterms
        unsigned n = preds.size();
        for (unsigned mask = 0; mask < (1u << n); ++mask) {
            expr_ref_vector conj(m);
            for (unsigned i = 0; i < n; ++i) {
                if (mask & (1u << i))
                    conj.push_back(preds.get(i));
                else
                    conj.push_back(m_seq.re.mk_complement(preds.get(i)));
            }
            // intersect all terms
            expr_ref mt(conj.get(0), m);
            for (unsigned i = 1; i < conj.size(); ++i)
                mt = m_seq.re.mk_inter(mt, conj.get(i));
            minterms.push_back(mk(mt));
        }
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
        st.update("seq-graph-hash-hits", m_stats.m_num_hash_hits);
        m_egraph.collect_statistics(st);
    }

}

