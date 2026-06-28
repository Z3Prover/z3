/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_sgraph.cpp

Abstract:

    Sequence/string graph implementation

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/

#include "ast/euf/euf_sgraph.h"
#include "ast/euf/euf_seq_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_pp.h"

namespace euf {

    sgraph::sgraph(ast_manager& m, egraph& eg, bool add_plugin):
        m(m),
        m_seq(m),
        m_rewriter(m),
        m_th_rewriter(m),
        m_sk(m, m_th_rewriter),
        m_egraph(eg),
        m_str_sort(m_seq.str.mk_string_sort(), m),
        m_pin(m) {
        // create seq_plugin and register it with the egraph
        if (add_plugin)
            m_egraph.add_plugin(alloc(seq_plugin, m_egraph, this));
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
            return snode_kind::s_var;
        if (m_seq.str.is_empty(e))
            return snode_kind::s_empty;

        {
            zstring s;
            if (m_seq.str.is_string(e, s))
                return s.empty() ? snode_kind::s_empty : snode_kind::s_var;
        }

        if (m_seq.str.is_concat(e) || m_seq.re.is_concat(e))
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

        if (m_seq.re.is_plus(e))
            return snode_kind::s_plus;

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

        if (m_seq.re.is_range(e))
            return snode_kind::s_range;

        if (m.is_ite(e))
            return snode_kind::s_ite;

        if (m_seq.re.is_to_re(e))
            return snode_kind::s_to_re;

        if (m_seq.str.is_in_re(e))
            return snode_kind::s_in_re;

        return snode_kind::s_var;
    }

    void sgraph::compute_metadata(snode* n) {
        switch (n->m_kind) {
        case snode_kind::s_empty:
            n->m_ground = true;
            n->m_regex_free = true;
            n->m_level = 0;
            n->m_length = 0;
            break;

        case snode_kind::s_char:
            n->m_ground = true;
            n->m_regex_free = true;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_var:
            // NSB review: a variable node can be a "value". Should it be ground then?
            n->m_ground = false;
            n->m_regex_free = true;
            n->m_level = 1;
            n->m_length = 1;
            n->m_is_classical = false;
            // Defined seq operations (str.replace*, str.replace_all, str.replace_re*) are
            // classified as s_var because they have no dedicated snode kind, but they are NOT
            // free variables: their value is fixed by the recfun/axiom layer. Mark them rigid
            // so the Nielsen modifiers never eliminate or split them (see snode::is_rigid).
            {
                expr* e = n->m_expr;
                n->m_rigid = e && (m_seq.str.is_replace(e) || m_seq.str.is_replace_all(e) ||
                                   m_seq.str.is_replace_re(e) || m_seq.str.is_replace_re_all(e));
            }
            break;

        case snode_kind::s_unit:
            // NSB review: SASSERT(n->num_args() == 1); and simplify code
            n->m_ground = n->num_args() > 0 ? n->arg(0)->is_ground() : true;
            n->m_regex_free = true;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_concat: {
            SASSERT(n->num_args() == 2);
            const snode* l = n->arg(0);
            const snode* r = n->arg(1);
            n->m_ground = l->is_ground() && r->is_ground();
            n->m_regex_free = l->is_regex_free() && r->is_regex_free();
            n->m_is_classical = l->is_classical() && r->is_classical();
            n->m_level = std::max(l->level(), r->level()) + 1;
            n->m_length = l->length() + r->length();
            ++m_stats.m_num_concat;
            break;
        }

        case snode_kind::s_power: {
            // s^n: nullable follows base, consistent with ZIPT's PowerToken
            // the exponent n is assumed to be a symbolic integer, may or may not be zero
            // NSB review: SASSERT(n->num_args() == 2); and simplify code       
            // NSB review: is this the correct definition of ground what about the exponent?
            SASSERT(n->num_args() >= 1);
            snode const* base = n->arg(0);
            n->m_ground = base->is_ground();
            n->m_regex_free = base->is_regex_free();
            n->m_is_classical = base->is_classical();
            n->m_level = 1;
            n->m_length = 1;
            ++m_stats.m_num_power;
            break;
        }

        case snode_kind::s_star:
        case snode_kind::s_plus:
            SASSERT(n->num_args() == 1);
            n->m_ground = n->arg(0)->is_ground();
            n->m_regex_free = false;
            n->m_is_classical = n->arg(0)->is_classical();
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_loop: {
            n->m_ground = n->num_args() > 0 ? n->arg(0)->is_ground() : true;
            n->m_regex_free = false;
            // nullable iff lower bound is 0: r{0,n} accepts the empty string
            n->m_is_classical = n->arg(0)->is_classical();
            // default lo=1 (non-nullable) in case extraction fails
            unsigned lo = 1, hi = 1;
            expr* loop_body = nullptr;
            // try bounded r{lo,hi} first; fall back to unbounded r{lo,}
            if (n->get_expr() &&
                !m_seq.re.is_loop(n->get_expr(), loop_body, lo, hi))
                m_seq.re.is_loop(n->get_expr(), loop_body, lo);
            n->m_level = 1;
            n->m_length = 1;
            break;
        }

        case snode_kind::s_union:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();
            n->m_regex_free = false;
            n->m_is_classical = n->arg(0)->is_classical() && n->arg(1)->is_classical();
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_intersect:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();     
            n->m_regex_free = false;
            n->m_is_classical = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_complement:
            SASSERT(n->num_args() == 1);
            n->m_ground = n->arg(0)->is_ground();
            n->m_regex_free = false;
            n->m_is_classical = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_fail:
            n->m_ground = true;
            n->m_regex_free = false;
            n->m_is_classical = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_full_char:
            n->m_ground = true;
            n->m_regex_free = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_full_seq:
            n->m_ground = true;
            n->m_regex_free = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_range:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();
            n->m_regex_free = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_ite:
            SASSERT(n->num_args() == 3);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground() && n->arg(2)->is_ground();
            n->m_regex_free = n->arg(1)->is_regex_free() && n->arg(2)->is_regex_free();
            n->m_is_classical = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_to_re:
            SASSERT(n->num_args() == 1);
            n->m_ground = n->arg(0)->is_ground();
            n->m_regex_free = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        case snode_kind::s_in_re:
            SASSERT(n->num_args() == 2);
            n->m_ground = n->arg(0)->is_ground() && n->arg(1)->is_ground();
            n->m_regex_free = false;
            n->m_level = 1;
            n->m_length = 1;
            break;

        default:
            // NSB review: is this the correct defaults for unclassified nodes?
            // Is this UNREACHABLE()?
            n->m_ground = true;
            n->m_regex_free = true;
            n->m_level = 1;
            n->m_length = 1;
            break;
        }
    }

    static constexpr unsigned HASH_BASE = 31;

    // Compute a 2x2 polynomial hash matrix for associativity-respecting hashing.
    // Unsigned overflow is intentional and well-defined (mod 2^32).
    // M[0][0] tracks HASH_BASE^(num_leaves), which is always nonzero since
    // HASH_BASE is odd. M[0][1] is the actual hash value.
    void sgraph::compute_hash_matrix(snode* n) {
        if (n->is_empty()) {
            // identity matrix: concat with empty is identity
            n->m_hash_matrix[0][0] = 1;
            n->m_hash_matrix[0][1] = 0;
            n->m_hash_matrix[1][0] = 0;
            n->m_hash_matrix[1][1] = 1;
        }
        else if (n->is_concat()) {
            snode const* l = n->arg(0);
            snode const* r = n->arg(1);
            if (l->has_cached_hash() && r->has_cached_hash()) {
                // 2x2 matrix multiplication: M(L) * M(R)
                n->m_hash_matrix[0][0] = l->m_hash_matrix[0][0] * r->m_hash_matrix[0][0] + l->m_hash_matrix[0][1] * r->m_hash_matrix[1][0];
                n->m_hash_matrix[0][1] = l->m_hash_matrix[0][0] * r->m_hash_matrix[0][1] + l->m_hash_matrix[0][1] * r->m_hash_matrix[1][1];
                n->m_hash_matrix[1][0] = l->m_hash_matrix[1][0] * r->m_hash_matrix[0][0] + l->m_hash_matrix[1][1] * r->m_hash_matrix[1][0];
                n->m_hash_matrix[1][1] = l->m_hash_matrix[1][0] * r->m_hash_matrix[0][1] + l->m_hash_matrix[1][1] * r->m_hash_matrix[1][1];
            }
        }
        else {
            // leaf/token: [[HASH_BASE, value], [0, 1]]
            // +1 avoids zero hash values; wraps safely on unsigned overflow
            // for slices it is the same as its parent
            expr* e = n->get_expr();
            SASSERT(e);
            unsigned v;
            if (m_sk.is_slice(e)) {
                do {
                    // get root variable
                    e = to_app(e)->get_arg(0);
                } while (m_sk.is_slice(e));
                v = e->get_id();
            }
            else
                v = e->get_id() + 1;

            n->m_hash_matrix[0][0] = HASH_BASE;
            n->m_hash_matrix[0][1] = v;
            n->m_hash_matrix[1][0] = 0;
            n->m_hash_matrix[1][1] = 1;
        }
    }

    snode* sgraph::mk_snode(expr *e, const snode_kind k, const unsigned num_args, snode const** args) {
        SASSERT(e);
        const unsigned id = m_nodes.size();
        snode *n = snode::mk(m_region, e, k, id, num_args, args);
        compute_metadata(n);
        compute_hash_matrix(n);
        m_nodes.push_back(n);
        SASSERT(!n->is_char_or_unit() || m_seq.str.is_unit(n->get_expr()));
        unsigned eid = e->get_id();
        m_expr2snode.reserve(eid + 1, nullptr);
        m_expr2snode[eid] = n;
        // Pin the expression for the lifetime of the sgraph: the egraph trail
        // would otherwise release it on pop, but the underlying snode lives in
        // m_region (never freed) and may still be referenced by clients past
        // that pop.  See the comment on m_pin in euf_sgraph.h.
        m_pin.push_back(e);
        // also keep the enode pinning behaviour so congruence closure sees e
        mk_enode(e);
        ++m_stats.m_num_nodes;
        return n;
    }

    snode const* sgraph::mk(expr* e) {
        SASSERT(e);
        expr_ref _e(e, m); // pin locally to not clash with character creation, never needed if we use mk_enode early.
        snode const* n = find(e);
        if (n)
            return n;

        // decompose non-empty string constants into character chains
        // so that Nielsen graph can do prefix matching on them
        zstring s;
        if (m_seq.str.is_string(e, s) && !s.empty()) {
            snode const* result = mk_char(s[s.length() - 1]);
            for (unsigned i = s.length() - 1; i-- > 0; )
                result = mk_concat(mk_char(s[i]), result);
            // register the original string expression as an alias
            unsigned eid = e->get_id();
            m_expr2snode.reserve(eid + 1, nullptr);
            m_expr2snode[eid] = result;
            m_alias_trail.push_back(eid);
            mk_enode(e);
            return result;
        }

        const snode_kind k = classify(e);

        if (!is_app(e))
            return mk_snode(e, k, 0, nullptr);

        app* a = to_app(e);
        const unsigned arity = a->get_num_args();

        // recursively register children
        // for seq/re children, create classified snodes
        // for other children, e.g. integer exponents, create s_var snodes
        snode_vector child_nodes;
        for (unsigned i = 0; i < arity; ++i) {
            expr* ch = a->get_arg(i);
            snode const* cn = mk(ch);
            child_nodes.push_back(cn);
        }

        return mk_snode(e, k, child_nodes.size(), child_nodes.data());
    }

    snode const* sgraph::find(expr* e) const {
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
        m_alias_trail_lim.push_back(m_alias_trail.size());
        ++m_num_scopes;
        m_egraph.push();
    }

    void sgraph::pop(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        SASSERT(num_scopes <= m_num_scopes);
        const unsigned new_lvl = m_num_scopes - num_scopes;
        const unsigned old_sz = m_scopes[new_lvl];

        for (unsigned i = m_nodes.size(); i-- > old_sz; ) {
            snode const* n = m_nodes[i];
            if (n->get_expr()) {
                const unsigned eid = n->get_expr()->get_id();
                if (eid < m_expr2snode.size())
                    m_expr2snode[eid] = nullptr;
            }
        }
        m_nodes.shrink(old_sz);
        m_scopes.shrink(new_lvl);
        // undo alias entries (string constant decompositions)
        const unsigned alias_old = m_alias_trail_lim[new_lvl];
        for (unsigned i = m_alias_trail.size(); i-- > alias_old; ) {
            const unsigned eid = m_alias_trail[i];
            if (eid < m_expr2snode.size())
                m_expr2snode[eid] = nullptr;
        }
        m_alias_trail.shrink(alias_old);
        m_alias_trail_lim.shrink(new_lvl);
        m_num_scopes = new_lvl;
        m_egraph.pop(num_scopes);
    }

    snode const* sgraph::mk_var(symbol const& name, sort* s) {
        const expr_ref e(m.mk_const(name, s), m);
        return mk(e);
    }

    snode const* sgraph::mk_char(unsigned ch) {
        const expr_ref c(m_seq.str.mk_char(ch), m);
        const expr_ref u(m_seq.str.mk_unit(c), m);
        return mk(u);
    }

    snode const* sgraph::mk_empty_seq(sort* s) {
        const expr_ref e(m_seq.str.mk_empty(s), m);
        return mk(e);
    }

    snode const* sgraph::mk_concat(snode const* a, snode const* b) {
        if (a->is_empty()) return b;
        if (b->is_empty()) return a;
        if (m_seq.is_re(a->get_expr()))
            return mk(expr_ref(m_seq.re.mk_concat(a->get_expr(), b->get_expr()), m));
        return mk(expr_ref(m_seq.str.mk_concat(a->get_expr(), b->get_expr()), m));
    }

    snode const* sgraph::drop_first(snode const* n) {
        if (n->is_empty() || n->is_token())
            return mk_empty_seq(n->get_sort());
        SASSERT(n->is_concat());
        snode const* l = n->arg(0);
        snode const* r = n->arg(1);
        if (l->is_token() || l->is_empty())
            return r;
        return mk_concat(drop_first(l), r);
    }

    snode const* sgraph::drop_last(snode const* n) {
        if (n->is_empty() || n->is_token())
            return mk_empty_seq(n->get_sort());
        SASSERT(n->is_concat());
        snode const* l = n->arg(0);
        snode const* r = n->arg(1);
        if (r->is_token() || r->is_empty())
            return l;
        return mk_concat(l, drop_last(r));
    }

    snode const* sgraph::drop_left(snode const* n, unsigned count) {
        if (count == 0 || n->is_empty()) return n;
        if (count >= n->length()) return mk_empty_seq(n->get_sort());
        SASSERT(n->is_concat());
        unsigned left_len = n->arg(0)->length();
        if (count < left_len)
            return mk_concat(drop_left(n->arg(0), count), n->arg(1));
        return drop_left(n->arg(1), count - left_len);
    }

    snode const* sgraph::drop_right(snode const * n, unsigned count) {
        if (count == 0 || n->is_empty()) return n;
        if (count >= n->length()) return mk_empty_seq(n->get_sort());
        SASSERT(n->is_concat());
        unsigned right_len = n->arg(1)->length();
        if (count < right_len)
            return mk_concat(n->arg(0), drop_right(n->arg(1), count));
        return drop_right(n->arg(0), count - right_len);
    }

    snode const* sgraph::subst(snode const* n, snode const* var, snode const* replacement) {
        if (n == var)
            return replacement;
        if (n->is_empty() || n->is_char())
            return n;
        if (n->is_concat()) {
            auto s1 = subst(n->arg(0), var, replacement);
            auto s2 = subst(n->arg(1), var, replacement);
            if (s1 != n->arg(0) || s2 != n->arg(1))
                return mk_concat(s1, s2);
            return n;
        }
        if (n->is_ite() && var->is_unit()) {
            // We only need to replace in case we are replacing units;
            // we would not generate any proper string replacements that  propagates into the ite
            auto s1 = subst(n->arg(0), var, replacement);
            auto s2 = subst(n->arg(1), var, replacement);
            auto s3 = subst(n->arg(2), var, replacement);
            if (s1 != n->arg(0) || s2 != n->arg(1) || s3 != n->arg(2))
                return mk(expr_ref(m.mk_ite(s1->get_expr(), s2->get_expr(), s3->get_expr()), m));
            return n;
        }
        // for non-concat compound nodes (power, star, etc.), no substitution into children
        // TODO: This might change in the future foe e.g., powers
        return n;
    }

    lbool sgraph::re_nullable(snode const* re) {
        if (!re)
            return l_undef;
        return m_seq.re.get_info(re->get_expr()).nullable;
    }

    snode const* sgraph::brzozowski_deriv(snode const* re, snode const* elem) {
        expr* re_expr = re->get_expr();
        expr* elem_expr = elem->get_expr();
        SASSERT(re_expr);
        SASSERT(elem_expr);
        // std::cout << "Derivative of " << seq::snode_label_html(re, m) << "\nwith respect to " << seq::snode_label_html(elem, m) << std::endl;
        // if (allowed_range)
        //     std::cout << "using " << seq::snode_label_html(allowed_range, m) << std::endl;

        // If it is a disjunction just take one of the elements
        while (m_seq.re.is_union(elem_expr)) {
            elem_expr = to_app(elem_expr)->get_arg(0);
        }

        // unwrap str.unit to get the character expression
        expr* ch = nullptr;
        if (m_seq.str.is_unit(elem_expr, ch))
            elem_expr = ch;

        // If an explicit allowed_range is provided (which is a regex minterm),
        // we extract a representative character (like 'lo') from it,
        // and evaluate the derivative with respect to that representative character.
        // This avoids generating massive 'ite' structures for symbolic variables.
        sort* seq_sort = nullptr, *ele_sort = nullptr;
        if (m_seq.is_re(re_expr, seq_sort) && m_seq.is_seq(seq_sort, ele_sort)) {
            if (ele_sort != elem_expr->get_sort()) {
                // std::cout << "Different sorts: " << ele_sort->get_name() << " vs " << elem_expr->get_sort()->get_name() << std::endl;
                expr* lo = nullptr, *hi = nullptr;
                if (m_seq.re.is_full_char(elem_expr)) {
                    elem_expr = m_seq.str.mk_char(0);
                }
                else if (m_seq.re.is_range(elem_expr, lo, hi) && lo) {
                    expr* lo_ch = nullptr;
                    zstring zs;
                    if (m_seq.str.is_unit(lo, lo_ch))
                        elem_expr = lo_ch;
                    else if (m_seq.str.is_string(lo, zs) && zs.length() > 0)
                        elem_expr = m_seq.str.mk_char(zs[0]);
                    else
                        elem_expr = lo;
                }
                else {
                    std::cout << "Unexpected node: " << mk_pp(elem_expr, m) << std::endl;
                    UNREACHABLE();
                }
            }
        }
        
        expr_ref result(m_rewriter.mk_derivative(elem_expr, re_expr), m);
        SASSERT(result);
        // Canonicalize with th_rewriter so that derivative states share a snode
        // id regardless of how they were reached (concrete vs. via a symbolic
        // ite resolved by apply_regex_if_split, which also th_rewrites its leaf).
        // Without this, semantically equal but syntactically different residuals
        // — notably intersections like (A∩B) vs (B∩A) or (a|∅)·R vs a·R — get
        // distinct ids, breaking partial-DFA Q-membership and view/guard lap
        // detection (the multi-cycle / intersection divergence).
        th_rewriter trw(m);
        trw(result);
        return mk(result);
    }

    bool sgraph::are_unit_distinct(snode const* a, snode const* b) const {
        return a->is_char_or_unit() && b->is_char_or_unit() && m.are_distinct(a->get_expr(), b->get_expr());
    }

    void sgraph::collect_re_predicates(snode const* re, expr_ref_vector& preds) {
        if (!re)
            return;
        expr* e = re->get_expr();
        SASSERT(e);
        expr* lo = nullptr, *hi = nullptr;
        // leaf regex predicates: character ranges and single characters
        if (m_seq.re.is_range(e, lo, hi)) {
            preds.push_back(e);
            return;
        }
        if (m_seq.re.is_to_re(e)) {
            expr* s = nullptr;
            if (m_seq.re.is_to_re(e, s)) {
                zstring zs;
                expr* ch_expr = nullptr;
                if (m_seq.str.is_string(s, zs) && zs.length() > 0) {
                    unsigned c = zs[0];
                    ch_expr = m_seq.str.mk_char(c);
                } else if (m_seq.str.is_unit(s, ch_expr)) {
                    // ch_expr correctly extracted
                }

                if (ch_expr) {
                    expr_ref unit_str(m_seq.str.mk_unit(ch_expr), m);
                    expr_ref re_char(m_seq.re.mk_to_re(unit_str), m);
                    bool dup = false;
                    for (expr* p : preds) {
                        if (p == re_char) { 
                            dup = true; 
                            break;
                        }
                    }
                    if (!dup)
                        preds.push_back(re_char);
                }
            }
            return;
        }
        if (m_seq.re.is_full_char(e))
            return;
        if (m_seq.re.is_full_seq(e))
            return;
        if (m_seq.re.is_empty(e))
            return;

        // Expected compound regex operators are handled by recursion below.
        // If a leaf survives to this point, it is an unhandled regex form.
        if (re->num_args() == 0) {
            UNREACHABLE();
            return;
        }

        // recurse into compound regex operators
        for (unsigned i = 0; i < re->num_args(); ++i) {
            collect_re_predicates(re->arg(i), preds);
        }
    }

    void sgraph::compute_minterms(snode const* re, snode_vector& minterms) {
        expr_ref_vector preds(m);
        collect_re_predicates(re, preds);
        
        const unsigned max_c = m_seq.max_char();

        if (preds.empty()) {
            const expr_ref fc(m_seq.re.mk_full_char(m_str_sort), m);
            minterms.push_back(mk(fc));
            return;
        }

        std::vector<char_set> classes;
        classes.push_back(char_set::full(max_c));

        for (expr* p : preds) {
            char_set p_set;
            expr* lo = nullptr, *hi = nullptr;
            
            if (m_seq.re.is_range(p, lo, hi)) {
                unsigned vlo = 0, vhi = 0;
                bool has_lo = false, has_hi = false;

                if (lo) {
                    if (decode_re_char(lo, vlo))
                        has_lo = true;
                }

                if (hi) {
                    if (decode_re_char(hi, vhi))
                        has_hi = true;
                }

                if (has_lo && has_hi && vlo <= vhi)
                    p_set = char_set(char_range(vlo, vhi + 1));
            } 
            else if (m_seq.re.is_to_re(p)) {
                expr* str_arg = nullptr;
                unsigned char_val = 0;
                if (m_seq.re.is_to_re(p, str_arg) &&
                    decode_re_char(str_arg, char_val)) {
                    p_set.add(char_val);
                }
            } 
            else if (m_seq.re.is_full_char(p))
                p_set = char_set::full(max_c);
            else {
                UNREACHABLE();
                continue;
            }
            
            if (p_set.is_empty() || p_set.is_full(max_c))
                continue;

            std::vector<char_set> next_classes;
            char_set p_comp = p_set.complement(max_c);
            for (auto const& c : classes) {
                char_set in_c = c.intersect_with(p_set);
                char_set out_c = c.intersect_with(p_comp);
                if (!in_c.is_empty()) next_classes.push_back(in_c);
                if (!out_c.is_empty()) next_classes.push_back(out_c);
            }
            classes = std::move(next_classes);
        }        
        for (auto const& c : classes) {
            expr_ref class_expr(m);
            for (auto const& r : c.ranges()) {
                zstring z_lo(r.m_lo);
                zstring z_hi(r.m_hi - 1);
                expr_ref c_lo(m_seq.str.mk_string(z_lo), m);
                expr_ref c_hi(m_seq.str.mk_string(z_hi), m);
                expr_ref range_expr(m_seq.re.mk_range(c_lo, c_hi), m);
                if (!class_expr)
                    class_expr = range_expr;
                else
                    class_expr = m_seq.re.mk_union(class_expr, range_expr);
            }
            if (class_expr)
                minterms.push_back(mk(class_expr));
        }
    }

    bool sgraph::decode_re_char(expr* ex, unsigned& out) const {
        if (!ex)
            return false;
        if (m_seq.is_const_char(ex, out))
            return true;
        expr* ch = nullptr;
        if (m_seq.str.is_unit(ex, ch) && m_seq.is_const_char(ch, out))
            return true;
        zstring s;
        if (m_seq.str.is_string(ex, s) && s.length() == 1) {
            out = s[0];
            return true;
        }
        return false;
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
            case snode_kind::s_plus:       return "plus";
            case snode_kind::s_loop:       return "loop";
            case snode_kind::s_union:      return "union";
            case snode_kind::s_intersect:  return "intersect";
            case snode_kind::s_complement: return "complement";
            case snode_kind::s_fail:       return "fail";
            case snode_kind::s_full_char:  return "full_char";
            case snode_kind::s_full_seq:   return "full_seq";
            case snode_kind::s_range:      return "range";
            case snode_kind::s_ite:        return "ite";
            case snode_kind::s_to_re:      return "to_re";
            case snode_kind::s_in_re:      return "in_re";
            }
            return "?";
        };
        for (snode const* n : m_nodes) {
            out << "snode[" << n->id() << "] "
                << kind_str(n->kind())
                << " level=" << n->level()
                << " len=" << n->length()
                << " ground=" << n->is_ground()
                << " rfree=" << n->is_regex_free();
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
