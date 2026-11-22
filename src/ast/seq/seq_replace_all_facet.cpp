/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_replace_all_facet.cpp

Abstract:

    See seq_replace_all_facet.h.

Author:

    Clemens Eisenhofer 2026

--*/
#include "ast/seq/seq_replace_all_facet.h"
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/ast_pp.h"

namespace seq {

    expr_ref str_replace_all::fact(seq_util& u) const {
        ast_manager& m = u.get_manager();
        sort* s = m_pattern->get_sort();
        expr_ref result(u.str.mk_concat(m_result, s), m), input(u.str.mk_concat(m_input, s), m);
        expr_ref repl(u.str.mk_concat(m_repl, s), m);
        expr* args[3] = { input, m_pattern, repl };
        expr_ref replaced(m.mk_app(u.get_family_id(), OP_SEQ_REPLACE_ALL, 3, args), m);
        return expr_ref(m.mk_eq(result, replaced), m);
    }

    void replace_all_facet::remove(unsigned idx, symbol rule, proof* pr) {
        if (m_dm.proofs_enabled()) {
            m_trail.push(vector_field_trail<str_replace_all, proof_ref>(m_ras, idx, &str_replace_all::m_proof));
            m_ras[idx].m_proof = m_dm.mk_proof(rule, m.mk_true(), { m_ras[idx].m_proof.get(), pr });
        }
        m_trail.push(vector_field_trail<str_replace_all, bool>(m_ras, idx, &str_replace_all::m_active));
        m_ras[idx].m_active = false;
    }

    void replace_all_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_ras.size(); ++i) {
            if (!m_ras[i].active())
                continue;
            bool touched = subst_in_trailed(m_trail, m_ras, i, &str_replace_all::m_result, var, repl);
            touched |= subst_in_trailed(m_trail, m_ras, i, &str_replace_all::m_input, var, repl);
            touched |= subst_in_trailed(m_trail, m_ras, i, &str_replace_all::m_repl, var, repl);
            if (touched && m_dm.proofs_enabled()) {
                seq_util u(m);
                m_trail.push(vector_field_trail<str_replace_all, proof_ref>(m_ras, i, &str_replace_all::m_proof));
                m_ras[i].m_proof = m_dm.mk_proof(symbol("replace-all-substitute"), m_ras[i].fact(u),
                                              { m_ras[i].m_proof.get(), m_dm.substitution_proof() });
            }
            if (touched && subst_dep) {
                m_trail.push(vector_field_trail<str_replace_all, eq_tree::dep_tracker>(m_ras, i, &str_replace_all::m_dep));
                m_ras[i].m_dep = m_dm.mk_join(m_ras[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* replace_all_facet::clone(trail_stack& trail) const {
        replace_all_facet* f = alloc(replace_all_facet, trail, m, m_dm);
        f->m_ras.append(m_ras);
        return f;
    }

    std::ostream& replace_all_facet::display(std::ostream& out) const {
        out << "replace_all_facet:\n";
        for (auto const& ra : m_ras) {
            if (!ra.active())
                continue;
            out << "  ";
            for (expr* t : ra.m_result) {
                out << mk_pp(t, m) << " ";
            }
            out << "= replace_all(";
            for (expr* t : ra.m_input) {
                out << mk_pp(t, m) << " ";
            }
            out << ", " << mk_pp(ra.m_pattern, m) << ", ";
            for (expr* t : ra.m_repl) {
                out << mk_pp(t, m) << " ";
            }
            out << ")\n";
        }
        return out;
    }

    static bool is_const_unit(seq_util& u, expr* t, unsigned& c) {
        expr* ch = nullptr;
        return u.str.is_unit(t, ch) && u.is_const_char(ch, c);
    }

    expr_ref replace_all_length_relation(seq_util& u, arith_util& a, expr* result, expr* input, expr* pattern, expr_ref_vector const& repl) {
        ast_manager& m = repl.get_manager();
        zstring p;
        unsigned c;
        VERIFY(u.str.is_string(pattern, p));
        for (expr* t : repl) {
            if (!is_const_unit(u, t, c))
                return expr_ref(m);
        }
        expr_ref lr(u.str.mk_length(result), m), li(u.str.mk_length(input), m);
        if (repl.size() == p.length())
            return expr_ref(m.mk_eq(lr, li), m);
        if (repl.size() > p.length())
            return expr_ref(a.mk_ge(lr, li), m);
        return expr_ref(a.mk_le(lr, li), m);
    }

    // Appends a fresh r to `out` with the obligation r = replace_all(ts, pattern, repl).
    static void add_rest(ambient_ref<eq_tree::node, eq_tree::dep_tracker> const& ac, expr* pattern, expr_ref_vector const& repl,
                         eq_tree::dep_tracker dep, unsigned n, expr* const* ts, expr_ref_vector& out, proof* source,
                         symbol rule) {
        if (n == 0)
            return;
        ast_manager& m = out.get_manager();
        seq_util& u = ac.eq_facet_ref().get_seq_util();
        auto& sf = ac.solver_facet_ref();
        expr_ref_vector result(m), input(m);
        input.append(n, ts);
        sort* s = pattern->get_sort();
        expr_ref input_expr(u.str.mk_concat(input, s), m);
        expr_ref repl_expr(u.str.mk_concat(repl, s), m);
        expr_ref r(ac.mk_fresh_var("replace-all-result", s, { input_expr, pattern, repl_expr }), m);
        result.push_back(r);
        auto& f = ac.replace_all_facet_ref();
        proof_ref pr(m);
        if (f.dm().proofs_enabled()) {
            str_replace_all ra(result, input, pattern, repl, dep);
            pr = f.dm().mk_proof(rule, ra.fact(u), { source });
        }
        f.add(result, input, pattern, repl, dep, pr, rule);
        expr_ref rel = replace_all_length_relation(u, sf.get_arith_util(), r, input_expr, pattern, repl);
        if (rel)
            sf.add_constraint(rel, dep, pr, symbol("replace-all-rest-length"));
        out.push_back(r);
    }

    // No proper non-empty prefix of `p` is also a suffix, so occurrences cannot overlap.
    static bool is_unbordered(zstring const& p) {
        for (unsigned k = 1; k < p.length(); ++k) {
            if (p.extract(0, k) == p.extract(p.length() - k, k))
                return false;
        }
        return true;
    }

    // Does the pattern start at `pos`? Undefined as soon as a token is not a constant character.
    static lbool match_at(seq_util& u, expr_ref_vector const& input, unsigned pos, zstring const& p) {
        for (unsigned k = 0; k < p.length(); ++k) {
            unsigned c;
            if (pos + k >= input.size())
                return l_false;
            if (!is_const_unit(u, input.get(pos + k), c))
                return l_undef;
            if (c != p[k])
                return l_false;
        }
        return l_true;
    }

    stx::simplify_result replace_all_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.replace_all_facet_ref();
        auto& ef = ac.eq_facet_ref();
        bool changed = false;
        for (unsigned idx = 0; idx < f.obligations().size(); ++idx) {
            if (!f.obligations()[idx].active())
                continue;
            // Copies: adding obligations may reallocate the vector.
            str_replace_all const& ra = f.obligations()[idx];
            expr_ref_vector result(ra.m_result), input(ra.m_input), repl(ra.m_repl);
            expr_ref pattern(ra.m_pattern);
            proof_ref source(ra.m_proof);
            eq_tree::dep_tracker dep = ra.m_dep;
            zstring p;
            VERIFY(u.str.is_string(pattern, p));
            expr_ref_vector out(m);
            unsigned c;

            if (p.length() == 1) {
                // Homomorphism: every token is handled on its own.
                if (input.size() == 1 && !is_const_unit(u, input.get(0), c))
                    continue;
                for (expr* t : input) {
                    if (!is_const_unit(u, t, c))
                        add_rest(ac, pattern, repl, dep, 1, &t, out, source, symbol("replace-all-homomorphism-rest"));
                    else if (c == p[0])
                        out.append(repl);
                    else
                        out.push_back(t);
                }
                ef.add_equation(result, out, dep, source, symbol("replace-all-homomorphism-result"));
                f.remove(idx, symbol("replace-all-homomorphism-discharge"));
                changed = true;
                ++m_stats.m_num_eval;
                continue;
            }

            unsigned pos = 0;
            while (pos < input.size()) {
                lbool r = match_at(u, input, pos, p);
                if (r == l_undef)
                    break;
                if (r == l_true) {
                    out.append(repl);
                    pos += p.length();
                }
                else
                    out.push_back(input.get(pos++));
            }
            if (pos > 0 || input.empty()) {
                add_rest(ac, pattern, repl, dep, input.size() - pos, input.data() + pos, out, source, symbol("replace-all-evaluate-prefix-rest"));
                ef.add_equation(result, out, dep, source, symbol("replace-all-evaluate-prefix-result"));
                f.remove(idx, symbol("replace-all-evaluate-prefix-discharge"));
                changed = true;
                ++m_stats.m_num_eval;
                continue;
            }

            if (!is_unbordered(p))
                continue;
            pos = 1;
            while (pos < input.size() && match_at(u, input, pos, p) != l_true) {
                ++pos;
            }
            if (pos >= input.size())
                continue;
            add_rest(ac, pattern, repl, dep, pos, input.data(), out, source, symbol("replace-all-unbordered-prefix"));
            out.append(repl);
            pos += p.length();
            add_rest(ac, pattern, repl, dep, input.size() - pos, input.data() + pos, out, source, symbol("replace-all-unbordered-suffix"));
            ef.add_equation(result, out, dep, source, symbol("replace-all-unbordered-cut-result"));
            f.remove(idx, symbol("replace-all-unbordered-cut-discharge"));
            changed = true;
            ++m_stats.m_num_cut;
        }
        if (!changed)
            return stx::simplify_result::noop;
        return f.is_satisfied() ? stx::simplify_result::satisfied : stx::simplify_result::proceed;
    }

    // Case c for input V: 1: V = "", 2: V = p.w, and with k = c/2 - 1
    // even c > 2: V = p[0..k), odd c > 2: V = p[0..k).y.w with y != p[k].
    bool replace_all_split::apply_case(eq_tree::node& n, unsigned idx, unsigned c, eq_tree::edge& out) {
        auto ac = get_ambient(n);
        auto& f = ac.replace_all_facet_ref();
        auto& ef = ac.eq_facet_ref();
        str_replace_all const& ra = f.obligations()[idx];
        expr_ref_vector result(ra.m_result), input(ra.m_input), repl(ra.m_repl);
        expr_ref pattern(ra.m_pattern);
        proof_ref source(ra.m_proof);
        eq_tree::dep_tracker dep = ra.m_dep;
        zstring p;
        VERIFY(u.str.is_string(pattern, p));
        if (!case_in_range(c, p.length()))
            return false;
        bool match = c == 2;
        bool ends = c == 1 || (c > 2 && c % 2 == 0);
        unsigned k = match ? p.length() : c < 3 ? 0 : c / 2 - 1;
        sort* srt = pattern->get_sort();
        expr_ref_vector pat(m), in_rhs(m), out_rhs(m), rest_in(m);
        u.str.get_concat_units(pattern, pat);
        in_rhs.append(k, pat.data());
        if (ends) {
            ef.add_equation(input, in_rhs, dep, nullptr, symbol("replace-all-end-input"));
            ef.add_equation(result, in_rhs, dep, source, symbol("replace-all-end-result"));
            f.remove(idx, symbol("replace-all-end-discharge"));
            out = eq_tree::edge("replace-all end", dep, true, 0);
            return true;
        }
        expr_ref input_expr(u.str.mk_concat(input, srt), m);
        expr_ref prefix(u.str.mk_concat(in_rhs, srt), m);
        if (match)
            out_rhs.append(repl);
        else {
            expr_ref y(ac.mk_fresh_var("replace-all-copy-char", srt, { input_expr, pattern, prefix }), m);
            auto& sf = ac.solver_facet_ref();
            sf.add_constraint(expr_ref(m.mk_eq(u.str.mk_length(y), sf.get_arith_util().mk_int(1)), m), dep,
                              nullptr, symbol("replace-all-copy-character-length"));
            sort* re_sort = u.re.mk_re(srt);
            expr_ref other(u.re.mk_inter(u.re.mk_full_char(re_sort), u.re.mk_complement(u.re.mk_to_re(u.str.mk_string(zstring(p[k]))))), m);
            expr_ref_vector yv(m);
            yv.push_back(y);
            ac.mem_facet_ref().add(str_mem(m, yv, view::membership(other, m), dep), symbol("replace-all-copy-character-mismatch"));
            in_rhs.push_back(y);
            // Only the first character is copied, scanning resumes after it.
            out_rhs.push_back(in_rhs.get(0));
            rest_in.append(in_rhs.size() - 1, in_rhs.data() + 1);
        }
        expr_ref rest(ac.mk_fresh_var(match ? "replace-all-match-tail" : "replace-all-copy-tail",
                                     srt, { input_expr, pattern, prefix }), m);
        in_rhs.push_back(rest);
        rest_in.push_back(rest);
        ef.add_equation(input, in_rhs, dep, nullptr, symbol(match ? "replace-all-match-input" : "replace-all-copy-input"));
        add_rest(ac, pattern, repl, dep, rest_in.size(), rest_in.data(), out_rhs, source,
                 symbol(match ? "replace-all-match-rest" : "replace-all-copy-rest"));
        ef.add_equation(result, out_rhs, dep, source, symbol(match ? "replace-all-match-result" : "replace-all-copy-result"));
        f.remove(idx, symbol(match ? "replace-all-match-discharge" : "replace-all-copy-discharge"));
        // The input is not bounded, so this does not count as progress.
        out = eq_tree::edge(match ? "replace-all match" : "replace-all copy", dep, false, 0);
        return true;
    }

    scoped_ptr<eq_tree::split_iterator_i> replace_all_split::split(eq_tree::node& n, unsigned, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto& f = get_ambient(n).replace_all_facet_ref();
        for (unsigned idx = 0; idx < f.obligations().size(); ++idx) {
            if (!f.obligations()[idx].active())
                continue;
            VERIFY(apply_case(n, idx, 1, out));
            committed = true;
            ++m_stats.m_num_splits;
            return alloc(iterator, *this, n, idx);
        }
        return nullptr;
    }

    bool replace_all_split::iterator::next(eq_tree::edge& out) {
        return m_owner.apply_case(m_n, m_idx, ++m_next_case, out);
    }

}
