/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_witness.cpp

Abstract:

    Implementation of seq::regex_witness.  See seq_regex_witness.h.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/rewriter/seq_regex_witness.h"

namespace seq {

    regex_witness::regex_witness(seq_rewriter& rw, transition_mode mode, unsigned max_states):
        m(rw.m()), m_rw(rw), m_mode(mode), m_max_states(max_states),
        m_pin(rw.m()), m_rp_cache(rw.m()) {
    }

    lbool regex_witness::nullable(expr* r) const {
        lbool i = re().get_info(r).nullable;
        if (i != l_undef)
            return i;
        expr_ref nb = m_rw.is_nullable(r);
        if (m.is_true(nb))  return l_true;
        if (m.is_false(nb)) return l_false;
        return l_undef;
    }

    expr_ref_pair_vector const& regex_witness::cofactors(expr* r) const {
        return m_rw.get_derive().get_cached_cofactors(m_mode, r);
    }

    lbool regex_witness::search(expr* r, expr_ref* witness) {
        m_pin.reset();
        m_rp_cache.maybe_reset(1u << 16);
        sort* seq_sort = nullptr;
        if (!u().is_re(r, seq_sort))
            return l_undef;
        sort* elem_sort = nullptr;
        if (!u().is_seq(seq_sort, elem_sort))
            return l_undef;
        if (re().is_empty(r))
            return l_false;

        expr_ref v0(m.mk_var(0, elem_sort), m);

        // BFS over derivative states, so the first nullable state reached gives a
        // shortest witness.  `parent` records, for every discovered state other than
        // the root, the state it was reached from and the element read on that edge; it
        // is only built when the caller asked for a witness.
        expr_mark visited;
        ptr_vector<expr> work;
        obj_map<expr, std::pair<expr*, expr*>> parent;
        work.push_back(r);
        visited.mark(r);

        auto reconstruct = [&](expr* accept) {
            ptr_vector<expr> elems;                  // collected in accept..root order
            expr* s = accept;
            while (s != r) {
                std::pair<expr*, expr*> pr;
                if (!parent.find(s, pr))
                    break;                           // should not happen
                auto [pred, elem] = pr;
                elems.push_back(elem);
                s = pred;
            }
            expr_ref_vector es(m);                    // root..accept order
            for (unsigned i = elems.size(); i-- > 0; )
                es.push_back(u().str.mk_unit(elems[i]));
            *witness = expr_ref(u().str.mk_concat(es.size(), es.data(), seq_sort), m);
        };

        unsigned num_states = 0;
        bool bail = false;                            // some visited state's status was undecided
        unsigned head = 0;
        while (head < work.size()) {
            if (!m.inc())
                return l_undef;
            expr* state = work[head++];
            if (++num_states > m_max_states) {
                bail = true;
                continue;
            }
            lbool nb = nullable(state);
            if (nb == l_true) {
                if (witness)
                    reconstruct(state);
                return l_true;
            }
            if (nb == l_undef) {
                bail = true;
                continue;                             // cannot certify this state is a dead end
            }
            for (auto const& [g, t] : cofactors(state)) {
                if (re().is_empty(t) || visited.is_marked(t))
                    continue;
                guard_set gs(m, u(), elem_sort, v0, &m_rp_cache);
                gs.conjoin(g);
                expr_ref elem(m);
                lbool sat = gs.eval(witness ? &elem : nullptr);
                if (sat == l_undef) {
                    bail = true;                       // guard outside the supported grammar
                    continue;
                }
                if (sat == l_false)
                    continue;                          // empty guard: unreachable on this edge
                visited.mark(t);
                m_pin.push_back(t);
                if (elem)
                    m_pin.push_back(elem);
                if (witness)
                    parent.insert(t, { state, elem.get() });
                work.push_back(t);
            }
        }
        return bail ? l_undef : l_false;
    }

    lbool regex_witness::get_witness(expr* r, expr_ref& witness) {
        return search(r, &witness);
    }

    lbool regex_witness::accepts(expr* word, expr* r) {
        unsigned work = 0;
        return accepts(word, r, 0, work);
    }

    lbool regex_witness::accepts(expr* word, expr* r, unsigned depth, unsigned& work) {
        if (depth > 128 || ++work > 4096 || !m.inc())
            return l_undef;
        rational length;
        if (!m_rw.get_ground_seq_length(word, length))
            return l_undef;
        if (re().is_empty(r))
            return l_false;
        if (re().is_full_seq(r))
            return l_true;
        if (length.is_zero())
            return nullable(r);
        expr* a = nullptr, *b = nullptr;
        if (re().is_to_re(r, a))
            return m_rw.compare_ground_seqs(word, a);
        if (re().is_complement(r, a))
            return ~accepts(word, a, depth + 1, work);
        if (re().is_union(r) || re().is_intersection(r)) {
            bool conjunction = re().is_intersection(r);
            lbool result = conjunction ? l_true : l_false;
            for (expr* arg : *to_app(r)) {
                lbool value = accepts(word, arg, depth + 1, work);
                if (value == (conjunction ? l_false : l_true))
                    return value;
                if (value == l_undef)
                    result = l_undef;
            }
            return result;
        }
        if (re().is_full_char(r))
            return length.is_one() ? l_true : l_false;

        unsigned lo = 0, hi = UINT_MAX;
        bool bounded = re().is_loop(r, a, lo, hi);
        bool repetition = bounded;
        if (!repetition && re().is_loop(r, a, lo))
            repetition = true;
        if (re().is_star(r, a) || re().is_plus(r, a)) {
            lo = re().is_plus(r) ? 1 : 0;
            hi = UINT_MAX;
            bounded = false;
            repetition = true;
        }
        if (repetition) {
            if (re().is_full_char(a))
                return length >= rational(lo) && (!bounded || length <= rational(hi)) ? l_true : l_false;
            expr* base = nullptr, *exponent = nullptr;
            rational count;
            arith_util arith(m);
            if (u().str.is_power(word, base, exponent) && arith.is_numeral(exponent, count) &&
                count >= rational(lo) && (!bounded || count <= rational(hi)) &&
                accepts(base, a, depth + 1, work) == l_true)
                return l_true;
        }
        if (re().is_concat(r)) {
            app* cat = to_app(r);
            a = cat->get_arg(0);
            expr_ref rest(cat->get_arg(cat->get_num_args() - 1), m);
            for (unsigned i = cat->get_num_args() - 1; i-- > 1;)
                rest = re().mk_concat(cat->get_arg(i), rest);
            rational cuts[3] = { rational(re().min_length(a)),
                                 length - rational(re().min_length(rest)), length };
            expr* first = word;
            if (u().str.is_concat(word))
                first = to_app(word)->get_arg(0);
            m_rw.get_ground_seq_length(first, cuts[2]);
            for (auto const& cut : cuts) {
                if (cut.is_neg() || cut > length)
                    continue;
                expr_ref left(m), right(m);
                if (!m_rw.slice_ground_seq(word, rational(0), cut, left) ||
                    !m_rw.slice_ground_seq(word, cut, length - cut, right))
                    continue;
                if (accepts(left, a, depth + 1, work) == l_true &&
                    accepts(right, rest, depth + 1, work) == l_true)
                    return l_true;
            }
        }

        // Bounded concrete fallback; large powers must not be unrolled here.
        if (length > rational(4096 - std::min(work, 4096u)))
            return l_undef;
        expr_ref state(r, m);
        for (unsigned i = 0; i < length.get_unsigned(); ++i) {
            if (++work > 4096 || !m.inc())
                return l_undef;
            expr_ref piece(m);
            expr* element = nullptr;
            zstring text;
            if (!m_rw.slice_ground_seq(word, rational(i), rational(1), piece))
                return l_undef;
            if (u().str.is_string(piece, text) && text.length() == 1)
                element = u().str.mk_char(text[0]);
            else if (!u().str.is_unit(piece, element))
                return l_undef;
            state = m_rw.mk_derivative(element, state);
            if (re().is_empty(state))
                return l_false;
        }
        return nullable(state);
    }

    lbool regex_witness::get_compact_witness(expr* r, expr_ref& word) {
        unsigned work = 0;
        return compact_witness(r, word, 0, work);
    }

    lbool regex_witness::compact_witness(expr* r, expr_ref& word, unsigned depth, unsigned& work) {
        if (depth > 128 || ++work > 4096 || !m.inc())
            return l_undef;
        sort* seq_sort = nullptr;
        if (!u().is_re(r, seq_sort))
            return l_undef;
        if (nullable(r) == l_true) {
            word = u().str.mk_empty(seq_sort);
            return l_true;
        }
        expr* a = nullptr;
        if (re().is_empty(r))
            return l_false;
        if (re().is_to_re(r, a)) {
            rational length;
            if (!m_rw.get_ground_seq_length(a, length))
                return l_undef;
            word = a;
            return l_true;
        }
        if (re().is_concat(r)) {
            word = u().str.mk_empty(seq_sort);
            for (expr* arg : *to_app(r)) {
                expr_ref part(m);
                lbool result = compact_witness(arg, part, depth + 1, work);
                if (result != l_true)
                    return result;
                if (u().str.is_empty(word))
                    word = part;
                else if (!u().str.is_empty(part))
                    word = u().str.mk_concat(word, part);
            }
            return l_true;
        }
        if (re().is_union(r) || re().is_intersection(r)) {
            bool intersection = re().is_intersection(r);
            bool unknown = false;
            expr_ref shortest(m);
            rational shortest_length;
            for (expr* arg : *to_app(r)) {
                expr_ref candidate(m);
                lbool result = compact_witness(arg, candidate, depth + 1, work);
                if (result == l_false && intersection)
                    return l_false;
                if (result == l_true) {
                    if (intersection && accepts(candidate, r, depth + 1, work) == l_true) {
                        word = candidate;
                        return l_true;
                    }
                    rational length;
                    if (!intersection && m_rw.get_ground_seq_length(candidate, length) &&
                        (!shortest || length < shortest_length)) {
                        shortest = candidate;
                        shortest_length = length;
                    }
                }
                unknown |= result != l_false;
            }
            if (shortest) {
                word = shortest;
                return l_true;
            }
            if (!unknown)
                return l_false;
        }
        unsigned lo = 0, hi = 0;
        bool bounded = re().is_loop(r, a, lo, hi);
        bool loop = bounded || re().is_loop(r, a, lo);
        if (bounded && lo > hi)
            return l_false;
        if (re().is_plus(r, a)) {
            lo = 1;
            loop = true;
        }
        if (loop) {
            expr_ref base(m);
            lbool result = compact_witness(a, base, depth + 1, work);
            if (result != l_true)
                return result;
            arith_util arith(m);
            expr_ref exponent(arith.mk_int(lo), m);
            word = lo == 1 ? base.get() : u().str.mk_power(base, exponent);
            return l_true;
        }
        return search(r, &word);
    }

    lbool regex_witness::nonempty(expr* r) {
        return search(r, nullptr);
    }

    lbool regex_witness::intersect_nonempty(expr* r1, expr* r2) {
        SASSERT(u().is_re(r1) && r1->get_sort() == r2->get_sort());        
        expr_ref r = m_rw.mk_inter(r1, r2);
        return search(r, nullptr);
    }

    bool regex_witness::decode_string(seq_util& u, expr* e, zstring& out) {
        while (true) {
            if (u.str.is_empty(e))
                return true;
            if (u.str.is_concat(e)) {
                app* a = to_app(e);
                unsigned n = a->get_num_args();
                if (n == 0)
                    return true;
                for (unsigned i = 0; i + 1 < n; ++i)
                    if (!decode_string(u, a->get_arg(i), out))
                        return false;
                e = a->get_arg(n - 1);
                continue;
            }
            zstring s;
            if (u.str.is_string(e, s)) {
                out += s;
                return true;
            }
            expr* ch = nullptr;
            unsigned c;
            if (u.str.is_unit(e, ch) && u.is_const_char(ch, c)) {
                out += zstring(c);
                return true;
            }
            return false;
        }
    }

    lbool regex_witness::get_witness(expr* r, zstring& s) {
        sort* seq_sort = nullptr;
        VERIFY(u().is_re(r, seq_sort));
        if (!u().is_string(seq_sort))
            return l_undef;
        expr_ref w(m);
        lbool res = get_witness(r, w);
        if (res != l_true)
            return res;
        zstring out;
        if (!decode_string(u(), w, out))
            return l_undef;
        s = out;
        return l_true;
    }

}
