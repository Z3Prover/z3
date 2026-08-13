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
        return m.is_true(nb) ? l_true : (m.is_false(nb) ? l_false : l_undef);
    }

    expr_ref_pair_vector const& regex_witness::cofactors(expr* r) const {
        return m_rw.get_derive().get_cached_cofactors(m_mode, r);
    }

    lbool regex_witness::get_witness(expr* r, expr_ref& witness) {
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
        // the root, the state it was reached from and the element read on that edge,
        // enabling witness reconstruction by walking back to the root.
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
                    break;                            // should not happen
                elems.push_back(pr.second);
                s = pr.first;
            }
            expr_ref_vector es(m);                    // root..accept order
            for (unsigned i = elems.size(); i-- > 0; )
                es.push_back(u().str.mk_unit(elems[i]));
            witness = expr_ref(u().str.mk_concat(es.size(), es.data(), seq_sort), m);
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
                lbool sat = gs.eval(&elem);
                if (sat == l_undef) {
                    bail = true;                       // guard outside the supported grammar
                    continue;
                }
                if (sat == l_false)
                    continue;                          // empty guard: unreachable on this edge
                visited.mark(t);
                m_pin.push_back(t);
                m_pin.push_back(elem);
                parent.insert(t, { state, elem.get() });
                work.push_back(t);
            }
        }
        return bail ? l_undef : l_false;
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
        if (!u().is_re(r, seq_sort) || !u().is_string(seq_sort))
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
