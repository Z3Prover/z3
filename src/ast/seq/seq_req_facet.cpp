/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_req_facet.cpp

Abstract:

    See seq_req_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#include "ast/seq/seq_req_facet.h"
#include "ast/rewriter/seq_regex_bisim.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

    bool str_req::operator<(str_req const& other) const {
        if (m_p.get() != other.m_p.get())
            return m_p->get_id() < other.m_p->get_id();
        if (m_q.get() != other.m_q.get())
            return m_q->get_id() < other.m_q->get_id();
        return m_is_eq < other.m_is_eq;
    }

    bool str_req::operator==(str_req const& other) const {
        return m_p.get() == other.m_p.get() && m_q.get() == other.m_q.get() && m_is_eq == other.m_is_eq;
    }

    void req_facet::set_status(unsigned idx, lbool status) {
        m_trail.push(vector_field_trail<str_req, lbool>(m_reqs, idx, &str_req::m_status));
        m_reqs[idx].m_status = status;
    }

    void req_facet::advance_qhead(unsigned head) {
        m_trail.push(value_trail<unsigned>(m_qhead));
        m_qhead = head;
    }

    void req_facet::remove(unsigned idx) {
        m_trail.push(vector_erase_trail<str_req>(m_reqs, idx));
        m_reqs.erase(m_reqs.begin() + idx);
        // Any request at or after `idx` that m_qhead had already passed
        // shifts down by one; since requests are only ever removed once
        // resolved (i.e. at an index already < m_qhead, see
        // req_propagation::propagate), m_qhead itself needs to shrink by
        // one to keep pointing at the same logical "first unexamined"
        // boundary.
        if (idx < m_qhead)
            advance_qhead(m_qhead - 1);
    }

    stx::facet_i* req_facet::clone(trail_stack& trail) const {
        req_facet* f = alloc(req_facet, trail, m, u, m_dm);
        f->m_reqs.append(m_reqs);
        f->m_qhead = m_qhead;
        return f;
    }

    std::ostream& req_facet::display(std::ostream& out) const {
        out << "req_facet: " << m_reqs.size() << " request(s), qhead=" << m_qhead << "\n";
        for (auto const& r : m_reqs) {
            out << "  " << mk_pp(r.m_p.get(), m) << (r.m_is_eq ? " = " : " != ") << mk_pp(r.m_q.get(), m)
                << "  [status=" << r.m_status << "]\n";
        }
        return out;
    }

    stx::simplify_result req_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.req_facet_ref();
        m_stats.m_num_propagate++;

        bool changed = false;
        unsigned head = f.qhead();
        // Examine every request from qhead() to the end exactly once per
        // round; a request whose bisimulation verdict remains l_undef is
        // simply left behind (qhead advances past it too - nothing in
        // this facet ever mutates a pending request's p/q, so retrying
        // it on a later round cannot help, see module comment).
        while (head < f.reqs().size()) {
            str_req const& r = f.reqs()[head];
            regex_bisim bisim(m_rw);
            lbool verdict = bisim.are_equivalent(r.m_p, r.m_q);
            switch (verdict) {
            case l_true:
                if (r.m_is_eq) {
                    // p = q confirmed: discharge.
                    f.remove(head);
                    changed = true;
                    continue; // re-examine same index (now the next request)
                }
                else {
                    // p != q was asserted, but p and q are equivalent: conflict.
                    n.set_conflict(stx::br_plugin_base, r.m_dep);
                    return stx::simplify_result::conflict;
                }
            case l_false:
                if (!r.m_is_eq) {
                    // p != q confirmed: discharge.
                    f.remove(head);
                    changed = true;
                    continue;
                }
                else {
                    // p = q was asserted, but p and q are distinct: conflict.
                    n.set_conflict(stx::br_plugin_base, r.m_dep);
                    return stx::simplify_result::conflict;
                }
            case l_undef:
            default:
                if (r.m_status != l_undef)
                    ; // already recorded, nothing to change
                else
                    f.set_status(head, l_undef);
                ++head;
                break;
            }
        }
        if (head != f.qhead()) {
            f.advance_qhead(head);
            changed = true;
        }
        m_stats.m_num_resolved += changed ? 1 : 0;
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
