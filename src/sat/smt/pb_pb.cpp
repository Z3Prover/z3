/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    pb_pb.cpp

Abstract:
 
    Interface for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#include "sat/smt/pb_pb.h"

namespace pb {

    pbc& constraint::to_pb() {
        SASSERT(is_pb());
        return static_cast<pbc&>(*this);
    }

    pbc const& constraint::to_pb() const {
        SASSERT(is_pb());
        return static_cast<pbc const&>(*this);
    }

    // -----------------------------------
    // pb

    pbc::pbc(unsigned id, literal lit, svector<wliteral> const& wlits, unsigned k) :
        constraint(tag_t::pb_t, id, lit, wlits.size(), get_obj_size(wlits.size()), k),
        m_slack(0),
        m_num_watch(0),
        m_max_sum(0) {
        for (unsigned i = 0; i < size(); ++i) {
            m_wlits[i] = wlits[i];
        }
        update_max_sum();
    }

    void pbc::update_max_sum() {
        m_max_sum = 0;
        for (unsigned i = 0; i < size(); ++i) {
            m_wlits[i].first = std::min(k(), m_wlits[i].first);
            if (m_max_sum + m_wlits[i].first < m_max_sum) {
                throw default_exception("addition of pb coefficients overflows");
            }
            m_max_sum += m_wlits[i].first;
        }
    }

    void pbc::negate() {
        m_lit.neg();
        unsigned w = 0, m = 0;
        for (unsigned i = 0; i < m_size; ++i) {
            m_wlits[i].second.neg();
            VERIFY(w + m_wlits[i].first >= w);
            w += m_wlits[i].first;
            m = std::max(m, m_wlits[i].first);
        }
        m_k = w - m_k + 1;
        if (m > m_k)  
            for (unsigned i = 0; i < m_size; ++i) 
                m_wlits[i].first = std::min(m_k, m_wlits[i].first);
                       
        VERIFY(w >= m_k && m_k > 0);
    }

    bool pbc::is_watching(literal l) const {
        for (unsigned i = 0; i < m_num_watch; ++i) {
            if ((*this)[i].second == l) return true;
        }
        return false;
    }

    bool pbc::is_cardinality() const {
        if (size() == 0) return false;
        unsigned w = (*this)[0].first;
        for (wliteral wl : *this) if (w != wl.first) return false;
        return true;
    }

    double pbc::get_reward(solver_interface const& s, sat::literal_occs_fun& occs) const {
        unsigned k = this->k(), slack = 0;
        bool do_add = s.get_config().m_lookahead_reward == sat::heule_schur_reward;
        double to_add = do_add ? 0 : 1;
        double undefs = 0;
        for (wliteral wl : *this) {
            literal l = wl.second;
            unsigned w = wl.first;
            switch (s.value(l)) {
            case l_true:  if (k <= w) return 0;
            case l_undef:
                if (do_add) to_add += occs(l);
                ++undefs;
                slack += w;
                break; // TBD multiplier factor on this
            case l_false: break;
            }
        }
        if (k >= slack || 0 == undefs) return 0;
        double avg = slack / undefs;
        return pow(0.5, (slack - k + 1) / avg) * to_add;
    }


    void pbc::clear_watch(solver_interface& s) {
        reset_watch();
        for (unsigned i = 0; i < num_watch(); ++i) {
            unwatch_literal(s, (*this)[i].second);
        }
        set_num_watch(0);
        DEBUG_CODE(for (wliteral wl : *this) VERIFY(!is_watched(s, wl.second)););
    }


    // watch a prefix of literals, such that the slack of these is >= k
    bool pbc::init_watch(solver_interface& s) {
        SASSERT(well_formed());
        auto& p = *this;
        clear_watch(s);
        if (lit() != sat::null_literal && s.value(p.lit()) == l_false) {
            negate();
        }

        VERIFY(lit() == sat::null_literal || s.value(lit()) == l_true);
        unsigned sz = size(), bound = k();

        // put the non-false literals into the head.
        unsigned slack = 0, slack1 = 0, num_watch = 0, j = 0;
        for (unsigned i = 0; i < sz; ++i) {
            if (s.value(p[i].second) != l_false) {
                if (j != i) {
                    swap(i, j);
                }
                if (slack <= bound) {
                    slack += p[j].first;
                    ++num_watch;
                }
                else {
                    slack1 += p[j].first;
                }
                ++j;
            }
        }

        DEBUG_CODE(
            bool is_false = false;
        for (unsigned k = 0; k < sz; ++k) {
            SASSERT(!is_false || s.value(p[k].second) == l_false);
            SASSERT((k < j) == (s.value(p[k].second) != l_false));
            is_false = s.value(p[k].second) == l_false;
        });

        if (slack < bound) {
            literal lit = p[j].second;
            VERIFY(s.value(lit) == l_false);
            for (unsigned i = j + 1; i < sz; ++i) {
                if (s.lvl(lit) < s.lvl(p[i].second)) {
                    lit = p[i].second;
                }
            }
            s.set_conflict(p, lit);
            return false;
        }
        else {
            for (unsigned i = 0; i < num_watch; ++i) {
                p.watch_literal(s, p[i].second);
            }
            p.set_slack(slack);
            p.set_num_watch(num_watch);

            // SASSERT(validate_watch(p, sat::null_literal));

            TRACE("ba", display(tout << "init watch: ", s, true););


            // slack is tight:
            if (slack + slack1 == bound) {
                SASSERT(slack1 == 0);
                SASSERT(j == num_watch);
                for (unsigned i = 0; i < j; ++i) {
                    s.assign(p, p[i].second);
                }
            }
            return true;
        }
    }


    std::ostream& pbc::display(std::ostream& out) const {
        bool first = true;
        for (wliteral wl : *this) {
            if (!first) out << "+ ";
            if (wl.first != 1) out << wl.first << " * ";
            out << wl.second << " ";
            first = false;
        }
        return out << " >= " << k();
    }

    std::ostream& pbc::display(std::ostream& out, solver_interface const& s, bool values) const {
        auto const& p = *this;
        if (p.lit() != sat::null_literal) out << p.lit() << " == ";
        if (values) {
            out << "[watch: " << p.num_watch() << ", slack: " << p.slack() << "]";
        }
        if (p.lit() != sat::null_literal && values) {
            out << "@(" << s.value(p.lit());
            if (s.value(p.lit()) != l_undef) {
                out << ":" << s.lvl(p.lit());
            }
            out << "): ";
        }
        unsigned i = 0;
        for (wliteral wl : p) {
            literal l = wl.second;
            unsigned w = wl.first;
            if (i > 0) out << "+ ";
            if (i++ == p.num_watch()) out << " | ";
            if (w > 1) out << w << " * ";
            out << l;
            if (values) {
                out << "@(" << s.value(l);
                if (s.value(l) != l_undef) {
                    out << ":" << s.lvl(l);
                }
                out << ") ";
            }
            else {
                out << " ";
            }
        }
        return out << ">= " << p.k() << "\n";
    }

    bool pbc::validate_unit_propagation(solver_interface const& s, literal alit) const { 
        if (lit() != sat::null_literal && s.value(lit()) != l_true)             
            return false;

        unsigned sum = 0;
        TRACE("ba", display(tout << "validate: " << alit << "\n", s, true););
        for (wliteral wl : *this) {
            literal l = wl.second;
            lbool val = s.value(l);
            if (val != l_false && l != alit) {
                sum += wl.first;
            }
        }
        return sum < k();
    }

    lbool pbc::eval(sat::model const& m) const {
        auto const& p = *this;
        unsigned trues = 0, undefs = 0;
        for (wliteral wl : p) {
            switch (pb::value(m, wl.second)) {
            case l_true: trues += wl.first; break;
            case l_undef: undefs += wl.first; break;
            default: break;
            }
        }
        if (trues + undefs < p.k()) return l_false;
        if (trues >= p.k()) return l_true;
        return l_undef;        
    }

    lbool pbc::eval(solver_interface const& s) const {
        auto const& p = *this;        
        unsigned trues = 0, undefs = 0;
        for (wliteral wl : p) {
            switch (s.value(wl.second)) {
            case l_true: trues += wl.first; break;
            case l_undef: undefs += wl.first; break;
            default: break;
            }
        }
        if (trues + undefs < p.k()) return l_false;
        if (trues >= p.k()) return l_true;
        return l_undef;        
    }

    void pbc::init_use_list(sat::ext_use_list& ul) const {
        auto idx = cindex();
        for (auto l : *this)
            ul.insert(l.second, idx);
    }

    bool pbc::is_blocked(sat::simplifier& sim, literal lit) const {
        unsigned weight = 0, offset = 0;
        for (wliteral l2 : *this) {
            if (~l2.second == lit) {
                offset = l2.first;
                break;
            }
        }
        SASSERT(offset != 0);
        for (wliteral l2 : *this) {
            if (sim.is_marked(~l2.second)) {
                weight += std::min(offset, l2.first);
            }
        }
        return weight >= k();
    }
}
