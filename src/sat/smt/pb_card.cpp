/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_card.cpp

Abstract:
 
    Interface for Cardinality constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#include "sat/smt/pb_card.h"
#include "sat/smt/pb_solver.h"
#include "sat/sat_simplifier.h"

namespace pb {

    card::card(unsigned id, literal lit, literal_vector const& lits, unsigned k) :
        constraint(tag_t::card_t, id, lit, lits.size(), get_obj_size(lits.size()), k) {
        for (unsigned i = 0; i < size(); ++i) {
            m_lits[i] = lits[i];
        }
    }

    void card::negate() {
        m_lit.neg();
        for (unsigned i = 0; i < m_size; ++i) {
            m_lits[i].neg();
        }
        m_k = m_size - m_k + 1;
        SASSERT(m_size >= m_k && m_k > 0);
    }

    bool card::is_watching(literal l) const {
        unsigned sz = std::min(k() + 1, size());
        for (unsigned i = 0; i < sz; ++i) {
            if ((*this)[i] == l) return true;
        }
        return false;
    }

    double card::get_reward(solver_interface const& s, sat::literal_occs_fun& literal_occs) const {
        unsigned k = this->k(), slack = 0;
        bool do_add = s.get_config().m_lookahead_reward == sat::heule_schur_reward;
        double to_add = do_add ? 0 : 1;
        for (literal l : *this) {
            switch (s.value(l)) {
            case l_true:  --k; if (k == 0) return 0;
            case l_undef:
                if (do_add) to_add += literal_occs(l);
                ++slack; break;
            case l_false: break;
            }
        }
        if (k >= slack) return 1;
        return pow(0.5, static_cast<double>(slack - k + 1)) * to_add;
    }

    std::ostream& card::display(std::ostream& out) const {
        for (literal l : *this) 
            out << l << " ";        
        return out << " >= " << k();
    }

    void constraint::display_lit(std::ostream& out, solver_interface const& s, literal lit, unsigned sz, bool values) const {
        if (lit != sat::null_literal) {
            if (values) {
                out << lit << "[" << sz << "]";
                out << "@(" << s.value(lit);
                if (s.value(lit) != l_undef) {
                    out << ":" << s.lvl(lit);
                }
                out << "): ";
            }
            else {
                out << lit << " == ";
            }
        }
    }

    std::ostream& card::display(std::ostream& out, solver_interface const& s, bool values) const {
        auto const& c = *this;
        display_lit(out, s, c.lit(), c.size(), values);
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c[i];
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
        return out << ">= " << c.k() << "\n";
    }

    void card::clear_watch(solver_interface& s) {
        if (is_clear()) return;
        reset_watch();
        unsigned sz = std::min(k() + 1, size());
        for (unsigned i = 0; i < sz; ++i) 
            unwatch_literal(s, (*this)[i]);        
    }

    bool card::init_watch(solver_interface& s) {
        auto& c = *this;
        literal root = c.lit();
        if (root != sat::null_literal && s.value(root) == l_false) {
            clear_watch(s);
            negate();
            root.neg();
        }
        if (root != sat::null_literal) {
            if (!is_watched(s, root)) watch_literal(s, root);
            if (!is_pure() && !is_watched(s, ~root)) watch_literal(s, ~root);
        }
        TRACE("ba", display(tout << "init watch: ", s, true););
        SASSERT(root == sat::null_literal || s.value(root) == l_true);
        unsigned j = 0, sz = c.size(), bound = c.k();
        // put the non-false literals into the head.

        if (bound == sz) {
            for (literal l : c) s.assign(c, l);
            return false;
        }

        for (unsigned i = 0; i < sz; ++i) {
            if (s.value(c[i]) != l_false) {
                if (j != i) {
                    if (c.is_watched() && j <= bound && i > bound) {
                        c.unwatch_literal(s, c[j]);
                        c.watch_literal(s, c[i]);
                    }
                    c.swap(i, j);
                }
                ++j;
            }
        }
        DEBUG_CODE(
            bool is_false = false;
        for (literal l : c) {
            SASSERT(!is_false || s.value(l) == l_false);
            is_false = s.value(l) == l_false;
        });

        // j is the number of non-false, sz - j the number of false.

        if (j < bound) {
            if (is_watched()) clear_watch(s);
            SASSERT(0 < bound && bound < sz);
            literal alit = c[j];

            //
            // we need the assignment level of the asserting literal to be maximal.
            // such that conflict resolution can use the asserting literal as a starting
            // point.
            //

            for (unsigned i = bound; i < sz; ++i) {
                if (s.lvl(alit) < s.lvl(c[i])) {
                    c.swap(i, j);
                    alit = c[j];
                }
            }
            s.set_conflict(c, alit);
            return false;
        }
        else if (j == bound) {
            for (unsigned i = 0; i < bound; ++i) {
                s.assign(c, c[i]);
            }
            return false;
        }
        else {
            if (c.is_watched()) return true;
            clear_watch(s);
            for (unsigned i = 0; i <= bound; ++i) {
                c.watch_literal(s, c[i]);
            }
            c.set_watch();
            return true;
        }
    }


    card& constraint::to_card() {
        SASSERT(is_card());
        return static_cast<card&>(*this);
    }

    card const& constraint::to_card() const {
        SASSERT(is_card());
        return static_cast<card const&>(*this);
    }

    
    bool card::is_extended_binary(literal_vector& r) const {
        auto const& ca = *this;
        if (ca.size() == ca.k() + 1 && ca.lit() == sat::null_literal) {
            r.reset();
            for (literal l : ca) r.push_back(l);
            return true;
        }
        else  {
            return false;
        }
    }

    bool card::validate_unit_propagation(solver_interface const& s, literal alit) const { 
        (void) alit;
        if (lit() != sat::null_literal && s.value(lit()) != l_true) 
            return false;
        for (unsigned i = k(); i < size(); ++i) 
            if (s.value((*this)[i]) != l_false) 
                return false;
        return true;
    }

    lbool card::eval(solver_interface const& s) const {
        unsigned trues = 0, undefs = 0;
        for (literal l : *this) {
            switch (s.value(l)) {
            case l_true: trues++; break;
            case l_undef: undefs++; break;
            default: break;
            }
        }
        if (trues + undefs < k()) return l_false;
        if (trues >= k()) return l_true;
        return l_undef;        
    }

    lbool card::eval(sat::model const& m) const {
        unsigned trues = 0, undefs = 0;
        for (literal l : *this) {
            switch (pb::value(m, l)) {
            case l_true: trues++; break;
            case l_undef: undefs++; break;
            default: break;
            }
        }
        if (trues + undefs < k()) return l_false;
        if (trues >= k()) return l_true;
        return l_undef;        
    }

    void card::init_use_list(sat::ext_use_list& ul) const {
        auto idx = cindex();
        for (auto l : *this)
            ul.insert(l, idx);
    }

    bool card::is_blocked(sat::simplifier& sim, literal lit) const {
        unsigned weight = 0;
         for (literal l2 : *this) 
            if (sim.is_marked(~l2)) ++weight;
        
        return weight >= k();
    }
    
}
