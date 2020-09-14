/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_xor.cpp

Abstract:
 
    Interface for Xor constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#include "sat/smt/ba_xor.h"
#include "sat/smt/ba_solver.h"

namespace ba {

    xr& constraint::to_xr() {
        SASSERT(is_xr());
        return static_cast<xr&>(*this);
    }

    xr const& constraint::to_xr() const {
        SASSERT(is_xr());
        return static_cast<xr const&>(*this);
    }

    xr::xr(unsigned id, literal_vector const& lits) :
        constraint(ba::tag_t::xr_t, id, sat::null_literal, lits.size(), get_obj_size(lits.size())) {
        for (unsigned i = 0; i < size(); ++i) {
            m_lits[i] = lits[i];
        }
    }


    bool xr::is_watching(literal l) const {
        return
            l == (*this)[0] || l == (*this)[1] ||
            ~l == (*this)[0] || ~l == (*this)[1];
    }

    bool xr::well_formed() const {
        uint_set vars;
        if (lit() != sat::null_literal) vars.insert(lit().var());
        for (literal l : *this) {
            bool_var v = l.var();
            if (vars.contains(v)) return false;
            vars.insert(v);
        }
        return true;
    }

    std::ostream& xr::display(std::ostream& out) const {
        for (unsigned i = 0; i < size(); ++i) {
            out << (*this)[i] << " ";
            if (i + 1 < size()) out << "x ";
        }
        return out;
    }

    void xr::clear_watch(solver_interface& s) {
        auto& x = *this;
        x.reset_watch();
        x.unwatch_literal(s, x[0]);
        x.unwatch_literal(s, x[1]);
        x.unwatch_literal(s, ~x[0]);
        x.unwatch_literal(s, ~x[1]);
    }


    bool xr::init_watch(solver_interface& s) {
        auto& x = *this;
        x.clear_watch(s);
        VERIFY(x.lit() == sat::null_literal);
        TRACE("ba", x.display(tout););
        unsigned sz = x.size();
        unsigned j = 0;
        for (unsigned i = 0; i < sz && j < 2; ++i) {
            if (s.value(x[i]) == l_undef) {
                x.swap(i, j);
                ++j;
            }
        }
        switch (j) {
        case 0:
            if (!parity(s, 0)) {
                unsigned l = s.lvl(x[0]);
                j = 1;
                for (unsigned i = 1; i < sz; ++i) {
                    if (s.lvl(x[i]) > l) {
                        j = i;
                        l = s.lvl(x[i]);
                    }
                }
                s.set_conflict(x, x[j]);
            }
            return false;
        case 1:
            SASSERT(x.lit() == sat::null_literal || s.value(x.lit()) == l_true);
            s.assign(x, parity(s, 1) ? ~x[0] : x[0]);
            return false;
        default:
            SASSERT(j == 2);
            x.watch_literal(s, x[0]);
            x.watch_literal(s, x[1]);
            x.watch_literal(s, ~x[0]);
            x.watch_literal(s, ~x[1]);
            return true;
        }
    }

    bool xr::parity(solver_interface const& s, unsigned offset) const {
        auto const& x = *this;
        bool odd = false;
        unsigned sz = x.size();
        for (unsigned i = offset; i < sz; ++i) {
            SASSERT(s.value(x[i]) != l_undef);
            if (s.value(x[i]) == l_true) {
                odd = !odd;
            }
        }
        return odd;
    }


    std::ostream& xr::display(std::ostream& out, solver_interface const& s, bool values) const {
        auto const& x = *this;
        out << "xr: ";
        for (literal l : x) {
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
        return out << "\n";
    }

    bool xr::validate_unit_propagation(solver_interface const& s, literal alit) const {
        if (s.value(lit()) != l_true) return false;
        for (unsigned i = 1; i < size(); ++i) {
            if (s.value((*this)[i]) == l_undef) return false;
        }
        return true;
    }

    lbool xr::eval(solver_interface const& s) const {
        auto const& x = *this;
        bool odd = false;        
        for (auto l : x) {
            switch (s.value(l)) {
            case l_true: odd = !odd; break;
            case l_false: break;
            default: return l_undef;
            }
        }
        return odd ? l_true : l_false;
    }

    lbool xr::eval(sat::model const& m) const {
        auto const& x = *this;
        bool odd = false;        
        for (auto l : x) {
            switch (ba::value(m, l)) {
            case l_true: odd = !odd; break;
            case l_false: break;
            default: return l_undef;
            }
        }
        return odd ? l_true : l_false;
    }

    void xr::init_use_list(sat::ext_use_list& ul) const {
        auto idx = cindex();
        for (auto l : *this) {
            ul.insert(l, idx);
            ul.insert(~l, idx);
        }
    }

}
