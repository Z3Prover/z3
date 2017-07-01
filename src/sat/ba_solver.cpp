/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_solver.cpp

Abstract:

    Extension for cardinality and xor reasoning.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/

#include"ba_solver.h"
#include"sat_types.h"

namespace sat {

    ba_solver::card& ba_solver::constraint::to_card() {
        SASSERT(is_card());
        return static_cast<card&>(*this);
    }

    ba_solver::card const& ba_solver::constraint::to_card() const{
        SASSERT(is_card());
        return static_cast<card const&>(*this);
    }

    ba_solver::pb& ba_solver::constraint::to_pb() {
        SASSERT(is_pb());
        return static_cast<pb&>(*this);
    }

    ba_solver::pb const& ba_solver::constraint::to_pb() const{
        SASSERT(is_pb());
        return static_cast<pb const&>(*this);
    }

    ba_solver::xor& ba_solver::constraint::to_xor() {
        SASSERT(is_xor());
        return static_cast<xor&>(*this);
    }

    ba_solver::xor const& ba_solver::constraint::to_xor() const{
        SASSERT(is_xor());
        return static_cast<xor const&>(*this);
    }

    std::ostream& operator<<(std::ostream& out, ba_solver::constraint const& cnstr) {
        if (cnstr.lit() != null_literal) out << cnstr.lit() << " == ";
        switch (cnstr.tag()) {
        case ba_solver::card_t: {
            ba_solver::card const& c = cnstr.to_card();
            for (literal l : c) {
                out << l << " ";
            }
            out << " >= " << c.k();
            break;
        }
        case ba_solver::pb_t: {
            ba_solver::pb const& p = cnstr.to_pb();
            for (ba_solver::wliteral wl : p) {
                if (wl.first != 1) out << wl.first << " * ";
                out << wl.second << " ";
            }
            out << " >= " << p.k();
            break;
        }
        case ba_solver::xor_t: {
            ba_solver::xor const& x = cnstr.to_xor();
            for (unsigned i = 0; i < x.size(); ++i) {
                out << x[i] << " ";
                if (i + 1 < x.size()) out << "x ";
            }            
            break;
        }
        default:
            UNREACHABLE();
        }
        return out;
    }


    // -----------------------
    // pb_base

    bool ba_solver::pb_base::well_formed() const {
        uint_set vars;        
        for (unsigned i = 0; i < size(); ++i) {
            bool_var v = get_lit(i).var();
            if (vars.contains(v)) return false;
            if (get_coeff(i) > k()) return false;
            vars.insert(v);
        }
        return true;
    }

    // ----------------------
    // card

    ba_solver::card::card(literal lit, literal_vector const& lits, unsigned k):
        pb_base(card_t, lit, lits.size(), get_obj_size(lits.size()), k) {
        for (unsigned i = 0; i < size(); ++i) {
            m_lits[i] = lits[i];
        }
    }

    void ba_solver::card::negate() {
        m_lit.neg();
        for (unsigned i = 0; i < m_size; ++i) {
            m_lits[i].neg();
        }
        m_k = m_size - m_k + 1;
        SASSERT(m_size >= m_k && m_k > 0);
    }

    bool ba_solver::card::is_watching(literal l) const {
        unsigned sz = std::min(k() + 1, size());
        for (unsigned i = 0; i < sz; ++i) {
            if ((*this)[i] == l) return true;
        }
        return false;
    }

    // -----------------------------------
    // pb

    ba_solver::pb::pb(literal lit, svector<ba_solver::wliteral> const& wlits, unsigned k):
        pb_base(pb_t, lit, wlits.size(), get_obj_size(wlits.size()), k),
        m_slack(0),
        m_num_watch(0),
        m_max_sum(0) {
        for (unsigned i = 0; i < size(); ++i) {
            m_wlits[i] = wlits[i];
        }
        update_max_sum();
    }

    void ba_solver::pb::update_max_sum() {
        m_max_sum = 0;
        for (unsigned i = 0; i < size(); ++i) {
            m_wlits[i].first = std::min(k(), m_wlits[i].first);
            if (m_max_sum + m_wlits[i].first < m_max_sum) {
                throw default_exception("addition of pb coefficients overflows");
            }
            m_max_sum += m_wlits[i].first;
        }
    }

    void ba_solver::pb::negate() {
        m_lit.neg();
        unsigned w = 0;
        for (unsigned i = 0; i < m_size; ++i) {
            m_wlits[i].second.neg();
            w += m_wlits[i].first;
        }
        m_k = w - m_k + 1;
        SASSERT(w >= m_k && m_k > 0);
    }

    bool ba_solver::pb::is_watching(literal l) const {
        for (unsigned i = 0; i < m_num_watch; ++i) {
            if ((*this)[i].second == l) return true;
        }
        return false;
    }


    bool ba_solver::pb::is_cardinality() const {
        if (size() == 0) return false;
        unsigned w = (*this)[0].first;
        for (wliteral wl : *this) if (w != wl.first) return false;
        return true;
    }


    // -----------------------------------
    // xor
    
    ba_solver::xor::xor(literal lit, literal_vector const& lits):
    constraint(xor_t, lit, lits.size(), get_obj_size(lits.size())) {
        for (unsigned i = 0; i < size(); ++i) {
            m_lits[i] = lits[i];
        }
    }

    bool ba_solver::xor::is_watching(literal l) const {
        return 
            l == (*this)[0] || l == (*this)[1] ||
            ~l == (*this)[0] || ~l == (*this)[1];            
    }

    bool ba_solver::xor::well_formed() const {
        uint_set vars;        
        for (literal l : *this) {
            bool_var v = l.var();
            if (vars.contains(v)) return false;
            vars.insert(v);
        }
        return true;
    }

    // ----------------------------
    // card

    void ba_solver::init_watch(card& c, bool is_true) {
        clear_watch(c);
        if (c.lit() != null_literal && c.lit().sign() == is_true) {
            c.negate();
        }
        TRACE("sat", display(tout << "init watch: ", c, true););
        SASSERT(c.lit() == null_literal || value(c.lit()) == l_true);
        unsigned j = 0, sz = c.size(), bound = c.k();
        if (bound == sz) {
            for (unsigned i = 0; i < sz && !inconsistent(); ++i) {
                assign(c, c[i]);
            }
            return;
        }
        // put the non-false literals into the head.
        for (unsigned i = 0; i < sz; ++i) {
            if (value(c[i]) != l_false) {
                if (j != i) {
                    c.swap(i, j);
                }
                ++j;
            }
        }
        DEBUG_CODE(
            bool is_false = false;
            for (literal l : c) {
                SASSERT(!is_false || value(l) == l_false);
                is_false = value(l) == l_false;
            });

        // j is the number of non-false, sz - j the number of false.
        if (j < bound) {
            SASSERT(0 < bound && bound < sz);
            literal alit = c[j];
            
            //
            // we need the assignment level of the asserting literal to be maximal.
            // such that conflict resolution can use the asserting literal as a starting
            // point.
            //

            for (unsigned i = bound; i < sz; ++i) {                
                if (lvl(alit) < lvl(c[i])) {
                    c.swap(i, j);
                    alit = c[j];
                }
            }
            set_conflict(c, alit);
        }
        else if (j == bound) {
            for (unsigned i = 0; i < bound && !inconsistent(); ++i) {
                assign(c, c[i]);                
            }
        }
        else {
            for (unsigned i = 0; i <= bound; ++i) {
                watch_literal(c[i], c);
            }
        }
    }

    void ba_solver::clear_watch(card& c) {
        unsigned sz = std::min(c.k() + 1, c.size());
        for (unsigned i = 0; i < sz; ++i) {
            unwatch_literal(c[i], c);            
        }
    }

    // -----------------------
    // constraint

    void ba_solver::set_conflict(constraint& c, literal lit) {
        m_stats.m_num_conflicts++;
        TRACE("sat", display(tout, c, true); );
        SASSERT(validate_conflict(c));
        if (c.is_xor() && value(lit) == l_true) lit.neg();
        SASSERT(value(lit) == l_false);
        set_conflict(justification::mk_ext_justification(c.index()), ~lit);
        SASSERT(inconsistent());
    }

    void ba_solver::assign(constraint& c, literal lit) {
        switch (value(lit)) {
        case l_true: 
            break;
        case l_false: 
            set_conflict(c, lit); 
            break;
        default:
            m_stats.m_num_propagations++;
            m_num_propagations_since_pop++;
            //TRACE("sat", tout << "#prop: " << m_stats.m_num_propagations << " - " << c.lit() << " => " << lit << "\n";);
            SASSERT(validate_unit_propagation(c, lit));
            if (get_config().m_drat) {
                svector<drat::premise> ps;
                literal_vector lits;
                get_antecedents(lit, c, lits);
                lits.push_back(lit);
                ps.push_back(drat::premise(drat::s_ext(), c.lit())); // null_literal case.
                drat_add(lits, ps);
            }
            assign(lit, justification::mk_ext_justification(c.index()));
            break;
        }
    }

    // -------------------
    // pb


    // watch a prefix of literals, such that the slack of these is >= k
    void ba_solver::init_watch(pb& p, bool is_true) {
        clear_watch(p);
        if (p.lit() != null_literal && p.lit().sign() == is_true) {
            p.negate();
        }
        
        SASSERT(p.lit() == null_literal || value(p.lit()) == l_true);
        unsigned sz = p.size(), bound = p.k();

        // put the non-false literals into the head.
        unsigned slack = 0, num_watch = 0, j = 0;
        for (unsigned i = 0; i < sz; ++i) {
            if (value(p[i].second) != l_false) {
                if (j != i) {
                    p.swap(i, j);
                }
                if (slack < bound) {
                    slack += p[j].first;
                    ++num_watch;
                }
                ++j;
            }
        }
        DEBUG_CODE(
            bool is_false = false;
            for (unsigned k = 0; k < sz; ++k) {
                SASSERT(!is_false || value(p[k].second) == l_false);
                SASSERT(k < j == (value(p[k].second) != l_false));
                is_false = value(p[k].second) == l_false;
            });

        if (slack < bound) {
            literal lit = p[j].second;
            SASSERT(value(lit) == l_false);
            for (unsigned i = j + 1; i < sz; ++i) {
                if (lvl(lit) < lvl(p[i].second)) {
                    lit = p[i].second;
                }
            }
            set_conflict(p, lit);
        }
        else {            
            for (unsigned i = 0; i < num_watch; ++i) {
                watch_literal(p[i], p);
            }
            p.set_slack(slack);
            p.set_num_watch(num_watch);
        }
        TRACE("sat", display(tout << "init watch: ", p, true););
    }

    /*
      Chai Kuhlmann:
      Lw - set of watched literals
      Lu - set of unwatched literals that are not false
      
      Lw = Lw \ { alit }
      Sw -= value
      a_max = max { a | l in Lw u Lu, l = undef }
      while (Sw < k + a_max & Lu != 0) {
        a_s = max { a | l in Lu }
        Sw += a_s
        Lw = Lw u {l_s}
        Lu = Lu \ {l_s}
     }
     if (Sw < k) conflict
     while (Sw < k + a_max) {
         assign (l_max)
         a_max = max { ai | li in Lw, li = undef }
     }
     ASSERT(Sw >= bound)
     return no-conflict

     a_max index: index of non-false literal with maximal weight.


    */
    void ba_solver::add_index(pb& p, unsigned index, literal lit) {
        if (value(lit) == l_undef) {
            m_pb_undef.push_back(index);
            if (p[index].first > m_a_max) {
                m_a_max = p[index].first;
            }
        }
    }
    
    lbool ba_solver::add_assign(pb& p, literal alit) {
        
        TRACE("sat", display(tout << "assign: " << alit << "\n", p, true););
        SASSERT(!inconsistent());
        unsigned sz = p.size();
        unsigned bound = p.k();
        unsigned num_watch = p.num_watch();
        unsigned slack = p.slack();
        SASSERT(value(alit) == l_false);
        SASSERT(p.lit() == null_literal || value(p.lit()) == l_true);
        SASSERT(num_watch <= sz);
        SASSERT(num_watch > 0);
        unsigned index = 0;
        m_a_max = 0;
        m_pb_undef.reset();
        for (; index < num_watch; ++index) {
            literal lit = p[index].second;
            if (lit == alit) {
                break;
            }
            add_index(p, index, lit);
        }
        SASSERT(index < num_watch);
        if (index >= num_watch) {
            std::cout << "BAD assign. " << alit << " not found within " << num_watch << "\n";
            std::cout << p << "\n";
        }
        
        unsigned index1 = index + 1;
        for (; m_a_max == 0 && index1 < num_watch; ++index1) {
            add_index(p, index1, p[index1].second);
        }
        
        unsigned val = p[index].first;
        SASSERT(value(p[index].second) == l_false);
        SASSERT(val <= slack);
        slack -= val;
        // find literals to swap with:            
        for (unsigned j = num_watch; j < sz && slack < bound + m_a_max; ++j) {
            literal lit = p[j].second;
            if (value(lit) != l_false) {
                slack += p[j].first;
                watch_literal(p[j], p);
                p.swap(num_watch, j);
                add_index(p, num_watch, lit);
                ++num_watch;
            }
        }
        
        SASSERT(!inconsistent());
        DEBUG_CODE(for (auto idx : m_pb_undef) { SASSERT(value(p[idx].second) == l_undef); });
        
        if (slack < bound) {
            // maintain watching the literal
            slack += val;
            p.set_slack(slack);
            p.set_num_watch(num_watch);
            SASSERT(bound <= slack);
            TRACE("sat", tout << "conflict " << alit << "\n";);
            set_conflict(p, alit);
            return l_false;
        }
        
        if (index > p.size() || num_watch > p.size() || num_watch == 0) {
            display(std::cout, p, true);
            std::cout << "size: " << p.size() << "index: " << index << " num watch: " << num_watch << "\n";
        }
        // swap out the watched literal.
        --num_watch;
        SASSERT(num_watch > 0);
        p.set_slack(slack);
        p.set_num_watch(num_watch);
        p.swap(num_watch, index);

        if (slack < bound + m_a_max) {
            TRACE("sat", tout << p; for(auto j : m_pb_undef) tout << j << "\n";);
            literal_vector to_assign;
            while (!m_pb_undef.empty()) {
                index1 = m_pb_undef.back();
                if (index1 == num_watch) index1 = index; // it was swapped with index above.
                if (index1 >= num_watch) {
                    std::cout << "BAD assignment at position " << index1 << " with " << num_watch << "\n";
                    std::cout << p << "\n";
                }
                literal lit = p[index1].second;
                SASSERT(value(lit) == l_undef);
                TRACE("sat", tout << index1 << " " << lit << "\n";);
                if (slack >= bound + p[index1].first) {
                    break;
                }
                m_pb_undef.pop_back();
                to_assign.push_back(lit);
            }

            for (literal lit : to_assign) {
                if (inconsistent()) break;
                assign(p, lit);
            }
        }


        TRACE("sat", display(tout << "assign: " << alit << "\n", p, true););

        return l_undef;
    }

    void ba_solver::watch_literal(wliteral l, pb& p) {
        watch_literal(l.second, p);
    }

    void ba_solver::clear_watch(pb& p) {
        for (wliteral wl : p) unwatch_literal(wl.second, p);            
    }

    /*
      \brief lit <=> conjunction of unconstrained lits
     */
    void ba_solver::assert_unconstrained(literal lit, literal_vector const& lits) {
        if (lit == null_literal) {
            for (literal l : lits) {
                if (value(l) == l_undef) {
                    s().assign(l, justification());
                }
            }
        }
        else {
            // add clauses for: lit <=> conjunction of undef literals
            SASSERT(value(lit) == l_undef);
            literal_vector cl;
            cl.push_back(lit);
            for (literal l : lits) {
                if (value(l) == l_undef) {
                    s().mk_clause(~lit, l);
                    cl.push_back(~l);
                }
            }    
            s().mk_clause(cl);
        }
    }

    void ba_solver::simplify2(pb& p) {
        return;
        if (p.is_cardinality()) {
            literal_vector lits(p.literals());
            unsigned k = (p.k() + p[0].first - 1) / p[0].first;
            add_at_least(p.lit(), lits, k);
            remove_constraint(p);
        }
        else if (p.lit() == null_literal) {
            for (wliteral wl : p) {
                if (p.k() > p.max_sum() - wl.first) {
                    TRACE("sat", 
                          tout << "unit literal " << wl.second << "\n";
                          display(tout, p, true););
                    
                    s().assign(wl.second, justification());
                }
            }
        }
    }

    void ba_solver::simplify(pb_base& p) {
        if (p.lit() != null_literal && value(p.lit()) == l_false) {
            TRACE("sat", tout << "pb: flip sign " << p << "\n";);
            return;
            init_watch(p, !p.lit().sign());
        }
        if (p.lit() != null_literal && value(p.lit()) == l_true) {
            SASSERT(lvl(p.lit()) == 0);
            nullify_tracking_literal(p);
        }

        SASSERT(p.lit() == null_literal || value(p.lit()) == l_undef);

        unsigned true_val = 0, slack = 0, num_false = 0;
        for (unsigned i = 0; i < p.size(); ++i) {
            switch (value(p.get_lit(i))) {
            case l_true: true_val += p.get_coeff(i); break;
            case l_false: ++num_false; break;
            default: slack += p.get_coeff(i); break;
            }
        }
        if (true_val == 0 && num_false == 0) {
            // no op
        }
        else if (true_val >= p.k()) {
            if (p.lit() != null_literal) {
                s().assign(p.lit(), justification());
            }        
            remove_constraint(p);
        }
        else if (slack + true_val < p.k()) {
            if (p.lit() != null_literal) {
                s().assign(~p.lit(), justification());
            }
            else {
                IF_VERBOSE(0, verbose_stream() << "unsat during simplification\n";);
                s().set_conflict(justification());
            }
            remove_constraint(p);
        }
        else if (slack + true_val == p.k()) {
            literal_vector lits(p.literals());
            assert_unconstrained(p.lit(), lits);
            remove_constraint(p);
        }
        else {
            unsigned sz = p.size();
            clear_watch(p);
            for (unsigned i = 0; i < sz; ++i) {
                if (value(p.get_lit(i)) != l_undef) {
                    --sz;
                    p.swap(i, sz);
                    --i;
                }
            }
            p.set_size(sz);
            p.set_k(p.k() - true_val);
            // display(verbose_stream(), c, true);
            if (p.lit() == null_literal) {
                init_watch(p, true);
            }
            else {
                SASSERT(value(p.lit()) == l_undef);
            }
            SASSERT(p.well_formed());
            if (p.is_pb()) simplify2(p.to_pb());
            m_simplify_change = true;
        }
    }

    void ba_solver::display(std::ostream& out, constraint const& c, bool values) const {
        switch (c.tag()) {
        case card_t: display(out, c.to_card(), values); break;
        case pb_t: display(out, c.to_pb(), values); break;
        case xor_t: display(out, c.to_xor(), values); break;
        default: UNREACHABLE(); break;
        }
    }

    void ba_solver::display(std::ostream& out, pb const& p, bool values) const {
        if (p.lit() != null_literal) out << p.lit() << " == ";
        if (p.lit() != null_literal && values) {
            out << "[watch: " << p.num_watch() << ", slack: " << p.slack() << "]";
            out << "@(" << value(p.lit());
            if (value(p.lit()) != l_undef) {
                out << ":" << lvl(p.lit());
            }
            out << "): ";
        }
        for (wliteral wl : p) {
            literal l = wl.second;
            unsigned w = wl.first;
            if (w > 1) out << w << " * ";
            out << l;
            if (values) {
                out << "@(" << value(l);
                if (value(l) != l_undef) {
                    out << ":" << lvl(l);
                }
                out << ") ";
            }
            else {
                out << " ";
            }
        }
        out << ">= " << p.k()  << "\n";
    }

    // --------------------
    // xor:

    void ba_solver::clear_watch(xor& x) {
        unwatch_literal(x[0], x);
        unwatch_literal(x[1], x);         
        unwatch_literal(~x[0], x);
        unwatch_literal(~x[1], x);         
    }

    bool ba_solver::parity(xor const& x, unsigned offset) const {
        bool odd = false;
        unsigned sz = x.size();
        for (unsigned i = offset; i < sz; ++i) {
            SASSERT(value(x[i]) != l_undef);
            if (value(x[i]) == l_true) {
                odd = !odd;
            }
        }
        return odd;
    }

    void ba_solver::init_watch(xor& x, bool is_true) {
        clear_watch(x);
        if (x.lit() != null_literal && x.lit().sign() == is_true) {
            x.negate();
        }
        TRACE("sat", display(tout, x, true););
        unsigned sz = x.size();
        unsigned j = 0;
        for (unsigned i = 0; i < sz && j < 2; ++i) {
            if (value(x[i]) == l_undef) {
                x.swap(i, j);
                ++j;
            }
        }
        switch (j) {
        case 0: 
            if (!parity(x, 0)) {
                unsigned l = lvl(x[0]);
                j = 1;
                for (unsigned i = 1; i < sz; ++i) {
                    if (lvl(x[i]) > l) {
                        j = i;
                        l = lvl(x[i]);
                    } 
                }
                set_conflict(x, x[j]);
            }
            break;
        case 1: 
            assign(x, parity(x, 1) ? ~x[0] : x[0]);
            break;
        default: 
            SASSERT(j == 2);
            watch_literal(x[0], x);
            watch_literal(x[1], x);
            watch_literal(~x[0], x);
            watch_literal(~x[1], x);
            break;
        }
    }


    lbool ba_solver::add_assign(xor& x, literal alit) {
        // literal is assigned     
        unsigned sz = x.size();
        TRACE("sat", tout << "assign: " << x.lit() << ": " << ~alit << "@" << lvl(~alit) << "\n";);

        SASSERT(x.lit() == null_literal || value(x.lit()) == l_true);
        SASSERT(value(alit) != l_undef);
        unsigned index = 0;
        for (; index <= 2; ++index) {
            if (x[index].var() == alit.var()) break;
        }
        if (index == 2) {
            // literal is no longer watched.
            return l_undef;
        }
        SASSERT(x[index].var() == alit.var());
        
        // find a literal to swap with:
        for (unsigned i = 2; i < sz; ++i) {
            literal lit2 = x[i];
            if (value(lit2) == l_undef) {
                x.swap(index, i);
                watch_literal(lit2, x);
                return l_undef;
            }
        }
        if (index == 0) {
            x.swap(0, 1);
        }
        // alit resides at index 1.
        SASSERT(x[1].var() == alit.var());        
        if (value(x[0]) == l_undef) {
            bool p = parity(x, 1);
            assign(x, p ? ~x[0] : x[0]);            
        }
        else if (!parity(x, 0)) {
            set_conflict(x, ~x[1]);
        }      
        return inconsistent() ? l_false : l_true;  
    }

    // ---------------------------
    // conflict resolution
    
    void ba_solver::normalize_active_coeffs() {
        while (!m_active_var_set.empty()) m_active_var_set.erase();
        unsigned i = 0, j = 0, sz = m_active_vars.size();
        for (; i < sz; ++i) {
            bool_var v = m_active_vars[i];
            if (!m_active_var_set.contains(v) && get_coeff(v) != 0) {
                m_active_var_set.insert(v);
                if (j != i) {
                    m_active_vars[j] = m_active_vars[i];
                }
                ++j;
            }
        }
        sz = j;
        m_active_vars.shrink(sz);
    }

    void ba_solver::inc_coeff(literal l, int offset) {
        SASSERT(offset > 0);
        bool_var v = l.var();
        SASSERT(v != null_bool_var);
        if (static_cast<bool_var>(m_coeffs.size()) <= v) {
            m_coeffs.resize(v + 1, 0);
        }
        int coeff0 = m_coeffs[v];
        if (coeff0 == 0) {
            m_active_vars.push_back(v);
        }
        
        int inc = l.sign() ? -offset : offset;
        int coeff1 = inc + coeff0;
        m_coeffs[v] = coeff1;

        if (coeff0 > 0 && inc < 0) {
            m_bound -= coeff0 - std::max(0, coeff1);
        }
        else if (coeff0 < 0 && inc > 0) {
            m_bound -= std::min(0, coeff1) - coeff0;
        }
        // reduce coefficient to be no larger than bound.
        if (coeff1 > m_bound) {
            m_coeffs[v] = m_bound;
        }
        else if (coeff1 < 0 && -coeff1 > m_bound) {
            m_coeffs[v] = -m_bound;
        }
    }

    int ba_solver::get_coeff(bool_var v) const {
        return m_coeffs.get(v, 0);
    }

    int ba_solver::get_abs_coeff(bool_var v) const {
        return abs(get_coeff(v));
    }

    void ba_solver::reset_coeffs() {
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            m_coeffs[m_active_vars[i]] = 0;
        }
        m_active_vars.reset();
    }

    static bool _debug_conflict = false;

    bool ba_solver::resolve_conflict() {        
        if (0 == m_num_propagations_since_pop) {
            return false;
        }
        reset_coeffs();
        m_num_marks = 0;
        m_bound = 0;
        literal consequent = s().m_not_l;
        justification js = s().m_conflict;
        TRACE("sat", tout << consequent << " " << js << "\n";);
        TRACE("sat", s().display(tout););
        m_conflict_lvl = s().get_max_lvl(consequent, js);
        if (consequent != null_literal) {
            consequent.neg();
            process_antecedent(consequent, 1);
        }
        literal_vector const& lits = s().m_trail;
        unsigned idx = lits.size()-1;
        int offset = 1;
        DEBUG_CODE(active2pb(m_A););

        unsigned init_marks = m_num_marks;

        vector<justification> jus;

        // if (null_literal != consequent) std::cout << "resolve " << consequent << " " << value(consequent) << "\n";

        do {

            if (offset == 0) {
                goto process_next_resolvent;            
            }
            // TBD: need proper check for overflow.
            if (offset > (1 << 12)) {
                IF_VERBOSE(12, verbose_stream() << "offset: " << offset << "\n";
                           active2pb(m_A);
                           display(verbose_stream(), m_A);
                           );
                goto bail_out;
            }

            // TRACE("sat", display(tout, m_A););
            TRACE("sat", tout << "process consequent: " << consequent << ":\n"; s().display_justification(tout, js) << "\n";);
            SASSERT(offset > 0);
            SASSERT(m_bound >= 0);

            DEBUG_CODE(justification2pb(js, consequent, offset, m_B););
            
            if (_debug_conflict) {
                std::cout << consequent << "\n";
                s().display_justification(std::cout, js);
                std::cout << "\n";
            }
            switch(js.get_kind()) {
            case justification::NONE:
                SASSERT (consequent != null_literal);
                m_bound += offset;
                break;
            case justification::BINARY:
                m_bound += offset;
                SASSERT (consequent != null_literal);
                inc_coeff(consequent, offset);
                process_antecedent(js.get_literal(), offset);
                break;
            case justification::TERNARY:
                m_bound += offset;
                SASSERT (consequent != null_literal);
                inc_coeff(consequent, offset);
                process_antecedent(js.get_literal1(), offset);
                process_antecedent(js.get_literal2(), offset);
                break;
            case justification::CLAUSE: {
                m_bound += offset;
                clause & c = *(s().m_cls_allocator.get_clause(js.get_clause_offset()));
                unsigned i = 0;
                if (consequent != null_literal) {
                    inc_coeff(consequent, offset);
                    if (c[0] == consequent) {
                        i = 1;
                    }
                    else {
                        SASSERT(c[1] == consequent);
                        process_antecedent(c[0], offset);
                        i = 2;
                    }
                }
                unsigned sz = c.size();
                for (; i < sz; i++)
                    process_antecedent(c[i], offset);
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                constraint& cnstr = index2constraint(js.get_ext_justification_idx());
                ++m_stats.m_num_resolves;
                switch (cnstr.tag()) {
                case card_t: {
                    card& c = cnstr.to_card();
                    m_bound += offset * c.k();
                    process_card(c, offset);
                    break;
                }
                case pb_t: {
                    pb& p = cnstr.to_pb();
                    m_lemma.reset();
                    m_bound += offset;
                    inc_coeff(consequent, offset);
                    get_antecedents(consequent, p, m_lemma);
                    TRACE("sat", display(tout, p, true); tout << m_lemma << "\n";);
                    if (_debug_conflict) {
                        std::cout << consequent << " ";
                        std::cout << "antecedents: " << m_lemma << "\n";
                    }
                    for (literal l : m_lemma) process_antecedent(~l, offset);
                    break;
                }
                case xor_t: {
                    // jus.push_back(js);
                    m_lemma.reset();
                    m_bound += offset;
                    inc_coeff(consequent, offset);
                    get_xor_antecedents(consequent, idx, js, m_lemma);
                    for (literal l : m_lemma) process_antecedent(~l, offset);
                    break;
                }
                default:
                    UNREACHABLE();
                    break;
                }
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            
            SASSERT(validate_lemma());            


            DEBUG_CODE(
                active2pb(m_C);
                //SASSERT(validate_resolvent());
                m_A = m_C;);

            TRACE("sat", display(tout << "conflict:\n", m_A););
            // cut();

        process_next_resolvent:
            
            // find the next marked variable in the assignment stack
            //
            bool_var v;
            while (true) {
                consequent = lits[idx];
                v = consequent.var();
                if (s().is_marked(v)) break;
                if (idx == 0) {
                    IF_VERBOSE(2, verbose_stream() << "did not find marked literal\n";);
                    goto bail_out;
                }
                SASSERT(idx > 0);
                --idx;
            }
            
            SASSERT(lvl(v) == m_conflict_lvl);
            s().reset_mark(v);
            --idx;
            TRACE("sat", tout << "Unmark: v" << v << "\n";);
            --m_num_marks;
            js = s().m_justification[v];
            offset = get_abs_coeff(v);
            if (offset > m_bound) {
                m_coeffs[v] = (get_coeff(v) < 0) ? -m_bound : m_bound;
                offset = m_bound;
                DEBUG_CODE(active2pb(m_A););
            }
            SASSERT(value(consequent) == l_true);

        }        
        while (m_num_marks > 0);
        
        DEBUG_CODE(for (bool_var i = 0; i < static_cast<bool_var>(s().num_vars()); ++i) SASSERT(!s().is_marked(i)););
        SASSERT(validate_lemma());

        normalize_active_coeffs();
        
        int slack = -m_bound;
        for (unsigned i = 0; i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            slack += get_abs_coeff(v);
        }

        m_lemma.reset();        

        m_lemma.push_back(null_literal);
        for (unsigned i = 0; 0 <= slack && i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            int coeff = get_coeff(v);
            lbool val = value(v);
            bool is_true = val == l_true;
            bool append = coeff != 0 && val != l_undef && (coeff < 0 == is_true);
            if (append) {
                literal lit(v, !is_true);
                if (lvl(lit) == m_conflict_lvl) {
                    if (m_lemma[0] == null_literal) {
                        slack -= abs(coeff);
                        m_lemma[0] = ~lit;
                    }
                }
                else {
                    slack -= abs(coeff);
                    m_lemma.push_back(~lit);
                }
            }
        }

#if 0
        if (jus.size() > 1) {
            std::cout << jus.size() << "\n";
            for (unsigned i = 0; i < jus.size(); ++i) {
                s().display_justification(std::cout, jus[i]); std::cout << "\n";
            }
            std::cout << m_lemma << "\n";
            active2pb(m_A);
            display(std::cout, m_A);
        }
#endif


        if (slack >= 0) {
            IF_VERBOSE(2, verbose_stream() << "(sat.card bail slack objective not met " << slack << ")\n";);
            goto bail_out;
        }

        if (m_lemma[0] == null_literal) {
            m_lemma[0] = m_lemma.back();
            m_lemma.pop_back();
            unsigned level = m_lemma.empty() ? 0 : lvl(m_lemma[0]);
            for (unsigned i = 1; i < m_lemma.size(); ++i) {
                if (lvl(m_lemma[i]) > level) {
                    level = lvl(m_lemma[i]);
                    std::swap(m_lemma[0], m_lemma[i]);
                }
            }
            IF_VERBOSE(2, verbose_stream() << "(sat.card set level to " << level << " < " << m_conflict_lvl << ")\n";);
        }        

        SASSERT(slack < 0);

        SASSERT(validate_conflict(m_lemma, m_A));
        
        TRACE("sat", tout << m_lemma << "\n";);

        if (get_config().m_drat) {
            svector<drat::premise> ps; // TBD fill in
            drat_add(m_lemma, ps);
        }

        s().m_lemma.reset();
        s().m_lemma.append(m_lemma);
        for (unsigned i = 1; i < m_lemma.size(); ++i) {
            CTRACE("sat", s().is_marked(m_lemma[i].var()), tout << "marked: " << m_lemma[i] << "\n";);
            s().mark(m_lemma[i].var());
        }

        return true;

    bail_out:
        while (m_num_marks > 0 && idx >= 0) {
            bool_var v = lits[idx].var();
            if (s().is_marked(v)) {
                s().reset_mark(v);
                --m_num_marks;
            }
            if (idx == 0 && !_debug_conflict) {
                _debug_conflict = true;
                // s().display(std::cout);
                std::cout << s().m_not_l << "\n";
                for (literal l : lits) {
                    if (s().is_marked(l.var())) {
                        std::cout << "missing mark: " << l << "\n";
                        s().reset_mark(l.var());
                    }
                }
                m_num_marks = 0;
                resolve_conflict();                
            }
            --idx;
        }
        return false;
    }

    void ba_solver::process_card(card& c, int offset) {
        literal lit = c.lit();
        SASSERT(c.k() <= c.size());       
        SASSERT(lit == null_literal || value(lit) == l_true);
        SASSERT(0 < offset);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            process_antecedent(c[i], offset);
        }
        for (unsigned i = 0; i < c.k(); ++i) {
            inc_coeff(c[i], offset);                        
        }
        if (lit != null_literal) {
            process_antecedent(~lit, c.k() * offset);
        }
    }

    void ba_solver::process_antecedent(literal l, int offset) {
        SASSERT(value(l) == l_false);
        bool_var v = l.var();
        unsigned level = lvl(v);

        if (level > 0 && !s().is_marked(v) && level == m_conflict_lvl) {
            s().mark(v);
            TRACE("sat", tout << "Mark: v" << v << "\n";);
            ++m_num_marks;
        }
        inc_coeff(l, offset);                
    }   

    literal ba_solver::get_asserting_literal(literal p) {
        if (get_abs_coeff(p.var()) != 0) {
            return p;
        }
        unsigned level = 0;        
        for (unsigned i = 0; i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            literal lit(v, get_coeff(v) < 0);
            if (value(lit) == l_false && lvl(lit) > level) {
                p = lit;
                level = lvl(lit);
            }
        }
        return p;        
    }

    ba_solver::ba_solver(): m_solver(0), m_lookahead(0) {        
        TRACE("sat", tout << this << "\n";);
    }

    ba_solver::~ba_solver() {
        m_stats.reset();
        while (!m_constraints.empty()) {
            pop_constraint();
        }
    }

    void ba_solver::add_at_least(bool_var v, literal_vector const& lits, unsigned k) {
        literal lit = v == null_bool_var ? null_literal : literal(v, false);
        add_at_least(lit, lits, k);
    }

    void ba_solver::add_at_least(literal lit, literal_vector const& lits, unsigned k) {
        void * mem = m_allocator.allocate(card::get_obj_size(lits.size()));
        card* c = new (mem) card(lit, lits, k);
        add_constraint(c);
    }

    void ba_solver::add_constraint(constraint* c) {
        m_constraints.push_back(c);
        literal lit = c->lit();
        if (lit == null_literal) {
            init_watch(*c, true);
        }
        else {
            s().set_external(lit.var());
            get_wlist(lit).push_back(c->index());
            get_wlist(~lit).push_back(c->index());
        }        
        SASSERT(c->well_formed());
    }


    void ba_solver::init_watch(constraint& c, bool is_true) {
        switch (c.tag()) {
        case card_t: init_watch(c.to_card(), is_true); break;
        case pb_t: init_watch(c.to_pb(), is_true); break;
        case xor_t: init_watch(c.to_xor(), is_true); break;
        }
    }   

    lbool ba_solver::add_assign(constraint& c, literal l) {
        switch (c.tag()) {
        case card_t: return add_assign(c.to_card(), l); 
        case pb_t: return add_assign(c.to_pb(), l); 
        case xor_t: return add_assign(c.to_xor(), l); 
        }
        UNREACHABLE();
        return l_undef;
    }

    ba_solver::pb const& ba_solver::add_pb_ge(literal lit, svector<wliteral> const& wlits, unsigned k) {
        void * mem = m_allocator.allocate(pb::get_obj_size(wlits.size()));
        pb* p = new (mem) pb(lit, wlits, k);
        add_constraint(p);
        return *p;
    }

    void ba_solver::add_pb_ge(bool_var v, svector<wliteral> const& wlits, unsigned k) {
        literal lit = v == null_bool_var ? null_literal : literal(v, false);
        add_pb_ge(lit, wlits, k);
    }

    void ba_solver::add_xor(bool_var v, literal_vector const& lits) {
        add_xor(literal(v, false), lits);
    }

    void ba_solver::add_xor(literal lit, literal_vector const& lits) {
        void * mem = m_allocator.allocate(xor::get_obj_size(lits.size()));
        xor* x = new (mem) xor(lit, lits);
        add_constraint(x);
        for (literal l : lits) s().set_external(l.var()); // TBD: determine if goal2sat does this.
    }

    void ba_solver::propagate(literal l, ext_constraint_idx idx, bool & keep) {
        SASSERT(value(l) == l_true);
        TRACE("sat", tout << l << " " << idx << "\n";);
        constraint& c = index2constraint(idx);
        if (c.lit() != null_literal && l.var() == c.lit().var()) {
            init_watch(c, !l.sign());
            keep = true;
        }
        else if (c.lit() != null_literal && value(c.lit()) != l_true) {
            keep = false;
        }
        else {
            keep = l_undef != add_assign(c, ~l);
        }
    }


    void ba_solver::ensure_parity_size(bool_var v) {
        if (m_parity_marks.size() <= static_cast<unsigned>(v)) {
            m_parity_marks.resize(static_cast<unsigned>(v) + 1, 0);
        }
    }
    
    unsigned ba_solver::get_parity(bool_var v) {
        return m_parity_marks.get(v, 0);
    }

    void ba_solver::inc_parity(bool_var v) {
        ensure_parity_size(v);
        m_parity_marks[v]++;
    }

    void ba_solver::reset_parity(bool_var v) {
        ensure_parity_size(v);
        m_parity_marks[v] = 0;
    }
    
    /**
       \brief perform parity resolution on xor premises.
       The idea is to collect premises based on xor resolvents. 
       Variables that are repeated an even number of times cancel out.
     */
    void ba_solver::get_xor_antecedents(literal l, unsigned index, justification js, literal_vector& r) {
        unsigned level = lvl(l);
        bool_var v = l.var();
        SASSERT(js.get_kind() == justification::EXT_JUSTIFICATION);
        TRACE("sat", tout << l << ": " << js << "\n"; tout << s().m_trail << "\n";);

        unsigned num_marks = 0;
        unsigned count = 0;
        while (true) {
            ++count;
            if (js.get_kind() == justification::EXT_JUSTIFICATION) {
                constraint& c = index2constraint(js.get_ext_justification_idx());
                if (!c.is_xor()) {
                    r.push_back(l);
                }
                else {
                    xor& x = c.to_xor();
                    if (x.lit() != null_literal && lvl(x.lit()) > 0) r.push_back(x.lit());
                    if (x[1].var() == l.var()) {
                        x.swap(0, 1);
                    }
                    SASSERT(x[0].var() == l.var());
                    for (unsigned i = 1; i < x.size(); ++i) {
                        literal lit(value(x[i]) == l_true ? x[i] : ~x[i]);
                        inc_parity(lit.var());
                        if (true || lvl(lit) == level) {
                            ++num_marks;
                        }
                        else {
                            m_parity_trail.push_back(lit);
                        }
                    }
                }
            }
            else {
                r.push_back(l);
            }
            while (num_marks > 0) {
                l = s().m_trail[index];
                v = l.var();
                unsigned n = get_parity(v);
                if (n > 0) {
                    reset_parity(v);
                    if (n > 1) {
                        IF_VERBOSE(2, verbose_stream() << "parity greater than 1: " << l << " " << n << "\n";);
                    }
                    if (n % 2 == 1) {
                        break;
                    }
                    IF_VERBOSE(2, verbose_stream() << "skip even parity: " << l << "\n";);
                    --num_marks;
                }
                --index;
            }
            if (num_marks == 0) {
                break;
            }
            --index;
            --num_marks;
            js = s().m_justification[v];
        }

        // now walk the defined literals 

        for (unsigned i = 0; i < m_parity_trail.size(); ++i) {
            literal lit = m_parity_trail[i];
            if (get_parity(lit.var()) % 2 == 1) {
                r.push_back(lit);
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "skip even parity: " << lit << "\n";);
            }
            reset_parity(lit.var());
        }
        m_parity_trail.reset();
        TRACE("sat", tout << r << "\n";);
    }

    void ba_solver::get_antecedents(literal l, pb const& p, literal_vector& r) {
        if (p.lit() != null_literal) r.push_back(p.lit());
        SASSERT(p.lit() == null_literal || value(p.lit()) == l_true);
        TRACE("sat", display(tout, p, true););

        if (value(l) == l_false) {
            // The literal comes from a conflict.
            // it is forced true, but assigned to false.
            unsigned slack = 0;
            unsigned miss = 0;
            unsigned worth = 0;
            unsigned k = p.k();
            for (wliteral wl : p) {
                literal lit = wl.second;
                if (lit == l) {
                    worth = wl.first;                    
                }
                else if (value(lit) == l_false) {
                    miss += wl.first;
                }
                else {
                    slack += wl.first;
                }
            }
            SASSERT(slack < k);
            SASSERT(0 < worth);
            
            slack += worth;            
            for (wliteral wl : p) {
                literal lit = wl.second;
                if (lit != l && value(lit) == l_false) {
                    unsigned w = wl.first;
                    if (slack + w >= k) {
                        r.push_back(~lit);
                    }
                    else {
                        slack += w;
                        std::cout << "increase slack by " << w << " to " << slack << " worth: " << worth << "\n";
                    }
                } 
            }
#if 0
            std::cout << p << "\n";
            std::cout << r << "\n";
            std::cout << "slack:" << slack << " miss: " << miss << "\n";
#endif
            return;
        }

        unsigned coeff = 0;
        for (unsigned j = 0; j < p.num_watch(); ++j) {
            if (p[j].second == l) {
                coeff = p[j].first;
                break;
            }
        }
        
        if (_debug_conflict) {
            std::cout << p << "\n";
            std::cout << l << " " << coeff << " num_watch: " << p.num_watch() << "\n";
        }

        CTRACE("sat", coeff == 0, display(tout << l << " coeff: " << coeff << "\n", p, true);); 

        SASSERT(coeff > 0);
        unsigned slack = p.slack() - coeff;
        unsigned i = p.num_watch();

        // skip entries that are not required for unit propagation.
        // slack - coeff + w_head < k
        unsigned h = 0;
        for (; i < p.size() && p[i].first + h + slack < p.k(); ++i) { 
            h += p[i].first;
        }
        for (; i < p.size(); ++i) {
            literal lit = p[i].second;
            CTRACE("sat", l_false != value(lit),
                   tout << l << " index: " << i << " slack: " << slack << " h: " << h << " coeff: " << coeff << "\n";
                   display(tout, p, true);); 
            SASSERT(l_false == value(lit));
            r.push_back(~lit);
        }
    }

    void ba_solver::simplify(xor& x) {
        // no-op
    }

    void ba_solver::get_antecedents(literal l, card const& c, literal_vector& r) {
        DEBUG_CODE(
            bool found = false;
            for (unsigned i = 0; !found && i < c.k(); ++i) {
                found = c[i] == l;
            }
            SASSERT(found););
        
        if (c.lit() != null_literal) r.push_back(c.lit());
        SASSERT(c.lit() == null_literal || value(c.lit()) == l_true);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            SASSERT(value(c[i]) == l_false);
            r.push_back(~c[i]);
        }
    }

    void ba_solver::get_antecedents(literal l, xor const& x, literal_vector& r) {
        if (x.lit() != null_literal) r.push_back(x.lit());
        // TRACE("sat", display(tout << l << " ", x, true););
        SASSERT(x.lit() == null_literal || value(x.lit()) == l_true);
        SASSERT(x[0].var() == l.var() || x[1].var() == l.var());
        if (x[0].var() == l.var()) {
            SASSERT(value(x[1]) != l_undef);
            r.push_back(value(x[1]) == l_true ? x[1] : ~x[1]);                
        }
        else {
            SASSERT(value(x[0]) != l_undef);
            r.push_back(value(x[0]) == l_true ? x[0] : ~x[0]);                
        }
        for (unsigned i = 2; i < x.size(); ++i) {
            SASSERT(value(x[i]) != l_undef);
            r.push_back(value(x[i]) == l_true ? x[i] : ~x[i]);                
        }
    }

    // ----------------------------
    // constraint generic methods

    void ba_solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) {
        get_antecedents(l, index2constraint(idx), r);
    }
    
    void ba_solver::unwatch_literal(literal lit, constraint& c) {
        get_wlist(~lit).erase(watched(c.index()));
    }

    void ba_solver::watch_literal(literal lit, constraint& c) {
        get_wlist(~lit).push_back(watched(c.index()));
    }

    void ba_solver::get_antecedents(literal l, constraint const& c, literal_vector& r) {
        switch (c.tag()) {
        case card_t: get_antecedents(l, c.to_card(), r); break;
        case pb_t: get_antecedents(l, c.to_pb(), r); break;
        case xor_t: get_antecedents(l, c.to_xor(), r); break;
        default: UNREACHABLE(); break;
        }
    }

    void ba_solver::nullify_tracking_literal(constraint& c) {
        if (c.lit() != null_literal) {
            unwatch_literal(c.lit(), c);
            unwatch_literal(~c.lit(), c);
            c.nullify_literal();
        }
    }

    void ba_solver::clear_watch(constraint& c) {
        switch (c.tag()) {
        case card_t:
            clear_watch(c.to_card());
            break;
        case pb_t:
            clear_watch(c.to_pb());
            break;
        case xor_t:
            clear_watch(c.to_xor());
            break;
        default:
            UNREACHABLE();
        }
    }

    void ba_solver::remove_constraint(constraint& c) {
        nullify_tracking_literal(c);
        clear_watch(c);
        c.remove();
        m_constraint_removed = true;
    }

    // --------------------------------
    // validation

    bool ba_solver::validate_unit_propagation(constraint const& c, literal l) const {
        return true;
        switch (c.tag()) {
        case card_t:  return validate_unit_propagation(c.to_card(), l); 
        case pb_t: return validate_unit_propagation(c.to_pb(), l);
        case xor_t: return true;
        default: UNREACHABLE(); break;
        }
        return false;
    }

    bool ba_solver::validate_conflict(constraint const& c) const {
        return eval(c) == l_false;
    }

    lbool ba_solver::eval(constraint const& c) const {
        lbool v1 = c.lit() == null_literal ? l_true : value(c.lit());
        switch (c.tag()) {
        case card_t: return eval(v1, eval(c.to_card())); 
        case pb_t:   return eval(v1, eval(c.to_pb()));
        case xor_t:  return eval(v1, eval(c.to_xor()));
        default: UNREACHABLE(); break;
        }
        return l_undef;        
    }

    lbool ba_solver::eval(lbool a, lbool b) const {
        if (a == l_undef || b == l_undef) return l_undef;
        return (a == b) ? l_true : l_false;
    }

    lbool ba_solver::eval(card const& c) const {
        unsigned trues = 0, undefs = 0;
        for (literal l : c) {
            switch (value(l)) {
            case l_true: trues++; break;
            case l_undef: undefs++; break;
            default: break;
            }
        }
        if (trues + undefs < c.k()) return l_false;
        if (trues >= c.k()) return l_true;
        return l_undef;        
    }

    lbool ba_solver::eval(pb const& p) const {
        unsigned trues = 0, undefs = 0;
        for (wliteral wl : p) {
            switch (value(wl.second)) {
            case l_true: trues += wl.first; break;
            case l_undef: undefs += wl.first; break;
            default: break;
            }
        }
        if (trues + undefs < p.k()) return l_false;
        if (trues >= p.k()) return l_true;
        return l_undef;        
    }

    lbool ba_solver::eval(xor const& x) const {
        bool odd = false;
        
        for (auto l : x) {
            switch (value(l)) {
            case l_true: odd = !odd; break;
            case l_false: break;
            default: return l_undef;
            }
        }
        return odd ? l_true : l_false;
    }

    void ba_solver::validate() {
        if (validate_watch_literals()) {
            for (constraint* c : m_constraints) {
                if (!validate_watched_constraint(*c)) break;
            }
        }
    }

    bool ba_solver::validate_watch_literals() const {
        for (unsigned v = 0; v < s().num_vars(); ++v) {
            literal lit(v, false);
            if (lvl(lit) == 0) continue;
            if (!validate_watch_literal(lit)) return false;
            if (!validate_watch_literal(~lit)) return false;
        }        
        return true;
    }

    bool ba_solver::validate_watch_literal(literal lit) const {
        if (lvl(lit) == 0) return true;
        for (auto const & w : get_wlist(lit)) {
            if (w.get_kind() == watched::EXT_CONSTRAINT) {
                constraint const& c = index2constraint(w.get_ext_constraint_idx());
                if (!c.is_watching(~lit) && lit.var() != c.lit().var()) {
                    std::cout << lit << " " << lvl(lit) << " is not watched in " << c << "\n";
                    display(std::cout, c, true);
                    UNREACHABLE();
                    return false;
                }
            }
        }
        return true;
    }

    bool ba_solver::validate_watched_constraint(constraint const& c) const {
        if (c.lit() != null_literal && value(c.lit()) != l_true) return true;
        if (c.lit() != null_literal && lvl(c.lit()) != 0) {
            if (!is_watching(c.lit(), c) || !is_watching(~c.lit(), c)) {
                std::cout << "Definition literal is not watched " << c.lit() << " " << c << "\n";
                display_watch_list(std::cout, s().m_cls_allocator, get_wlist(c.lit())) << "\n";
                display_watch_list(std::cout, s().m_cls_allocator, get_wlist(~c.lit())) << "\n";
                return false;
            }
        }
        if (eval(c) == l_true) {
            return true;
        }
        literal_vector lits(c.literals());
        for (literal l : lits) {
            if (lvl(l) == 0) continue;
            bool found = is_watching(l, c);
            if (found != c.is_watching(l)) {
                std::cout << "Discrepancy of watched literal: " << l << ": " << c.index() << " " << c << (found?" is watched, but shouldn't be":" not watched, but should be") << "\n";
                display_watch_list(std::cout << l << ": ", s().m_cls_allocator, get_wlist(l)) << "\n";
                display_watch_list(std::cout << ~l << ": ", s().m_cls_allocator, get_wlist(~l)) << "\n";
                std::cout << "value: " << value(l) << " level: " << lvl(l) << "\n";
                display(std::cout, c, true);
                if (c.lit() != null_literal) std::cout << value(c.lit()) << "\n";
                UNREACHABLE();
                exit(1);
                return false;
            }
        }
        return true;
    }
    
    bool ba_solver::is_watching(literal lit, constraint const& c) const {
        for (auto w : get_wlist(~lit)) {
            if (w.get_kind() == watched::EXT_CONSTRAINT && w.get_ext_constraint_idx() == c.index()) 
                return true;
        }
        return false;
    }

    /**
       \brief Lex on (glue, size)
    */
    struct constraint_glue_lt {
        bool operator()(ba_solver::constraint const * c1, ba_solver::constraint const * c2) const {
            return 
                (c1->glue()  < c2->glue()) ||
                (c1->glue() == c2->glue() && c1->size() < c2->size());
        }
    };

    void ba_solver::gc() {
        std::stable_sort(m_learned.begin(), m_learned.end(), constraint_glue_lt());
        gc_half("glue");
        cleanup_constraints(m_learned);
    }

    void ba_solver::gc_half(char const* st_name) {
        TRACE("sat", tout << "gc\n";);
        unsigned sz     = m_learned.size();
        unsigned new_sz = sz/2;
        unsigned j      = new_sz;
        for (unsigned i = new_sz; i < sz; i++) {
            remove_constraint(*(m_learned[i]));
        }
        m_learned.shrink(j);
        IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat-gc :strategy " << st_name << " :deleted " << (sz - j) << ")\n";);

    }

    lbool ba_solver::add_assign(card& c, literal alit) {
        // literal is assigned to false.        
        unsigned sz = c.size();
        unsigned bound = c.k();
        TRACE("sat", tout << "assign: " << c.lit() << ": " << ~alit << "@" << lvl(~alit) << "\n";);

        SASSERT(0 < bound && bound < sz);
        SASSERT(value(alit) == l_false);
        SASSERT(c.lit() == null_literal || value(c.lit()) == l_true);
        unsigned index = 0;
        for (index = 0; index <= bound; ++index) {
            if (c[index] == alit) {
                break;
            }
        }
        if (index == bound + 1) {
            // literal is no longer watched.
            return l_undef;
        }
        SASSERT(index <= bound);
        SASSERT(c[index] == alit);
        
        // find a literal to swap with:
        for (unsigned i = bound + 1; i < sz; ++i) {
            literal lit2 = c[i];
            if (value(lit2) != l_false) {
                c.swap(index, i);
                watch_literal(lit2, c);
                return l_undef;
            }
        }

        // conflict
        if (bound != index && value(c[bound]) == l_false) {
            TRACE("sat", tout << "conflict " << c[bound] << " " << alit << "\n";);
            set_conflict(c, alit);
            return l_false;
        }

        // TRACE("sat", tout << "no swap " << index << " " << alit << "\n";);
        // there are no literals to swap with,
        // prepare for unit propagation by swapping the false literal into 
        // position bound. Then literals in positions 0..bound-1 have to be
        // assigned l_true.
        if (index != bound) {
            c.swap(index, bound);
        }        
        for (unsigned i = 0; i < bound && !inconsistent(); ++i) {
            assign(c, c[i]);
        }

        return inconsistent() ? l_false : l_true;
    }

    void ba_solver::asserted(literal l) {
    }


    check_result ba_solver::check() { return CR_DONE; }

    void ba_solver::push() {
        m_constraint_lim.push_back(m_constraints.size());
    }

    void ba_solver::pop_constraint() {
        constraint* c = m_constraints.back();
        m_constraints.pop_back();
        remove_constraint(*c);
        m_allocator.deallocate(c->obj_size(), c);
    }


    void ba_solver::pop(unsigned n) {        
        TRACE("sat_verbose", tout << "pop:" << n << "\n";);
        unsigned new_lim = m_constraint_lim.size() - n;
        unsigned sz = m_constraint_lim[new_lim];
        while (m_constraints.size() > sz) {
            pop_constraint();
        }
        m_constraint_lim.resize(new_lim);
        m_num_propagations_since_pop = 0;
    }

    void ba_solver::simplify(constraint& c) {
        if (!s().at_base_lvl()) s().pop_to_base_level();
        switch (c.tag()) {
        case card_t:
            simplify(c.to_card());
            break;
        case pb_t:
            simplify(c.to_pb());
            break;
        case xor_t:
            simplify(c.to_xor());
            break;
        default:
            UNREACHABLE();
        }                
    }

    void ba_solver::simplify() {
        if (!s().at_base_lvl()) s().pop_to_base_level();
        unsigned trail_sz;
        do {
            trail_sz = s().init_trail_size();
            IF_VERBOSE(1, verbose_stream() << "(bool-algebra-solver simplify-begin " << trail_sz << ")\n";);
            m_simplify_change = false;
            m_clause_removed = false;
            m_constraint_removed = false;
            // for (constraint* c : m_constraints) simplify(*c);
            init_use_lists();
            remove_unused_defs();
            set_non_external();
            elim_pure();
            subsumption();
            cleanup_clauses();
            cleanup_constraints();
            IF_VERBOSE(1, verbose_stream() << "(bool-algebra-solver simplify-end :trail " << trail_sz << " :vars " << s().num_vars() - trail_sz << ")\n";);
        }        
        while (m_simplify_change || trail_sz < s().init_trail_size());

        mutex_reduction();
        // or could create queue of constraints that are affected
    }

    void ba_solver::mutex_reduction() {
        literal_vector lits;
        for (unsigned v = 0; v < s().num_vars(); ++v) {
            lits.push_back(literal(v, false));
            lits.push_back(literal(v, true));
        }
        vector<literal_vector> mutexes;
        s().find_mutexes(lits, mutexes);
        std::cout << "mutexes: " << mutexes.size() << "\n";
        for (literal_vector& mux : mutexes) {
            if (mux.size() > 2) {
                std::cout << "mux: " << mux << "\n";
                for (unsigned i = 0; i < mux.size(); ++i) mux[i].neg(); 
                add_at_least(null_literal, mux, mux.size() - 1);
            }
        }
    }

    // -------------------------------
    // set literals equivalent

    bool ba_solver::set_root(literal l, literal r) { 
        if (s().is_assumption(l.var())) {
            return false;
        }
        for (unsigned i = m_roots.size(); i < 2 * s().num_vars(); ++i) {
            m_roots.push_back(to_literal(i));
        }
        m_roots[l.index()] = r;
        m_roots[(~l).index()] = ~r;
        return true;
    }

    void ba_solver::flush_roots() {
        if (m_roots.empty()) return;

        // validate();

        m_visited.resize(s().num_vars()*2, false);
        m_constraint_removed = false;
        for (constraint* c : m_constraints) {
            flush_roots(*c);
        }
        cleanup_constraints();

        // validate();
    }

    void ba_solver::recompile(constraint& c) {
        switch (c.tag()) {
        case card_t:
            recompile(c.to_card());
            break;
        case pb_t:
            recompile(c.to_pb());
            break;
        case xor_t:
            NOT_IMPLEMENTED_YET();
            break;
        default:
            UNREACHABLE();
        }                
    }

    void ba_solver::recompile(card& c) {
        // IF_VERBOSE(0, verbose_stream() << "re: " << c << "\n";);
        m_weights.resize(2*s().num_vars(), 0);
        for (literal l : c) {
            ++m_weights[l.index()];
        }
        unsigned k = c.k();
        bool is_card = true;
        unsigned sz = c.size();
        unsigned_vector coeffs;
        for (unsigned i = 0; i < sz && 0 < k; ++i) {
            literal l = c[i];
            unsigned w = m_weights[l.index()];
            unsigned w2 = m_weights[(~l).index()];
            if (w == 0 || w < w2) {
                c.swap(i, sz - 1);
                --sz;
                --i;
            }
            else if (k <= w2) {
                k = 0;
                break;
            }
            else {
                SASSERT(w2 <= w && w2 < k);
                k -= w2;
                w -= w2;
                m_weights[(~l).index()] = 0;        
                m_weights[l.index()] = 0;        
                if (w == 0) {
                    c.swap(i, sz - 1);
                    --sz;
                    --i;
                }    
                else {
                    is_card &= (w == 1);
                    coeffs.push_back(w);
                }
            }
        }
        // clear weights
        for (literal l : c) {
            m_weights[l.index()] = 0;
            m_weights[(~l).index()] = 0;
        }       

        if (k == 0) {
            remove_constraint(c);
            return;
        }

        c.set_size(sz);
        c.set_k(k);

        if (!is_card) {            
            TRACE("sat", tout << "replacing by pb: " << c << "\n";);
            svector<wliteral> wlits;
            for (unsigned i = 0; i < sz; ++i) {
                wlits.push_back(wliteral(coeffs[i], c[i]));
            }
            literal root = c.lit();
            remove_constraint(c);
            pb const& p = add_pb_ge(root, wlits, k);
            IF_VERBOSE(1, verbose_stream() << p << "\n";);
        }
        else {
            // IF_VERBOSE(1, verbose_stream() << "new: " << c << "\n";);
            if (c.lit() == null_literal || value(c.lit()) == l_true) {
                init_watch(c, true);
            }
            SASSERT(c.well_formed());
        }
        
    }

    void ba_solver::recompile(pb& p) {
        IF_VERBOSE(0, verbose_stream() << "re: " << p << "\n";);
        m_weights.resize(2*s().num_vars(), 0);
        for (wliteral wl : p) {
            m_weights[wl.second.index()] += wl.first;
        }
        unsigned k = p.k();
        unsigned sz = p.size();
        for (unsigned i = 0; i < sz && 0 < k; ++i) {
            literal l = p[i].second;
            unsigned w1 = m_weights[l.index()];
            unsigned w2 = m_weights[(~l).index()];
            if (w1 == 0 || w1 < w2) {
                p.swap(i, sz - 1);
                --sz;
                --i;
            }
            else if (k <= w2) {
                k = 0;
                break;
            }
            else {
                SASSERT(w2 <= w1 && w2 < k);
                k -= w2;
                w1 -= w2;
                m_weights[l.index()] = 0;
                m_weights[(~l).index()] = 0;        
                if (w1 == 0) {
                    p.swap(i, sz - 1);
                    --sz;
                    --i;
                }    
                else {
                    p[i] = wliteral(w1, l);            
                }
            }
        }
        // clear weights
        for (wliteral wl : p) {
            m_weights[wl.second.index()] = 0;
            m_weights[(~wl.second).index()] = 0;
        }

        if (k == 0) {
            remove_constraint(p);
            return;
        }

        p.set_size(sz);
        p.set_k(k);
        SASSERT(p.well_formed());

        IF_VERBOSE(0, verbose_stream() << "new: " << p << "\n";);

        if (p.lit() == null_literal || value(p.lit()) == l_true) {
            init_watch(p, true);
        }
    }

    void ba_solver::flush_roots(constraint& c) {
        bool found = c.lit() != null_literal && m_roots[c.lit().index()] != c.lit();
        for (unsigned i = 0; !found && i < c.size(); ++i) {
            found = m_roots[c.get_lit(i).index()] != c.get_lit(i);
        }
        if (!found) return;
        clear_watch(c);
        
        // this could create duplicate literals
        for (unsigned i = 0; i < c.size(); ++i) {
            c.set_lit(i, m_roots[c.get_lit(i).index()]);            
        }

        if (c.lit() != null_literal && m_roots[c.lit().index()] != c.lit()) {
            literal r = m_roots[c.lit().index()];
            nullify_tracking_literal(c);
            c.update_literal(r);
            get_wlist(r).push_back(c.index());
            get_wlist(~r).push_back(c.index());
        }

        bool found_dup = false;
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.get_lit(i);
            if (is_marked(l)) {
                found_dup = true;
                break;
            }
            else {
                mark_visited(l);
                mark_visited(~l);
            }
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.get_lit(i);
            unmark_visited(l);
            unmark_visited(~l);
        }

        if (found_dup) {
            // std::cout << "FOUND DUP " << p << "\n";
            recompile(c);
            return;
        }
        // review for potential incompleteness: if c.lit() == l_false, do propagations happen?
        if (c.lit() == null_literal || value(c.lit()) == l_true) {    
            init_watch(c, true);
        }
        SASSERT(c.well_formed());
    }

    unsigned ba_solver::get_num_non_learned_bin(literal l) {
        return s().m_simplifier.get_num_non_learned_bin(l);
    }

    /*
      \brief garbage collection.
      This entails 
      - finding pure literals, 
      - setting literals that are not used in the extension to non-external.
      - subsumption
      - resolution 
      - blocked literals
     */
    void ba_solver::init_use_lists() {
        m_visited.resize(s().num_vars()*2, false);
        m_clause_use_list.init(s().num_vars());
        m_cnstr_use_list.reset();
        m_cnstr_use_list.resize(2*s().num_vars());
        for (clause* c : s().m_clauses) {
            if (!c->frozen()) 
                m_clause_use_list.insert(*c);
        }
        for (constraint* cp : m_constraints) {
            literal lit = cp->lit();
            if (lit != null_literal) {
                m_cnstr_use_list[lit.index()].push_back(cp);
                m_cnstr_use_list[(~lit).index()].push_back(cp);
            }
            switch (cp->tag()) {
            case card_t: {
                card& c = cp->to_card();
                for (literal l : c) {
                    m_cnstr_use_list[l.index()].push_back(&c);
                    if (lit != null_literal) m_cnstr_use_list[(~l).index()].push_back(&c);
                }  
                break;
            }
            case pb_t: {
                pb& p = cp->to_pb();
                for (wliteral wl : p) {
                    literal l = wl.second;
                    m_cnstr_use_list[l.index()].push_back(&p);
                    if (lit != null_literal) m_cnstr_use_list[(~l).index()].push_back(&p);
                }
                break;
            }
            case xor_t: {
                xor& x = cp->to_xor();
                for (literal l : x) {
                    m_cnstr_use_list[l.index()].push_back(&x);
                    m_cnstr_use_list[(~l).index()].push_back(&x);
                }             
                break;
            }
            }
        }
    }

    void ba_solver::remove_unused_defs() {
        // remove constraints where indicator literal isn't used.
        for (constraint* cp : m_constraints) {
            constraint& c = *cp;
            literal lit = c.lit();
            switch (c.tag()) {
            case card_t: 
            case pb_t: {
                if (lit != null_literal && 
                    use_count(lit) == 1 &&
                    use_count(~lit) == 1 &&
                    get_num_non_learned_bin(lit) == 0 && 
                    get_num_non_learned_bin(~lit) == 0) {
                    remove_constraint(c);
                }
                break;
            }
            default:
                break;
            }
        }
    }
    
    unsigned ba_solver::set_non_external() {
        // set variables to be non-external if they are not used in theory constraints.
        unsigned ext = 0;
        for (unsigned v = 0; v < s().num_vars(); ++v) {
            literal lit(v, false);
            if (s().is_external(v) && m_cnstr_use_list[lit.index()].size() == 0 && m_cnstr_use_list[(~lit).index()].size() == 0 && !s().is_assumption(v)) {
                s().set_non_external(v);
                ++ext;
            }            
        }
        IF_VERBOSE(10, verbose_stream() << "non-external variables converted: " << ext << "\n";);
        return ext;
    }

    bool ba_solver::elim_pure(literal lit) {
        if (value(lit) != l_undef) return false;
        if (!m_cnstr_use_list[lit.index()].empty() && use_count(~lit) == 0 && 
            get_num_non_learned_bin(~lit) == 0) {
            s().assign(lit, justification());
            return true;
        }
        return false;
    }

    unsigned ba_solver::elim_pure() {
        // eliminate pure literals
        unsigned pure_literals = 0;
        for (unsigned v = 0; v < s().num_vars(); ++v) {
            literal lit(v, false);
            if (value(v) != l_undef) continue;
            if (m_cnstr_use_list[lit.index()].empty() &&
                m_cnstr_use_list[(~lit).index()].empty()) continue;

            if (elim_pure(lit) || elim_pure(~lit)) {
                ++pure_literals;
            }
        }
        IF_VERBOSE(10, verbose_stream() << "pure literals converted: " << pure_literals << " " << inconsistent() << "\n";);
        return pure_literals;
    }

    void ba_solver::subsumption() {
        unsigned bin_sub = m_stats.m_num_bin_subsumes;
        unsigned clause_sub = m_stats.m_num_clause_subsumes;
        unsigned card_sub = m_stats.m_num_card_subsumes;
        for (constraint* cp : m_constraints) {
            if (cp->was_removed()) continue;
            switch (cp->tag()) {
            case card_t: {
                card& c = cp->to_card();
                if (c.k() > 1) subsumption(c);
                break;
            }
            default:
                break;                
            }
        }
        IF_VERBOSE(1, verbose_stream() << "binary subsumes: " << m_stats.m_num_bin_subsumes - bin_sub << "\n";);
        IF_VERBOSE(1, verbose_stream() << "clause subsumes: " << m_stats.m_num_clause_subsumes - clause_sub << "\n";);
        IF_VERBOSE(1, verbose_stream() << "card subsumes: " << m_stats.m_num_card_subsumes - card_sub << "\n";);

    }

    void ba_solver::cleanup_clauses() {
        if (!m_clause_removed) return;
        // version in simplify first clears 
        // all watch literals, then reinserts them.
        // this ensures linear time cleanup.
        clause_vector::iterator it = s().m_clauses.begin();
        clause_vector::iterator end = s().m_clauses.end();
        clause_vector::iterator it2 = it;
        for (; it != end; ++it) {
            clause* c = *it;
            if (c->was_removed()) {
                s().detach_clause(*c);
                s().del_clause(*c);
            }
            else {
                if (it2 != it) {
                    *it2 = *it;
                }
                ++it2;
            }
        }
        s().m_clauses.set_end(it2);        
    }
    
    void ba_solver::cleanup_constraints() {
        if (!m_constraint_removed) return;
        cleanup_constraints(m_constraints);
        cleanup_constraints(m_learned);
        m_constraint_removed = false;
    }

    void ba_solver::cleanup_constraints(ptr_vector<constraint>& cs) {
        ptr_vector<constraint>::iterator it = cs.begin();
        ptr_vector<constraint>::iterator it2 = it;
        ptr_vector<constraint>::iterator end = cs.end();
        for (; it != end; ++it) {
            constraint& c = *(*it);
            if (c.was_removed()) {
                m_allocator.deallocate(c.obj_size(), &c);
            }
            else {
                if (it != it2) {
                    *it2 = *it;
                }
                ++it2;
            }
        }
        cs.set_end(it2);
    }

    /*
      \brief subsumption between two cardinality constraints
      - A >= k       subsumes A + B >= k' for k' <= k
      - A + A' >= k  subsumes A + B >= k' for k' + |A'| <= k
      - A + lit >= k self subsumes A + ~lit + B >= k' into A + B >= k' for k' <= k
      - TBD: consider version that generalizes self-subsumption to more than one literal
        A + ~L + B >= k'   =>    A + B >= k'    if A + A' + L >= k and k' + |L| + |A'| <= k
     */
    bool ba_solver::subsumes(card& c1, card& c2, literal_vector & comp) {
        if (c2.lit() != null_literal) return false; 

        unsigned c2_exclusive = 0;
        unsigned common = 0;
        comp.reset();
        for (literal l : c2) {
            if (is_marked(l)) {
                ++common;
            }
            else if (is_marked(~l)) {
                comp.push_back(l);
            }
            else {
                ++c2_exclusive;
            }
        }

        unsigned c1_exclusive = c1.size() - common - comp.size();
        return c1_exclusive + c2.k() + comp.size() <= c1.k();
    }

    bool ba_solver::subsumes(card& c1, clause& c2, literal_vector & comp) {
        unsigned c2_exclusive = 0;
        unsigned common = 0;
        comp.reset();
        for (literal l : c2) {
            if (is_marked(l)) {
                ++common;
            }
            else if (is_marked(~l)) {
                comp.push_back(l);
            }
            else {
                ++c2_exclusive;
            }
        }

        if (!comp.empty()) {
            // self-subsumption is TBD.
            return false;
        }
        unsigned c1_exclusive = c1.size() - common - comp.size();
        return c1_exclusive + 1 <= c1.k();
    }

    literal ba_solver::get_min_occurrence_literal(card const& c) {
        unsigned occ_count = UINT_MAX;
        literal lit = null_literal;
        for (literal l : c) {
            unsigned occ_count1 = m_cnstr_use_list[l.index()].size();
            if (occ_count1 < occ_count) {
                lit = l;
                occ_count = occ_count1;
            }
        }
        return lit;
    }

    void ba_solver::card_subsumption(card& c1, literal lit) {
        literal_vector slit;
        for (constraint* c : m_cnstr_use_list[lit.index()]) {
            if (!c || c->tag() != card_t || c == &c1 || c->was_removed()) {
                continue;
            }
            card& c2 = c->to_card();

            SASSERT(c1.index() != c2.index());
            if (subsumes(c1, c2, slit)) {
                if (slit.empty()) {
                    TRACE("sat", tout << "subsume cardinality\n" << c1.index() << ":" << c1 << "\n" << c2.index() << ":" << c2 << "\n";);
                    remove_constraint(c2);
                    ++m_stats.m_num_card_subsumes;
                }
                else {
                    TRACE("sat", tout << "self subsume carinality\n";);
                    IF_VERBOSE(0, 
                               verbose_stream() << "self-subsume cardinality is TBD\n"; 
                               verbose_stream() << c1 << "\n";
                               verbose_stream() << c2 << "\n";);
#if 0
                    clear_watch(c2);                    
                    for (unsigned i = 0; i < c2.size(); ++i) {
                        if (slit == c2[i]) {
                            c2.swap(i, c2.size() -1);
                            break;
                        }
                    }
                    c2.set_size(c2.size() - 1);
                    init_watch(c2, true);
                    m_simplify_change = true;
#endif
                }
            }
        }
    }

    void ba_solver::clause_subsumption(card& c1, literal lit) {
        SASSERT(!c1.was_removed());
        literal_vector slit;
        clause_use_list::iterator it = m_clause_use_list.get(lit).mk_iterator();
        while (!it.at_end()) {
            clause& c2 = it.curr();
            if (!c2.was_removed() && subsumes(c1, c2, slit)) {
                if (slit.empty()) {
                    TRACE("sat", tout << "remove\n" << c1 << "\n" << c2 << "\n";);
                    c2.set_removed(true);
                    m_clause_removed = true;
                    ++m_stats.m_num_clause_subsumes;
                }
                else {
                    IF_VERBOSE(0, verbose_stream() << "self-subsume clause is TBD\n";);
                    // remove literal slit from c2.
                    TRACE("sat", tout << "TBD remove literals " << slit << " from " << c2 << "\n";);
                }
            }            
            it.next();
        }
    }

    void ba_solver::binary_subsumption(card& c1, literal lit) {
        if (c1.k() + 1 != c1.size()) return;
        SASSERT(is_marked(lit));
        SASSERT(!c1.was_removed());
        watch_list & wlist = get_wlist(~lit);
        watch_list::iterator it = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();
        for (; it != end; ++it) {
            watched w = *it;
            if (w.is_binary_clause() && is_marked(w.get_literal())) {
                ++m_stats.m_num_bin_subsumes;
                // IF_VERBOSE(10, verbose_stream() << c1 << " subsumes (" << lit << " " << w.get_literal() << ")\n";);
            }
            else {
                if (it != it2) {
                    *it2 = *it;
                }
                ++it2;
            }
        }
        if (it != it2) {
            wlist.set_end(it2);
        }
    }

    void ba_solver::subsumption(card& c1) {
        SASSERT(!c1.was_removed());
        if (c1.lit() != null_literal) {
            return;
        }
        for (literal l : c1) mark_visited(l);  
        for (unsigned i = 0; i < std::min(c1.size(), c1.k() + 1); ++i) {
            literal lit = c1[i];            
            card_subsumption(c1, lit);
            clause_subsumption(c1, lit);
            binary_subsumption(c1, lit);                   
        }
        for (literal l : c1) unmark_visited(l);
    }

    void ba_solver::clauses_modifed() {}

    lbool ba_solver::get_phase(bool_var v) { return l_undef; }


    extension* ba_solver::copy(solver* s) {
        ba_solver* result = alloc(ba_solver);
        result->set_solver(s);
        literal_vector lits;
        svector<wliteral> wlits;
        for (constraint* cp : m_constraints) {
            switch (cp->tag()) {
            case card_t: {
                card const& c = cp->to_card();
                lits.reset();
                for (literal l : c) lits.push_back(l);
                result->add_at_least(c.lit(), lits, c.k());        
                break;
            }
            case pb_t: {
                pb const& p = cp->to_pb();
                wlits.reset();
                for (wliteral w : p) {
                    wlits.push_back(w);
                }
                result->add_pb_ge(p.lit(), wlits, p.k());
                break;
            }
            case xor_t: {
                xor const& x = cp->to_xor();
                lits.reset();
                for (literal l : x) lits.push_back(l);
                result->add_xor(x.lit(), lits);        
                break;
            }
            default:
                UNREACHABLE();
            }                
        }

        return result;
    }

    void ba_solver::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {
        literal_set slits(lits);
        bool change = false;
        for (constraint* cp : m_constraints) {
            if (!cp->is_card()) continue;
            card const& c = cp->to_card();
            if (c.size() == c.k() + 1) {
                literal_vector mux;
                for (literal lit : c) {
                    if (slits.contains(~lit)) {
                        mux.push_back(~lit);
                    }
                }
                if (mux.size() <= 1) {
                    continue;
                }

                for (literal m : mux) {
                    slits.remove(m);
                }
                change = true;
                mutexes.push_back(mux);
            }
        }        
        if (!change) return;
        lits.reset();
        for (literal l : slits) {
            lits.push_back(l);
        }
    }

    void ba_solver::display(std::ostream& out, ineq& ineq) const {
        for (unsigned i = 0; i < ineq.m_lits.size(); ++i) {
            out << ineq.m_coeffs[i] << "*" << ineq.m_lits[i] << " ";
        }
        out << ">= " << ineq.m_k << "\n";
    }

    void ba_solver::display(std::ostream& out, xor const& x, bool values) const {
        out << "xor " << x.lit();
        if (x.lit() != null_literal && values) {
            out << "@(" << value(x.lit());
            if (value(x.lit()) != l_undef) {
                out << ":" << lvl(x.lit());
            }
            out << "): ";
        }
        else {
            out << ": ";
        }
        for (unsigned i = 0; i < x.size(); ++i) {
            literal l = x[i];
            out << l;
            if (values) {
                out << "@(" << value(l);
                if (value(l) != l_undef) {
                    out << ":" << lvl(l);
                }
                out << ") ";
            }
            else {
                out << " ";
            }
        }        
        out << "\n";
    }

    void ba_solver::display(std::ostream& out, card const& c, bool values) const {
        if (c.lit() != null_literal) {
            if (values) {
                out << c.lit() << "[" << c.size() << "]";
                out << "@(" << value(c.lit());
                if (value(c.lit()) != l_undef) {
                    out << ":" << lvl(c.lit());
                }
                out << "): ";
            }
            else {
                out << c.lit() << " == ";
            }
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c[i];
            out << l;
            if (values) {
                out << "@(" << value(l);
                if (value(l) != l_undef) {
                    out << ":" << lvl(l);
                }
                out << ") ";
            }
            else {
                out << " ";
            }
        }
        out << ">= " << c.k()  << "\n";
    }

    std::ostream& ba_solver::display(std::ostream& out) const {
        for (constraint const* c : m_constraints) {
            switch (c->tag()) {
            case card_t: 
                out << c->to_card() << "\n";
                break;
            case pb_t:
                out << c->to_pb() << "\n";
                break;
            case xor_t:
                display(out, c->to_xor(), false);
                break;
            default:
                UNREACHABLE();
            }                
        }
        return out;
    }

    std::ostream& ba_solver::display_justification(std::ostream& out, ext_justification_idx idx) const {
        constraint const& cnstr = index2constraint(idx);
        return out << index2constraint(idx);
    }

    void ba_solver::collect_statistics(statistics& st) const {
        st.update("ba propagations", m_stats.m_num_propagations);
        st.update("ba conflicts", m_stats.m_num_conflicts);
        st.update("ba resolves", m_stats.m_num_resolves);
    }

    bool ba_solver::validate_unit_propagation(card const& c, literal alit) const { 
        (void) alit;
        if (c.lit() != null_literal && value(c.lit()) != l_true) return false;
        for (unsigned i = c.k(); i < c.size(); ++i) {
            if (value(c[i]) != l_false) return false;
        }
        return true;
    }

    bool ba_solver::validate_unit_propagation(pb const& p, literal alit) const { 
        if (p.lit() != null_literal && value(p.lit()) != l_true) return false;

        unsigned sum = 0;
        TRACE("sat", display(tout << "validate: " << alit << "\n", p, true););
        for (wliteral wl : p) {
            literal lit = wl.second;
            lbool val = value(lit);
            if (val != l_false && lit != alit) {
                sum += wl.first;
            }
        }
        return sum < p.k();
    }

    bool ba_solver::validate_unit_propagation(xor const& x, literal alit) const {
        if (value(x.lit()) != l_true) return false;
        for (unsigned i = 1; i < x.size(); ++i) {
            if (value(x[i]) == l_undef) return false;
        }
        return true;
    }

    bool ba_solver::validate_lemma() { 
        int val = -m_bound;
        normalize_active_coeffs();
        for (bool_var v : m_active_vars) {
            int coeff = get_coeff(v);
            literal lit(v, false);
            SASSERT(coeff != 0);
            if (coeff < 0 && value(lit) != l_true) {
                val -= coeff;
            }
            else if (coeff > 0 && value(lit) != l_false) {
                val += coeff;
            }
        }
        CTRACE("sat", val >= 0, active2pb(m_A); display(tout, m_A););
        return val < 0;
    }

    void ba_solver::active2pb(ineq& p) {
        normalize_active_coeffs();
        p.reset(m_bound);
        for (bool_var v : m_active_vars) {
            literal lit(v, get_coeff(v) < 0);
            p.m_lits.push_back(lit);
            p.m_coeffs.push_back(get_abs_coeff(v));
        }
    }

    void ba_solver::justification2pb(justification const& js, literal lit, unsigned offset, ineq& ineq) {
        switch (js.get_kind()) {
        case justification::NONE:
            ineq.reset(offset);
            ineq.push(lit, offset);
            break;
        case justification::BINARY:
            ineq.reset(offset);
            ineq.push(lit, offset);
            ineq.push(js.get_literal(), offset);
            break;
        case justification::TERNARY:
            ineq.reset(offset);
            ineq.push(lit, offset);
            ineq.push(js.get_literal1(), offset);
            ineq.push(js.get_literal2(), offset);
            break;
        case justification::CLAUSE: {
            ineq.reset(offset);
            clause & c = *(s().m_cls_allocator.get_clause(js.get_clause_offset()));
            for (literal l : c) ineq.push(l, offset);
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            ext_justification_idx index = js.get_ext_justification_idx();
            constraint& cnstr = index2constraint(index);
            switch (cnstr.tag()) {
            case card_t: {
                card& c = cnstr.to_card();
                ineq.reset(offset*c.k());
                for (literal l : c) ineq.push(l, offset);
                if (c.lit() != null_literal) ineq.push(~c.lit(), offset*c.k());                
                break;
            }
            case pb_t: {
                pb& p = cnstr.to_pb();
                ineq.reset(p.k());
                for (wliteral wl : p) ineq.push(wl.second, wl.first);
                if (p.lit() != null_literal) ineq.push(~p.lit(), p.k());
                break;
            }
            case xor_t: {
                xor& x = cnstr.to_xor();
                literal_vector ls;
                get_antecedents(lit, x, ls);                
                ineq.reset(offset);
                for (literal l : ls) ineq.push(~l, offset);
                literal lxor = x.lit();                
                if (lxor != null_literal) ineq.push(~lxor, offset);
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }


    // validate that m_A & m_B implies m_C

    bool ba_solver::validate_resolvent() {
        u_map<unsigned> coeffs;
        unsigned k = m_A.m_k + m_B.m_k;
        for (unsigned i = 0; i < m_A.m_lits.size(); ++i) {
            unsigned coeff = m_A.m_coeffs[i];
            SASSERT(!coeffs.contains(m_A.m_lits[i].index()));
            coeffs.insert(m_A.m_lits[i].index(), coeff);
        }
        for (unsigned i = 0; i < m_B.m_lits.size(); ++i) {
            unsigned coeff1 = m_B.m_coeffs[i], coeff2;
            literal lit = m_B.m_lits[i];
            if (coeffs.find((~lit).index(), coeff2)) {
                if (coeff1 == coeff2) {
                    coeffs.remove((~lit).index());
                    k += coeff1;
                }
                else if (coeff1 < coeff2) {
                    coeffs.insert((~lit).index(), coeff2 - coeff1);
                    k += coeff1;
                }
                else {
                    SASSERT(coeff2 < coeff1);
                    coeffs.remove((~lit).index());
                    coeffs.insert(lit.index(), coeff1 - coeff2);
                    k += coeff2;
                }
            }
            else if (coeffs.find(lit.index(), coeff2)) {
                coeffs.insert(lit.index(), coeff1 + coeff2);
            }
            else {
                coeffs.insert(lit.index(), coeff1);
            }
        }
        // C is above the sum of A and B
        for (unsigned i = 0; i < m_C.m_lits.size(); ++i) {
            literal lit = m_C.m_lits[i];
            unsigned coeff;
            if (coeffs.find(lit.index(), coeff)) {
                if (coeff > m_C.m_coeffs[i] && m_C.m_coeffs[i] < m_C.m_k) {
                    IF_VERBOSE(0, verbose_stream() << i << ": " << m_C.m_coeffs[i] << " " << m_C.m_k << "\n";);
                    goto violated;
                }
                coeffs.remove(lit.index());
            }
        }
        if (!coeffs.empty()) goto violated;
        if (m_C.m_k > k) goto violated;
        SASSERT(coeffs.empty());
        SASSERT(m_C.m_k <= k);
        return true;

    violated:
        IF_VERBOSE(0, 
                   display(verbose_stream(), m_A);
                   display(verbose_stream(), m_B);
                   display(verbose_stream(), m_C);
                   for (auto& e : coeffs) {
                       verbose_stream() << to_literal(e.m_key) << ": " << e.m_value << "\n";
                   });
        
        return false;
    }

    bool ba_solver::validate_conflict(literal_vector const& lits, ineq& p) { 
        for (literal l : lits) {
            if (value(l) != l_false) {
                TRACE("sat", tout << "literal " << l << " is not false\n";);
                return false;
            }
        }
        unsigned value = 0;        
        for (unsigned i = 0; i < p.m_lits.size(); ++i) {
            unsigned coeff = p.m_coeffs[i];
            if (!lits.contains(p.m_lits[i])) {
                value += coeff;
            }
        }
        CTRACE("sat", value >= p.m_k, tout << "slack: " << value << " bound " << p.m_k << "\n";
               display(tout, p);
               tout << lits << "\n";);
        return value < p.m_k;
    }
    
};

