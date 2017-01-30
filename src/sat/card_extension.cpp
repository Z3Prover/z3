/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    card_extension.cpp

Abstract:

    Extension for cardinality reasoning.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/

#include"card_extension.h"
#include"sat_types.h"

namespace sat {

    card_extension::card::card(unsigned index, literal lit, literal_vector const& lits, unsigned k):
        m_index(index),
        m_lit(lit),
        m_k(k),
        m_size(lits.size()), 
        m_lits(lits) {
    }

    void card_extension::card::negate() {
        m_lit.neg();
        for (unsigned i = 0; i < m_size; ++i) {
            m_lits[i].neg();
        }
        m_k = m_size - m_k + 1;
        SASSERT(m_size >= m_k && m_k > 0);
    }

    void card_extension::init_watch(bool_var v) {
        if (m_var_infos.size() <= static_cast<unsigned>(v)) {
            m_var_infos.resize(static_cast<unsigned>(v)+100);
        }
    }

    void card_extension::init_watch(card& c, bool is_true) {
        clear_watch(c);
        if (c.lit().sign() == is_true) {
            c.negate();
        }
        SASSERT(s().value(c.lit()) == l_true);
        unsigned j = 0, sz = c.size(), bound = c.k();
        if (bound == sz) {
            for (unsigned i = 0; i < sz && !s().inconsistent(); ++i) {
                assign(c, c[i]);
            }
            return;
        }
        // put the non-false literals into the head.
        for (unsigned i = 0; i < sz; ++i) {
            if (s().value(c[i]) != l_false) {
                if (j != i) {
                    c.swap(i, j);
                }
                ++j;
            }
        }
        DEBUG_CODE(
            bool is_false = false;
            for (unsigned k = 0; k < sz; ++k) {
                SASSERT(!is_false || s().value(c[k]) == l_false);
                is_false = s().value(c[k]) == l_false;
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
                if (s().lvl(alit) < s().lvl(c[i])) {
                    c.swap(i, j);
                    alit = c[j];
                }
            }
            set_conflict(c, alit);
        }
        else if (j == bound) {
            for (unsigned i = 0; i < bound && !s().inconsistent(); ++i) {
                assign(c, c[i]);                
            }
        }
        else {
            for (unsigned i = 0; i <= bound; ++i) {
                watch_literal(c, c[i]);
            }
        }
    }

    void card_extension::clear_watch(card& c) {
        unsigned sz = std::min(c.k() + 1, c.size());
        for (unsigned i = 0; i < sz; ++i) {
            unwatch_literal(c[i], &c);            
        }
    }

    void card_extension::unwatch_literal(literal lit, card* c) {
        if (m_var_infos.size() <= static_cast<unsigned>(lit.var())) {
            return;
        }
        ptr_vector<card>* cards = m_var_infos[lit.var()].m_lit_watch[lit.sign()];
        if (cards) {
            remove(*cards, c);        
        }
    }

    void card_extension::remove(ptr_vector<card>& cards, card* c) {
        for (unsigned j = 0; j < cards.size(); ++j) {
            if (cards[j] == c) {                        
                std::swap(cards[j], cards[cards.size()-1]);
                cards.pop_back();
                break;
            }
        }
    }

    void card_extension::assign(card& c, literal lit) {
        if (s().value(lit) == l_true) {
            return;
        }
        m_stats.m_num_propagations++;
        //TRACE("sat", tout << "#prop: " << m_stats.m_num_propagations << " - " << c.lit() << " => " << lit << "\n";);
        SASSERT(validate_unit_propagation(c));
        s().assign(lit, justification::mk_ext_justification(c.index()));
        
    }

    void card_extension::watch_literal(card& c, literal lit) {
        init_watch(lit.var());
        ptr_vector<card>* cards = m_var_infos[lit.var()].m_lit_watch[lit.sign()];
        if (cards == 0) {
            cards = alloc(ptr_vector<card>);
            m_var_infos[lit.var()].m_lit_watch[lit.sign()] = cards;
        }
        cards->push_back(&c);
    }

    void card_extension::set_conflict(card& c, literal lit) {
        SASSERT(validate_conflict(c));
        literal_vector& lits = get_literals();
        SASSERT(s().value(lit) == l_false);
        SASSERT(s().value(c.lit()) == l_true);
        lits.push_back(~c.lit()); 
        lits.push_back(lit);
        unsigned sz = c.size();
        for (unsigned i = c.k(); i < sz; ++i) {
            SASSERT(s().value(c[i]) == l_false);
            lits.push_back(c[i]);
        }

        m_stats.m_num_conflicts++;
        if (!resolve_conflict(c, lits)) {
            s().mk_clause_core(lits.size(), lits.c_ptr(), true);
        }
        SASSERT(s().inconsistent());
    }
    
    void card_extension::normalize_active_coeffs() {
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

    void card_extension::inc_coeff(literal l, int offset) {
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
    }

    int card_extension::get_coeff(bool_var v) const {
        return m_coeffs.get(v, 0);
    }

    int card_extension::get_abs_coeff(bool_var v) const {
        int coeff = get_coeff(v);
        if (coeff < 0) coeff = -coeff;
        return coeff;
    }

    void card_extension::reset_coeffs() {
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            m_coeffs[m_active_vars[i]] = 0;
        }
        m_active_vars.reset();
    }

    bool card_extension::resolve_conflict(card& c, literal_vector const& conflict_clause) {

        bool_var v;
        m_conflict_lvl = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            literal lit = c[i];
            SASSERT(s().value(lit) == l_false);
            m_conflict_lvl = std::max(m_conflict_lvl, s().lvl(lit));
        }
        if (m_conflict_lvl < s().lvl(c.lit()) || m_conflict_lvl == 0) {
            return false;
        }

        reset_coeffs();
        m_num_marks = 0;
        m_bound = c.k();
        m_conflict.reset();
        literal_vector const& lits = s().m_trail;
        unsigned idx = lits.size()-1;
        justification js;
        literal consequent = ~conflict_clause[1];
        process_card(c, 1);
        literal alit;

        while (m_num_marks > 0) {

            v = consequent.var();

            int offset = get_abs_coeff(v);

            if (offset == 0) {
                goto process_next_resolvent;            
            }
            if (offset > 1000) {
                goto bail_out;
            }

            SASSERT(offset > 0);

            js = s().m_justification[v];
            
            int bound = 1;            
            switch(js.get_kind()) {
            case justification::NONE:
                break;
            case justification::BINARY:
                inc_coeff(consequent, offset);
                process_antecedent(~(js.get_literal()), offset);
                break;
            case justification::TERNARY:
                inc_coeff(consequent, offset);
                process_antecedent(~(js.get_literal1()), offset);
                process_antecedent(~(js.get_literal2()), offset);
                break;
            case justification::CLAUSE: {
                inc_coeff(consequent, offset);
                clause & c = *(s().m_cls_allocator.get_clause(js.get_clause_offset()));
                unsigned i   = 0;
                if (consequent != null_literal) {
                    SASSERT(c[0] == consequent || c[1] == consequent);
                    if (c[0] == consequent) {
                        i = 1;
                    }
                    else {
                        process_antecedent(~c[0], offset);
                        i = 2;
                    }
                }
                unsigned sz  = c.size();
                for (; i < sz; i++)
                    process_antecedent(~c[i], offset);
                break;
            }
            case justification::EXT_JUSTIFICATION: {
                unsigned index = js.get_ext_justification_idx();
                card& c2 = *m_constraints[index];
                process_card(c2, offset);
                bound = c2.k();
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
            m_bound += offset * bound;

            // cut();

        process_next_resolvent:
            
            // find the next marked variable in the assignment stack
            //
            while (true) {
                consequent = lits[idx];
                v = consequent.var();
                if (s().is_marked(v)) break;
                SASSERT(idx > 0);
                --idx;
            }
            
            SASSERT(s().lvl(v) == m_conflict_lvl);
            s().reset_mark(v);
            --idx;
            --m_num_marks;
        }        
        
        SASSERT(validate_lemma());

        normalize_active_coeffs();

        if (m_bound > 0 && m_active_vars.empty()) {
            return false;
        }

        int slack = -m_bound;
        for (unsigned i = 0; i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            slack += get_abs_coeff(v);
        }
        
        alit = get_asserting_literal(~consequent);
        slack -= get_abs_coeff(alit.var());
        m_conflict.push_back(alit);

        for (unsigned i = lits.size(); 0 <= slack && i > 0; ) {
            --i;
            literal lit = lits[i];
            bool_var v = lit.var();
            if (m_active_var_set.contains(v) && v != alit.var()) {
                int coeff = get_coeff(v);
                if (coeff < 0 && !lit.sign()) {
                    slack += coeff;
                    m_conflict.push_back(~lit);
                }
                else if (coeff > 0 && lit.sign()) {
                    slack -= coeff;
                    m_conflict.push_back(~lit);
                }
            }
        }
        SASSERT(slack < 0);
        SASSERT(validate_conflict(m_conflict));
        
        s().mk_clause_core(m_conflict.size(), m_conflict.c_ptr(), true);
        return true;

    bail_out:
        while (m_num_marks > 0 && idx > 0) {
            v = lits[idx].var();
            if (s().is_marked(v)) {
                s().reset_mark(v);
            }
            --idx;
        }
        return false;
    }

    void card_extension::process_card(card& c, int offset) {
        SASSERT(c.k() <= c.size());
        SASSERT(s().value(c.lit()) == l_true);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            process_antecedent(c[i], offset);
        }
        for (unsigned i = 0; i < c.k(); ++i) {
            inc_coeff(c[i], offset);                        
        }
        if (s().lvl(c.lit()) > 0) {
            m_conflict.push_back(~c.lit());
        }
    }

    void card_extension::process_antecedent(literal l, int offset) {
        SASSERT(s().value(l) == l_false);
        bool_var v = l.var();
        unsigned lvl = s().lvl(v);

        if (lvl > 0 && !s().is_marked(v) && lvl == m_conflict_lvl) {
            s().mark(v);
            ++m_num_marks;
        }
        inc_coeff(l, offset);                
    }   

    literal card_extension::get_asserting_literal(literal p) {
        if (get_abs_coeff(p.var()) != 0) {
            return p;
        }
        unsigned lvl = 0;        
        for (unsigned i = 0; i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            literal lit(v, get_coeff(v) < 0);
            if (s().value(lit) == l_false && s().lvl(lit) > lvl) {
                p = lit;
            }
        }
        return p;        
    }

    card_extension::card_extension(): m_solver(0) {}

    card_extension::~card_extension() {
        for (unsigned i = 0; i < m_var_infos.size(); ++i) {
            m_var_infos[i].reset();
        }
        m_var_trail.reset();
        m_var_lim.reset();
        m_stats.reset();
    }

    void card_extension::add_at_least(bool_var v, literal_vector const& lits, unsigned k) {
        unsigned index = m_constraints.size();
        card* c = alloc(card, index, literal(v, false), lits, k);
        m_constraints.push_back(c);
        init_watch(v);
        m_var_infos[v].m_card = c;
        m_var_trail.push_back(v);
    }

    void card_extension::propagate(literal l, ext_constraint_idx idx, bool & keep) {
        UNREACHABLE();
    }

    void card_extension::get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) {
        card& c = *m_constraints[idx];

        DEBUG_CODE(
            bool found = false;
            for (unsigned i = 0; !found && i < c.k(); ++i) {
                found = c[i] == l;
            }
            SASSERT(found););

        for (unsigned i = c.k(); i < c.size(); ++i) {
            SASSERT(s().value(c[i]) == l_false);
            r.push_back(c[i]);
        }
    }

    lbool card_extension::add_assign(card& c, literal alit) {
        // literal is assigned to false.        
        unsigned sz = c.size();
        unsigned bound = c.k();
        TRACE("pb", tout << "assign: " << c.lit() << " " << ~alit << " " << bound << "\n";);

        SASSERT(0 < bound && bound < sz);
        SASSERT(s().value(alit) == l_false);
        SASSERT(s().value(c.lit()) == l_true);
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
            if (s().value(lit2) != l_false) {
                c.swap(index, i);
                watch_literal(c, lit2);
                return l_undef;
            }
        }

        // conflict
        if (bound != index && s().value(c[bound]) == l_false) {
            TRACE("sat", tout << "conflict " << c[bound] << " " << alit << "\n";);
            set_conflict(c, alit);
            return l_false;
        }

        TRACE("pb", tout << "no swap " << index << " " << alit << "\n";);
        // there are no literals to swap with,
        // prepare for unit propagation by swapping the false literal into 
        // position bound. Then literals in positions 0..bound-1 have to be
        // assigned l_true.
        if (index != bound) {
            c.swap(index, bound);
        }
        SASSERT(validate_unit_propagation(c));
        
        for (unsigned i = 0; i < bound && !s().inconsistent(); ++i) {
            assign(c, c[i]);
        }

        return s().inconsistent() ? l_false : l_true;
    }

    void card_extension::asserted(literal l) {
        bool_var v = l.var();
        ptr_vector<card>* cards = m_var_infos[v].m_lit_watch[!l.sign()];
        if (cards != 0  && !cards->empty() && !s().inconsistent())  {
            ptr_vector<card>::iterator it = cards->begin(), it2 = it, end = cards->end();
            for (; it != end; ++it) {
                card& c = *(*it);
                if (s().value(c.lit()) != l_true) {
                    continue;
                }
                switch (add_assign(c, l)) {
                case l_false: // conflict
                    for (; it != end; ++it, ++it2) {
                        *it2 = *it;
                    }
                    SASSERT(s().inconsistent());
                    cards->set_end(it2);
                    return;
                case l_undef: // watch literal was swapped
                    break;
                case l_true: // unit propagation, keep watching the literal
                    if (it2 != it) {
                        *it2 = *it;
                    }
                    ++it2;
                    break;
                }
            }
            cards->set_end(it2);
        }

        card* crd = m_var_infos[v].m_card;
        if (crd != 0 && !s().inconsistent()) {
            init_watch(*crd, !l.sign());
        }
    }

    check_result card_extension::check() { return CR_DONE; }

    void card_extension::push() {
        m_var_lim.push_back(m_var_trail.size());
    }

    void card_extension::pop(unsigned n) {        
        unsigned new_lim = m_var_lim.size() - n;
        unsigned sz = m_var_lim[new_lim];
        while (m_var_trail.size() > sz) {
            bool_var v = m_var_trail.back();
            m_var_trail.pop_back();
            if (v != null_bool_var) {
                card* c = m_var_infos[v].m_card;
                clear_watch(*c);
                m_var_infos[v].m_card = 0;
                dealloc(c);
            }
        }
        m_var_lim.resize(new_lim);
    }

    void card_extension::simplify() {}
    void card_extension::clauses_modifed() {}
    lbool card_extension::get_phase(bool_var v) { return l_undef; }

    void card_extension::display_watch(std::ostream& out, bool_var v, bool sign) const {
        watch const* w = m_var_infos[v].m_lit_watch[sign];
        if (w) {
            watch const& wl = *w;
            out << "watch: " << literal(v, sign) << " |-> ";
            for (unsigned i = 0; i < wl.size(); ++i) {
                out << wl[i]->lit() << " ";
            }
            out << "\n";        
        }
    }

    void card_extension::display(std::ostream& out, card& c, bool values) const {
        out << c.lit();
        if (c.lit() != null_literal) {
            if (values) {
                out << "@(" << s().value(c.lit());
                if (s().value(c.lit()) != l_undef) {
                    out << ":" << s().lvl(c.lit());
                }
                out << ")";
            }
            out << c.lit() << "\n";
        }
        else {
            out << " ";
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c[i];
            out << l;
            if (values) {
                out << "@(" << s().value(l);
                if (s().value(l) != l_undef) {
                    out << ":" << s().lvl(l);
                }
                out << ") ";
            }
        }
        out << " >= " << c.k()  << "\n";
    }

    std::ostream& card_extension::display(std::ostream& out) const {
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            display_watch(out, vi, false);
            display_watch(out, vi, true);
        }
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            card* c = m_var_infos[vi].m_card;
            if (c) {
                display(out, *c, true);
            }
        }
        return out;
    }

    void card_extension::collect_statistics(statistics& st) const {
        st.update("card propagations", m_stats.m_num_propagations);
        st.update("card conflicts", m_stats.m_num_conflicts);
    }

    bool card_extension::validate_conflict(card& c) { 
        if (!validate_unit_propagation(c)) return false;
        for (unsigned i = 0; i < c.k(); ++i) {
            if (s().value(c[i]) == l_false) return true;
        }
        return false;
    }
    bool card_extension::validate_unit_propagation(card const& c) { 
        for (unsigned i = c.k(); i < c.size(); ++i) {
            if (s().value(c[i]) != l_false) return false;
        }
        return true;
    }
    bool card_extension::validate_lemma() { 
        int value = -m_bound;
        normalize_active_coeffs();
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            int coeff = get_coeff(v);
            SASSERT(coeff != 0);
            if (coeff < 0 && s().value(v) != l_true) {
                value -= coeff;
            }
            else if (coeff > 0 && s().value(v) != l_false) {
                value += coeff;
            }
        }
        return value < 0;
    }

    bool card_extension::validate_assign(literal_vector const& lits, literal lit) { return true; }
    bool card_extension::validate_conflict(literal_vector const& lits) { return true; }

    
};

