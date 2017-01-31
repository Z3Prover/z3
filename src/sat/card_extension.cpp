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
        m_size(lits.size())
    {
        for (unsigned i = 0; i < lits.size(); ++i) {
            m_lits[i] = lits[i];
        }
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
        SASSERT(value(c.lit()) == l_true);
        unsigned j = 0, sz = c.size(), bound = c.k();
        if (bound == sz) {
            for (unsigned i = 0; i < sz && !s().inconsistent(); ++i) {
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
            for (unsigned k = 0; k < sz; ++k) {
                SASSERT(!is_false || value(c[k]) == l_false);
                is_false = value(c[k]) == l_false;
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
        if (value(lit) == l_true) {
            return;
        }
        m_stats.m_num_propagations++;
        //TRACE("sat", tout << "#prop: " << m_stats.m_num_propagations << " - " << c.lit() << " => " << lit << "\n";);
        SASSERT(validate_unit_propagation(c));
        s().assign(lit, justification::mk_ext_justification(c.index()));
        
    }

    void card_extension::watch_literal(card& c, literal lit) {
        TRACE("sat", tout << "watch: " << lit << "\n";);
        init_watch(lit.var());
        ptr_vector<card>* cards = m_var_infos[lit.var()].m_lit_watch[lit.sign()];
        if (cards == 0) {
            cards = alloc(ptr_vector<card>);
            m_var_infos[lit.var()].m_lit_watch[lit.sign()] = cards;
        }
        TRACE("sat", tout << "insert: " << lit.var() << " " << lit.sign() << "\n";);
        cards->push_back(&c);
    }

    void card_extension::set_conflict(card& c, literal lit) {
        SASSERT(validate_conflict(c));

        m_stats.m_num_conflicts++;
        if (!resolve_conflict(c, lit)) {

            literal_vector& lits = get_literals();
            SASSERT(value(lit) == l_false);
            SASSERT(value(c.lit()) == l_true);
            lits.push_back(~c.lit()); 
            lits.push_back(lit);
            unsigned sz = c.size();
            for (unsigned i = c.k(); i < sz; ++i) {
                SASSERT(value(c[i]) == l_false);
                lits.push_back(c[i]);
            }
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

    bool card_extension::resolve_conflict(card& c, literal alit) {

        bool_var v;
        m_conflict_lvl = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            literal lit = c[i];
            SASSERT(value(lit) == l_false);
            m_conflict_lvl = std::max(m_conflict_lvl, lvl(lit));
        }
        if (m_conflict_lvl < lvl(c.lit()) || m_conflict_lvl == 0) {
            return false;
        }

        reset_coeffs();
        m_num_marks = 0;
        m_bound = c.k();
        m_conflict.reset();
        literal_vector const& lits = s().m_trail;
        unsigned idx = lits.size()-1;
        justification js;
        literal consequent = ~alit;
        process_card(c, 1);

        DEBUG_CODE(active2pb(m_A););

        while (m_num_marks > 0) {
            SASSERT(value(consequent) == l_true);
            v = consequent.var();
            int offset = get_abs_coeff(v);

            if (offset == 0) {
                goto process_next_resolvent;            
            }
            if (offset > 1000) {
                goto bail_out;
            }

            SASSERT(validate_lemma());
            SASSERT(offset > 0);

            js = s().m_justification[v];
            DEBUG_CODE(justification2pb(js, consequent, offset, m_B););
            
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
                SASSERT(c[0] == consequent || c[1] == consequent);
                if (c[0] == consequent) {
                    i = 1;
                }
                else {
                    process_antecedent(~c[0], offset);
                    i = 2;
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
            
            DEBUG_CODE(
                active2pb(m_C);
                SASSERT(validate_resolvent());
                m_A = m_C;);

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
            
            SASSERT(lvl(v) == m_conflict_lvl);
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
        SASSERT(value(c.lit()) == l_true);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            process_antecedent(c[i], offset);
        }
        for (unsigned i = 0; i < c.k(); ++i) {
            inc_coeff(c[i], offset);                        
        }
        if (lvl(c.lit()) > 0) {
            m_conflict.push_back(~c.lit());
        }
    }

    void card_extension::process_antecedent(literal l, int offset) {
        SASSERT(value(l) == l_false);
        bool_var v = l.var();
        unsigned level = lvl(v);

        if (level > 0 && !s().is_marked(v) && level == m_conflict_lvl) {
            s().mark(v);
            ++m_num_marks;
        }
        inc_coeff(l, offset);                
    }   

    literal card_extension::get_asserting_literal(literal p) {
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

    card_extension::card_extension(): m_solver(0) {        
        TRACE("sat", tout << this << "\n";);
    }

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
        card* c = new (memory::allocate(__FILE__,__LINE__, "card", card::get_obj_size(lits.size()))) card(index, literal(v, false), lits, k);
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

        r.push_back(c.lit());
        SASSERT(value(c.lit()) == l_true);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            SASSERT(value(c[i]) == l_false);
            r.push_back(~c[i]);
        }
    }


    lbool card_extension::add_assign(card& c, literal alit) {
        // literal is assigned to false.        
        unsigned sz = c.size();
        unsigned bound = c.k();
        TRACE("sat", tout << "assign: " << c.lit() << " " << ~alit << " " << bound << "\n";);

        SASSERT(0 < bound && bound < sz);
        SASSERT(value(alit) == l_false);
        SASSERT(value(c.lit()) == l_true);
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
                watch_literal(c, lit2);
                return l_undef;
            }
        }

        // conflict
        if (bound != index && value(c[bound]) == l_false) {
            TRACE("sat", tout << "conflict " << c[bound] << " " << alit << "\n";);
            set_conflict(c, alit);
            return l_false;
        }

        TRACE("sat", tout << "no swap " << index << " " << alit << "\n";);
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
        if (v >= m_var_infos.size()) return;
        ptr_vector<card>* cards = m_var_infos[v].m_lit_watch[!l.sign()];
        TRACE("sat", tout << "retrieve: " << v << " " << !l.sign() << "\n";);
        TRACE("sat", tout << "asserted: " << l << " " << (cards ? "non-empty" : "empty") << "\n";);
        if (cards != 0  && !cards->empty() && !s().inconsistent())  {
            ptr_vector<card>::iterator it = cards->begin(), it2 = it, end = cards->end();
            for (; it != end; ++it) {
                card& c = *(*it);
                if (value(c.lit()) != l_true) {
                    continue;
                }
                switch (add_assign(c, ~l)) {
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
        TRACE("sat", tout << "pop:" << n << "\n";);
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

    extension* card_extension::copy(solver* s) {
        card_extension* result = alloc(card_extension);
        result->set_solver(s);
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            literal_vector lits;
            card& c = *m_constraints[i];
            for (unsigned i = 0; i < c.size(); ++i) {
                lits.push_back(c[i]);
            }
            result->add_at_least(c.lit().var(), lits, c.k());
        }
        for (unsigned i = 0; i < m_var_trail.size(); ++i) {
            bool_var v = m_var_trail[i];
            if (v != null_bool_var) {
                card* c = m_var_infos[v].m_card;
                card* c2 = m_constraints[c->index()];
                result->m_var_trail.reserve(v + 10);
                NOT_IMPLEMENTED_YET();
            }
        }
        return result;
    }


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
        if (c.lit() != null_literal && values) {
            out << "@(" << value(c.lit());
            if (value(c.lit()) != l_undef) {
                out << ":" << lvl(c.lit());
            }
            out << "): ";
        }
        else {
            out << ": ";
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

    std::ostream& card_extension::display(std::ostream& out) const {
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            display_watch(out, vi, false);
            display_watch(out, vi, true);
        }
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            card* c = m_var_infos[vi].m_card;
            if (c) {
                display(out, *c, false);
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
            if (value(c[i]) == l_false) return true;
        }
        return false;
    }
    bool card_extension::validate_unit_propagation(card const& c) { 
        if (value(c.lit()) != l_true) return false;
        for (unsigned i = c.k(); i < c.size(); ++i) {
            if (value(c[i]) != l_false) return false;
        }
        return true;
    }
    bool card_extension::validate_lemma() { 
        int val = -m_bound;
        normalize_active_coeffs();
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
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
        return val < 0;
    }

    void card_extension::active2pb(ineq& p) {
        normalize_active_coeffs();
        p.reset(m_bound);
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            literal lit(v, get_coeff(v) < 0);
            p.m_lits.push_back(lit);
            p.m_coeffs.push_back(get_abs_coeff(v));
        }
    }

    void card_extension::justification2pb(justification const& js, literal lit, unsigned offset, ineq& p) {
        switch (js.get_kind()) {
        case justification::NONE:
            p.reset(0);
            break;
        case justification::BINARY:
            p.reset(offset);
            p.push(lit, offset);
            p.push(~js.get_literal(), offset);
            break;
        case justification::TERNARY:
            p.reset(offset);
            p.push(lit, offset);
            p.push(~(js.get_literal1()), offset);
            p.push(~(js.get_literal2()), offset);
            break;
        case justification::CLAUSE: {
            p.reset(offset);
            clause & c = *(s().m_cls_allocator.get_clause(js.get_clause_offset()));
            unsigned sz  = c.size();
            for (unsigned i = 0; i < sz; i++)
                p.push(~c[i], offset);
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            unsigned index = js.get_ext_justification_idx();
            card& c = *m_constraints[index];
            p.reset(offset*c.k());
            for (unsigned i = 0; i < c.size(); ++i) {
                p.push(c[i], offset);
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }


    // validate that m_A & m_B implies m_C

    bool card_extension::validate_resolvent() {
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
                SASSERT(coeff <= m_C.m_coeffs[i]);
                coeffs.remove(lit.index());
            }
        }
        SASSERT(coeffs.empty());
        SASSERT(m_C.m_k <= k);
        return true;
    }

    bool card_extension::validate_conflict(literal_vector const& lits) { 
        for (unsigned i = 0; i < lits.size(); ++i) {
            if (value(lits[i]) != l_false) return false;
        }
        return true; 
    }

    
};

