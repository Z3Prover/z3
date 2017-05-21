/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    card_extension.cpp

Abstract:

    Extension for cardinality and xor reasoning.

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
        m_size(lits.size()) {
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

    card_extension::pb::pb(unsigned index, literal lit, svector<card_extension::wliteral> const& wlits, unsigned k):
        m_index(index),
        m_lit(lit),
        m_k(k),
        m_size(wlits.size()),
        m_slack(0),
        m_num_watch(0),
        m_max_sum(0) {
        for (unsigned i = 0; i < wlits.size(); ++i) {
            m_wlits[i] = wlits[i];
            if (m_max_sum + wlits[i].first < m_max_sum) {
                throw default_exception("addition of pb coefficients overflows");
            }
            m_max_sum += wlits[i].first;
        }
    }

    void card_extension::pb::negate() {
        m_lit.neg();
        unsigned w = 0;
        for (unsigned i = 0; i < m_size; ++i) {
            m_wlits[i].second.neg();
            w += m_wlits[i].first;
        }
        m_k = w - m_k + 1;
        SASSERT(w >= m_k && m_k > 0);
    }

    card_extension::xor::xor(unsigned index, literal lit, literal_vector const& lits):
        m_index(index),
        m_lit(lit),
        m_size(lits.size())
    {
        for (unsigned i = 0; i < lits.size(); ++i) {
            m_lits[i] = lits[i];
        }
    }

    void card_extension::init_watch(bool_var v) {
        if (m_var_infos.size() <= static_cast<unsigned>(v)) {
            m_var_infos.resize(static_cast<unsigned>(v)+100);
        }
    }

    void card_extension::init_watch(card& c, bool is_true) {
        clear_watch(c);
        if (c.lit() != null_literal && c.lit().sign() == is_true) {
            c.negate();
        }
        TRACE("sat", display(tout << "init watch: ", c, true););
        SASSERT(c.lit() == null_literal || value(c.lit()) == l_true);
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
        ptr_vector<card>*& cards = m_var_infos[lit.var()].m_card_watch[lit.sign()];
        if (!is_tag_empty(cards)) {
            if (remove(*cards, c)) {
                cards = set_tag_empty(cards);
            }        
        }
    }

    void card_extension::assign(card& c, literal lit) {
        switch (value(lit)) {
        case l_true: 
            break;
        case l_false: 
            set_conflict(c, lit); 
            break;
        default:
            m_stats.m_num_card_propagations++;
            m_num_propagations_since_pop++;
            //TRACE("sat", tout << "#prop: " << m_stats.m_num_propagations << " - " << c.lit() << " => " << lit << "\n";);
            SASSERT(validate_unit_propagation(c));
            if (s().m_config.m_drat) {
                svector<drat::premise> ps;
                literal_vector lits;
                if (c.lit() != null_literal) lits.push_back(~c.lit());
                for (unsigned i = c.k(); i < c.size(); ++i) {
                    lits.push_back(c[i]);
                }
                lits.push_back(lit);
                ps.push_back(drat::premise(drat::s_ext(), c.lit())); // null_literal case.
                s().m_drat.add(lits, ps);
            }
            s().assign(lit, justification::mk_ext_justification(c.index()));
            break;
        }
    }

    void card_extension::watch_literal(card& c, literal lit) {
        TRACE("sat_verbose", tout << "watch: " << lit << "\n";);
        init_watch(lit.var());
        ptr_vector<card>* cards = m_var_infos[lit.var()].m_card_watch[lit.sign()];
        if (cards == 0) {
            cards = alloc(ptr_vector<card>);
            m_var_infos[lit.var()].m_card_watch[lit.sign()] = cards;
        }
        else if (is_tag_empty(cards)) {
            cards = set_tag_non_empty(cards);
            m_var_infos[lit.var()].m_card_watch[lit.sign()] = cards;            
        }
        TRACE("sat_verbose", tout << "insert: " << lit.var() << " " << lit.sign() << "\n";);
        cards->push_back(&c);
    }

    void card_extension::set_conflict(card& c, literal lit) {
        m_stats.m_num_card_conflicts++;
        TRACE("sat", display(tout, c, true); );
        SASSERT(validate_conflict(c));
        SASSERT(value(lit) == l_false);
        s().set_conflict(justification::mk_ext_justification(c.index()), ~lit);
        SASSERT(s().inconsistent());
    }

    // pb:

    void card_extension::copy_pb(card_extension& result) {
        for (unsigned i = 0; i < m_pbs.size(); ++i) {
            svector<wliteral> wlits;
            pb& p = *m_pbs[i];
            for (unsigned i = 0; i < p.size(); ++i) {
                wlits.push_back(p[i]);
            }
            bool_var v = p.lit() == null_literal ? null_bool_var : p.lit().var();
            result.add_pb_ge(v, wlits, p.k());
        }
    }

    // watch a prefix of literals, such that the slack of these is >= k
    void card_extension::init_watch(pb& p, bool is_true) {
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
            SASSERT(value(p[j].second) == l_false);
            for (unsigned i = j + 1; i < sz; ++i) {
                if (lvl(lit) < lvl(p[i].second)) {
                    lit = p[i].second;
                }
            }
            set_conflict(p, lit);
        }
        else {            
            for (unsigned i = 0; i < num_watch; ++i) {
                watch_literal(p, p[i]);
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
    void card_extension::add_index(pb& p, unsigned index, literal lit) {
        if (value(lit) == l_undef) {
            m_pb_undef.push_back(index);
            if (p[index].first > m_a_max) {
                m_a_max = p[index].first;
            }
        }
    }

    lbool card_extension::add_assign(pb& p, literal alit) {

        TRACE("sat", display(tout << "assign: " << alit << "\n", p, true););
        SASSERT(!s().inconsistent());
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
                watch_literal(p, p[j]);
                p.swap(num_watch, j);
                add_index(p, num_watch, lit);
                ++num_watch;
            }
        }

        SASSERT(!s().inconsistent());
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

        // swap out the watched literal.
        --num_watch;
        SASSERT(num_watch > 0);
        p.set_slack(slack);
        p.set_num_watch(num_watch);
        p.swap(num_watch, index);

        if (slack < bound + m_a_max) {
            TRACE("sat", display(tout, p, false); for(auto j : m_pb_undef) tout << j << "\n";);
            literal_vector to_assign;
            while (!m_pb_undef.empty()) {
                index1 = m_pb_undef.back();
                literal lit = p[index1].second;
                TRACE("sat", tout << index1 << " " << lit << "\n";);
                if (slack >= bound + p[index1].first) {
                    break;
                }
                m_pb_undef.pop_back();
                to_assign.push_back(lit);
            }

            for (literal lit : to_assign) {
                if (s().inconsistent()) break;
                if (value(lit) == l_undef) {
                    assign(p, lit);
                }				
            }
        }


        TRACE("sat", display(tout << "assign: " << alit << "\n", p, true););

        return l_undef;
    }

    void card_extension::watch_literal(pb& p, wliteral l) {
        literal lit = l.second;
        init_watch(lit.var());
        ptr_vector<pb>* pbs = m_var_infos[lit.var()].m_pb_watch[lit.sign()];
        if (pbs == 0) {
            pbs = alloc(ptr_vector<pb>);
            m_var_infos[lit.var()].m_pb_watch[lit.sign()] = pbs;
        }
        else if (is_tag_empty(pbs)) {
            pbs = set_tag_non_empty(pbs);
            m_var_infos[lit.var()].m_pb_watch[lit.sign()] = pbs;            
        }
        TRACE("sat_verbose", tout << "insert: " << lit.var() << " " << lit.sign() << "\n";);
        pbs->push_back(&p);
    }

    void card_extension::clear_watch(pb& p) {
        unsigned sz = p.size();
        for (unsigned i = 0; i < sz; ++i) {
            unwatch_literal(p[i].second, &p);            
        }
    }
    
    void card_extension::unwatch_literal(literal lit, pb* p) {
        if (m_var_infos.size() <= static_cast<unsigned>(lit.var())) {
            return;
        }
        pb_watch*& pbs = m_var_infos[lit.var()].m_pb_watch[lit.sign()];
        if (!is_tag_empty(pbs)) {
            if (remove(*pbs, p)) {
                pbs = set_tag_empty(pbs);
            }        
        }
    }

    void card_extension::set_conflict(pb& p, literal lit) {
        m_stats.m_num_pb_conflicts++;
        TRACE("sat", display(tout, p, true); );
        // SASSERT(validate_conflict(p));
        SASSERT(value(lit) == l_false);
        s().set_conflict(justification::mk_ext_justification(p.index()), ~lit);
        SASSERT(s().inconsistent());
    }

    void card_extension::assign(pb& p, literal lit) {
        switch (value(lit)) {
        case l_true: 
            break;
        case l_false: 
            set_conflict(p, lit); 
            break;
        default:
            SASSERT(validate_unit_propagation(p, lit));
            m_stats.m_num_pb_propagations++;
            m_num_propagations_since_pop++;
            if (s().m_config.m_drat) {
                svector<drat::premise> ps;
                literal_vector lits;
                get_pb_antecedents(lit, p, lits);
                lits.push_back(lit);
                ps.push_back(drat::premise(drat::s_ext(), p.lit()));
                s().m_drat.add(lits, ps);
            }
            s().assign(lit, justification::mk_ext_justification(p.index()));
            break;
        }
    }

    void card_extension::display(std::ostream& out, pb const& p, bool values) const {
        if (p.lit() != null_literal) out << p.lit();
        out << "[watch: " << p.num_watch() << ", slack: " << p.slack() << "]";
        if (p.lit() != null_literal && values) {
            out << "@(" << value(p.lit());
            if (value(p.lit()) != l_undef) {
                out << ":" << lvl(p.lit());
            }
            out << "): ";
        }
        else {
            out << ": ";
        }
        for (unsigned i = 0; i < p.size(); ++i) {
            literal l = p[i].second;
            unsigned w = p[i].first;
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

    void card_extension::asserted_pb(literal l, ptr_vector<pb>* pbs, pb* p0) {
        TRACE("sat", tout << "literal: " << l << " has pb: " << !is_tag_empty(pbs) << " p0 != 0: " << (p0 != 0) << "\n";);
        if (!is_tag_empty(pbs)) {
            ptr_vector<pb>::iterator begin = pbs->begin();
            ptr_vector<pb>::iterator it = begin, it2 = it, end = pbs->end();
            for (; it != end; ++it) {
                pb& p = *(*it);
                if (p.lit() != null_literal && value(p.lit()) != l_true) {
                    continue;
                }
                switch (add_assign(p, ~l)) {
                case l_true: // unit propagation, keep watching the literal
                    if (it2 != it) {
                        *it2 = *it;
                    }
                    ++it2;
                    break;
                case l_false: // conflict.
                    SASSERT(s().inconsistent());
                    for (; it != end; ++it, ++it2) {
                        *it2 = *it;
                    }
                    pbs->set_end(it2);
                    return;                
                case l_undef: // watch literal was swapped
                    if (s().inconsistent()) {
                        ++it;
                        for (; it != end; ++it, ++it2) {
                            *it2 = *it;
                        }
                        pbs->set_end(it2);
                        return;
                    }
                    break; 
                }
            }
            pbs->set_end(it2);
            if (pbs->empty()) {
                m_var_infos[l.var()].m_pb_watch[!l.sign()] = set_tag_empty(pbs);
            }
        }

        if (p0 != 0 && !s().inconsistent()) {
            init_watch(*p0, !l.sign());
        }        
    }

    // xor:

    void card_extension::copy_xor(card_extension& result) {
        for (unsigned i = 0; i < m_xors.size(); ++i) {
            literal_vector lits;
            xor& x = *m_xors[i];
            for (unsigned i = 0; i < x.size(); ++i) {
                lits.push_back(x[i]);
            }
            bool_var v = x.lit() == null_literal ? null_bool_var : x.lit().var();
            result.add_xor(v, lits);
        }
    }

    void card_extension::clear_watch(xor& x) {
        unwatch_literal(x[0], &x);
        unwatch_literal(x[1], &x);         
    }

    void card_extension::unwatch_literal(literal lit, xor* c) {
        if (m_var_infos.size() <= static_cast<unsigned>(lit.var())) {
            return;
        }
        xor_watch*& xors = m_var_infos[lit.var()].m_xor_watch;
        if (!is_tag_empty(xors)) {
            if (remove(*xors, c)) {
                xors = set_tag_empty(xors);
            }        
        }
    }

    bool card_extension::parity(xor const& x, unsigned offset) const {
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

    void card_extension::init_watch(xor& x, bool is_true) {
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
                literal_set litset;
                for (unsigned i = 0; i < sz; ++i) {
                    litset.insert(x[i]);
                }
                literal_vector const& lits = s().m_trail;
                unsigned idx = lits.size()-1;
                while (!litset.contains(lits[idx])) {
                    --idx;
                }                
                set_conflict(x, lits[idx]);
            }
            break;
        case 1: 
            assign(x, parity(x, 1) ? ~x[0] : x[0]);
            break;
        default: 
            SASSERT(j == 2);
            watch_literal(x, x[0]);
            watch_literal(x, x[1]);
            break;
        }
    }

    void card_extension::assign(xor& x, literal lit) {
        SASSERT(!s().inconsistent());
        switch (value(lit)) {
        case l_true: 
            break;
        case l_false: 
            set_conflict(x, lit); 
            SASSERT(s().inconsistent());
            break;
        default:
            m_stats.m_num_xor_propagations++;
            m_num_propagations_since_pop++;
            if (s().m_config.m_drat) {
                svector<drat::premise> ps;
                literal_vector lits;
                if (x.lit() != null_literal) lits.push_back(~x.lit());
                for (unsigned i = 1; i < x.size(); ++i) {
                    lits.push_back(x[i]);
                }
                lits.push_back(lit);
                ps.push_back(drat::premise(drat::s_ext(), x.lit()));
                s().m_drat.add(lits, ps);
            }
            TRACE("sat", display(tout << lit << " ", x, true););
            s().assign(lit, justification::mk_ext_justification(x.index()));
            break;
        }
    }

    void card_extension::watch_literal(xor& x, literal lit) {
        TRACE("sat_verbose", tout << "watch: " << lit << "\n";);
        init_watch(lit.var());
        xor_watch*& xors = m_var_infos[lit.var()].m_xor_watch;
        if (xors == 0) {
            xors = alloc(ptr_vector<xor>);
        }
        else if (is_tag_empty(xors)) {
            xors = set_tag_non_empty(xors);
        }
        xors->push_back(&x);
        TRACE("sat_verbose", tout << "insert: " << lit.var() << " " << lit.sign() << "\n";);
    }


    void card_extension::set_conflict(xor& x, literal lit) {
        m_stats.m_num_xor_conflicts++;
        TRACE("sat", display(tout, x, true); );
        if (value(lit) == l_true) lit.neg();
        SASSERT(validate_conflict(x));
        TRACE("sat", display(tout << lit << " ", x, true););
        s().set_conflict(justification::mk_ext_justification(x.index()), ~lit);
        SASSERT(s().inconsistent());
    }

    lbool card_extension::add_assign(xor& x, literal alit) {
        // literal is assigned     
        unsigned sz = x.size();
        TRACE("sat", tout << "assign: " << x.lit() << ": " << ~alit << "@" << lvl(~alit) << "\n";);

        SASSERT(value(alit) != l_undef);
        SASSERT(x.lit() == null_literal || value(x.lit()) == l_true);
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
                watch_literal(x, lit2);
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
        return s().inconsistent() ? l_false : l_true;  
    }

    void card_extension::asserted_xor(literal l, ptr_vector<xor>* xors, xor* x) {
        TRACE("sat", tout << l << " " << !is_tag_empty(xors) << " " << (x != 0) << "\n";);
        if (!is_tag_empty(xors)) {
            ptr_vector<xor>::iterator begin = xors->begin();
            ptr_vector<xor>::iterator it = begin, it2 = it, end = xors->end();
            for (; it != end; ++it) {
                xor& c = *(*it);
                if (c.lit() != null_literal && value(c.lit()) != l_true) {
                    continue;
                }
                switch (add_assign(c, ~l)) {
                case l_false: // conflict
                    for (; it != end; ++it, ++it2) {
                        *it2 = *it;
                    }
                    SASSERT(s().inconsistent());
                    xors->set_end(it2);
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
            xors->set_end(it2);
            if (xors->empty()) {
                m_var_infos[l.var()].m_xor_watch = set_tag_empty(xors);
            }
        }

        if (x != 0 && !s().inconsistent()) {
            init_watch(*x, !l.sign());
        }
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
        // reduce coefficient to be no larger than bound.
        if (coeff1 > m_bound) {
            m_coeffs[v] = m_bound;
        }
        else if (coeff1 < 0 && -coeff1 > m_bound) {
            m_coeffs[v] = -m_bound;
        }
    }

    int card_extension::get_coeff(bool_var v) const {
        return m_coeffs.get(v, 0);
    }

    int card_extension::get_abs_coeff(bool_var v) const {
        return abs(get_coeff(v));
    }

    void card_extension::reset_coeffs() {
        for (unsigned i = 0; i < m_active_vars.size(); ++i) {
            m_coeffs[m_active_vars[i]] = 0;
        }
        m_active_vars.reset();
    }


    bool card_extension::resolve_conflict() {        
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
                unsigned index = js.get_ext_justification_idx();
                if (is_card_index(index)) {
                    card& c = index2card(index);
                    m_bound += offset * c.k();
                    process_card(c, offset);
                    ++m_stats.m_num_card_resolves;
                }
                else if (is_xor_index(index)) {
                    // jus.push_back(js);
                    m_lemma.reset();
                    m_bound += offset;
                    inc_coeff(consequent, offset);
                    get_xor_antecedents(consequent, idx, js, m_lemma);
                    for (unsigned i = 0; i < m_lemma.size(); ++i) {
                        process_antecedent(~m_lemma[i], offset);
                    }
                    ++m_stats.m_num_xor_resolves;
                }
                else if (is_pb_index(index)) {
                    pb& p = index2pb(index);
                    m_lemma.reset();
                    m_bound += offset;
                    inc_coeff(consequent, offset);
                    get_pb_antecedents(consequent, p, m_lemma);
                    TRACE("sat", display(tout, p, true); tout << m_lemma << "\n";);
                    for (unsigned i = 0; i < m_lemma.size(); ++i) {
                        process_antecedent(~m_lemma[i], offset);
                    }
                    ++m_stats.m_num_pb_resolves;
                }
                else {
                    UNREACHABLE();
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

#if 1
        m_lemma.push_back(null_literal);
        for (unsigned i = 0; 0 <= slack && i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            int coeff = get_coeff(v);
            lbool val = m_solver->value(v);
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

        if (jus.size() > 1) {
            std::cout << jus.size() << "\n";
            for (unsigned i = 0; i < jus.size(); ++i) {
                s().display_justification(std::cout, jus[i]); std::cout << "\n";
            }
            std::cout << m_lemma << "\n";
            active2pb(m_A);
            display(std::cout, m_A);
        }


        if (slack >= 0) {
            IF_VERBOSE(2, verbose_stream() << "(sat.card bail slack objective not met " << slack << ")\n";);
            goto bail_out;
        }

        if (m_lemma[0] == null_literal) {
            m_lemma[0] = m_lemma.back();
            m_lemma.pop_back();
            unsigned level = lvl(m_lemma[0]);
            for (unsigned i = 1; i < m_lemma.size(); ++i) {
                if (lvl(m_lemma[i]) > level) {
                    level = lvl(m_lemma[i]);
                    std::swap(m_lemma[0], m_lemma[i]);
                }
            }
            IF_VERBOSE(2, verbose_stream() << "(sat.card set level to " << level << " < " << m_conflict_lvl << ")\n";);
        }        
#else
        ++idx;
        while (0 <= slack) {            
            literal lit = lits[idx];
            bool_var v = lit.var();
            if (m_active_var_set.contains(v)) {
                int coeff = get_coeff(v);
                if (coeff < 0 && !lit.sign()) {
                    slack += coeff;
                    m_lemma.push_back(~lit);
                }
                else if (coeff > 0 && lit.sign()) {
                    slack -= coeff;
                    m_lemma.push_back(~lit);
                }
            }
            if (idx == 0 && slack >= 0) {
                IF_VERBOSE(2, verbose_stream() << "(sat.card non-asserting)\n";);
                goto bail_out;
            }
            SASSERT(idx > 0 || slack < 0);
            --idx;
        }
        if (m_lemma.size() >= 2 && lvl(m_lemma[1]) == m_conflict_lvl) {
            // TRACE("sat", tout << "Bail out on no progress " << lit << "\n";);
            IF_VERBOSE(2, verbose_stream() << "(sat.card bail non-asserting resolvent)\n";);
            goto bail_out;
        }

#endif


        SASSERT(slack < 0);

        SASSERT(validate_conflict(m_lemma, m_A));
        
        TRACE("sat", tout << m_lemma << "\n";);

        if (s().m_config.m_drat) {
            svector<drat::premise> ps; // TBD fill in
            s().m_drat.add(m_lemma, ps);
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
            --idx;
        }
        return false;
    }

    void card_extension::process_card(card& c, int offset) {
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

    void card_extension::process_antecedent(literal l, int offset) {
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

    card_extension::card_extension(): m_solver(0), m_has_xor(false) {        
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
        unsigned index = 4*m_cards.size();
        SASSERT(is_card_index(index));
        literal lit = v == null_bool_var ? null_literal : literal(v, false);
        card* c = new (memory::allocate(card::get_obj_size(lits.size()))) card(index, lit, lits, k);
        m_cards.push_back(c);
        if (v == null_bool_var) {
            // it is an axiom.
            init_watch(*c, true);
            m_card_axioms.push_back(c);
        }
        else {
            init_watch(v);
            m_var_infos[v].m_card = c;
            m_var_trail.push_back(v);
        }
    }

    void card_extension::add_pb_ge(bool_var v, svector<wliteral> const& wlits, unsigned k) {
        unsigned index = 4*m_pbs.size() + 0x3;
        SASSERT(is_pb_index(index));
        literal lit = v == null_bool_var ? null_literal : literal(v, false);
        pb* p = new (memory::allocate(pb::get_obj_size(wlits.size()))) pb(index, lit, wlits, k);
        m_pbs.push_back(p);
        if (v == null_bool_var) {
            init_watch(*p, true);
            m_pb_axioms.push_back(p);
        }
        else {
            init_watch(v);
            m_var_infos[v].m_pb = p;
            m_var_trail.push_back(v);
        }
    }


    void card_extension::add_xor(bool_var v, literal_vector const& lits) {
        m_has_xor = true;
        unsigned index = 4*m_xors.size() + 0x1;
        SASSERT(is_xor_index(index));
        xor* x = new (memory::allocate(xor::get_obj_size(lits.size()))) xor(index, literal(v, false), lits);
        m_xors.push_back(x);
        init_watch(v);
        m_var_infos[v].m_xor = x;
        m_var_trail.push_back(v);
    }


    void card_extension::propagate(literal l, ext_constraint_idx idx, bool & keep) {
        UNREACHABLE();
    }


    void card_extension::ensure_parity_size(bool_var v) {
        if (m_parity_marks.size() <= static_cast<unsigned>(v)) {
            m_parity_marks.resize(static_cast<unsigned>(v) + 1, 0);
        }
    }
    
    unsigned card_extension::get_parity(bool_var v) {
        return m_parity_marks.get(v, 0);
    }

    void card_extension::inc_parity(bool_var v) {
        ensure_parity_size(v);
        m_parity_marks[v]++;
    }

    void card_extension::reset_parity(bool_var v) {
        ensure_parity_size(v);
        m_parity_marks[v] = 0;
    }
    
    /**
       \brief perform parity resolution on xor premises.
       The idea is to collect premises based on xor resolvents. 
       Variables that are repeated an even number of times cancel out.
     */
    void card_extension::get_xor_antecedents(literal l, unsigned index, justification js, literal_vector& r) {
        unsigned level = lvl(l);
        bool_var v = l.var();
        SASSERT(js.get_kind() == justification::EXT_JUSTIFICATION);
        SASSERT(is_xor_index(js.get_ext_justification_idx()));
        TRACE("sat", tout << l << ": " << js << "\n"; tout << s().m_trail << "\n";);

        unsigned num_marks = 0;
        unsigned count = 0;
        while (true) {
            ++count;
            if (js.get_kind() == justification::EXT_JUSTIFICATION) {
                unsigned idx = js.get_ext_justification_idx();
                if (!is_xor_index(idx)) {
                    r.push_back(l);
                }
                else {
                    xor& x = index2xor(idx);
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

    void card_extension::get_pb_antecedents(literal l, pb const& p, literal_vector& r) {
        if (p.lit() != null_literal) r.push_back(p.lit());
        SASSERT(p.lit() == null_literal || value(p.lit()) == l_true);
        TRACE("sat", display(tout, p, true););

        // unsigned coeff = get_coeff(p, l);
        unsigned coeff = 0;
        for (unsigned j = 0; j < p.num_watch(); ++j) {
            if (p[j].second == l) {
                coeff = p[j].first;
                break;
            }
        }
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
            SASSERT(l_false == value(lit));
            r.push_back(~lit);
        }
    }

    void card_extension::get_card_antecedents(literal l, card const& c, literal_vector& r) {
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

    void card_extension::get_xor_antecedents(literal l, xor const& x, literal_vector& r) {
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

    void card_extension::get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) {
        if (is_card_index(idx)) {
            get_card_antecedents(l, index2card(idx), r);
        }
        else if (is_xor_index(idx)) {
            get_xor_antecedents(l, index2xor(idx), r);
        }
        else if (is_pb_index(idx)) {
            get_pb_antecedents(l, index2pb(idx), r);
        }
        else {
            UNREACHABLE();
        }
    }


    lbool card_extension::add_assign(card& c, literal alit) {
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

        // TRACE("sat", tout << "no swap " << index << " " << alit << "\n";);
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
        if (s().inconsistent()) return;
        if (v >= m_var_infos.size()) return;
        var_info& vinfo = m_var_infos[v];
        ptr_vector<card>* cards = vinfo.m_card_watch[!l.sign()];
        ptr_vector<xor>* xors = vinfo.m_xor_watch;
        ptr_vector<pb>* pbs = vinfo.m_pb_watch[!l.sign()];
        pb* p = vinfo.m_pb;
        card* crd = vinfo.m_card;
        xor* x = vinfo.m_xor;

        if (!is_tag_empty(cards)) {
            ptr_vector<card>::iterator begin = cards->begin();
            ptr_vector<card>::iterator it = begin, it2 = it, end = cards->end();
            for (; it != end; ++it) {
                card& c = *(*it);
                if (c.lit() != null_literal && value(c.lit()) != l_true) {
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
            if (cards->empty()) {
                m_var_infos[v].m_card_watch[!l.sign()] = set_tag_empty(cards);
            }
        }

        if (crd != 0 && !s().inconsistent()) {
            init_watch(*crd, !l.sign());
        }
        
        if ((!is_tag_empty(pbs) || p) && !s().inconsistent()) {
            asserted_pb(l, pbs, p);
        }

        if (m_has_xor && !s().inconsistent()) {
            asserted_xor(l, xors, x);
        }
    }


    check_result card_extension::check() { return CR_DONE; }

    void card_extension::push() {
        m_var_lim.push_back(m_var_trail.size());
    }

    void card_extension::pop(unsigned n) {        
        TRACE("sat_verbose", tout << "pop:" << n << "\n";);
        unsigned new_lim = m_var_lim.size() - n;
        unsigned sz = m_var_lim[new_lim];
        while (m_var_trail.size() > sz) {
            bool_var v = m_var_trail.back();
            m_var_trail.pop_back();
            if (v != null_bool_var) {
                card* c = m_var_infos[v].m_card;
                if (c) {
                    clear_watch(*c);
                    m_var_infos[v].m_card = 0;
                    dealloc(c);
                }
                xor* x = m_var_infos[v].m_xor;
                if (x) {
                    clear_watch(*x);
                    m_var_infos[v].m_xor = 0;
                    dealloc(x);
                }
            }
        }
        m_var_lim.resize(new_lim);
        m_num_propagations_since_pop = 0;
    }

    void card_extension::simplify() {}
    void card_extension::clauses_modifed() {}
    lbool card_extension::get_phase(bool_var v) { return l_undef; }

    extension* card_extension::copy(solver* s) {
        card_extension* result = alloc(card_extension);
        result->set_solver(s);
        for (unsigned i = 0; i < m_cards.size(); ++i) {
            literal_vector lits;
            card& c = *m_cards[i];
            for (unsigned i = 0; i < c.size(); ++i) {
                lits.push_back(c[i]);
            }
            bool_var v = c.lit() == null_literal ? null_bool_var : c.lit().var();
            result->add_at_least(v, lits, c.k());
        }
        copy_xor(*result);
        copy_pb(*result);
        return result;
    }

    void card_extension::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {
        literal_set slits(lits);
        bool change = false;
        for (unsigned i = 0; i < m_cards.size(); ++i) {
            card& c = *m_cards[i];
            if (c.size() == c.k() + 1) {
                literal_vector mux;
                for (unsigned j = 0; j < c.size(); ++j) {
                    literal lit = ~c[j];
                    if (slits.contains(lit)) {
                        mux.push_back(lit);
                    }
                }
                if (mux.size() <= 1) {
                    continue;
                }

                for (unsigned j = 0; j < mux.size(); ++j) {
                    slits.remove(mux[j]);
                }
                change = true;
                mutexes.push_back(mux);
            }
        }        
        if (!change) return;
        literal_set::iterator it = slits.begin(), end = slits.end();
        lits.reset();
        for (; it != end; ++it) {
            lits.push_back(*it);
        }
    }

     void card_extension::display_watch(std::ostream& out, bool_var v, bool sign) const {
        card_watch const* w = m_var_infos[v].m_card_watch[sign];
        if (!is_tag_empty(w)) {
            card_watch const& wl = *w;
            out << literal(v, sign) << " |-> ";
            for (unsigned i = 0; i < wl.size(); ++i) {
                out << wl[i]->lit() << " ";
            }
            out << "\n";        
        }
    }

    void card_extension::display_watch(std::ostream& out, bool_var v) const {
        xor_watch const* w = m_var_infos[v].m_xor_watch;
        if (!is_tag_empty(w)) {
            xor_watch const& wl = *w;
            out << "v" << v << " |-> ";
            for (unsigned i = 0; i < wl.size(); ++i) {
                out << wl[i]->lit() << " ";
            }
            out << "\n";        
        }
    }

    void card_extension::display(std::ostream& out, ineq& ineq) const {
        for (unsigned i = 0; i < ineq.m_lits.size(); ++i) {
            out << ineq.m_coeffs[i] << "*" << ineq.m_lits[i] << " ";
        }
        out << ">= " << ineq.m_k << "\n";
    }

    void card_extension::display(std::ostream& out, xor const& x, bool values) const {
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

    void card_extension::display(std::ostream& out, card const& c, bool values) const {
        out << c.lit() << "[" << c.size() << "]";
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
            display_watch(out, vi);
        }
        for (unsigned vi = 0; vi < m_var_infos.size(); ++vi) {
            card* c = m_var_infos[vi].m_card;
            if (c) display(out, *c, false);
            xor* x = m_var_infos[vi].m_xor;
            if (x) display(out, *x, false);
        }
        return out;
    }

    std::ostream& card_extension::display_justification(std::ostream& out, ext_justification_idx idx) const {
        if (is_card_index(idx)) {
            card& c = index2card(idx);
            out << "bound ";
            if (c.lit() != null_literal) out << c.lit();
            out << ": ";
            for (unsigned i = 0; i < c.size(); ++i) {
                out << c[i] << " ";
            }
            out << ">= " << c.k();
        }
        else if (is_xor_index(idx)) {
            xor& x = index2xor(idx);
            out << "xor ";
            if (x.lit() != null_literal) out << x.lit();
            out << ": ";
            for (unsigned i = 0; i < x.size(); ++i) {
                out << x[i] << " ";
            }            
        }
        else if (is_pb_index(idx)) {
            pb& p = index2pb(idx);
            out << "pb ";
            if (p.lit() != null_literal) out << p.lit();
            out << ": ";
            for (unsigned i = 0; i < p.size(); ++i) {
                out << p[i].first << "*" << p[i].second << " ";
            }
            out << ">= " << p.k();
        }
        else {
            UNREACHABLE();
        }
        return out;
    }

    void card_extension::collect_statistics(statistics& st) const {
        st.update("cardinality propagations", m_stats.m_num_card_propagations);
        st.update("cardinality conflicts", m_stats.m_num_card_conflicts);
        st.update("cardinality resolves", m_stats.m_num_card_resolves);
        st.update("xor propagations", m_stats.m_num_xor_propagations);
        st.update("xor conflicts", m_stats.m_num_xor_conflicts);
        st.update("xor resolves", m_stats.m_num_xor_resolves);
        st.update("pb propagations", m_stats.m_num_pb_propagations);
        st.update("pb conflicts", m_stats.m_num_pb_conflicts);
        st.update("pb resolves", m_stats.m_num_pb_resolves);
    }

    bool card_extension::validate_conflict(card& c) { 
        if (!validate_unit_propagation(c)) return false;
        for (unsigned i = 0; i < c.k(); ++i) {
            if (value(c[i]) == l_false) return true;
        }
        return false;
    }
    bool card_extension::validate_conflict(xor& x) {
        return !parity(x, 0);
    }
    bool card_extension::validate_unit_propagation(card const& c) { 
        if (c.lit() != null_literal && value(c.lit()) != l_true) return false;
        for (unsigned i = c.k(); i < c.size(); ++i) {
            if (value(c[i]) != l_false) return false;
        }
        return true;
    }
    bool card_extension::validate_unit_propagation(pb const& p, literal alit) { 
        if (p.lit() != null_literal && value(p.lit()) != l_true) return false;

        unsigned sum = 0;
        TRACE("sat", display(tout << "validate: " << alit << "\n", p, true););
        for (unsigned i = 0; i < p.size(); ++i) {
            literal lit = p[i].second;
            lbool val = value(lit);
            if (val != l_false && lit != alit) {
                sum += p[i].first;
            }
        }
        return sum < p.k();
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
        CTRACE("sat", val >= 0, active2pb(m_A); display(tout, m_A););
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
            p.reset(offset);
            p.push(lit, offset);
            break;
        case justification::BINARY:
            p.reset(offset);
            p.push(lit, offset);
            p.push(js.get_literal(), offset);
            break;
        case justification::TERNARY:
            p.reset(offset);
            p.push(lit, offset);
            p.push(js.get_literal1(), offset);
            p.push(js.get_literal2(), offset);
            break;
        case justification::CLAUSE: {
            p.reset(offset);
            clause & c = *(s().m_cls_allocator.get_clause(js.get_clause_offset()));
            unsigned sz  = c.size();
            for (unsigned i = 0; i < sz; i++)
                p.push(c[i], offset);
            break;
        }
        case justification::EXT_JUSTIFICATION: {
            unsigned index = js.get_ext_justification_idx();
            if (is_card_index(index)) {
                card& c = index2card(index);
                p.reset(offset*c.k());
                for (unsigned i = 0; i < c.size(); ++i) {
                    p.push(c[i], offset);
                }
                if (c.lit() != null_literal) p.push(~c.lit(), offset*c.k());
            }
            else if (is_xor_index(index)) {
                literal_vector ls;
                get_antecedents(lit, index, ls);                
                p.reset(offset);
                for (unsigned i = 0; i < ls.size(); ++i) {
                    p.push(~ls[i], offset);
                }
                literal lxor = index2xor(index).lit();                
                if (lxor != null_literal) p.push(~lxor, offset);
            }
            else if (is_pb_index(index)) {
                pb& pb = index2pb(index);
                p.reset(pb.k());
                for (unsigned i = 0; i < pb.size(); ++i) {
                    p.push(pb[i].second, pb[i].first);
                }
                if (pb.lit() != null_literal) p.push(~pb.lit(), pb.k());
            }
            else {
                UNREACHABLE();
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
                if (coeff > m_C.m_coeffs[i] && m_C.m_coeffs[i] < m_C.m_k) {
                    std::cout << i << ": " << m_C.m_coeffs[i] << " " << m_C.m_k << "\n";
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
        display(std::cout, m_A);
        display(std::cout, m_B);
        display(std::cout, m_C);
        u_map<unsigned>::iterator it = coeffs.begin(), end = coeffs.end();
        for (; it != end; ++it) {
            std::cout << to_literal(it->m_key) << ": " << it->m_value << "\n";
        }
        
        return false;
    }

    bool card_extension::validate_conflict(literal_vector const& lits, ineq& p) { 
        for (unsigned i = 0; i < lits.size(); ++i) {
            if (value(lits[i]) != l_false) {
                TRACE("sat", tout << "literal " << lits[i] << " is not false\n";);
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

