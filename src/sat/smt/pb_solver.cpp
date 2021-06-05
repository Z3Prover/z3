/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    pb_solver.cpp

Abstract:

    Extension for cardinality reasoning.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#include <cmath>
#include "util/mpz.h"
#include "sat/sat_types.h"
#include "sat/smt/pb_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/sat_simplifier_params.hpp"

namespace pb {

    static unsigned _bad_id = 11111111; // 2759; //
#define BADLOG(_cmd_) if (p.id() == _bad_id) { _cmd_; }


    // -----------------------
    // constraint

    void solver::set_conflict(constraint& c, literal lit) {
        m_stats.m_num_conflicts++;
        TRACE("ba", display(tout, c, true); );
        if (!validate_conflict(c)) {
            IF_VERBOSE(0, display(verbose_stream(), c, true));
            UNREACHABLE();
        }
        SASSERT(validate_conflict(c));
        SASSERT(value(lit) == l_false);
        set_conflict(sat::justification::mk_ext_justification(s().scope_lvl(), c.cindex()), ~lit);
        SASSERT(inconsistent());
    }

    void solver::assign(constraint& c, literal lit) {
        if (inconsistent()) return;
        switch (value(lit)) {
        case l_true: 
            break;
        case l_false: 
            set_conflict(c, lit); 
            break;
        default:
            m_stats.m_num_propagations++;
            m_num_propagations_since_pop++;
            //TRACE("ba", tout << "#prop: " << m_stats.m_num_propagations << " - " << c.lit() << " => " << lit << "\n";);
            SASSERT(validate_unit_propagation(c, lit));
            assign(lit, sat::justification::mk_ext_justification(s().scope_lvl(), c.cindex()));
            break;
        }
    }

    // -------------------
    // pb_base

    void solver::simplify(constraint& p) {
        SASSERT(s().at_base_lvl());
        if (p.lit() != sat::null_literal && value(p.lit()) == l_false) {
            TRACE("ba", tout << "pb: flip sign " << p << "\n";);
            IF_VERBOSE(1, verbose_stream() << "sign is flipped " << p << "\n";);
            return;
        }
        bool nullify = p.lit() != sat::null_literal && value(p.lit()) == l_true;
        if (nullify) {
            IF_VERBOSE(100, display(verbose_stream() << "nullify tracking literal\n", p, true););
            SASSERT(lvl(p.lit()) == 0);
            p.nullify_tracking_literal(*this);
            init_watch(p);
        }

        SASSERT(p.lit() == sat::null_literal || value(p.lit()) != l_false);

        unsigned true_val = 0, slack = 0, num_false = 0;
        for (unsigned i = 0; i < p.size(); ++i) {
            literal l = p.get_lit(i);
            bool_var v = l.var();
            if (s().was_eliminated(v)) {
                VERIFY(p.learned());
                remove_constraint(p, "contains eliminated");
                return;
            }
            switch (value(l)) {
            case l_true: true_val += p.get_coeff(i); break;
            case l_false: ++num_false; break;
            default: slack += p.get_coeff(i); break;
            }
        }
        if (p.k() == 1 && p.lit() == sat::null_literal) {
            literal_vector lits(p.literals());
            s().mk_clause(lits.size(), lits.data(), sat::status::th(p.learned(), get_id()));
            IF_VERBOSE(100, display(verbose_stream() << "add clause: " << lits << "\n", p, true););
            remove_constraint(p, "implies clause");
        }
        else if (true_val == 0 && num_false == 0) {
            if (p.lit() == sat::null_literal || value(p.lit()) == l_true) {
                init_watch(p);
            }
        }
        else if (true_val >= p.k()) {
            if (p.lit() != sat::null_literal) {
                IF_VERBOSE(100, display(verbose_stream() << "assign true literal ", p, true););
                s().assign_scoped(p.lit());
            }        
            remove_constraint(p, "is true");
        }
        else if (slack + true_val < p.k()) {
            if (p.lit() != sat::null_literal) {
                IF_VERBOSE(100, display(verbose_stream() << "assign false literal ", p, true););
                s().assign_scoped(~p.lit());
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "unsat during simplification\n";);
                s().set_conflict(sat::justification(0));
            }
            remove_constraint(p, "is false");
        }
        else if (slack + true_val == p.k()) {
            literal_vector lits(p.literals());    
            assert_unconstrained(p.lit(), lits);
            remove_constraint(p, "is tight");
        }
        else {
            unsigned sz = p.size();
            clear_watch(p);
            unsigned j = 0;
            for (unsigned i = 0; i < sz; ++i) {
                literal l = p.get_lit(i);
                if (value(l) == l_undef) {
                    if (i != j) p.swap(i, j);
                    ++j;
                }
            }
            sz = j;
            // _bad_id = p.id();
            BADLOG(display(verbose_stream() << "simplify ", p, true));

            unsigned k = p.k() - true_val;

            if (k == 1 && p.lit() == sat::null_literal) {
                literal_vector lits(sz, p.literals().data());
                s().mk_clause(sz, lits.data(), sat::status::th(p.learned(), get_id()));
                remove_constraint(p, "is clause");
                return;
            }
            p.set_size(sz);
            p.set_k(k);
            if (p.lit() == sat::null_literal || value(p.lit()) == l_true) {
                init_watch(p);
            }
            else {
                SASSERT(value(p.lit()) == l_undef);
            }
            BADLOG(display(verbose_stream() << "simplified ", p, true); verbose_stream() << "\n");
            // display(verbose_stream(), c, true);
            _bad_id = 11111111;
            SASSERT(p.well_formed());
            m_simplify_change = true;
        }
    }

    /*
      \brief split PB constraint into two because root is reused in arguments.
    
      x <=> a*x + B*y >= k
     
      x => a*x + By >= k
      ~x => a*x + By < k
     
      k*~x + a*x + By >= k
      (B+a-k + 1)*x + a*~x + B*~y >= B + a - k + 1

      (k - a) * ~x + By >= k - a
      k' * x + B'y >= k'
       
    */
    
    void solver::split_root(constraint& p) {
        SASSERT(p.lit() != sat::null_literal);
        SASSERT(!p.learned());
        m_weights.resize(2*s().num_vars(), 0);
        unsigned k = p.k();
        unsigned w, w1, w2;
        literal root = p.lit();
        m_weights[(~root).index()] = k;
        for (unsigned i = 0; i < p.size(); ++i) {
            m_weights[p.get_lit(i).index()] += p.get_coeff(i);
        }
        literal_vector lits(p.literals());
        lits.push_back(~root);

        for (literal l : lits) {
            w1 = m_weights[l.index()];
            w2 = m_weights[(~l).index()];
            if (w1 >= w2) {
                if (w2 >= k) {
                    for (literal l2 : lits) m_weights[l2.index()] = 0;
                    // constraint is true
                    return;
                }
                k -= w2;
                m_weights[(~l).index()] = 0;
                m_weights[l.index()] = w1 - w2;
            }
        }
        SASSERT(k > 0);

        // ~root * (k - a) + p >= k - a

        m_wlits.reset();
        for (literal l : lits) {
            w = m_weights[l.index()];
            if (w != 0) {
                m_wlits.push_back(wliteral(w, l));
            } 
            m_weights[l.index()] = 0;
        }
        
        add_pb_ge(sat::null_literal, m_wlits, k, false);        
    }


    // -------------------
    // pb


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
      if (Sw < k) return conflict
      for (li in Lw | Sw < k + ai) 
         assign li
      return no-conflict

     a_max index: index of non-false literal with maximal weight.
    */

    void solver::add_index(pbc& p, unsigned index, literal lit) {
        if (value(lit) == l_undef) {
            m_pb_undef.push_back(index);
            if (p[index].first > m_a_max) {
                m_a_max = p[index].first;
            }
        }
    }    
    
    /*
      \brief propagate assignment to alit in constraint p.
      
      TBD: 
      - consider reordering literals in watch list so that the search for watched literal takes average shorter time.
      - combine with caching literals that are assigned to 'true' to a cold store where they are not being revisited.
        Since 'true' literals may be unassigned (unless they are assigned at level 0) the cache has to be backtrack
        friendly (and the overhead of backtracking has to be taken into account).
     */
    lbool solver::add_assign(pbc& p, literal alit) {
        BADLOG(display(verbose_stream() << "assign: " << alit << " watch: " << p.num_watch() << " size: " << p.size(), p, true));
        TRACE("ba", display(tout << "assign: " << alit << "\n", p, true););
        SASSERT(!inconsistent());
        unsigned sz = p.size();
        unsigned bound = p.k();
        unsigned num_watch = p.num_watch();
        unsigned slack = p.slack();
        SASSERT(value(alit) == l_false);
        SASSERT(p.lit() == sat::null_literal || value(p.lit()) == l_true);
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
        if (index == num_watch || num_watch == 0) {
            _bad_id = p.id();
            BADLOG(
                verbose_stream() << "BAD: " << p.id() << "\n";
                display(verbose_stream(), p, true);
                verbose_stream() << "alit: " << alit << "\n";
                verbose_stream() << "num watch " << num_watch << "\n");
            UNREACHABLE();
            return l_undef;
        }
        
        SASSERT(validate_watch(p, sat::null_literal));
        // SASSERT(validate_watch(p, sat::null_literal));
        
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
                SASSERT(!p.is_watched(*this, p[j].second));
                p.watch_literal(*this, p[j].second);
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
            SASSERT(validate_watch(p, sat::null_literal));
            BADLOG(display(verbose_stream() << "conflict: " << alit << " watch: " << p.num_watch() << " size: " << p.size(), p, true));            
            SASSERT(bound <= slack);
            TRACE("ba", tout << "conflict " << alit << "\n";);
            set_conflict(p, alit);
            return l_false;
        }

        if (num_watch == 1) { _bad_id = p.id(); }

        BADLOG(verbose_stream() << "size: " << p.size() << " index: " << index << " num watch: " << num_watch << "\n");

        // swap out the watched literal.
        --num_watch;
        SASSERT(num_watch > 0);
        p.set_slack(slack);
        p.set_num_watch(num_watch);
        p.swap(num_watch, index);


        // 
        // slack >= bound, but slack - w(l) < bound 
        // l must be true.
        // 
        if (slack < bound + m_a_max) {            
            BADLOG(verbose_stream() << "slack " << slack << " " << bound << " " << m_a_max << "\n";);
            TRACE("ba", tout << p << "\n"; for(auto j : m_pb_undef) tout << j << " "; tout << "\n";);
            for (unsigned index1 : m_pb_undef) {
                if (index1 == num_watch) {
                    index1 = index;
                }
                wliteral wl = p[index1];
                literal lit = wl.second;
                SASSERT(value(lit) == l_undef);
                if (slack < bound + wl.first) {
                    BADLOG(verbose_stream() << "Assign " << lit << " " << wl.first << "\n");                
                    assign(p, lit);
                }
            }
        }

        SASSERT(validate_watch(p, alit)); // except that alit is still watched.

        TRACE("ba", display(tout << "assign: " << alit << "\n", p, true););

        BADLOG(verbose_stream() << "unwatch " << alit << " watch: " << p.num_watch() << " size: " << p.size() << " slack: " << p.slack() << " " << inconsistent() << "\n");

        return l_undef;
    }

    void solver::recompile(pbc& p) {
        // IF_VERBOSE(2, verbose_stream() << "re: " << p << "\n";);
        SASSERT(p.num_watch() == 0);
        m_weights.resize(2*s().num_vars(), 0);
        for (wliteral wl : p) {
            m_weights[wl.second.index()] += wl.first;
        }
        unsigned k = p.k();
        unsigned sz = p.size();
        bool all_units = true;
        unsigned j = 0;
        for (unsigned i = 0; i < sz && 0 < k; ++i) {
            literal l = p[i].second;
            unsigned w1 = m_weights[l.index()];
            unsigned w2 = m_weights[(~l).index()];
            if (w1 == 0 || w1 < w2) {
                continue;
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
                    continue;
                }    
                else {
                    p[j] = wliteral(w1, l);            
                    all_units &= w1 == 1;
                    ++j;
                }
            }
        }
        sz = j;
        // clear weights
        for (wliteral wl : p) {
            m_weights[wl.second.index()] = 0;
            m_weights[(~wl.second).index()] = 0;
        }

        if (k == 0) {
            if (p.lit() != sat::null_literal) {
                s().assign_scoped(p.lit());
            }
            remove_constraint(p, "recompiled to true");
            return;
        }

        else if (k == 1 && p.lit() == sat::null_literal) {
            literal_vector lits(sz, p.literals().data());
            s().mk_clause(sz, lits.data(), sat::status::th(p.learned(), get_id()));
            remove_constraint(p, "recompiled to clause");
            return;
        }

        else if (all_units) {
            literal_vector lits(sz, p.literals().data());
            add_at_least(p.lit(), lits, k, p.learned());
            remove_constraint(p, "recompiled to cardinality");
            return;
        }
        else {
            p.set_size(sz);
            p.update_max_sum();
            if (p.max_sum() < k) {
                if (p.lit() == sat::null_literal) {
                    s().set_conflict(sat::justification(0));
                }
                else {
                    s().assign_scoped(~p.lit());
                }
                remove_constraint(p, "recompiled to false");
                return;
            }
            p.set_k(k);
            SASSERT(p.well_formed());
            
            if (clausify(p)) {
                return;
            }
            if (p.lit() == sat::null_literal || value(p.lit()) == l_true) {
                init_watch(p);
            }
        }
    }


    // ---------------------------
    // conflict resolution
    

    void solver::inc_coeff(literal l, unsigned offset) {
        SASSERT(offset > 0);
        bool_var v = l.var();
        SASSERT(v != sat::null_bool_var);
        m_coeffs.reserve(v + 1, 0);
        TRACE("ba_verbose", tout << l << " " << offset << "\n";);

        int64_t coeff0 = m_coeffs[v];
        if (coeff0 == 0) {
            m_active_vars.push_back(v);
        }
        
        int64_t loffset = static_cast<int64_t>(offset);
        int64_t inc = l.sign() ? -loffset : loffset;
        int64_t coeff1 = inc + coeff0;
        m_coeffs[v] = coeff1;
        if (coeff1 > INT_MAX || coeff1 < INT_MIN) {
            m_overflow = true;
            return;
        }

        if (coeff0 > 0 && inc < 0) {
            inc_bound(std::max((int64_t)0, coeff1) - coeff0);
        }
        else if (coeff0 < 0 && inc > 0) {
            inc_bound(coeff0 - std::min((int64_t)0, coeff1));
        }
        int64_t lbound = static_cast<int64_t>(m_bound);

        // reduce coefficient to be no larger than bound.
        if (coeff1 > lbound) {
            m_coeffs[v] = lbound;
        }
        else if (coeff1 < 0 && -coeff1 > lbound) {
            m_coeffs[v] = -lbound;
        }        
    }

    int64_t solver::get_coeff(bool_var v) const {
        return m_coeffs.get(v, 0);
    }

    uint64_t solver::get_coeff(literal lit) const {
        int64_t c1 = get_coeff(lit.var());
        SASSERT((c1 < 0) == lit.sign());
        int64_t c = std::abs(c1);
        m_overflow |= (c != c1);
        return static_cast<uint64_t>(c);
    }

    wliteral solver::get_wliteral(bool_var v) {
        int64_t c1 = get_coeff(v);
        literal l = literal(v, c1 < 0);
        c1 = std::abs(c1);
        unsigned c = static_cast<unsigned>(c1);
        // TRACE("ba", tout << l << " " << c << "\n";);
        m_overflow |= c != c1;
        return wliteral(c, l);
    }

    unsigned solver::get_abs_coeff(bool_var v) const {
        int64_t c1 = std::abs(get_coeff(v));
        unsigned c = static_cast<unsigned>(c1);
        m_overflow |= c != c1;
        return c;
    }

    int solver::get_int_coeff(bool_var v) const {
        int64_t c1 = m_coeffs.get(v, 0);
        int c = static_cast<int>(c1);
        m_overflow |= c != c1;
        return c;
    }

    void solver::inc_bound(int64_t i) {
        int64_t new_bound = m_bound;
        new_bound += i;
        unsigned nb = static_cast<unsigned>(new_bound);
        m_overflow |= new_bound < 0 || nb != new_bound;
        m_bound = nb;        
    }

    void solver::reset_coeffs() {
        for (unsigned i = m_active_vars.size(); i-- > 0; ) {
            m_coeffs[m_active_vars[i]] = 0;
        }
        m_active_vars.reset();
    }


    static bool _debug_conflict = false;
    static literal _debug_consequent = sat::null_literal;
    static unsigned_vector _debug_var2position;

// #define DEBUG_CODE(_x_) _x_

    void solver::bail_resolve_conflict(unsigned idx) {
        literal_vector const& lits = s().m_trail;
        while (m_num_marks > 0) {
            bool_var v = lits[idx].var();
            if (s().is_marked(v)) {
                s().reset_mark(v);
                --m_num_marks;
            }
            if (idx == 0 && !_debug_conflict) {
                _debug_conflict = true;
                _debug_var2position.reserve(s().num_vars());
                for (unsigned i = 0; i < lits.size(); ++i) {
                    _debug_var2position[lits[i].var()] = i;
                }
                IF_VERBOSE(0, 
                           active2pb(m_A);
                           uint64_t c = 0;
                           for (wliteral l : m_A.m_wlits) c += l.first;
                           verbose_stream() << "sum of coefficients: " << c << "\n";
                           display(verbose_stream(), m_A, true);
                           verbose_stream() << "conflicting literal: " << s().m_not_l << "\n";);

                for (literal l : lits) {
                    if (s().is_marked(l.var())) {
                        IF_VERBOSE(0, verbose_stream() << "missing mark: " << l << "\n";);
                        s().reset_mark(l.var());
                    }
                }
                m_num_marks = 0;
                resolve_conflict();                
            }
            --idx;
        }
    }

    lbool solver::resolve_conflict() { 
        if (0 == m_num_propagations_since_pop) {
            return l_undef;
        }

        if (s().m_config.m_pb_resolve == sat::PB_ROUNDING) {
            return resolve_conflict_rs();
        }
       
        m_overflow = false;
        reset_coeffs();
        m_num_marks = 0;
        m_bound = 0;
        literal consequent = s().m_not_l;
        sat::justification js = s().m_conflict;
        TRACE("ba", tout << consequent << " " << js << "\n";);
        bool unique_max;
        m_conflict_lvl = s().get_max_lvl(consequent, js, unique_max);
        if (m_conflict_lvl == 0) {
            return l_undef;
        }
        if (consequent != sat::null_literal) {
            consequent.neg();
            process_antecedent(consequent, 1);
        }
        literal_vector const& lits = s().m_trail;
        unsigned idx = lits.size() - 1;
        unsigned offset = 1;
        DEBUG_CODE(active2pb(m_A););

        do {


            if (m_overflow || offset > (1 << 12)) {
                IF_VERBOSE(20, verbose_stream() << "offset: " << offset << "\n";
                           DEBUG_CODE(active2pb(m_A); display(verbose_stream(), m_A);););
                goto bail_out;
            }

            if (offset == 0) {
                goto process_next_resolvent;            
            }

            DEBUG_CODE(TRACE("sat_verbose", display(tout, m_A);););
            TRACE("ba", tout << "process consequent: " << consequent << " : "; s().display_justification(tout, js) << "\n";);
            SASSERT(offset > 0);

            DEBUG_CODE(justification2pb(js, consequent, offset, m_B););
            
            if (_debug_conflict) {
                IF_VERBOSE(0, 
                           verbose_stream() << consequent << "\n";
                           s().display_justification(verbose_stream(), js);
                           verbose_stream() << "\n";);
                _debug_consequent = consequent;
            }
            switch(js.get_kind()) {
            case sat::justification::NONE:
                SASSERT (consequent != sat::null_literal);
                inc_bound(offset);
                break;
            case sat::justification::BINARY:
                inc_bound(offset);
                SASSERT (consequent != sat::null_literal);
                inc_coeff(consequent, offset);
                process_antecedent(js.get_literal(), offset);
                break;
            case sat::justification::TERNARY:
                inc_bound(offset); 
                SASSERT (consequent != sat::null_literal);
                inc_coeff(consequent, offset);				
                process_antecedent(js.get_literal1(), offset);
                process_antecedent(js.get_literal2(), offset);
                break;
            case sat::justification::CLAUSE: {
                inc_bound(offset); 
                sat::clause & c = s().get_clause(js);
                unsigned i = 0;
                if (consequent != sat::null_literal) {
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
            case sat::justification::EXT_JUSTIFICATION: {
                auto cindex = js.get_ext_justification_idx();
                auto* ext = sat::constraint_base::to_extension(cindex);
                if (ext != this) {
                    m_lemma.reset();
                    ext->get_antecedents(consequent, idx, m_lemma, false);
                    for (literal l : m_lemma) process_antecedent(~l, offset);
                    break;
                }
                constraint& cnstr = index2constraint(cindex);
                ++m_stats.m_num_resolves;
                switch (cnstr.tag()) {
                case pb::tag_t::card_t: {
                    card& c = cnstr.to_card();
                    inc_bound(static_cast<int64_t>(offset) * c.k());
                    process_card(c, offset);
                    break;
                }
                case pb::tag_t::pb_t: {
                    pbc& p = cnstr.to_pb();
                    m_lemma.reset();
                    inc_bound(offset);
                    inc_coeff(consequent, offset);
                    get_antecedents(consequent, p, m_lemma);
                    TRACE("ba", display(tout, p, true); tout << m_lemma << "\n";);
                    if (_debug_conflict) {
                        verbose_stream() << consequent << " ";
                        verbose_stream() << "antecedents: " << m_lemma << "\n";
                    }
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
                VERIFY(validate_resolvent());
                m_A = m_C;
                TRACE("ba", display(tout << "conflict: ", m_A);););

            cut();

        process_next_resolvent:
            
            // find the next marked variable in the assignment stack
            bool_var v;
            while (true) {
                consequent = lits[idx];
                v = consequent.var();
                if (s().is_marked(v)) {
                    if (s().lvl(v) == m_conflict_lvl) {
                        break;
                    }
                }
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
            TRACE("sat_verbose", tout << "Unmark: v" << v << "\n";);
            --m_num_marks;
            js = s().m_justification[v];
            offset = get_abs_coeff(v);
            if (offset > m_bound) {
                int64_t bound64 = static_cast<int64_t>(m_bound);
                m_coeffs[v] = (get_coeff(v) < 0) ? -bound64 : bound64;
                offset = m_bound;
                DEBUG_CODE(active2pb(m_A););
            }
            SASSERT(value(consequent) == l_true);
        }        
        while (m_num_marks > 0);
        
        DEBUG_CODE(for (bool_var i = 0; i < static_cast<bool_var>(s().num_vars()); ++i) SASSERT(!s().is_marked(i)););
        SASSERT(validate_lemma());

        if (!create_asserting_lemma()) {
            goto bail_out;
        }
        active2lemma();


        DEBUG_CODE(VERIFY(validate_conflict(m_lemma, m_A)););
        
        return l_true;

    bail_out:
        if (m_overflow) {
            ++m_stats.m_num_overflow;
            m_overflow = false;
        }
        bail_resolve_conflict(idx);
        return l_undef;
    }


    unsigned solver::ineq::bv_coeff(bool_var v) const {
        for (unsigned i = size(); i-- > 0; ) {
            if (lit(i).var() == v) return coeff(i);
        }
        UNREACHABLE();
        return 0;
    }

    void solver::ineq::divide(unsigned c) {
        if (c == 1) return;
        for (unsigned i = size(); i-- > 0; ) {
            m_wlits[i].first = (coeff(i) + c - 1) / c;
        }
        m_k = (m_k + c - 1) / c;
    }

    /**
     * Remove literal at position i, subtract coefficient from bound.
     */
    void solver::ineq::weaken(unsigned i) {
        unsigned ci = coeff(i);
        SASSERT(m_k >= ci);
        m_k -= ci;
        m_wlits[i] = m_wlits.back();
        m_wlits.pop_back();
    }

    /** 
     * Round coefficient of inequality to 1.
     */
    void solver::round_to_one(ineq& ineq, bool_var v) {
        unsigned c = ineq.bv_coeff(v);
        if (c == 1) return;
        unsigned sz = ineq.size();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned ci = ineq.coeff(i); 
            unsigned q = ci % c;
            if (q != 0 && !is_false(ineq.lit(i))) {
#if 1
                // code review by Elffers:
                ineq.weaken(i);
                --i;
                --sz;                
#else
                if (q == ci) {
                    ineq.weaken(i);
                    --i;
                    --sz;
                }
                else {
                    ineq.m_wlits[i].first -= q;
                    ineq.m_k -= q;
                }
#endif
            }
        }
        ineq.divide(c);
        TRACE("ba", display(tout << "var: " << v << " " << c << ": ", ineq, true););
    }

    void solver::round_to_one(bool_var w) {
        unsigned c = get_abs_coeff(w);
        if (c == 1 || c == 0) return;
        for (bool_var v : m_active_vars) {
            wliteral wl = get_wliteral(v);
            unsigned q = wl.first % c;
            if (q != 0 && !is_false(wl.second)) {
                m_coeffs[v] = wl.first - q;
                m_bound -= q;
                SASSERT(m_bound > 0);
            }
        }        
        SASSERT(validate_lemma());
        divide(c);
        SASSERT(validate_lemma());
        TRACE("ba", active2pb(m_B); display(tout, m_B, true););
    }

    void solver::divide(unsigned c) {
        SASSERT(c != 0);
        if (c == 1) return;
        reset_active_var_set();
        unsigned j = 0, sz = m_active_vars.size();
        for (unsigned i = 0; i < sz; ++i) {
            bool_var v = m_active_vars[i];
            int ci = get_int_coeff(v);
            if (!test_and_set_active(v) || ci == 0) continue;
            if (ci > 0) {
                m_coeffs[v] = (ci + c - 1) / c;
            }
            else {
                m_coeffs[v] = -static_cast<int64_t>((-ci + c - 1) / c);
            }
            m_active_vars[j++] = v;
        }
        m_active_vars.shrink(j);
        m_bound = static_cast<unsigned>((m_bound + c - 1) / c);                    
    }

    void solver::resolve_on(literal consequent) {
        round_to_one(consequent.var());
        m_coeffs[consequent.var()] = 0;
    }

    void solver::resolve_with(ineq const& ineq) {
        TRACE("ba", display(tout, ineq, true););
        inc_bound(ineq.m_k);        
        TRACE("ba", tout << "bound: " << m_bound << "\n";);

        for (unsigned i = ineq.size(); i-- > 0; ) {
            literal l = ineq.lit(i);
            inc_coeff(l, static_cast<unsigned>(ineq.coeff(i)));
            TRACE("ba", tout << "bound: " << m_bound << " lit: " << l << " coeff: " << ineq.coeff(i) << "\n";);
        }
    }

    void solver::reset_marks(unsigned idx) {
        while (m_num_marks > 0) {
            SASSERT(idx > 0);
            bool_var v = s().m_trail[idx].var();
            if (s().is_marked(v)) {
                s().reset_mark(v);
                --m_num_marks;
            }
            --idx;
        }
    }
    
    /**
     * \brief mark variables that are on the assignment stack but 
     * below the current processing level.
     */
    void solver::mark_variables(ineq const& ineq) {
        for (wliteral wl : ineq.m_wlits) {
            literal l = wl.second;
            if (!is_false(l)) continue;
            bool_var v = l.var();
            unsigned level = lvl(v);
            if (!s().is_marked(v) && !is_visited(v) && level == m_conflict_lvl) {
                s().mark(v);
                ++m_num_marks;
            }
        }
    }

    lbool solver::resolve_conflict_rs() {
        if (0 == m_num_propagations_since_pop) {
            return l_undef;
        }
        m_overflow = false;
        reset_coeffs();
        init_visited();
        m_num_marks = 0;
        m_bound = 0;
        literal consequent = s().m_not_l;
        sat::justification js = s().m_conflict;
        bool unique_max;
        m_conflict_lvl = s().get_max_lvl(consequent, js, unique_max);
        if (m_conflict_lvl == 0) {
            return l_undef;
        }
        if (consequent != sat::null_literal) {
            consequent.neg();
            process_antecedent(consequent, 1);
        }
        TRACE("ba", tout << consequent << " " << js << "\n";);
        unsigned idx = s().m_trail.size() - 1;
        
        do {
            TRACE("ba", s().display_justification(tout << "process consequent: " << consequent << " : ", js) << "\n";
                  if (consequent != sat::null_literal) { active2pb(m_A); display(tout, m_A, true); }
                  );

            switch (js.get_kind()) {
            case sat::justification::NONE:
                SASSERT(consequent != sat::null_literal);
                round_to_one(consequent.var());
                inc_bound(1);
                inc_coeff(consequent, 1);
                break;
            case sat::justification::BINARY:
                SASSERT(consequent != sat::null_literal);
                round_to_one(consequent.var());
                inc_bound(1);
                inc_coeff(consequent, 1);
                process_antecedent(js.get_literal());
                break;
            case sat::justification::TERNARY:
                SASSERT(consequent != sat::null_literal);
                round_to_one(consequent.var());
                inc_bound(1);
                inc_coeff(consequent, 1);
                process_antecedent(js.get_literal1());
                process_antecedent(js.get_literal2());
                break;
            case sat::justification::CLAUSE: {
                sat::clause & c = s().get_clause(js);
                unsigned i = 0;
                if (consequent != sat::null_literal) {
                    round_to_one(consequent.var());
                    inc_coeff(consequent, 1);
                    if (c[0] == consequent) {
                        i = 1;
                    }
                    else {
                        SASSERT(c[1] == consequent);
                        process_antecedent(c[0]);
                        i = 2;
                    }
                }
                inc_bound(1);
                unsigned sz = c.size();
                for (; i < sz; i++)
                    process_antecedent(c[i]);
                break;
            }
            case sat::justification::EXT_JUSTIFICATION: {
                ++m_stats.m_num_resolves;
                sat::ext_justification_idx index = js.get_ext_justification_idx();
                auto* ext = sat::constraint_base::to_extension(index);
                if (ext != this) {
                    m_lemma.reset();
                    ext->get_antecedents(consequent, index, m_lemma, false);
                    for (literal l : m_lemma) 
                        process_antecedent(~l, 1);
                    break;
                }
                constraint& p = index2constraint(index);
                SASSERT(!p.was_removed());
                unsigned k = p.k(), sz = p.size();
                m_A.reset(0);
                for (unsigned i = 0; i < sz; ++i) {
                    literal l = p.get_lit(i);
                    unsigned c = p.get_coeff(i);
                    if (l == consequent || !is_visited(l.var())) {
                        m_A.push(l, c);
                    }
                    else {
                        SASSERT(k > c);
                        TRACE("ba", tout << "visited: " << l << "\n";);
                        k -= c;
                    }
                }
                SASSERT(k > 0);
                if (p.lit() != sat::null_literal) m_A.push(~p.lit(), k);
                m_A.m_k = k;

                mark_variables(m_A);
                if (consequent == sat::null_literal) {
                    SASSERT(validate_ineq(m_A)); 
                    m_bound = static_cast<unsigned>(m_A.m_k);
                    for (wliteral wl : m_A.m_wlits) {
                        process_antecedent(wl.second, wl.first);
                    } 
                }
                else {
                    round_to_one(consequent.var());
                    if (p.is_pb()) round_to_one(m_A, consequent.var()); 
                    SASSERT(validate_ineq(m_A)); 
                    resolve_with(m_A);
                }
                break;
            }
            default:
                UNREACHABLE();
                break;
            }            

            SASSERT(validate_lemma());
            cut();

            // find the next marked variable in the assignment stack
            bool_var v;
            while (true) {
                consequent = s().m_trail[idx];
                v = consequent.var();
                mark_visited(v);
                if (s().is_marked(v)) {
                    int64_t c = get_coeff(v);
                    if (c == 0 || ((c < 0) == consequent.sign())) {
                        s().reset_mark(v);
                        --m_num_marks;
                    }
                    else {
                        break;
                    }
                }
                if (idx == 0) {
                    TRACE("ba", tout << "there is no consequent\n";);
                    goto bail_out;
                }
                --idx;
            }
            
            SASSERT(lvl(v) == m_conflict_lvl);
            s().reset_mark(v);
            --idx;
            --m_num_marks;
            js = s().m_justification[v];
        }        
        while (m_num_marks > 0 && !m_overflow);
        TRACE("ba", active2pb(m_A); display(tout, m_A, true););

        // TBD: check if this is useful
        if (!m_overflow && consequent != sat::null_literal) {
            round_to_one(consequent.var());
        }
        if (!m_overflow && create_asserting_lemma()) {
            active2lemma();
            return l_true;
        }
        
    bail_out:
        TRACE("ba", tout << "bail " << m_overflow << "\n";);
        if (m_overflow) {
            ++m_stats.m_num_overflow;
            m_overflow = false;
        }
        return l_undef;
    }


    bool solver::create_asserting_lemma() {
        int64_t bound64 = m_bound;
        int64_t slack = -bound64;
        reset_active_var_set();
        unsigned j = 0, sz = m_active_vars.size();
        for (unsigned i = 0; i < sz; ++i) {
            bool_var v = m_active_vars[i];
            unsigned c = get_abs_coeff(v);
            if (!test_and_set_active(v) || c == 0) continue;
            slack += c;
            m_active_vars[j++] = v;
        }
        m_active_vars.shrink(j);
        m_lemma.reset();        
        m_lemma.push_back(sat::null_literal);
        unsigned num_skipped = 0;
        int64_t asserting_coeff = 0;
        for (unsigned i = 0; 0 <= slack && i < m_active_vars.size(); ++i) { 
            bool_var v = m_active_vars[i];
            int64_t coeff = get_coeff(v);
            lbool val = value(v);
            bool is_true = val == l_true;
            bool append = coeff != 0 && val != l_undef && ((coeff < 0) == is_true);
            if (append) {
                literal lit(v, !is_true);
                if (lvl(lit) == m_conflict_lvl) {
                    if (m_lemma[0] == sat::null_literal) {
                        asserting_coeff = std::abs(coeff);
                        slack -= asserting_coeff;
                        m_lemma[0] = ~lit;
                    }
                    else {
                        ++num_skipped;
                        if (asserting_coeff < std::abs(coeff)) {
                            m_lemma[0] = ~lit;
                            slack -= (std::abs(coeff) - asserting_coeff);
                            asserting_coeff = std::abs(coeff);
                        }
                    }
                }
                else if (lvl(lit) < m_conflict_lvl) {
                    slack -= std::abs(coeff);
                    m_lemma.push_back(~lit);
                }
            }
        }
        if (slack >= 0) {
            TRACE("ba", tout << "slack is non-negative\n";);
            IF_VERBOSE(20, verbose_stream() << "(sat.card slack: " << slack << " skipped: " << num_skipped << ")\n";);
            return false;
        }
        if (m_overflow) {
            TRACE("ba", tout << "overflow\n";);
            return false;
        }        
        if (m_lemma[0] == sat::null_literal) {
            if (m_lemma.size() == 1) {
                s().set_conflict(sat::justification(0));
            }
            TRACE("ba", tout << "no asserting literal\n";);
            return false;
        }

        TRACE("ba", tout << m_lemma << "\n";);

        if (get_config().m_drat && m_solver) {
            s().m_drat.add(m_lemma, sat::status::th(true, get_id()));
        }

        s().m_lemma.reset();
        s().m_lemma.append(m_lemma);
        for (unsigned i = 1; i < m_lemma.size(); ++i) {
            CTRACE("ba", s().is_marked(m_lemma[i].var()), tout << "marked: " << m_lemma[i] << "\n";);
            s().mark(m_lemma[i].var());
        }
        return true;
    }

    /*
      \brief compute a cut for current resolvent.
     */

    void solver::cut() {

        // bypass cut if there is a unit coefficient
        for (bool_var v : m_active_vars) {
            if (1 == get_abs_coeff(v)) return;
        }

        unsigned g = 0;

        for (unsigned i = 0; g != 1 && i < m_active_vars.size(); ++i) {
            bool_var v = m_active_vars[i];
            unsigned coeff = get_abs_coeff(v);
            if (coeff == 0) {
                continue;
            }
            if (m_bound < coeff) {
                int64_t bound64 = m_bound;
                if (get_coeff(v) > 0) {
                    m_coeffs[v] = bound64;
                }
                else {
                    m_coeffs[v] = -bound64;
                }
                coeff = m_bound;
            }
            SASSERT(0 < coeff && coeff <= m_bound);
            if (g == 0) {
                g = coeff;
            }
            else {
                g = u_gcd(g, coeff);
            }
        }

        if (g >= 2) {
            reset_active_var_set();
            unsigned j = 0, sz = m_active_vars.size();
            for (unsigned i = 0; i < sz; ++i) {
                bool_var v = m_active_vars[i];
                int64_t c = m_coeffs[v];
                if (!test_and_set_active(v) || c == 0) continue;
                m_coeffs[v] /= static_cast<int>(g);
                m_active_vars[j++] = v;
            }
            m_active_vars.shrink(j);
            m_bound = (m_bound + g - 1) / g;
            ++m_stats.m_num_cut;
        }        
    }

    void solver::process_card(card& c, unsigned offset) {
        literal lit = c.lit();
        SASSERT(c.k() <= c.size());       
        SASSERT(lit == sat::null_literal || value(lit) != l_undef);
        SASSERT(0 < offset);
        for (unsigned i = c.k(); i < c.size(); ++i) {
            process_antecedent(c[i], offset);
        }
        for (unsigned i = 0; i < c.k(); ++i) {
            inc_coeff(c[i], offset);                        
        }
        if (lit != sat::null_literal) {
            uint64_t offset1 = static_cast<uint64_t>(offset) * c.k();
            if (offset1 > UINT_MAX) {
                m_overflow = true;
            }
            if (value(lit) == l_true) {
                process_antecedent(~lit, static_cast<unsigned>(offset1));
            }
            else {
                process_antecedent(lit, static_cast<unsigned>(offset1));
            }
        }
    }

    void solver::process_antecedent(literal l, unsigned offset) {
        SASSERT(value(l) == l_false);
        bool_var v = l.var();
        unsigned level = lvl(v);

        if (!s().is_marked(v) && level == m_conflict_lvl) {
            s().mark(v);
            ++m_num_marks;
            if (_debug_conflict && _debug_consequent != sat::null_literal && _debug_var2position[_debug_consequent.var()] < _debug_var2position[l.var()]) {
                IF_VERBOSE(0, verbose_stream() << "antecedent " << l << " is above consequent in stack\n";);
            }
        }
        inc_coeff(l, offset);                
    }   

    literal solver::get_asserting_literal(literal p) {
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

    solver::solver(euf::solver& ctx, euf::theory_id id) :
        solver(ctx.get_manager(), ctx.get_si(), id) {}

    solver::solver(ast_manager& m, sat::sat_internalizer& si, euf::theory_id id)
        : euf::th_solver(m, symbol("ba"), id),
          si(si), m_pb(m),
          m_lookahead(nullptr), 
          m_constraint_id(0), m_ba(*this), m_sort(m_ba) {
        TRACE("ba", tout << this << "\n";);
        m_num_propagations_since_pop = 0;
    }

    solver::~solver() {
        m_stats.reset();
        for (constraint* c : m_constraints) {
            c->deallocate(m_allocator);
        }
        for (constraint* c : m_learned) {
            c->deallocate(m_allocator);
        }
    }

    void solver::add_at_least(bool_var v, literal_vector const& lits, unsigned k) {
        literal lit = v == sat::null_bool_var ? sat::null_literal : literal(v, false);
        add_at_least(lit, lits, k, m_is_redundant);
    }

    constraint* solver::add_at_least(literal lit, literal_vector const& lits, unsigned k, bool learned) {
        if (k == 1 && lit == sat::null_literal) {
            literal_vector _lits(lits);
            s().mk_clause(_lits.size(), _lits.data(), sat::status::th(learned, get_id()));
            return nullptr;
        }
        if (!learned && clausify(lit, lits.size(), lits.data(), k)) {
            return nullptr;
        }
        void * mem = m_allocator.allocate(card::get_obj_size(lits.size()));
        sat::constraint_base::initialize(mem, this);
        card* c = new (sat::constraint_base::ptr2mem(mem)) card(next_id(), lit, lits, k);
        c->set_learned(learned);
        add_constraint(c);
        return c;
    }

    void solver::add_constraint(constraint* c) {
        literal_vector lits(c->literals());
        if (c->learned()) {
            m_learned.push_back(c);
        }
        else {
            SASSERT(!m_solver || s().at_base_lvl());
            m_constraints.push_back(c);
        }
        literal lit = c->lit();
        if (c->learned() && m_solver && !s().at_base_lvl()) {
            SASSERT(lit == sat::null_literal);
            // gets initialized after backjump.
            m_constraint_to_reinit.push_back(c);
        }
        else if (lit == sat::null_literal) {
            init_watch(*c);
        }
        else {
            if (m_solver) m_solver->set_external(lit.var());
            c->watch_literal(*this, lit);
            c->watch_literal(*this, ~lit);
        }        
        SASSERT(c->well_formed());
        if (m_solver && m_solver->get_config().m_drat) {
            std::function<void(std::ostream& out)> fn = [&](std::ostream& out) {
                out << "c ba constraint " << *c << " 0\n";
            };
            m_solver->get_drat().log_adhoc(fn);
        }
    }


    bool solver::init_watch(constraint& c) {
        return !inconsistent() && c.init_watch(*this);
    }

    lbool solver::add_assign(constraint& c, literal l) {
        switch (c.tag()) {
        case pb::tag_t::card_t: return add_assign(c.to_card(), l);
        case pb::tag_t::pb_t: return add_assign(c.to_pb(), l);
        }
        UNREACHABLE();
        return l_undef;
    }

    constraint* solver::add_pb_ge(literal lit, svector<wliteral> const& wlits, unsigned k, bool learned) {
        bool units = true;
        for (wliteral wl : wlits) units &= wl.first == 1;
        if (k == 0 && lit == sat::null_literal) {
            return nullptr;
        }
        if (!learned) {
            for (wliteral wl : wlits) s().set_external(wl.second.var()); 
        }
        if (units || k == 1) {
            literal_vector lits;
            for (wliteral wl : wlits) lits.push_back(wl.second);
            return add_at_least(lit, lits, k, learned);
        }
        void * mem = m_allocator.allocate(pbc::get_obj_size(wlits.size()));
        sat::constraint_base::initialize(mem, this);
        pbc* p = new (sat::constraint_base::ptr2mem(mem)) pbc(next_id(), lit, wlits, k);
        p->set_learned(learned);
        add_constraint(p);
        return p;
    }

    void solver::add_pb_ge(bool_var v, svector<wliteral> const& wlits, unsigned k) {
        literal lit = v == sat::null_bool_var ? sat::null_literal : literal(v, false);
        add_pb_ge(lit, wlits, k, m_is_redundant);
    }

    bool solver::is_external(bool_var v) {
        return false;
    }

    /*
      \brief return true to keep watching literal.
    */
    bool solver::propagated(literal l, sat::ext_constraint_idx idx) {
        SASSERT(value(l) == l_true);
        constraint& c = index2constraint(idx);
        if (c.lit() != sat::null_literal && l.var() == c.lit().var()) {
            init_watch(c);
            return true;
        }
        else if (c.lit() != sat::null_literal && value(c.lit()) != l_true) {
            return true;
        }
        else {
            return l_undef != add_assign(c, ~l);
        }
    }


    double solver::get_reward(literal l, sat::ext_justification_idx idx, sat::literal_occs_fun& occs) const {
        constraint const& c = index2constraint(idx);
        return c.get_reward(*this, occs);
    }


    void solver::ensure_parity_size(bool_var v) {
        if (m_parity_marks.size() <= static_cast<unsigned>(v)) {
            m_parity_marks.resize(static_cast<unsigned>(v) + 1, 0);
        }
    }
    
    unsigned solver::get_parity(bool_var v) {
        return m_parity_marks.get(v, 0);
    }

    void solver::inc_parity(bool_var v) {
        ensure_parity_size(v);
        m_parity_marks[v]++;
    }

    void solver::reset_parity(bool_var v) {
        ensure_parity_size(v);
        m_parity_marks[v] = 0;
    }
    

    /**
       \brief retrieve a sufficient set of literals from p that imply l.
       
       Find partition: 

         - Ax + coeff*l + B*y >= k
         - all literals in x are false.
         - B < k

       Then x is an explanation for l

     */

    bool solver::assigned_above(literal above, literal below) {
        unsigned l = lvl(above);
        SASSERT(l == lvl(below));
        if (l == 0) return false;
        unsigned start = s().m_scopes[l-1].m_trail_lim;
        literal_vector const& lits = s().m_trail;
        for (unsigned sz = lits.size(); sz-- > start; ) {
            if (lits[sz] == above) return true;
            if (lits[sz] == below) return false;
        }
        UNREACHABLE();
        return false;
    }

    void solver::get_antecedents(literal l, pbc const& p, literal_vector& r) {
        TRACE("ba", display(tout << l << " level: " << s().scope_lvl() << " ", p, true););
        SASSERT(p.lit() == sat::null_literal || value(p.lit()) == l_true);

        if (p.lit() != sat::null_literal) {
            r.push_back(p.lit());
        }

        unsigned k = p.k();

        if (_debug_conflict) {
            IF_VERBOSE(0, display(verbose_stream(), p, true);
                       verbose_stream() << "literal: " << l << " value: " << value(l) << " num-watch: " << p.num_watch() << " slack: " << p.slack() << "\n";);
        }

        if (value(l) == l_false) {
            // The literal comes from a conflict.
            // it is forced true, but assigned to false.
            unsigned slack = 0;
            for (wliteral wl : p) {
                if (value(wl.second) != l_false) {
                    slack += wl.first;
                }
            }
            SASSERT(slack < k);
            for (wliteral wl : p) {
                literal lit = wl.second;
                if (lit != l && value(lit) == l_false) {
                    unsigned w = wl.first;
                    if (slack + w < k) {
                        slack += w;
                    }
                    else {
                        r.push_back(~lit);
                    }
                } 
            }
        }
        else {
            // comes from a unit propagation
            SASSERT(value(l) == l_true);
            unsigned coeff = 0, j = 0;
            for (; j < p.size(); ++j) {
                if (p[j].second == l) {
                    coeff = p[j].first;
                    break;
                }
            }
            
            ++j;
            if (j < p.num_watch()) {
                j = p.num_watch();
            }
            CTRACE("ba", coeff == 0, display(tout << l << " coeff: " << coeff << "\n", p, true);); 
            
            if (_debug_conflict) {
                std::cout << "coeff " << coeff << "\n";
            }

            SASSERT(coeff > 0);
            unsigned slack = p.max_sum() - coeff;
            
            // we need antecedents to be deeper than alit.
            for (; j < p.size(); ++j) {
                literal lit = p[j].second;
                unsigned w = p[j].first;
                if (l_false != value(lit)) {
                    // skip
                }
                else if (lvl(lit) > lvl(l)) {
                    // skip
                }
                else if (lvl(lit) == lvl(l) && assigned_above(~lit, l)) {
                    // skip
                }
                else if (slack + w < k) {
                    slack += w;
                }
                else {
                    r.push_back(~lit); 
                }
            }
        }
        SASSERT(validate_unit_propagation(p, r, l));
    }

    bool solver::is_extended_binary(sat::ext_justification_idx idx, literal_vector & r) {
        return index2constraint(idx).is_extended_binary(r);
    }


    void solver::get_antecedents(literal l, card const& c, literal_vector& r) {
        if (l == ~c.lit()) {
            for (unsigned i = c.k() - 1; i < c.size(); ++i) {
                VERIFY(value(c[i]) == l_false);
                r.push_back(~c[i]);
            }   
            return;
        }
        DEBUG_CODE(
            bool found = false;
            for (unsigned i = 0; !found && i < c.k(); ++i) {
                found = c[i] == l;
            }
            CTRACE("ba",!found, s().display(tout << l << ":" << c << "\n"););
            SASSERT(found););
        
        VERIFY(c.lit() == sat::null_literal || value(c.lit()) != l_false);
        if (c.lit() != sat::null_literal) r.push_back(value(c.lit()) == l_true ? c.lit() : ~c.lit());
        for (unsigned i = c.k(); i < c.size(); ++i) {
            SASSERT(value(c[i]) == l_false);
            r.push_back(~c[i]);
        }
    }


    // ----------------------------
    // constraint generic methods

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector & r, bool probing) {
        get_antecedents(l, index2constraint(idx), r, probing);
    }


    void solver::get_antecedents(literal l, constraint const& c, literal_vector& r, bool probing) {
        switch (c.tag()) {
        case pb::tag_t::card_t: get_antecedents(l, c.to_card(), r); break;
        case pb::tag_t::pb_t: get_antecedents(l, c.to_pb(), r); break;
        default: UNREACHABLE(); break;            
        }
        if (get_config().m_drat && m_solver && !probing) {
            literal_vector lits;
            for (literal lit : r) 
                lits.push_back(~lit);
            lits.push_back(l);
            s().m_drat.add(lits, sat::status::th(true, get_id()));
        }
    }

    void solver::clear_watch(constraint& c) {
        c.clear_watch(*this);
    }

    void solver::remove_constraint(constraint& c, char const* reason) {
        TRACE("ba", display(tout << "remove ", c, true) << " " << reason << "\n";);
        IF_VERBOSE(21, display(verbose_stream() << "remove " << reason << " ", c, true););
        c.nullify_tracking_literal(*this);
        clear_watch(c);
        c.set_removed();
        m_constraint_removed = true;
    }

    // --------------------------------
    // validation

    bool solver::validate_unit_propagation(constraint const& c, literal l) const {
        return true;
        return c.validate_unit_propagation(*this, l);
    }

    bool solver::validate_conflict(constraint const& c) const {
        return eval(c) == l_false;
    }

    lbool solver::eval(constraint const& c) const {
        lbool v1 = c.lit() == sat::null_literal ? l_true : value(c.lit());
        return eval(v1, c.eval(*this));
    }

    lbool solver::eval(sat::model const& m, constraint const& c) const {
        lbool v1 = c.lit() == sat::null_literal ? l_true : pb::value(m, c.lit());
        return eval(v1, c.eval(m));
    }

    lbool solver::eval(lbool a, lbool b) const {
        if (a == l_undef || b == l_undef) return l_undef;
        return (a == b) ? l_true : l_false;
    }

    bool solver::validate() {
        if (!validate_watch_literals()) {
            return false;
        }
        for (constraint* c : m_constraints) {
            if (!validate_watched_constraint(*c)) 
                return false;
        }
        for (constraint* c : m_learned) {
            if (!validate_watched_constraint(*c)) 
                return false;
        }
        return true;
    }

    bool solver::validate_watch_literals() const {
        for (unsigned v = 0; v < s().num_vars(); ++v) {
            literal lit(v, false);
            if (lvl(lit) == 0) continue;
            if (!validate_watch_literal(lit)) return false;
            if (!validate_watch_literal(~lit)) return false;
        }        
        return true;
    }

    bool solver::validate_watch_literal(literal lit) const {
        if (lvl(lit) == 0) return true;
        for (auto const & w : get_wlist(lit)) {
            if (w.get_kind() == sat::watched::EXT_CONSTRAINT) {
                constraint const& c = index2constraint(w.get_ext_constraint_idx());
                if (!c.is_watching(~lit) && lit.var() != c.lit().var()) {
                    IF_VERBOSE(0, display(verbose_stream() << lit << " " << lvl(lit) << " is not watched in " << c << "\n", c, true););
                    UNREACHABLE();
                    return false;
                }
            }
        }
        return true;
    }

    bool solver::validate_watched_constraint(constraint const& c) const {
        if (c.is_pb() && !validate_watch(c.to_pb(), sat::null_literal)) {
            return false;
        }
        if (c.lit() != sat::null_literal && value(c.lit()) != l_true) return true;
        SASSERT(c.lit() == sat::null_literal || lvl(c.lit()) == 0 || (c.is_watched(*this, c.lit()) && c.is_watched(*this, ~c.lit())));
        if (eval(c) == l_true) {
            return true;
        }
        literal_vector lits(c.literals());
        for (literal l : lits) {
            if (lvl(l) == 0) continue;
            bool found = c.is_watched(*this, l);
            if (found != c.is_watching(l)) {

                IF_VERBOSE(0, 
                           verbose_stream() << "Discrepancy of watched literal: " << l << " id: " << c.id() 
                           << " clause: " << c << (found?" is watched, but shouldn't be":" not watched, but should be") << "\n";
                           s().display_watch_list(verbose_stream() <<  l << ": ", get_wlist(l)) << "\n";
                           s().display_watch_list(verbose_stream() << ~l << ": ", get_wlist(~l)) << "\n";
                           verbose_stream() << "value: " << value(l) << " level: " << lvl(l) << "\n";
                           display(verbose_stream(), c, true);
                           if (c.lit() != sat::null_literal) verbose_stream() << value(c.lit()) << "\n";);

                IF_VERBOSE(0, s().display_watches(verbose_stream()));

                UNREACHABLE();
                return false;
            }
        }
        return true;
    }

    bool solver::validate_watch(pbc const& p, literal alit) const {
        for (unsigned i = 0; i < p.size(); ++i) {
            literal l = p[i].second;
            if (l != alit && lvl(l) != 0 && p.is_watched(*this, l) != (i < p.num_watch())) {
                IF_VERBOSE(0, display(verbose_stream(), p, true);
                           verbose_stream() << "literal " << l << " at position " << i << " " << p.is_watched(*this, l) << "\n";);
                UNREACHABLE();
                return false;
            }
        }
        unsigned slack = 0;
        for (unsigned i = 0; i < p.num_watch(); ++i) {
            slack += p[i].first;
        }
        if (slack != p.slack()) {
            IF_VERBOSE(0, display(verbose_stream(), p, true););
            UNREACHABLE();
            return false;
        }
        return true;
    }

    
    /**
       \brief Lex on (glue, size)
    */
    struct constraint_glue_psm_lt {
        bool operator()(constraint const * c1, constraint const * c2) const {
            return 
                (c1->glue()  < c2->glue()) ||
                (c1->glue() == c2->glue() && 
                 (c1->psm() < c2->psm() || 
                  (c1->psm() == c2->psm() && c1->size() < c2->size())));
        }
    };

    void solver::update_psm(constraint& c) const {
        unsigned r = 0;
        switch (c.tag()) {            
        case pb::tag_t::card_t:
            for (literal l : c.to_card()) {                
                if (s().m_phase[l.var()] == !l.sign()) ++r;
            }
            break;
        case pb::tag_t::pb_t:
            for (wliteral l : c.to_pb()) {                
                if (s().m_phase[l.second.var()] == !l.second.sign()) ++r;
            }
            break;
        default:
            break;
        }
        c.set_psm(r);
    }
    
    void solver::gc() {
        if (m_learned.size() >= 2 * m_constraints.size() && 
            (s().at_search_lvl() || s().at_base_lvl())) {
            for (auto & c : m_learned) update_psm(*c);
            std::stable_sort(m_learned.begin(), m_learned.end(), constraint_glue_psm_lt());
            gc_half("glue-psm");
            cleanup_constraints(m_learned, true);
        }
    }

    void solver::gc_half(char const* st_name) {
        TRACE("ba", tout << "gc\n";);
        unsigned sz     = m_learned.size();
        unsigned new_sz = sz/2;
        unsigned removed = 0;
        for (unsigned i = new_sz; i < sz; i++) {
            constraint* c = m_learned[i];
            if (!m_constraint_to_reinit.contains(c)) {
                remove_constraint(*c, "gc");
                c->deallocate(m_allocator);
                ++removed;
            }
            else {
                m_learned[new_sz++] = c;
            }
        }
        m_stats.m_num_gc += removed;
        m_learned.shrink(new_sz);
        IF_VERBOSE(2, verbose_stream() << "(sat-gc :strategy " << st_name << " :deleted " << removed << ")\n";);
    }


    void solver::gc_vars(unsigned num_vars) {
        gc_vars(num_vars, m_constraints);
        gc_vars(num_vars, m_learned);
    }

    void solver::gc_vars(unsigned num_vars, ptr_vector<constraint>& cs) {
        unsigned j = 0;
        for (unsigned i = 0; i < cs.size(); ++i) {
            auto* c = cs[i];
            unsigned m = c->fold_max_var(0);
            if (m >= num_vars) {
                clear_watch(*c);
                c->nullify_tracking_literal(*this);
                c->deallocate(m_allocator);
            }
            else 
                cs[j++] = c;
        }
        cs.shrink(j);
    }


    lbool solver::add_assign(card& c, literal alit) {
        // literal is assigned to false.        
        unsigned sz = c.size();
        unsigned bound = c.k();
        TRACE("ba", tout << "assign: " << c.lit() << ": " << ~alit << "@" << lvl(~alit) << " " << c << "\n";);

        SASSERT(0 < bound && bound <= sz);
        if (bound == sz) {
            if (c.lit() != sat::null_literal && value(c.lit()) == l_undef) {
                assign(c, ~c.lit());
                return inconsistent() ? l_false : l_true;
            }
            set_conflict(c, alit);
            return l_false;
        }
        SASSERT(value(alit) == l_false);
        VERIFY(c.lit() == sat::null_literal || value(c.lit()) != l_false);
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
        VERIFY(index <= bound);
        VERIFY(c[index] == alit);
        
        // find a literal to swap with:
        for (unsigned i = bound + 1; i < sz; ++i) {
            literal lit2 = c[i];
            if (value(lit2) != l_false) {
                c.swap(index, i);
                c.watch_literal(*this, lit2);
                return l_undef;
            }
        }

        // conflict
        if (bound != index && value(c[bound]) == l_false) {
            TRACE("ba", tout << "conflict " << c[bound] << " " << alit << "\n";);
            if (c.lit() != sat::null_literal && value(c.lit()) == l_undef) {
                if (index + 1 < bound) c.swap(index, bound - 1);
                assign(c, ~c.lit());
                return inconsistent() ? l_false : l_true;
            }
            set_conflict(c, alit);
            return l_false;
        }

        if (index != bound) {
            c.swap(index, bound);
        }        

        // TRACE("ba", tout << "no swap " << index << " " << alit << "\n";);
        // there are no literals to swap with,
        // prepare for unit propagation by swapping the false literal into 
        // position bound. Then literals in positions 0..bound-1 have to be
        // assigned l_true.

        if (c.lit() != sat::null_literal && value(c.lit()) == l_undef) {
            return l_true;
        }

        for (unsigned i = 0; i < bound; ++i) {
            assign(c, c[i]);
        }

        if (c.learned() && c.glue() > 2) {
            unsigned glue;
            if (s().num_diff_false_levels_below(c.size(), c.begin(), c.glue()-1, glue)) {
                c.set_glue(glue);
            }
        }

        return inconsistent() ? l_false : l_true;
    }

    void solver::asserted(literal l) {
    }


    sat::check_result solver::check() { return sat::check_result::CR_DONE; }

    void solver::push() {
        m_constraint_to_reinit_lim.push_back(m_constraint_to_reinit.size());
    }

    void solver::pop(unsigned n) {        
        TRACE("sat_verbose", tout << "pop:" << n << "\n";);
        unsigned new_lim = m_constraint_to_reinit_lim.size() - n;
        m_constraint_to_reinit_last_sz = m_constraint_to_reinit_lim[new_lim];
        m_constraint_to_reinit_lim.shrink(new_lim);
        m_num_propagations_since_pop = 0;
    }

    void solver::pop_reinit() {
        unsigned sz = m_constraint_to_reinit_last_sz;
        for (unsigned i = sz; i < m_constraint_to_reinit.size(); ++i) {
            constraint* c = m_constraint_to_reinit[i];
            if (!init_watch(*c) && !s().at_base_lvl()) {
                m_constraint_to_reinit[sz++] = c;
            }
        }
        m_constraint_to_reinit.shrink(sz);        
    }

    void solver::simplify() {        
        if (!s().at_base_lvl()) 
            s().pop_to_base_level();
        if (s().inconsistent())
            return;
        unsigned trail_sz, count = 0;
        do {
            trail_sz = s().init_trail_size();
            m_simplify_change = false;
            m_clause_removed = false;
            m_constraint_removed = false;
            for (unsigned sz = m_constraints.size(), i = 0; i < sz; ++i) simplify(*m_constraints[i]);
            for (unsigned sz = m_learned.size(), i = 0; i < sz; ++i) simplify(*m_learned[i]);
            init_use_lists();
            remove_unused_defs();
            set_non_external();
            elim_pure();
            for (unsigned sz = m_constraints.size(), i = 0; i < sz; ++i) subsumption(*m_constraints[i]);
            for (unsigned sz = m_learned.size(), i = 0; i < sz; ++i) subsumption(*m_learned[i]);    
            unit_strengthen();
            cleanup_clauses();
            cleanup_constraints();

            count++;
        }        
        while (count < 10 && (m_simplify_change || trail_sz < s().init_trail_size()));

        gc();

        // validate_eliminated();

        IF_VERBOSE(1, 
                   unsigned subs = m_stats.m_num_bin_subsumes + m_stats.m_num_clause_subsumes + m_stats.m_num_pb_subsumes;
                   verbose_stream() << "(ba.simplify" << " :constraints " << m_constraints.size();
                   if (!m_learned.empty()) verbose_stream() << " :lemmas " << m_learned.size();
                   if (subs > 0) verbose_stream() << " :subsumes " << subs;
                   if (m_stats.m_num_gc > 0) verbose_stream() << " :gc " << m_stats.m_num_gc;
                   verbose_stream() << ")\n";);

        // IF_VERBOSE(0, s().display(verbose_stream()));
        // mutex_reduction();
        // if (s().m_clauses.size() < 80000) lp_lookahead_reduction();
    }

    void solver::mutex_reduction() {
        literal_vector lits;
        for (unsigned v = 0; v < s().num_vars(); ++v) {
            lits.push_back(literal(v, false));
            lits.push_back(literal(v, true));
        }
        vector<literal_vector> mutexes;
        s().find_mutexes(lits, mutexes);
        for (literal_vector& mux : mutexes) {
            if (mux.size() > 2) {
                IF_VERBOSE(1, verbose_stream() << "mux: " << mux << "\n";);
                for (unsigned i = 0; i < mux.size(); ++i) mux[i].neg(); 
                add_at_least(sat::null_literal, mux, mux.size() - 1, false);
            }
        }
    }

    // -------------------------
    // sorting networks
    literal solver::ba_sort::mk_false() {
        return ~mk_true();
    }

    literal solver::ba_sort::mk_true() {
        if (m_true == sat::null_literal) {
            bool_var v = s.s().mk_var(false, false);
            m_true = literal(v, false);
            s.s().mk_clause(1,&m_true);
        }
        VERIFY(m_true != sat::null_literal);
        return m_true;
    }

    literal solver::ba_sort::mk_not(literal l) { 
        return ~l; 
    }

    literal solver::ba_sort::fresh(char const*) {
        bool_var v = s.s().mk_var(false, true);
        return literal(v, false);
    }


    literal solver::ba_sort::mk_max(unsigned n, literal const* lits) {
        m_lits.reset();        
        for (unsigned i = 0; i < n; ++i) {
            if (lits[i] == m_true) return m_true;
            if (lits[i] == ~m_true) continue;
            m_lits.push_back(lits[i]);
        }
        switch (m_lits.size()) {
        case 0: 
            return ~m_true;
        case 1: 
            return m_lits[0];
        default: {
            literal max = fresh("max");
            for (unsigned i = 0; i < n; ++i) {
                s.s().mk_clause(~m_lits[i], max);
            }
            m_lits.push_back(~max);
            s.s().mk_clause(m_lits.size(), m_lits.data());
            return max;
        }
        }
    }

    literal solver::ba_sort::mk_min(unsigned n, literal const* lits) {
        m_lits.reset();        
        for (unsigned i = 0; i < n; ++i) {
            if (lits[i] == ~m_true) return ~m_true;
            if (lits[i] == m_true) continue;
            m_lits.push_back(lits[i]);
        }
        switch (m_lits.size()) {
        case 0: 
            return m_true;
        case 1: 
            return m_lits[0];
        default: {
            literal min = fresh("min");
            for (unsigned i = 0; i < n; ++i) {
                s.s().mk_clause(~min, m_lits[i]);
                m_lits[i] = ~m_lits[i];
            }
            m_lits.push_back(min);
            s.s().mk_clause(m_lits.size(), m_lits.data());
            return min;
        }
        }
    }

    void solver::ba_sort::mk_clause(unsigned n, literal const* lits) {
        m_lits.reset();
        m_lits.append(n, lits);
        s.s().mk_clause(n, m_lits.data());
    }

    std::ostream& solver::ba_sort::pp(std::ostream& out, literal l) const {
        return out << l;
    }

    
    // -------------------------------
    // set literals equivalent

    void solver::reserve_roots() {
        m_root_vars.reserve(s().num_vars(), false);
        for (unsigned i = m_roots.size(); i < 2 * s().num_vars(); ++i) {
            m_roots.push_back(sat::to_literal(i));
        }
    }

    bool solver::set_root(literal l, literal r) { 
        if (s().is_assumption(l.var())) {
            return false;
        }
        reserve_roots();
        m_roots[l.index()] = r;
        m_roots[(~l).index()] = ~r;
        m_root_vars[l.var()] = true;
        return true;
    }

    void solver::flush_roots() {
        if (m_roots.empty()) return;
        reserve_roots();
        // validate();
        m_constraint_removed = false;
        for (unsigned sz = m_constraints.size(), i = 0; i < sz; ++i) 
            flush_roots(*m_constraints[i]);
        for (unsigned sz = m_learned.size(), i = 0; i < sz; ++i) 
            flush_roots(*m_learned[i]);
        cleanup_constraints();
        // validate();

        // validate_eliminated();
    }

    void solver::validate_eliminated() {
        validate_eliminated(m_constraints);
        validate_eliminated(m_learned);
    }

    void solver::validate_eliminated(ptr_vector<constraint> const& cs) {
        for (constraint const* c : cs) {
            if (c->learned()) continue;
            for (auto l : constraint::literal_iterator(*c))
                VERIFY(!s().was_eliminated(l.var()));
        }
    }

    void solver::recompile(constraint& c) {
        if (c.id() == _bad_id) {
            IF_VERBOSE(0, display(verbose_stream() << "recompile\n", c, true););
        }
        switch (c.tag()) {
        case pb::tag_t::card_t:
            recompile(c.to_card());
            break;
        case pb::tag_t::pb_t:
            recompile(c.to_pb());
            break;
        default:
            UNREACHABLE();
        }                
    }

    void solver::recompile(card& c) {
        SASSERT(c.lit() == sat::null_literal || c.is_watched(*this, c.lit()));

        // pre-condition is that the literals, except c.lit(), in c are unwatched.
        if (c.id() == _bad_id) std::cout << "recompile: " << c << "\n";
        m_weights.resize(2*s().num_vars(), 0);
        for (literal l : c) {
            ++m_weights[l.index()];
        }
        unsigned k = c.k();
        bool all_units = true;
        unsigned sz = c.size();
        unsigned_vector coeffs;
        literal_vector lits;
        unsigned j = 0;
        for (unsigned i = 0; i < sz && 0 < k; ++i) {
            literal l = c[i];
            unsigned w = m_weights[l.index()];
            unsigned w2 = m_weights[(~l).index()];
            if (w == 0 || w < w2) {
                continue;
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
                    continue;
                }    
                else {
                    all_units &= (w == 1);
                    coeffs.push_back(w);
                    c[j++] = l;
                }
            }
        }
        sz = j;

        // clear weights
        for (literal l : c) {
            m_weights[l.index()] = 0;
            m_weights[(~l).index()] = 0;
        }       

        if (k == 0 && c.lit() == sat::null_literal) {
            remove_constraint(c, "recompiled to true");
            return;
        }

        if (k == 1 && c.lit() == sat::null_literal) {
            literal_vector lits(sz, c.literals().data());
            s().mk_clause(sz, lits.data(), sat::status::th(c.learned(), get_id()));
            remove_constraint(c, "recompiled to clause");
            return;
        }

        if (sz == 0) {
            if (c.lit() == sat::null_literal) {
                if (k > 0) {
                    s().mk_clause(0, nullptr, sat::status::th(false, get_id()));
                }
            }
            else if (k > 0) {
                literal lit = ~c.lit();
                s().mk_clause(1, &lit, sat::status::th(c.learned(), get_id()));
            }
            else {
                literal lit = c.lit();
                s().mk_clause(1, &lit, sat::status::th(c.learned(), get_id()));
            }
            remove_constraint(c, "recompiled to clause");
            return;
        }
        if (all_units && sz < k) {
            if (c.lit() == sat::null_literal) {
                s().mk_clause(0, nullptr, sat::status::th(c.learned(), get_id()));
            }
            else {
                literal lit = ~c.lit();
                s().mk_clause(1, &lit, sat::status::th(c.learned(), get_id()));
            }
            remove_constraint(c, "recompiled to clause");
            return;            
        }
        VERIFY(!all_units || c.size() - c.k() >= sz - k);
        c.set_size(sz);
        c.set_k(k);    

        if (all_units && clausify(c)) {
            return;
        }

        if (!all_units) {            
            TRACE("ba", tout << "replacing by pb: " << c << "\n";);
            m_wlits.reset();
            for (unsigned i = 0; i < sz; ++i) {
                m_wlits.push_back(wliteral(coeffs[i], c[i]));
            }
            literal root = c.lit();
            remove_constraint(c, "recompiled to pb");
            add_pb_ge(root, m_wlits, k, c.learned());
        }
        else {
            if (c.lit() == sat::null_literal || value(c.lit()) == l_true) {
                init_watch(c);
            }
            SASSERT(c.lit() == sat::null_literal || c.is_watched(*this, c.lit()));
            SASSERT(c.well_formed());
        }        
    }

    bool solver::clausify(literal lit, unsigned n, literal const* lits, unsigned k) {
        return false;
        bool is_def = lit != sat::null_literal;
        if ((!is_def || !s().was_eliminated(lit)) && 
            !std::any_of(lits, lits + n, [&](literal l) { return s().was_eliminated(l); })) {
            literal def_lit = m_sort.ge(is_def, k, n, lits);
            if (is_def) {
                s().mk_clause(~lit,  def_lit);
                s().mk_clause( lit, ~def_lit);
            }
            return true;
        }
        return false;
    }


    bool solver::clausify(card& c) {
        return false;
        if (get_config().m_card_solver)
            return false;

        //
        // TBD: conditions for when to clausify are TBD and
        // handling of conditional cardinality as well.
        // 
        if (!c.learned() && clausify(c.lit(), c.size(), c.begin(), c.k())) {
            IF_VERBOSE(1, verbose_stream() << "clausify " << c << "\n";);                       
            // compiled
        }        
        remove_constraint(c, "recompiled to clauses");
        return true;        
    }

    bool solver::clausify(pbc& p) {
        return false;
        if (get_config().m_card_solver) 
            return false;
        
        bool ok = !p.learned();
        bool is_def = p.lit() != sat::null_literal;
        for (wliteral wl : p) {
            ok &= !s().was_eliminated(wl.second);
        }
        ok &= !is_def || !s().was_eliminated(p.lit());
        if (!ok) {
            remove_constraint(p, "recompiled to clauses");
            return true;
        }

        if (is_cardinality(p, m_lemma)) {
            literal lit = m_sort.ge(is_def, p.k(), m_lemma.size(), m_lemma.data());
            if (is_def) {
                s().mk_clause(p.lit(), ~lit);
                s().mk_clause(~p.lit(), lit);
            }
            remove_constraint(p, "recompiled to clauses");
            return true;
        }
        return false;
    }

    bool solver::is_cardinality(pbc const& p, literal_vector& lits) {
        lits.reset();
        p.size();
        for (wliteral wl : p) {
            if (lits.size() > 2*p.size() + wl.first) {
                return false;
            }
            for (unsigned i = 0; i < wl.first; ++i) {
                lits.push_back(wl.second);
            }
        }
        return true;
    }

    void solver::flush_roots(constraint& c) {
        if (c.lit() != sat::null_literal && !c.is_watched(*this, c.lit())) {
            c.watch_literal(*this, c.lit());
            c.watch_literal(*this, ~c.lit());
        }
        SASSERT(c.lit() == sat::null_literal || c.is_watched(*this, c.lit()));
        bool found = c.lit() != sat::null_literal && m_root_vars[c.lit().var()];
        for (unsigned i = 0; !found && i < c.size(); ++i) {
            found = m_root_vars[c.get_lit(i).var()];
        }
        if (!found) return;
        clear_watch(c);
        
        // this could create duplicate literals
        for (unsigned i = 0; i < c.size(); ++i) {
            literal lit = m_roots[c.get_lit(i).index()];
            c.set_lit(i, lit);
        }

        literal root = c.lit();
        if (root != sat::null_literal && m_roots[root.index()] != root) {
            root = m_roots[root.index()];
            c.nullify_tracking_literal(*this);
            c.update_literal(root);
            c.watch_literal(*this, root);
            c.watch_literal(*this, ~root);
        }

        bool found_dup = false;
        bool found_root = false;
        init_visited();
        for (unsigned i = 0; i < c.size(); ++i) {
            literal l = c.get_lit(i);
            if (is_visited(l)) {
                found_dup = true;
                break;
            }
            else {
                mark_visited(l);
                mark_visited(~l);
            }
        }
        for (unsigned i = 0; i < c.size(); ++i) {
            found_root |= c.get_lit(i).var() == root.var();
        }

        if (found_root) {
            split_root(c);
            c.negate();
            split_root(c);
            remove_constraint(c, "flush roots");
        }
        else if (found_dup) {
            recompile(c);
        }
        else {
            if (c.lit() == sat::null_literal || value(c.lit()) != l_undef) init_watch(c);            
            SASSERT(c.well_formed());
        }
    }

    unsigned solver::get_num_unblocked_bin(literal l) {
        return s().m_simplifier.num_nonlearned_bin(l);
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
    void solver::init_use_lists() {
        m_clause_use_list.init(s().num_vars());
        m_cnstr_use_list.reset();
        m_cnstr_use_list.resize(2*s().num_vars());
        for (sat::clause* c : s().m_clauses) {
            if (!c->frozen()) 
                m_clause_use_list.insert(*c);
        }
        for (constraint* cp : m_constraints) {
            literal lit = cp->lit();
            if (lit != sat::null_literal) {
                m_cnstr_use_list[lit.index()].push_back(cp);
                m_cnstr_use_list[(~lit).index()].push_back(cp);
            }
            for (literal l : constraint::literal_iterator(*cp)) {
                m_cnstr_use_list[l.index()].push_back(cp);
                if (lit != sat::null_literal) m_cnstr_use_list[(~l).index()].push_back(cp);
            }
        }
    }

    void solver::remove_unused_defs() {
        if (incremental_mode()) return;
        // remove constraints where indicator literal isn't used.
        for (constraint* cp : m_constraints) {
            constraint& c = *cp;
            literal lit = c.lit();
            if (lit != sat::null_literal &&
                value(lit) == l_undef && 
                use_count(lit) == 1 &&
                use_count(~lit) == 1 &&
                get_num_unblocked_bin(lit) == 0 && 
                get_num_unblocked_bin(~lit) == 0) {
                remove_constraint(c, "unused def");
            }
        }
    }

    bool solver::incremental_mode() const {
        sat_simplifier_params p(s().m_params);
        bool incremental_mode = s().get_config().m_incremental && !p.override_incremental();
        incremental_mode |=  s().tracking_assumptions();
        return incremental_mode;
    }
    
    unsigned solver::set_non_external() {
        // set variables to be non-external if they are not used in theory constraints.
        unsigned ext = 0;
        if (!incremental_mode() && s().get_extension() == this) {
            for (unsigned v = 0; v < s().num_vars(); ++v) {
                literal lit(v, false);
                if (s().is_external(v) && 
                    m_cnstr_use_list[lit.index()].empty() && 
                    m_cnstr_use_list[(~lit).index()].empty()) {
                    s().set_non_external(v);
                    ++ext;
                }            
            }
        }
        // ensure that lemmas use only non-eliminated variables
        for (constraint* cp : m_learned) {
            constraint& c = *cp;
            if (c.was_removed()) continue;
            SASSERT(c.lit() == sat::null_literal);
            for (unsigned i = 0; i < c.size(); ++i) {
                bool_var v = c.get_lit(i).var();
                if (s().was_eliminated(v)) {
                    remove_constraint(c, "contains eliminated var");                    
                    break;
                }
            }
        }
        return ext;
    }

    bool solver::elim_pure(literal lit) {
        if (value(lit) == l_undef && !m_cnstr_use_list[lit.index()].empty() && 
            use_count(~lit) == 0 && get_num_unblocked_bin(~lit) == 0) {
            IF_VERBOSE(100, verbose_stream() << "pure literal: " << lit << "\n";);
            s().assign_scoped(lit);
            return true;
        }
        return false;
    }

    unsigned solver::elim_pure() {
        if (!get_config().m_elim_vars || incremental_mode()) {
            return 0;
        }
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
        return pure_literals;
    }

    /**
     * Strengthen inequalities using binary implication information.
     *
     * x -> ~y, x -> ~z,   y + z + u >= 2
     * ----------------------------------
     *       y + z + u + ~x >= 3
     * 
     * for c : constraints
     *   for l : c:
     *    slack <- of c under root(~l)
     *    if slack < 0:
     *       add ~root(~l) to c, k <- k + 1
     */ 
    void solver::unit_strengthen() {
        sat::big big(s().m_rand);
        big.init(s(), true);
        for (unsigned sz = m_constraints.size(), i = 0; i < sz; ++i) 
            unit_strengthen(big, *m_constraints[i]);
        for (unsigned sz = m_learned.size(), i = 0; i < sz; ++i) 
            unit_strengthen(big, *m_learned[i]);          
    }

    void solver::unit_strengthen(sat::big& big, constraint& p) {
        if (p.lit() != sat::null_literal) return;
        unsigned sz = p.size();
        for (unsigned i = 0; i < sz; ++i) {
            literal u = p.get_lit(i);
            literal r = big.get_root(u);
            if (r == u) continue;
            unsigned k = p.k(), b = 0;
            for (unsigned j = 0; j < sz; ++j) {
                literal v = p.get_lit(j);
                if (r == big.get_root(v)) {
                    b += p.get_coeff(j);
                }
            }            
            if (b > k) {
                r.neg();
                unsigned coeff = b - k;
                
                svector<wliteral> wlits;
                // add coeff * r to p
                wlits.push_back(wliteral(coeff, r));
                for (unsigned j = 0; j < sz; ++j) {
                    u = p.get_lit(j);
                    unsigned c = p.get_coeff(j);
                    if (r == u) {
                        wlits[0].first += c;
                    }
                    else if (~r == u) {
                        if (coeff == c) {
                            wlits[0] = wlits.back();
                            wlits.pop_back();
                            b -= c;
                        }
                        else if (coeff < c) {
                            wlits[0].first = c - coeff;
                            wlits[0].second.neg();
                            b -= coeff;
                        }
                        else {
                            // coeff > c
                            wlits[0].first = coeff - c;
                            b -= c;
                        }
                    }
                    else {
                        wlits.push_back(wliteral(c, u));
                    }
                }
                ++m_stats.m_num_big_strengthenings;
                p.set_removed();
                add_pb_ge(sat::null_literal, wlits, b, p.learned());
                return;
            }
        }
    }

    void solver::subsumption(constraint& cnstr) {
        if (cnstr.was_removed())
            return;
        if (cnstr.k() <= 1)
            return;
        switch (cnstr.tag()) {
        case pb::tag_t::card_t:
            subsumption(cnstr.to_card());
            break;
        case pb::tag_t::pb_t:
            subsumption(cnstr.to_pb());
            break;
        }
    }

    void solver::init_visited() { s().init_visited(); }
    void solver::mark_visited(literal l) { s().mark_visited(l); }
    void solver::mark_visited(bool_var v) { s().mark_visited(v); }
    bool solver::is_visited(bool_var v) const { return s().is_visited(v); }    
    bool solver::is_visited(literal l) const { return s().is_visited(l); }

    void solver::cleanup_clauses() {
        if (m_clause_removed) {
            cleanup_clauses(s().m_clauses);
            cleanup_clauses(s().m_learned);
        }
    }

    typedef sat::clause_vector clause_vector;
    typedef sat::clause clause;

    void solver::cleanup_clauses(clause_vector& clauses) {
        // version in simplify first clears 
        // all watch literals, then reinserts them.
        // this ensures linear time cleanup.
        clause_vector::iterator it = clauses.begin();
        clause_vector::iterator end = clauses.end();
        clause_vector::iterator it2 = it;
        for (; it != end; ++it) {
            clause* c = *it;
            if (c->was_removed() && s().can_delete(*c)) {
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
        clauses.set_end(it2);        
    }
    
    void solver::cleanup_constraints() {
        if (m_constraint_removed) {
            cleanup_constraints(m_constraints, false);
            cleanup_constraints(m_learned, true);
            m_constraint_removed = false;
        }
    }

    void solver::cleanup_constraints(ptr_vector<constraint>& cs, bool learned) {
        ptr_vector<constraint>::iterator it = cs.begin();
        ptr_vector<constraint>::iterator it2 = it;
        ptr_vector<constraint>::iterator end = cs.end();
        for (; it != end; ++it) {
            constraint& c = *(*it);
            if (c.was_removed()) {
                clear_watch(c);
                c.nullify_tracking_literal(*this);
                c.deallocate(m_allocator);
            }
            else if (learned && !c.learned()) {
                m_constraints.push_back(&c);
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
      - version that generalizes self-subsumption to more than one literal
        A + ~L + B >= k'   =>    A + B >= k'    if A + A' + L >= k and k' + |L| + |A'| <= k
     */
    bool solver::subsumes(card& c1, card& c2, literal_vector & comp) {
        if (c2.lit() != sat::null_literal) return false; 

        unsigned c2_exclusive = 0;
        unsigned common = 0;
        comp.reset();
        for (literal l : c2) {
            if (is_visited(l)) {
                ++common;
            }
            else if (is_visited(~l)) {
                comp.push_back(l);
            }
            else {
                ++c2_exclusive;
            }
        }

        unsigned c1_exclusive = c1.size() - common - comp.size();
        return c1_exclusive + c2.k() + comp.size() <= c1.k();
    }

    /*
      \brief L + A >= k subsumes L + C if |A| < k
             A + L + B >= k self-subsumes A + ~L + C >= 1
             if k + 1 - |B| - |C| - |L| > 0
     */
    bool solver::subsumes(card& c1, sat::clause& c2, bool& self) {
        unsigned common = 0, complement = 0, c2_exclusive = 0;
        self = false;
        
        for (literal l : c2) {
            if (is_visited(l)) {
                ++common;
            }
            else if (is_visited(~l)) {
                ++complement;
            }
            else {
                ++c2_exclusive;
            }
        }
        unsigned c1_exclusive = c1.size() - common - complement;
        if (complement > 0 && c1.k() + 1 > c1_exclusive + c2_exclusive + common) {
            self = true;
            return true; 
        }
        return c1.size() - common < c1.k();
    }

    /*
      \brief Ax >= k subsumes By >= k' if
      all coefficients in A are <= B and k >= k'
     */
    bool solver::subsumes(pbc const& p1, constraint const& p2) {
        if (p1.k() < p2.k() || p1.size() > p2.size()) return false;
        unsigned num_sub = 0;
        for (unsigned i = 0; i < p2.size(); ++i) {
            literal l = p2.get_lit(i);
            if (is_visited(l) && m_weights[l.index()] <= p2.get_coeff(i)) {
                ++num_sub;
            }
            if (p1.size() + i > p2.size() + num_sub) return false;
        }
        return num_sub == p1.size();
    }

    void solver::subsumes(pbc& p1, literal lit) {
        for (constraint* c : m_cnstr_use_list[lit.index()]) {
            if (c == &p1 || c->was_removed()) continue;
            bool s = false;
            switch (c->tag()) {
            case pb::tag_t::card_t:
                s = subsumes(p1, c->to_card()); 
                break;
            case pb::tag_t::pb_t:
                s = subsumes(p1, c->to_pb()); 
                break;
            default: 
                break;
            }
            if (s) {
                ++m_stats.m_num_pb_subsumes;                
                set_non_learned(p1);
                remove_constraint(*c, "subsumed");
            }
        }
    }

    literal solver::get_min_occurrence_literal(card const& c) {
        unsigned occ_count = UINT_MAX;
        literal lit = sat::null_literal;
        for (literal l : c) {
            unsigned occ_count1 = m_cnstr_use_list[l.index()].size();
            if (occ_count1 < occ_count) {
                lit = l;
                occ_count = occ_count1;
            }
        }
        return lit;
    }

    void solver::card_subsumption(card& c1, literal lit) {
        literal_vector slit;
        for (constraint* c : m_cnstr_use_list[lit.index()]) {
            if (!c->is_card() || c == &c1 || c->was_removed()) {
                continue;
            }
            card& c2 = c->to_card();

            SASSERT(&c1 != &c2);
            if (subsumes(c1, c2, slit)) {
                if (slit.empty()) {
                    TRACE("ba", tout << "subsume cardinality\n" << c1 << "\n" << c2 << "\n";);
                    remove_constraint(c2, "subsumed");
                    ++m_stats.m_num_pb_subsumes;
                    set_non_learned(c1);
                }
                else {
                    TRACE("ba", tout << "self subsume cardinality\n";);
                    IF_VERBOSE(11, 
                               verbose_stream() << "self-subsume cardinality\n"; 
                               verbose_stream() << c1 << "\n";
                               verbose_stream() << c2 << "\n";);
                    clear_watch(c2);                    
                    unsigned j = 0;
                    for (unsigned i = 0; i < c2.size(); ++i) {
                        if (!is_visited(~c2[i])) {
                            c2[j++] = c2[i];
                        }
                    }
                    c2.set_size(j);
                    init_watch(c2);
                    m_simplify_change = true;
                }
            }
        }
    }

    void solver::clause_subsumption(card& c1, literal lit, sat::clause_vector& removed_clauses) {
        SASSERT(!c1.was_removed());
        sat::clause_use_list& occurs = m_clause_use_list.get(lit);
        sat::clause_use_list::iterator it = occurs.mk_iterator();
        while (!it.at_end()) {
            sat::clause& c2 = it.curr();
            bool self;
            if (!c2.was_removed() && subsumes(c1, c2, self)) {
                if (self) {
                    // self-subsumption is TBD
                }
                else {
                    TRACE("ba", tout << "remove\n" << c1 << "\n" << c2 << "\n";);
                    removed_clauses.push_back(&c2);
                    ++m_stats.m_num_clause_subsumes;
                    set_non_learned(c1);
                }            
            }
            it.next();
        }
    }

    void solver::set_non_learned(constraint& c) {
        literal lit = c.lit();
        if (lit != sat::null_literal) {
            s().set_external(lit.var());
        }
        for (literal lit : constraint::literal_iterator(c)) {
            s().set_external(lit.var());             
            SASSERT(!s().was_eliminated(lit.var()));
        }
        c.set_learned(false);
    }

    typedef sat::watch_list watch_list;

    void solver::binary_subsumption(card& c1, literal lit) {
        if (c1.k() + 1 != c1.size()) return;
        SASSERT(is_visited(lit));
        SASSERT(!c1.was_removed());
        watch_list & wlist = get_wlist(~lit);
        watch_list::iterator it = wlist.begin();
        watch_list::iterator it2 = it;
        watch_list::iterator end = wlist.end();
        for (; it != end; ++it) {
            sat::watched w = *it;
            if (w.is_binary_clause() && is_visited(w.get_literal())) {
                ++m_stats.m_num_bin_subsumes;
                IF_VERBOSE(20, verbose_stream() << c1 << " subsumes (" << lit << " " << w.get_literal() << ")\n";);
                if (!w.is_learned()) {
                    set_non_learned(c1);
                }
            }
            else {
                if (it != it2) {
                    *it2 = *it;
                }
                ++it2;
            }
        }
        wlist.set_end(it2);        
    }

    void solver::subsumption(card& c1) {
        if (c1.was_removed() || c1.lit() != sat::null_literal) {
            return;
        }
        sat::clause_vector removed_clauses;
        init_visited();
        for (literal l : c1) mark_visited(l);  
        for (unsigned i = 0; i < std::min(c1.size(), c1.k() + 1); ++i) {
            literal lit = c1[i];            
            card_subsumption(c1, lit);
            clause_subsumption(c1, lit, removed_clauses);
            binary_subsumption(c1, lit);                   
        }
        m_clause_removed |= !removed_clauses.empty();
        for (clause *c : removed_clauses) {
            c->set_removed(true);
            m_clause_use_list.erase(*c);
        }
    }

    void solver::subsumption(pbc& p1) {
        if (p1.was_removed() || p1.lit() != sat::null_literal) {
            return;
        }
        init_visited();
        for (wliteral l : p1) {
            SASSERT(m_weights.size() <= l.second.index() || m_weights[l.second.index()] == 0);
            m_weights.setx(l.second.index(), l.first, 0);
            mark_visited(l.second);  
        }
        for (unsigned i = 0; i < std::min(10u, p1.num_watch()); ++i) {
            unsigned j = s().m_rand() % p1.num_watch();
            subsumes(p1, p1[j].second);
        }
        for (wliteral l : p1) {
            m_weights[l.second.index()] = 0;
        }        
    }

    void solver::clauses_modifed() {}

    lbool solver::get_phase(bool_var v) { return l_undef; }

    /*
      \brief lit <=> conjunction of unconstrained lits
     */
    void solver::assert_unconstrained(literal lit, literal_vector const& lits) {
        if (lit == sat::null_literal) {
            for (literal l : lits) {
                if (value(l) == l_undef) {
                    s().assign_scoped(l);
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

    sat::extension* solver::copy(sat::solver* s) {
        return clone_aux(m, *s, si, m_id);
    }

    euf::th_solver* solver::clone(euf::solver& new_ctx) {
        return clone_aux(new_ctx.get_manager(), new_ctx.s(), new_ctx.get_si(), get_id());
    }

    euf::th_solver* solver::clone_aux(ast_manager& m, sat::solver& s, sat::sat_internalizer& si, euf::theory_id id) {
        solver* result = alloc(solver, m, si, id);
        result->set_solver(&s);
        copy_constraints(result, m_constraints);
        return result;
    }

    void solver::copy_constraints(solver* result, ptr_vector<constraint> const& constraints) {
        literal_vector lits;
        svector<wliteral> wlits;
        for (constraint* cp : constraints) {
            switch (cp->tag()) {
            case pb::tag_t::card_t: {
                card const& c = cp->to_card();
                lits.reset();
                for (literal l : c) lits.push_back(l);
                result->add_at_least(c.lit(), lits, c.k(), c.learned());        
                break;
            }
            case pb::tag_t::pb_t: {
                pbc const& p = cp->to_pb();
                wlits.reset();
                for (wliteral w : p) {
                    wlits.push_back(w);
                }
                result->add_pb_ge(p.lit(), wlits, p.k(), p.learned());
                break;
            }
            default:
                UNREACHABLE();
            }                
        }
    }

    void solver::init_use_list(sat::ext_use_list& ul) {
        ul.init(s().num_vars());
        for (constraint const* cp : m_constraints) {
            sat::ext_constraint_idx idx = cp->cindex();
            if (cp->lit() != sat::null_literal) {
                ul.insert(cp->lit(), idx);
                ul.insert(~cp->lit(), idx);                
            }
            cp->init_use_list(ul);
        }
    }

    //
    // literal is used in a clause (C or l), it
    // it occurs negatively in constraint c.
    // all literals in C are marked
    // 
    bool solver::is_blocked(literal l, sat::ext_constraint_idx idx) {
        constraint const& c = index2constraint(idx);
        sat::simplifier& sim = s().m_simplifier;
        if (c.lit() != sat::null_literal) return false;
        return c.is_blocked(sim, l);
    }


    void solver::find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) {
        sat::literal_set slits(lits);
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

    void solver::display(std::ostream& out, ineq const& ineq, bool values) const {
        for (unsigned i = 0; i < ineq.size(); ++i) {
            if (ineq.coeff(i) != 1) out << ineq.coeff(i) << "*";
            out << ineq.lit(i) << " ";
            if (values) out << value(ineq.lit(i)) << " ";
        }
        out << ">= " << ineq.m_k << "\n";
    }


    std::ostream& solver::display(std::ostream& out) const {
        for (constraint const* c : m_constraints) {
            out << (*c) << "\n";
        }
        if (!m_learned.empty()) {
            out << "learned:\n";
        }
        for (constraint const* c : m_learned) {
            out << (*c) << "\n";
        }
        return out;
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        return out << index2constraint(idx);
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out << index2constraint(idx);
    }

    std::ostream& solver::display(std::ostream& out, constraint const& c, bool values) const {
        return c.display(out, *this, values);
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("pb propagations", m_stats.m_num_propagations);
        st.update("pb conflicts", m_stats.m_num_conflicts);
        st.update("pb resolves", m_stats.m_num_resolves);
        st.update("pb cuts", m_stats.m_num_cut);
        st.update("pb gc", m_stats.m_num_gc);
        st.update("pb overflow", m_stats.m_num_overflow);
        st.update("pb big strengthenings", m_stats.m_num_big_strengthenings);
        st.update("pb lemmas", m_stats.m_num_lemmas);
        st.update("pb subsumes", m_stats.m_num_bin_subsumes + m_stats.m_num_clause_subsumes + m_stats.m_num_pb_subsumes);
    }


    bool solver::validate_unit_propagation(pbc const& p, literal_vector const& r, literal alit) const {
        // all elements of r are true, 
        for (literal l : r) {
            if (value(l) != l_true) {
                IF_VERBOSE(0, verbose_stream() << "value of " << l << " is " << value(l) << "\n";
                           display(verbose_stream(), p, true););
                return false;
            }
            if (value(alit) == l_true && lvl(l) > lvl(alit)) {
                IF_VERBOSE(0, 
                           verbose_stream() << "level of premise " << l << " is " << lvl(l) << "\n";
                           verbose_stream() << "level of asserting literal " << alit << " is " << lvl(alit) << "\n";
                           display(verbose_stream(), p, true););
                return false;                
            }
            // if (value(alit) == l_true && lvl(l) == lvl(alit)) {
            // std::cout << "same level " << alit << " " << l << "\n";
            // }
        }
        // the sum of elements not in r or alit add up to less than k.
        unsigned sum = 0;
        // 
        // a*x + b*alit + c*r >= k
        // sum a < k
        // val(r) = false
        // hence alit has to be true.
        for (wliteral wl : p) {
            literal lit = wl.second;
            if (lit != alit && !r.contains(~lit)) {
                sum += wl.first;
            }
        }
        if (sum >= p.k()) {
            IF_VERBOSE(0,             
                       verbose_stream() << "sum is " << sum << " >= " << p.k() << "\n";
                       display(verbose_stream(), p, true);
                       verbose_stream() << "id: " << p.id() << "\n";
                       sum = 0;
                       for (wliteral wl : p) sum += wl.first;
                       verbose_stream() << "overall sum " << sum << "\n";
                       verbose_stream() << "asserting literal: " << alit << "\n";
                       verbose_stream() << "reason: " << r << "\n";);
            return false;
        }
        for (wliteral wl : p) {
            if (alit == wl.second) {
                return true;
            }
        }
        IF_VERBOSE(0, verbose_stream() << alit << " not found among literals\n";);
        return false;
    }


    bool solver::validate_lemma() { 
        int64_t bound64 = m_bound;
        int64_t val = -bound64;
        reset_active_var_set();
        for (bool_var v : m_active_vars) {
            if (!test_and_set_active(v)) continue;
            wliteral wl = get_wliteral(v);
            if (wl.first == 0) continue;
            if (!is_false(wl.second)) {
                val += wl.first;
            }
        }
        CTRACE("ba", val >= 0, active2pb(m_A); display(tout, m_A, true););
        return val < 0;
    }

    /**
     * the slack of inequalities on the stack should be non-positive.
     */
    bool solver::validate_ineq(ineq const& ineq) const {
        int64_t k = -static_cast<int64_t>(ineq.m_k);
        for (wliteral wl : ineq.m_wlits) {
            if (!is_false(wl.second))
                k += wl.first;
        }
        CTRACE("ba", k > 0, display(tout, ineq, true););
        return k <= 0;
    }

    void solver::reset_active_var_set() {
        while (!m_active_var_set.empty()) m_active_var_set.erase();
    }

    bool solver::test_and_set_active(bool_var v) {
        if (m_active_var_set.contains(v)) {
            return false;
        }
        else {
            m_active_var_set.insert(v);
            return true;
        }
    }

    void solver::active2pb(ineq& p) {
        p.reset(m_bound);
        active2wlits(p.m_wlits);
    }

    void solver::active2wlits() {
        m_wlits.reset();
        active2wlits(m_wlits);
    }

    void solver::active2wlits(svector<wliteral>& wlits) {
        uint64_t sum = 0;        
        reset_active_var_set();
        for (bool_var v : m_active_vars) {
            if (!test_and_set_active(v)) continue;
            wliteral wl = get_wliteral(v);
            if (wl.first == 0) continue;
            wlits.push_back(wl);
            sum += wl.first;
        }
        m_overflow |= sum >= UINT_MAX/2;
    }

    constraint* solver::active2lemma() {
        switch (get_config().m_pb_lemma_format) {
        case sat::PB_LEMMA_CARDINALITY:
            return active2card();
        case sat::PB_LEMMA_PB:
            return active2constraint();
        default:
            UNREACHABLE();
            return nullptr;
        }
    }

    constraint* solver::active2constraint() {
        active2wlits();
        if (m_overflow) {
            return nullptr;
        }
        constraint* c = add_pb_ge(sat::null_literal, m_wlits, m_bound, true);                
        TRACE("ba", if (c) display(tout, *c, true););
        ++m_stats.m_num_lemmas;
        return c;
    }
    
    /*
      Chai Kuhlmann:
      
      a1*l1 + ... + a_n*l_n >= k
      s.t.
      a1 >= a2 >= .. >= a_n

      let m be such that

         sum_{i = 1}^{m-1} a_i < k <= sum_{i = 1}^{m}

      then 

      l1 + ... + l_n >= m

      furthermore, for the largest n' <= n, such that

         sum_{i = n'+1}^n a_i + sum_{i = 1}^{m-1} a_i < k

      then 

         l1 + ... + l_n' >= m
      
     */
    struct compare_wlit {
        bool operator()(wliteral l1, wliteral l2) const {
            return l1.first > l2.first;
        }
    };


    constraint* solver::active2card() {
        active2wlits();
        if (m_overflow) {
            return nullptr;
        }
        std::sort(m_wlits.begin(), m_wlits.end(), compare_wlit());
        unsigned k = 0;
        uint64_t sum = 0, sum0 = 0;
        for (wliteral wl : m_wlits) {
            if (sum >= m_bound) break;
            sum0 = sum;
            sum += wl.first;
            ++k;
        }
        if (k == 1) {
            return nullptr;
        }
        while (!m_wlits.empty()) {
            wliteral wl = m_wlits.back();
            if (wl.first + sum0 >= m_bound) break;
            m_wlits.pop_back();
            sum0 += wl.first;
        }

        unsigned slack = 0;
        unsigned max_level = 0;
        unsigned num_max_level = 0;
        for (wliteral wl : m_wlits) {
            if (value(wl.second) != l_false) ++slack;
            unsigned level = lvl(wl.second);
            if (level > max_level) {
                max_level = level;
                num_max_level = 1;
            }
            else if (max_level == level) {
                ++num_max_level;
            }
        }
        if (m_overflow) {
            return nullptr;
        }

        if (slack >= k) {
#if 0
            return active2constraint();
            active2pb(m_A);
            std::cout << "not asserting\n";
            display(std::cout, m_A, true);
#endif
            return nullptr;
        }

        // produce asserting cardinality constraint
        literal_vector lits;
        for (wliteral wl : m_wlits) { 
            lits.push_back(wl.second);
        }       
        constraint* c = add_at_least(sat::null_literal, lits, k, true);      

        ++m_stats.m_num_lemmas;

        if (c) {
            lits.reset();
            for (wliteral wl : m_wlits) {
                if (value(wl.second) == l_false) lits.push_back(wl.second);        
            }
            unsigned glue = s().num_diff_levels(lits.size(), lits.data());
            c->set_glue(glue);
        }
        return c;
    }


    void solver::justification2pb(sat::justification const& js, literal lit, unsigned offset, ineq& ineq) {
        switch (js.get_kind()) {
        case sat::justification::NONE:
            SASSERT(lit != sat::null_literal);
            ineq.reset(offset);
            ineq.push(lit, offset);
            break;
        case sat::justification::BINARY:
            SASSERT(lit != sat::null_literal);
            ineq.reset(offset);
            ineq.push(lit, offset);
            ineq.push(js.get_literal(), offset);
            break;
        case sat::justification::TERNARY:
            SASSERT(lit != sat::null_literal);
            ineq.reset(offset);
            ineq.push(lit, offset);
            ineq.push(js.get_literal1(), offset);
            ineq.push(js.get_literal2(), offset);
            break;
        case sat::justification::CLAUSE: {
            ineq.reset(offset);
            sat::clause & c = s().get_clause(js);
            for (literal l : c) ineq.push(l, offset);
            break;
        }
        case sat::justification::EXT_JUSTIFICATION: {
            sat::ext_justification_idx index = js.get_ext_justification_idx();
            VERIFY(this == sat::constraint_base::to_extension(index));
            constraint& cnstr = index2constraint(index);
            constraint2pb(cnstr, lit, offset, ineq);
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }

    void solver::constraint2pb(constraint& cnstr, literal lit, unsigned offset, ineq& ineq) {
        switch (cnstr.tag()) {
        case pb::tag_t::card_t: {
            card& c = cnstr.to_card();
            ineq.reset(static_cast<uint64_t>(offset)*c.k());
            for (literal l : c) ineq.push(l, offset);
            if (c.lit() != sat::null_literal) ineq.push(~c.lit(), offset*c.k());                
            break;
        }
        case pb::tag_t::pb_t: {
            pbc& p = cnstr.to_pb();
            ineq.reset(static_cast<uint64_t>(offset) * p.k());
            for (wliteral wl : p) ineq.push(wl.second, offset * wl.first);
            if (p.lit() != sat::null_literal) ineq.push(~p.lit(), offset * p.k());
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }

    // validate that m_A & m_B implies m_C

    bool solver::validate_resolvent() {
        return true;
        u_map<uint64_t> coeffs;
        uint64_t k = m_A.m_k + m_B.m_k;
        for (unsigned i = 0; i < m_A.size(); ++i) {
            uint64_t coeff = m_A.coeff(i);
            SASSERT(!coeffs.contains(m_A.lit(i).index()));
            coeffs.insert(m_A.lit(i).index(), coeff);
        }
        for (unsigned i = 0; i < m_B.size(); ++i) {
            uint64_t coeff1 = m_B.coeff(i), coeff2;
            literal lit = m_B.lit(i);
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
        for (unsigned i = 0; i < m_C.size(); ++i) {
            literal lit = m_C.lit(i);
            uint64_t coeff;
            if (coeffs.find(lit.index(), coeff)) {
                if (coeff > m_C.coeff(i) && m_C.coeff(i) < m_C.m_k) {
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
        // last ditch effort by translating to SAT.
        sat::solver s0(s().m_params, s().rlimit());
        u_map<bool_var> translation;
        literal l1 = translate_to_sat(s0, translation, m_A);
        if (l1 == sat::null_literal) return true;
        literal l2 = translate_to_sat(s0, translation, m_B);
        if (l2 == sat::null_literal) return true;
        ineq notC = negate(m_B);
        literal l3 = translate_to_sat(s0, translation, notC);
        if (l3 == sat::null_literal) return true;
        s0.assign_scoped(l1);
        s0.assign_scoped(l2);
        s0.assign_scoped(l3);
        lbool is_sat = s0.check();
        TRACE("ba", s0.display(tout << "trying sat encoding"););
        if (is_sat == l_false) return true;

        IF_VERBOSE(0, 
                   display(verbose_stream(), m_A);
                   display(verbose_stream(), m_B);
                   display(verbose_stream(), m_C);
                   for (auto& e : coeffs) {
                       verbose_stream() << sat::to_literal(e.m_key) << ": " << e.m_value << "\n";
                   });
        
        UNREACHABLE();
        return false;
    }

    /**
       \brief translate PB inequality to SAT formula.
     */
    literal solver::translate_to_sat(sat::solver& s, u_map<bool_var>& translation, ineq const& pb) {
        SASSERT(pb.m_k > 0);
        if (pb.size() > 1) {
            ineq a, b;
            a.reset(pb.m_k);
            b.reset(pb.m_k);
            for (unsigned i = 0; i < pb.size()/2; ++i) {
                a.push(pb.lit(i), pb.coeff(i));
            }
            for (unsigned i = pb.size()/2; i < pb.size(); ++i) {
                b.push(pb.lit(i), pb.coeff(i));
            }
            bool_var v = s.mk_var();
            literal lit(v, false);
            literal_vector lits;
            lits.push_back(~lit);            
            push_lit(lits, translate_to_sat(s, translation, a));
            push_lit(lits, translate_to_sat(s, translation, b));
            push_lit(lits, translate_to_sat(s, translation, a, b));
            s.mk_clause(lits);
            return lit;
        }
        if (pb.coeff(0) >= pb.m_k) {
            return translate_to_sat(s, translation, pb.lit(0));
        }
        else {
            return sat::null_literal;
        }
    }

    /*
      \brief encode the case where Sum(a) >= k-1 & Sum(b) >= 1 \/ ... \/ Sum(a) >= 1 & Sum(b) >= k-1
     */
    literal solver::translate_to_sat(sat::solver& s, u_map<bool_var>& translation, ineq& a, ineq& b) {
        uint64_t k0 = a.m_k;
        literal_vector lits;
        for (unsigned k = 1; k < a.m_k - 1; ++k) {
            a.m_k = k; b.m_k = k0 - k;
            literal lit1 = translate_to_sat(s, translation, a);
            literal lit2 = translate_to_sat(s, translation, b);
            if (lit1 != sat::null_literal && lit2 != sat::null_literal) {
                bool_var v = s.mk_var();
                literal lit(v, false);
                s.mk_clause(~lit, lit1);
                s.mk_clause(~lit, lit2);
                lits.push_back(lit);
            }
        }
        a.m_k = k0;
        b.m_k = k0;
        switch (lits.size()) {
        case 0: return sat::null_literal;
        case 1: return lits[0];
        default: {
            bool_var v = s.mk_var();
            literal lit(v, false);
            lits.push_back(~lit);
            s.mk_clause(lits);
            return lit;
        }
        }
    }
    
    literal solver::translate_to_sat(sat::solver& s, u_map<bool_var>& translation, literal lit) {
        bool_var v;
        if (!translation.find(lit.var(), v)) {            
            v = s.mk_var();
            translation.insert(lit.var(), v);
        }
        return literal(v, lit.sign());
    }

    solver::ineq solver::negate(ineq const& a) const {
        ineq result;
        uint64_t sum = 0;
        for (unsigned i = 0; i < a.size(); ++i) { 
            result.push(~a.lit(i), a.coeff(i));
            sum += a.coeff(i);
        }
        SASSERT(sum >= a.m_k + 1);
        result.m_k = sum + 1 - a.m_k;
        return result;
    }

    void solver::push_lit(literal_vector& lits, literal lit) {
        if (lit != sat::null_literal) {
            lits.push_back(lit);
        }
    }

    bool solver::validate_conflict(literal_vector const& lits, ineq& p) { 
        for (literal l : lits) {
            if (value(l) != l_false) {
                TRACE("ba", tout << "literal " << l << " is not false\n";);
                return false;
            }
            if (!p.contains(l)) {
                TRACE("ba", tout << "lemma contains literal " << l << " not in inequality\n";);
                return false;
            }
        }
        uint64_t value = 0;        
        for (unsigned i = 0; i < p.size(); ++i) {
            uint64_t coeff = p.coeff(i);
            if (!lits.contains(p.lit(i))) {
                value += coeff;
            }
        }
        CTRACE("ba", value >= p.m_k, tout << "slack: " << value << " bound " << p.m_k << "\n";
               display(tout, p);
               tout << lits << "\n";);
        return value < p.m_k;
    }

    bool solver::check_model(sat::model const& m) const {
        bool ok = true;
        for (constraint const* c : m_constraints) {
            if (c->was_removed()) {
                continue;
            }
            if (c->is_pure() && c->lit() != sat::null_literal && m[c->lit().var()] == (c->lit().sign() ? l_true : l_false)) {
                continue;
            }
            switch (eval(m, *c)) {
            case l_false: 
                IF_VERBOSE(0, verbose_stream() << "failed checking " << c->id() << ": " << *c << "\n";);
                ok = false;
                break;
            case l_true:
                break;
            case l_undef:
                IF_VERBOSE(0, verbose_stream() << "undef " << c->id() << ": " << *c << "\n";);
                break;
            }
        }
        return ok;
    }

    bool solver::extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& add_cardinality,
                               std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& add_pb) {
        
        unsigned_vector coeffs;
        literal_vector lits;
        for (constraint* cp : m_constraints) {
            switch (cp->tag()) {
            case pb::tag_t::card_t: {
                card const& c = cp->to_card();
                unsigned n = c.size();
                unsigned k = c.k();

                if (c.lit() == sat::null_literal) {
                    //    c.lits() >= k 
                    // <=> 
                    //    ~c.lits() <= n - k
                    lits.reset();
                    for (unsigned j = 0; j < n; ++j) lits.push_back(c[j]);
                    add_cardinality(lits.size(), lits.data(), n - k);
                }
                else {
                    //
                    // c.lit() <=> c.lits() >= k
                    // 
                    //    (c.lits() < k) or c.lit()
                    // =  (c.lits() + (n - k + 1)*~c.lit()) <= n    
                    //
                    //    ~c.lit() or (c.lits() >= k)
                    // =  ~c.lit() or (~c.lits() <= n - k)
                    // =  k*c.lit() + ~c.lits() <= n 
                    // 
                    lits.reset();
                    coeffs.reset();
                    for (literal l : c) lits.push_back(l), coeffs.push_back(1);
                    lits.push_back(~c.lit()); coeffs.push_back(n - k + 1);
                    add_pb(lits.size(), lits.data(), coeffs.data(), n);

                    lits.reset();
                    coeffs.reset();
                    for (literal l : c) lits.push_back(~l), coeffs.push_back(1);
                    lits.push_back(c.lit()); coeffs.push_back(k);
                    add_pb(lits.size(), lits.data(), coeffs.data(), n);
                }
                break;
            }
            case pb::tag_t::pb_t: {
                pbc const& p = cp->to_pb();
                lits.reset();
                coeffs.reset();
                unsigned sum = 0;
                for (wliteral wl : p) sum += wl.first;

                if (p.lit() == sat::null_literal) {
                    //   w1 + .. + w_n >= k
                    // <=> 
                    //  ~wl + ... + ~w_n <= sum_of_weights - k
                    for (wliteral wl : p) lits.push_back(~(wl.second)), coeffs.push_back(wl.first);
                    add_pb(lits.size(), lits.data(), coeffs.data(), sum - p.k());
                }
                else {
                    //    lit <=> w1 + .. + w_n >= k
                    // <=>
                    //     lit or w1 + .. + w_n <= k - 1
                    //    ~lit or w1 + .. + w_n >= k
                    // <=> 
                    //     (sum - k + 1)*~lit + w1 + .. + w_n <= sum
                    //     k*lit + ~wl + ... + ~w_n <= sum
                    lits.push_back(p.lit()), coeffs.push_back(p.k());
                    for (wliteral wl : p) lits.push_back(~(wl.second)), coeffs.push_back(wl.first);
                    add_pb(lits.size(), lits.data(), coeffs.data(), sum);

                    lits.reset();
                    coeffs.reset();
                    lits.push_back(~p.lit()), coeffs.push_back(sum + 1 - p.k());
                    for (wliteral wl : p) lits.push_back(wl.second), coeffs.push_back(wl.first);
                    add_pb(lits.size(), lits.data(), coeffs.data(), sum);
                }
                break;
            }
            }
        }
        return true;
    }
    
};


