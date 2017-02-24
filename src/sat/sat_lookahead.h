/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_lookahead.h

Abstract:
   
    Lookahead SAT solver in the style of March.

Author:

    Nikolaj Bjorner (nbjorner) 2017-2-11

Notes:

--*/
#ifndef _SAT_LOOKAHEAD_H_
#define _SAT_LOOKAHEAD_H_

namespace sat {
    class lookahead {
        solver& s;

        struct config {
            double   m_dl_success;
        };

        struct statistics {
            unsigned m_propagations;
            statistics() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        config                 m_config;
        double                 m_delta_trigger; 
        literal_vector         m_trail;
        unsigned_vector        m_trail_lim;
        literal_vector         m_units;
        unsigned_vector        m_units_lim;
        vector<literal_vector> m_binary;        // binary clauses
        unsigned_vector        m_binary_trail;  // trail of added binary clauses
        unsigned_vector        m_binary_trail_lim; 
        clause_vector          m_clauses;       // non-binary clauses
        clause_allocator       m_cls_allocator;        
        bool                   m_inconsistent;
        unsigned_vector        m_bstamp;        // timestamp for binary implication, one for each literal
        unsigned               m_bstamp_id;     // unique id for binary implication.
        unsigned               m_qhead;
        unsigned_vector        m_qhead_lim;
        char_vector            m_assignment;
        vector<watch_list>     m_watches;
        indexed_uint_set       m_free_vars;
        statistics             m_stats;

        void add_binary(literal l1, literal l2) {
            SASSERT(l1 != l2);
            SASSERT(~l1 != l2);
            m_binary[(~l1).index()].push_back(l2);
            m_binary[(~l2).index()].push_back(l1);
            m_binary_trail.push_back((~l1).index());
        }

        void del_binary(unsigned idx) {
            literal_vector & lits = m_binary[idx];
            literal l = lits.back();
            lits.pop_back();
            m_binary[(~l).index()].pop_back();
        }

        // -------------------------------------
        // track consequences of binary clauses
        // see also 72 - 77 in sat11.w

        void inc_bstamp() {
            ++m_bstamp_id;
            if (m_bstamp_id == 0) {
                ++m_bstamp_id;
                m_bstamp.fill(0);
            }
        }
        void set_bstamp(literal l) {
            m_bstamp[l.index()] = m_bstamp_id;
        }
        void set_bstamps(literal l) {
            set_bstamp(l);
            literal_vector const& conseq = m_binary[l.index()];
            for (unsigned i = 0; i < conseq.size(); ++i) {
                set_bstamp(conseq[i]);
            }
        }
        bool is_stamped(literal l) const { return m_bstamp[l.index()] == m_bstamp_id; }

        /**
           \brief add one-step transitive closure of binary implications
                  return false if we learn a unit literal.
           \pre all implicants of ~u are stamped.
                u \/ v is true
        **/

        bool add_tc1(literal u, literal v) {
            unsigned sz = m_binary[v.index()].size();
            for (unsigned i = 0; i < sz; ++i) {
                literal w = m_binary[v.index()][i];
                // ~v \/ w
                if (!is_fixed(w)) {
                    if (is_stamped(~w)) {
                        // u \/ v, ~v \/ w, u \/ ~w => u is unit
                        assign(u);        
                        return false;
                    }
                    add_binary(u, w);
                }
            }
            return true;
        }

        /**
           \brief main routine for adding a new binary clause dynamically.
         */
        void try_add_binary(literal u, literal v) {
            SASSERT(u.var() != v.var());
            inc_bstamp();
            set_bstamps(~u);
            if (is_stamped(~v)) {
                // u \/ ~v is a binary clause, u \/ v is true => u is a unit literal
                assign(u);
            }
            else if (!is_stamped(v) && add_tc1(u, v)) {
                // u \/ v is not in index
                // all implicants of ~u are stamped.                
                inc_bstamp();
                set_bstamps(~v);
                if (is_stamped(~u)) {
                    // v \/ ~u is a binary clause, u \/ v is true => v is a unit
                    assign(v);
                }
                else if (add_tc1(v, u)) {
                    add_binary(u, v);
                }
            }
        }
        
        void init_var(bool_var v) {
            m_assignment.push_back(l_undef);
            m_assignment.push_back(l_undef);
            m_binary.push_back(literal_vector());
            m_binary.push_back(literal_vector());
            m_watches.push_back(watch_list());
            m_watches.push_back(watch_list());
            m_bstamp.push_back(0);
            m_bstamp.push_back(0);
        }

        void init() {
            m_delta_trigger = s.num_vars()/10;
            m_config.m_dl_success = 0.8;
            m_inconsistent = false;
            m_qhead = 0;
            m_bstamp_id = 0;

            for (unsigned i = 0; i < s.num_vars(); ++i) {
                init_var(i);
            }

            // copy binary clauses
            unsigned sz = s.m_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l = ~to_literal(l_idx);
                watch_list const & wlist = s.m_watches[l_idx];
                watch_list::const_iterator it  = wlist.begin();
                watch_list::const_iterator end = wlist.end();
                for (; it != end; ++it) {
                    if (!it->is_binary_non_learned_clause())
                        continue;
                    literal l2 = it->get_literal();
                    if (l.index() < l2.index()) 
                        add_binary(l, l2);
                }
            }

            // copy clauses
            clause_vector::const_iterator it =  s.m_clauses.begin();
            clause_vector::const_iterator end = s.m_clauses.end();
            for (; it != end; ++it) {
                clause& c = *(*it);
                m_clauses.push_back(m_cls_allocator.mk_clause(c.size(), c.begin(), false));
                // TBD: add watch
            }

            // copy units
            unsigned trail_sz = s.init_trail_size();
            for (unsigned i = 0; i < trail_sz; ++i) {
                literal l = s.m_trail[i];
                m_units.push_back(l);
                assign(l);
            }
        }
        
        void push(literal lit) { 
            m_binary_trail_lim.push_back(m_binary_trail.size());
            m_units_lim.push_back(m_units.size());
            m_trail_lim.push_back(m_trail.size());
            m_qhead_lim.push_back(m_qhead);
            m_trail.push_back(lit);
            assign(lit);
            propagate();
        }

        void pop() { 
            // remove local binary clauses
            unsigned old_sz = m_binary_trail_lim.back();
            m_binary_trail_lim.pop_back();
            for (unsigned i = old_sz; i < m_binary_trail.size(); ++i) {
                del_binary(m_binary_trail[i]);
            }

            // add implied binary clauses
            unsigned new_unit_sz = m_units_lim.back();
            for (unsigned i = new_unit_sz; i < m_units.size(); ++i) {
                add_binary(~m_trail.back(), m_units[i]);
            }
            m_units.shrink(new_unit_sz);
            m_units_lim.pop_back();
            m_trail.shrink(m_trail_lim.size()); // reset assignment.
            m_trail_lim.pop_back();
            m_qhead_lim.pop_back();
            m_qhead = m_qhead_lim.back();

            m_inconsistent = false;
        }
        
        unsigned diff() const { return m_units.size() - m_units_lim.back(); }

        unsigned mix_diff(unsigned l, unsigned r) const { return l + r + (1 << 10) * l * r; }

        clause const& get_clause(watch_list::iterator it) const {
            clause_offset cls_off = it->get_clause_offset();
            return *(s.m_cls_allocator.get_clause(cls_off));
        }

        bool is_nary_propagation(clause const& c, literal l) const {
            bool r = c.size() > 2 && ((c[0] == l && value(c[1]) == l_false) || (c[1] == l && value(c[0]) == l_false));
            DEBUG_CODE(if (r) for (unsigned j = 2; j < c.size(); ++j) SASSERT(value(c[j]) == l_false););
            return r;
        }

        void propagate_clauses(literal l) {
            SASSERT(value(l) == l_true);
            SASSERT(value(~l) == l_false);
            if (inconsistent()) return;
            watch_list& wlist = m_watches[l.index()];
            watch_list::iterator it = wlist.begin(), it2 = it, end = wlist.end();
            for (; it != end && !inconsistent(); ++it) {
                switch (it->get_kind()) {
                case watched::BINARY:
                    UNREACHABLE();
                    break;
                case watched::TERNARY: {
                    literal l1 = it->get_literal1();
                    literal l2 = it->get_literal2();
                    lbool val1 = value(l1);
                    lbool val2 = value(l2);
                    if (val1 == l_false && val2 == l_undef) {
                        m_stats.m_propagations++;
                        assign(l2);
                    }
                    else if (val1 == l_undef && val2 == l_false) {
                        m_stats.m_propagations++;
                        assign(l1);
                    }
                    else if (val1 == l_false && val2 == l_false) {
                        set_conflict();
                    }
                    else if (val1 == l_undef && val2 == l_undef) {
                        // TBD: the clause has become binary.
                    }
                    *it2 = *it;
                    it2++;
                    break;
                }
                case watched::CLAUSE: {
                    clause_offset cls_off = it->get_clause_offset();
                    clause & c = *(s.m_cls_allocator.get_clause(cls_off));
                    TRACE("propagate_clause_bug", tout << "processing... " << c << "\nwas_removed: " << c.was_removed() << "\n";);
                    if (c[0] == ~l)
                        std::swap(c[0], c[1]);
                    if (value(c[0]) == l_true) {
                        it2->set_clause(c[0], cls_off);
                        it2++;
                        break;
                    }
                    literal * l_it  = c.begin() + 2;
                    literal * l_end = c.end();
                    unsigned found = 0;
                    for (; l_it != l_end && found < 2; ++l_it) {
                        if (value(*l_it) != l_false) {
                            ++found;
                            if (found == 2) {
                                break;
                            }
                            else {
                                c[1]  = *l_it;
                                *l_it = ~l;
                                m_watches[(~c[1]).index()].push_back(watched(c[0], cls_off));
                            }
                        }
                    }
                    if (found == 1) {
                        // TBD: clause has become binary
                        break; 
                    }
                    if (found > 1) {
                        // not a binary clause
                        break;
                    }
                    else if (value(c[0]) == l_false) {
                        set_conflict();
                    }
                    else {
                        SASSERT(value(c[0]) == l_undef);
                        *it2 = *it;
                        it2++;
                        m_stats.m_propagations++;
                        assign(c[0]);
                    }
                    break;
                }
                case watched::EXT_CONSTRAINT:
                    UNREACHABLE();
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
            for (; it != end; ++it, ++it2) {
                *it2 = *it;                         
            }
            wlist.set_end(it2);
        
            
            //
            // TBD: count binary clauses created by propagation.
            // They used to be in the watch list of l.index(), 
            // both new literals in watch list should be unassigned.
            //
        }

        void propagate_binary(literal l) {
            literal_vector const& lits = m_binary[l.index()];
            unsigned sz = lits.size();
            for (unsigned i = 0; !inconsistent() && i < sz; ++i) {
                assign(lits[i]);
            }
        }

        void propagate() {
            for (; m_qhead < m_trail.size(); ++m_qhead) {
                if (inconsistent()) break;
                literal l = m_trail[m_qhead];
                propagate_binary(l);
                propagate_clauses(l);
            }
            TRACE("sat", s.display(tout << scope_lvl() << " " << (inconsistent()?"unsat":"sat") << "\n"););
        }

        literal choose() {
            literal l;
            while (!choose1(l)) {};
            return l;
        }

        bool choose1(literal& l) {
            literal_vector P;
            pre_select(P);
            l = null_literal;
            if (P.empty()) {
                return true;
            }
            unsigned h = 0, count = 1;
            for (unsigned i = 0; i < P.size(); ++i) {
                literal lit = P[i];

                push(lit);
                if (do_double()) double_look(P);
                if (inconsistent()) {
                    pop();
                    assign(~lit);
                    if (do_double()) double_look(P);
                    if (inconsistent()) return true;
                    continue;
                }
                unsigned diff1 = diff();
                pop();
                
                push(~lit);
                if (do_double()) double_look(P);
                bool unsat2 = inconsistent();
                unsigned diff2 = diff();
                pop();

                if (unsat2) {
                    assign(lit);
                    continue;
                }

                unsigned mixd = mix_diff(diff1, diff2);


                if (mixd > h || (mixd == h && s.m_rand(count) == 0)) {
                    CTRACE("sat", l != null_literal, tout << lit << " diff1: " << diff1 << " diff2: " << diff2 << "\n";);
                    if (mixd > h) count = 1; else ++count;
                    h = mixd;
                    l = diff1 < diff2 ? lit : ~lit;
                }
            }
            return l != null_literal;
        }

        void double_look(literal_vector const& P) {
            bool unsat;
            for (unsigned i = 0; !inconsistent() && i < P.size(); ++i) {
                literal lit = P[i];
                if (value(lit) != l_undef) continue;

                push(lit);
                unsat = inconsistent();
                pop();
                if (unsat) {
                    TRACE("sat", tout << "unit: " << ~lit << "\n";);
                    assign(~lit);
                    continue;
                }

                push(~lit);
                unsat = inconsistent();
                pop();
                if (unsat) {
                    TRACE("sat", tout << "unit: " << lit << "\n";);
                    assign(lit);
                }
            }
            update_delta_trigger();
        }

        bool is_fixed(literal l) const { return value(l) != l_undef; }
        bool is_contrary(literal l) const { return value(l) == l_false; }
        void set_conflict() { m_inconsistent = true; }
        lbool value(literal l) const { return static_cast<lbool>(m_assignment[l.index()]); }
        unsigned scope_lvl() const { return m_trail_lim.size(); }

        void assign(literal l) {
            switch (value(l)) {
            case l_true: 
                break;
            case l_false: 
                set_conflict(); 
                break;
            default:
                m_assignment[l.index()] = l.sign() ? l_false : l_true;
                m_assignment[(~l).index()] = l.sign() ? l_false : l_true;
                m_trail.push_back(l);
                break;
            }
        }

        void set_inconsistent() { m_inconsistent = true; }
        bool inconsistent() { return m_inconsistent; }

        void pre_select(literal_vector& P) {
            select_variables(P);
            order_by_implication_trees(P);            
        }

        void order_by_implication_trees(literal_vector& P) {
            literal_set roots;
            literal_vector nodes, parent;

            //
            // Extract binary clauses in watch list. 
            // Produce implication graph between literals in P.
            //
            
            for (unsigned i = 0; i < P.size(); ++i) {
                literal lit1 = P[i], lit2;

                //
                // lit2 => lit1, where lit2 is a root.
                // make lit1 a root instead of lit2
                //

                literal_vector const& lits1 = m_binary[(~lit1).index()];
                unsigned sz = lits1.size();
                for (unsigned i = 0; i < sz; ++i) {
                    literal lit2 = lits1[i];
                    if (roots.contains(~lit2)) {
                        // ~lit2 => lit1
                        // if lit2 is a root, put it under lit2
                        parent.setx((~lit2).index(), lit1, null_literal);
                        roots.remove(~lit2);
                        roots.insert(lit1);
                        goto found;
                    }
                }

                //
                // lit1 => lit2.n
                // if lit2 is a node, put lit1 above lit2
                //

                literal_vector const& lits2 = m_binary[(~lit2).index()];
                sz = lits2.size();
                for (unsigned i = 0; i < sz; ++i) {
                    literal lit2 = lits2[i];
                    if (nodes.contains(lit2)) {
                        // lit1 => lit2
                        parent.setx(lit1.index(), lit2, null_literal);
                        nodes.insert(lit1);
                        goto found;
                    }
                }
                nodes.push_back(lit1);
                roots.insert(lit1);                
            found:
                ;
            }    
            TRACE("sat", 
                  tout << "implication trees\n";
                  for (unsigned i = 0; i < parent.size(); ++i) {
                      literal p = parent[i];
                      if (p != null_literal) {
                          tout << to_literal(i) << " |-> " << p << "\n";
                      }
                  });

            // TBD: extract ordering.
            
        }

        void select_variables(literal_vector& P) {
            for (unsigned i = 0; i < s.num_vars(); ++i) {
                if (value(literal(i,false)) == l_undef) {
                    P.push_back(literal(i, false));
                }
            }
        }

        bool do_double() {
            return !inconsistent() && diff() > m_delta_trigger;
        }

        void update_delta_trigger() {
            if (inconsistent()) {
                m_delta_trigger -= (1 - m_config.m_dl_success) / m_config.m_dl_success; 
            }
            else {
                m_delta_trigger += 1;
            }
            if (m_delta_trigger >= s.num_vars()) {
                // reset it.
            }
        }

        bool backtrack(literal_vector& trail) {
            if (trail.empty()) return false;      
            pop();                                  
            assign(~trail.back());                  
            trail.pop_back();               
            return true;
        }

        lbool search() {
            literal_vector trail;

            while (true) {
                s.checkpoint();
                literal l = choose();
                if (inconsistent()) {
                    if (!backtrack(trail)) return l_false;
                    continue;
                }
                if (l == null_literal) {
                    return l_true;
                }
                TRACE("sat", tout << "choose: " << l << " " << trail << "\n";);
                push(l);
                trail.push_back(l);
            }
        }

    public:
        lookahead(solver& s) : s(s) {
            init();
        }
        
        lbool check() {
            return search();
        }
              
    };
}

#endif

