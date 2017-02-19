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

        config          m_config;
        double          m_delta_trigger; 
        literal_vector  m_trail;
        literal_vector  m_units;
        unsigned_vector m_units_lim;
        unsigned_vector m_learned_lim;
        unsigned_vector m_binary;


        void init() {
            m_delta_trigger = s.num_vars()/10;
            m_config.m_dl_success = 0.8;
        }
        
        void push(literal lit) { 
            m_learned_lim.push_back(s.m_learned.size());
            m_units_lim.push_back(m_units.size());
            m_trail.push_back(lit);
            m_binary.push_back(0);
            s.push();
            assign(lit);
        }

        void pop() { 
            s.pop(1); 
            unsigned old_sz = m_learned_lim.back();
            m_learned_lim.pop_back();
            for (unsigned i = old_sz; i < s.m_learned.size(); ++i) {
                clause* r = s.m_learned[i];
                s.dettach_clause(*r);
                s.m_cls_allocator.del_clause(r);
            }
            s.m_learned.shrink(old_sz);
            unsigned new_unit_sz = m_units_lim.back();
            for (unsigned i = new_unit_sz; i < m_units.size(); ++i) {
                literal lits[2] = { ~m_trail.back(), m_units[i] };
                clause * r = s.m_cls_allocator.mk_clause(2, lits, true);
                s.m_learned.push_back(r);
            }
            m_units.shrink(new_unit_sz);
            m_units_lim.pop_back();
            m_trail.pop_back();
            m_binary.pop_back();
        }
        
        unsigned diff() const { return m_binary.back() + m_units.size() - m_units_lim.back(); }

        unsigned mix_diff(unsigned l, unsigned r) const { return l + r + (1 << 10) * l * r; }

        clause const& get_clause(watch_list::iterator it) const {
            clause_offset cls_off = it->get_clause_offset();
            return *(s.m_cls_allocator.get_clause(cls_off));
        }

        bool is_nary_propagation(clause const& c, literal l) const {
            bool r = c.size() > 2 && ((c[0] == l && s.value(c[1]) == l_false) || (c[1] == l && s.value(c[0]) == l_false));
            DEBUG_CODE(if (r) for (unsigned j = 2; j < c.size(); ++j) SASSERT(s.value(c[j]) == l_false););
            return r;
        }

        void get_resolvent_units(literal lit) {
            if (inconsistent()) return;
            for (unsigned i = s.m_trail.size(); i > 0; ) {
                --i;
                literal l = s.m_trail[i];
                if (l == lit) break;
                SASSERT(s.lvl(l) == s.scope_lvl());
                watch_list& wlist = s.m_watches[(~l).index()];
                watch_list::iterator it = wlist.begin(), end = wlist.end();
                for (; it != end; ++it) {
                    switch (it->get_kind()) {
                    case watched::TERNARY:
                        if (s.value(it->get_literal1()) == l_false && 
                            s.value(it->get_literal2()) == l_false) {
                            m_units.push_back(l);
                            goto done_finding_unit;
                        }
                        break;
                    case watched::CLAUSE: {
                        clause const & c = get_clause(it);
                        SASSERT(c[0] == l || c[1] == l);
                        if (is_nary_propagation(c, l)) {
                            m_units.push_back(l);
                            goto done_finding_unit;
                        }
                        break;
                    }
                    default:
                        break;
                    }
                }
            done_finding_unit:

                //
                // TBD: count binary clauses created by propagation.
                // They used to be in the watch list of l.index(), 
                // both new literals in watch list should be unassigned.
                //
                continue;

            }
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
                if (s.value(lit) != l_undef) continue;

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

        void assign(literal l) {
            s.assign(l, justification());
            s.propagate(false);
            get_resolvent_units(l);
            TRACE("sat", s.display(tout << l << " @ " << s.scope_lvl() << " " << (inconsistent()?"unsat":"sat") << "\n"););
        }

        bool inconsistent() { return s.inconsistent(); }

        void pre_select(literal_vector& P) {
            select_variables(P);
            order_by_implication_trees(P);            
        }

        void check_binary(clause const& c, literal lit1, literal& lit2) {
            if (c.size() == 2) {
                if (c[0] == lit1) {
                    lit2 = c[1];
                }
                else {
                    SASSERT(c[1] == lit1);
                    lit2 = c[0];
                }
            }
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

                watch_list& wlist = s.m_watches[(~lit1).index()];
                watch_list::iterator it = wlist.begin(), end = wlist.end();
                lit2 = null_literal;
                for (; it != end; ++it) {
                    switch (it->get_kind()) {
                    case watched::BINARY:
                        lit2 = it->get_literal();
                        break;
                    case watched::CLAUSE: {
                        clause const & c = get_clause(it);
                        check_binary(c, lit1, lit2);
                        break;
                    }
                    default:
                        break;
                    }
                    
                    if (lit2 != null_literal && roots.contains(~lit2)) {
                        // ~lit2 => lit1
                        // if lit2 is a root, put it under lit2
                        parent.setx((~lit2).index(), lit1, null_literal);
                        roots.remove(~lit2);
                        roots.insert(lit1);
                        goto found;
                    }
                }

                //
                // lit1 => lit2.
                // if lit2 is a node, put lit1 above lit2
                //

                it  = s.m_watches[lit1.index()].begin();
                end = s.m_watches[lit1.index()].end();
                for (; it != end; ++it) {
                    lit2 = null_literal;
                    switch (it->get_kind()) {
                    case watched::BINARY:
                        lit2 = it->get_literal();
                        break;
                    case watched::CLAUSE: {
                        clause const & c = get_clause(it);
                        check_binary(c, ~lit1, lit2);
                        break;
                    }
                    default:
                        break;
                    }
                    
                    if (lit2 != null_literal && nodes.contains(lit2)) {
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
                if (s.value(i) == l_undef) {
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

        lbool search() {
            literal_vector trail;

#define BACKTRACK                                       \
            if (inconsistent()) {                       \
                if (trail.empty()) return l_false;      \
                pop();                                  \
                assign(~trail.back());                  \
                trail.pop_back();                       \
                continue;                               \
            }                                           \

            while (true) {
                s.checkpoint();
                BACKTRACK;
                literal l = choose();
                BACKTRACK;
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

