/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_bcd.cpp

Abstract:

    Find candidate equivalent literals based on blocked clause decomposition.
    Based on LPAR-19 paper by Biere & Heule.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-27.


Revision History:

*/

#include "util/trace.h"
#include "util/bit_vector.h"
#include "util/map.h"
#include "sat/sat_bcd.h"
#include "sat/sat_solver.h"

namespace sat {
    
    bcd::bcd(solver & s): s(s) {}

    bcd::~bcd() {
        cleanup();
    }

    struct bcd::scoped_cleanup {
        bcd& f;
        scoped_cleanup(bcd& f):f(f) {}
        ~scoped_cleanup() { f.cleanup(); }        
    };

    struct bcd::report {
        bcd& f;
        report(bcd& f):f(f) {}
        ~report() {
            IF_VERBOSE(1, verbose_stream() << "Decomposed set " << f.m_L.size() << " rest: " << f.m_R.size() << "\n";);
            TRACE("sat",
                  tout << "Decomposed set " << f.m_L.size() << "\n";
                  for (bclause b : f.m_L) tout << b.lit << ": " << *b.cls << "\n";
                  tout << "Remainder " << f.m_R.size() << "\n";
                  for (bclause b : f.m_R) tout << b.lit << ": " << *b.cls << "\n";);            
        }
    };

    void bcd::operator()(union_find<>& uf) {
        scoped_cleanup _sc(*this);
        report _report(*this);
        pure_decompose();
        post_decompose();
        sat_sweep();
        extract_partition(uf);
    }    

    void bcd::operator()(clause_vector& clauses, svector<bin_clause>& bins) {
        scoped_cleanup _sc(*this);
        report _report(*this);
        pure_decompose();
        post_decompose();
        for (bclause bc : m_L) {
            if (bc.cls->size() == 2) 
                bins.push_back(bin_clause((*bc.cls)[0], (*bc.cls)[1]));
            else 
                clauses.push_back(bc.cls);                
        }
    }

    void bcd::init(use_list& ul) {
        for (clause* cls : s.clauses()) {
            if (!cls->was_removed()) {
                ul.insert(*cls);
                register_clause(cls);
            }
        }
        bin_clauses bc;
        s.collect_bin_clauses(bc, false, false); // exclude roots.
        for (auto b : bc) {
            literal lits[2] = { b.first, b.second };
            clause* cls = s.cls_allocator().mk_clause(2, lits, false);
            ul.insert(*cls);
            m_bin_clauses.push_back(cls);
            register_clause(cls);
        }
        TRACE("sat", for (clause* cls : m_clauses) if (cls) tout << *cls << "\n";);
    }

    void bcd::register_clause(clause* cls) {
        m_clauses.setx(cls->id(), cls, nullptr);
    }

    void bcd::unregister_clause(clause const& cls) {
        m_clauses.setx(cls.id(), 0, nullptr);
    }

    void bcd::pure_decompose() {
        use_list ul;
        ul.init(s.num_vars());
        init(ul);
        //
        // while F != empty
        //   pick a clause and variable x in clause.
        //   get use list U1 of x and U2 of ~x
        //   assume |U1| >= |U2|
        //   add U1 to clause set.
        //
        for (clause* cls : m_clauses) {
            if (cls) {
                pure_decompose(ul, (*cls)[s.rand()() % cls->size()]);
            }
        }
    }

    void bcd::pure_decompose(use_list& ul, literal lit) {
        svector<bclause> tmpL, tmpR;
        pure_decompose(ul,  lit, tmpL);
        pure_decompose(ul, ~lit, tmpR);
        if (tmpL.size() < tmpR.size()) {
            std::swap(tmpL, tmpR);
        }
        m_L.append(tmpL);
        m_R.append(tmpR);
        TRACE("bcd", tout << lit << " " << "pos: " << tmpL.size() << " " << "neg: " << tmpR.size() << "\n";);
    }
    
    void bcd::pure_decompose(use_list& ul, literal lit, svector<bclause>& clauses) {
        clause_use_list& uses = ul.get(lit); 
        auto it = uses.mk_iterator();
        for (; !it.at_end(); it.next()) {
            clause& cls = it.curr();
            if (m_clauses[cls.id()]) {
                clauses.push_back(bclause(lit, &cls));
                unregister_clause(cls);
            }
        }
    }

    void bcd::post_decompose() {
        m_marked.reset();
        m_marked.resize(2*s.num_vars(), false);
        use_list ul;
        ul.init(s.num_vars());
        for (bclause bc : m_L) {
            ul.insert(*bc.cls);
        }

        // cheap pass: add clauses from R in order
        // such that they are blocked with respect to
        // predecessors.
        reset_removed();
        unsigned j = 0;
        for (bclause const & bc : m_R) {
            literal lit = find_blocked(ul, *bc.cls);
            if (lit != null_literal) {
                m_L.push_back(bc);
                set_removed(*bc.cls);
                ul.insert(*bc.cls); 
            }
            else {
                m_R[j++] = bc;
            }
        }
        m_R.shrink(j);

#if 0
        // Super expensive pass: add clauses from R as long
        // as BCE produces the empty set of clauses.
        j = 0;
        for (bclause const& bc : m_R) {
            if (!bce(ul, *bc.cls)) {
                m_R[j++] = bc;
            }
        }        
        m_R.shrink(j);
#endif
    }

    // Note: replay blocked clause elimination:
    // Suppose C u { c1 } is blocked. 
    // annotate each clause by blocking literal.
    // for new clause c2, check if C u { c2 } is blocked.
    // For each c in C record which literal it is blocked.
    // (Order the clauses in C by block ordering)
    // l | c is blocked, 
    // => c2 contains ~l => check if c c2 is blocked
    //  
    bool bcd::bce(use_list& ul, clause& cls0) {
        IF_VERBOSE(1, verbose_stream() << "bce " << m_L.size() << " " << m_R.size() << " " << cls0 << "\n";);
        svector<bclause>&  live_clauses = m_live_clauses;
        live_clauses.reset();
        ul.insert(cls0);
        m_new_L.reset();
        m_new_L.push_back(bclause(cls0[0], &cls0));
        bool removed = false;
        reset_removed();
        for (bclause bc : m_L) {
            literal lit = find_blocked(ul, *bc.cls);
            if (lit == null_literal) {
                live_clauses.push_back(bc);
            }
            else {
                set_removed(*bc.cls);
                removed = true;
                m_new_L.push_back(bclause(lit, bc.cls));
            }
        }
        while (removed) {
            removed = false;
            unsigned j = 0;
            for (bclause bc : live_clauses) {
                literal lit = find_blocked(ul, *bc.cls);
                if (lit == null_literal) {
                    live_clauses[j++] = bc;
                }
                else {
                    set_removed(*bc.cls);
                    removed = true;
                    m_new_L.push_back(bclause(lit, bc.cls));
                }
            }
            live_clauses.shrink(j);
        }
        if (live_clauses.empty()) {
            m_L.reset();
            m_L.append(m_new_L);
        }
        else {
            ul.erase(cls0);
        }
        return live_clauses.empty();
    }

    literal bcd::find_blocked(use_list& ul, clause const& cls) {
        TRACE("bcd", tout << cls << "\n";);

        for (literal lit : cls) {            
            m_marked[(~lit).index()] = true;
        }
        literal result = null_literal;
        for (literal lit : cls) {
            if (is_blocked(ul, lit)) {
                TRACE("bcd", tout << "is blocked " << lit << " : " << cls << "\n";);
                result = lit;
                break;
            }
        }
        for (literal lit : cls) {
            m_marked[(~lit).index()] = false;
        }
        return result;
    }

    bool bcd::is_blocked(use_list& ul, literal lit) const {
        auto has_blocked_lit = [&,this](clause const& c) { 
            for (literal lit2 : c) 
                if (m_marked[lit2.index()] && ~lit != lit2) {
                    return true; 
                }
            return false; 
        };
        auto it = ul.get(~lit).mk_iterator();
        for (; !it.at_end(); it.next()) {
            clause & cls = it.curr();
            if (!is_removed(cls) && !has_blocked_lit(cls))
                return false;
        }
        return true;
    }

    void bcd::init_rbits() {
        m_rbits.reset();        
        for (unsigned i = 0; i < s.num_vars(); ++i) {
            uint64_t lo = s.rand()() + (s.rand()() << 16ull);
            uint64_t hi = s.rand()() + (s.rand()() << 16ull);
            m_rbits.push_back(lo + (hi << 32ull));
        }
    }
    
    uint64_t bcd::eval_clause(clause const& cls) const {
        uint64_t b = 0ull;
        for (literal lit : cls) {
            b |= lit.sign() ? ~m_rbits[lit.var()] : m_rbits[lit.var()];
        }
        return b;
    }

    void bcd::sat_sweep() {
        init_rbits();
        m_L.reverse();
        for (bclause& bc : m_L) {
            uint64_t b = eval_clause(*bc.cls);
            // v = 0, b = 0 => v := 1
            // v = 0, b = 1 => v := 0
            // v = 1, b = 0 => v := 0
            // v = 1, b = 1 => v := 1
            m_rbits[bc.lit.var()] ^= ~b;
            if (0 != ~b) IF_VERBOSE(0, verbose_stream() << "fix " << bc.lit << " " << *bc.cls << "\n");
            VERIFY(0 == ~eval_clause(*bc.cls));
        }
        DEBUG_CODE(verify_sweep(););
    }

    void bcd::verify_sweep() {
        for (bclause const& bc : m_L) {
            VERIFY(0 == ~eval_clause(*bc.cls));
        }
    }
    
    void bcd::extract_partition(union_find<>& uf) {
        u64_map<unsigned> table;
        for (unsigned i = 2 * s.num_vars(); i-- > 0; ) {
            uf.mk_var();
        }
        unsigned num_merge = 0;
        for (unsigned i = 0; i < s.num_vars(); ++i) {
            uint64_t val = m_rbits[i];
            literal lit(i, false);
            unsigned index = UINT_MAX;
            if (s.was_eliminated(lit) || s.value(lit) != l_undef) {
                // skip
            }
            else if (table.find(val, index)) {
                IF_VERBOSE(0, verbose_stream() << "merge " << val << " " << lit << " " << to_literal(index) << "\n");
                uf.merge(lit.index(), index);
                ++num_merge;
            }
            else if (table.find(~val, index)) {
                IF_VERBOSE(0, verbose_stream() << "merge " << val << " " << (~lit) << " " << to_literal(index) << "\n");
                uf.merge((~lit).index(), index);
                ++num_merge;
            }
            else {
                table.insert(val, lit.index());
            }
        }
        IF_VERBOSE(0, verbose_stream() << "num merge: " << num_merge << "\n");
        TRACE("sat", uf.display(tout););
    }

    void bcd::cleanup() {
        s.del_clauses(m_bin_clauses);
        m_bin_clauses.reset();
        m_clauses.reset();
        m_L.reset();
        m_R.reset();
    }

};
