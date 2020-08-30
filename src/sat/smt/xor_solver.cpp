/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    xor_solver.cpp

Abstract:

    Extension for xr reasoning.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/

#include "sat/sat_types.h"
#include "sat/smt/ba_solver.h"
#include "sat/sat_simplifier_params.hpp"
#include "sat/sat_xor_finder.h"

namespace sat {
    ba_solver::xr& ba_solver::constraint::to_xr() {
        SASSERT(is_xr());
        return static_cast<xr&>(*this);
    }

    ba_solver::xr const& ba_solver::constraint::to_xr() const{
        SASSERT(is_xr());
        return static_cast<xr const&>(*this);
    }

    ba_solver::xr::xr(unsigned id, literal_vector const& lits):
        constraint(xr_t, id, null_literal, lits.size(), get_obj_size(lits.size())) {
        for (unsigned i = 0; i < size(); ++i) {
            m_lits[i] = lits[i];
        }
    }

    bool ba_solver::xr::is_watching(literal l) const {
        return 
            l == (*this)[0] || l == (*this)[1] ||
            ~l == (*this)[0] || ~l == (*this)[1];            
    }

    bool ba_solver::xr::well_formed() const {
        uint_set vars;        
        if (lit() != null_literal) vars.insert(lit().var());
        for (literal l : *this) {
            bool_var v = l.var();
            if (vars.contains(v)) return false;
            vars.insert(v);            
        }
        return true;
    }

    // --------------------
    // xr:

    void ba_solver::clear_watch(xr& x) {
        x.clear_watch();
        unwatch_literal(x[0], x);
        unwatch_literal(x[1], x);         
        unwatch_literal(~x[0], x);
        unwatch_literal(~x[1], x);         
    }

    bool ba_solver::parity(xr const& x, unsigned offset) const {
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

    bool ba_solver::init_watch(xr& x) {
        clear_watch(x);
        VERIFY(x.lit() == null_literal);
        TRACE("ba", display(tout, x, true););
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
            return false;
        case 1: 
            SASSERT(x.lit() == null_literal || value(x.lit()) == l_true);
            assign(x, parity(x, 1) ? ~x[0] : x[0]);
            return false;
        default: 
            SASSERT(j == 2);
            watch_literal(x[0], x);
            watch_literal(x[1], x);
            watch_literal(~x[0], x);
            watch_literal(~x[1], x);
            return true;
        }
    }


    lbool ba_solver::add_assign(xr& x, literal alit) {
        // literal is assigned     
        unsigned sz = x.size();
        TRACE("ba", tout << "assign: "  << ~alit << "@" << lvl(~alit) << " " << x << "\n"; display(tout, x, true); );

        VERIFY(x.lit() == null_literal);
        SASSERT(value(alit) != l_undef);
        unsigned index = (x[1].var() == alit.var()) ? 1 : 0;
        VERIFY(x[index].var() == alit.var());
        
        // find a literal to swap with:
        for (unsigned i = 2; i < sz; ++i) {
            literal lit = x[i];
            if (value(lit) == l_undef) {
                x.swap(index, i);
                unwatch_literal(~alit, x);
                // alit gets unwatched by propagate_core because we return l_undef
                watch_literal(lit, x);
                watch_literal(~lit, x);
                TRACE("ba", tout << "swap in: " << lit << " " << x << "\n";);
                return l_undef;
            }
        }
        if (index == 0) {
            x.swap(0, 1);
        }
        // alit resides at index 1.
        VERIFY(x[1].var() == alit.var());        
        if (value(x[0]) == l_undef) {
            bool p = parity(x, 1);
            assign(x, p ? ~x[0] : x[0]);            
        }
        else if (!parity(x, 0)) {
            set_conflict(x, ~x[1]);
        }      
        return inconsistent() ? l_false : l_true;  
    }

    void ba_solver::add_xr(literal_vector const& lits) {
        add_xr(lits, false);
    }

    bool ba_solver::all_distinct(literal_vector const& lits) {
        return s().all_distinct(lits);
    }

    bool ba_solver::all_distinct(clause const& c) {
        return s().all_distinct(c);
    }

    bool ba_solver::all_distinct(xr const& x) {
        init_visited();
        for (literal l : x) {
            if (is_visited(l.var())) {
                return false;
            }
            mark_visited(l.var());
        }
        return true;
    }

    literal ba_solver::add_xor_def(literal_vector& lits, bool learned) {
        unsigned sz = lits.size();
        SASSERT (sz > 1);
        VERIFY(all_distinct(lits));
        init_visited();
        bool parity1 = true;
        for (literal l : lits) {            
            mark_visited(l.var());
            parity1 ^= l.sign();
        }
        for (auto const & w : get_wlist(lits[0])) {
            if (w.get_kind() != watched::EXT_CONSTRAINT) continue;
            constraint& c = index2constraint(w.get_ext_constraint_idx());
            if (!c.is_xr()) continue;
            xr& x = c.to_xr();
            if (sz + 1 != x.size()) continue;
            bool is_match = true;
            literal l0 = null_literal;
            bool parity2 = true;
            for (literal l : x) {
                if (!is_visited(l.var())) {
                    if (l0 == null_literal) {
                        l0 = l;
                    }
                    else {
                        is_match = false;
                        break;
                    }
                }
                else {
                    parity2 ^= l.sign();
                }
            }
            if (is_match) {
                SASSERT(all_distinct(x));
                if (parity1 == parity2) l0.neg();
                if (!learned && x.learned()) {
                    set_non_learned(x);
                }
                return l0;
            }
        }
        bool_var v = s().mk_var(true, true);
        literal lit(v, false);
        lits.push_back(~lit);
        add_xr(lits, learned);
        return lit;
    }


    ba_solver::constraint* ba_solver::add_xr(literal_vector const& _lits, bool learned) {
        literal_vector lits;
        u_map<bool> var2sign;
        bool sign = false, odd = false;
        for (literal lit : _lits) {
            if (var2sign.find(lit.var(), sign)) {
                var2sign.erase(lit.var());
                odd ^= (sign ^ lit.sign());
            }
            else {
                var2sign.insert(lit.var(), lit.sign());
            }
        }       
        
        for (auto const& kv : var2sign) {
            lits.push_back(literal(kv.m_key, kv.m_value));
        }
        if (odd && !lits.empty()) {
            lits[0].neg();
        }
        switch (lits.size()) {
        case 0:
            if (!odd)
                s().set_conflict(justification(0));
            return nullptr;
        case 1:            
            s().assign_scoped(lits[0]);
            return nullptr;
        default:
            break;
        }
        void * mem = m_allocator.allocate(xr::get_obj_size(lits.size()));
        constraint_base::initialize(mem, this);
        xr* x = new (constraint_base::ptr2mem(mem)) xr(next_id(), lits);
        x->set_learned(learned);
        add_constraint(x);
        return x;
    }

    /**
       \brief perform parity resolution on xr premises.
       The idea is to collect premises based on xr resolvents. 
       Variables that are repeated an even number of times cancel out.
     */

    void ba_solver::get_xr_antecedents(literal l, unsigned index, justification js, literal_vector& r) {
        unsigned level = lvl(l);
        bool_var v = l.var();
        SASSERT(js.get_kind() == justification::EXT_JUSTIFICATION);
        TRACE("ba", tout << l << ": " << js << "\n"; 
              for (unsigned i = 0; i <= index; ++i) tout << s().m_trail[i] << " "; tout << "\n";
              s().display_units(tout);
              );


        unsigned num_marks = 0;
        while (true) {
            TRACE("ba", tout << "process: " << l << " " << js << "\n";);
            if (js.get_kind() == justification::EXT_JUSTIFICATION) {
                constraint& c = index2constraint(js.get_ext_justification_idx());
                TRACE("ba", tout << c << "\n";);
                if (!c.is_xr()) {
                    r.push_back(l);
                }
                else {
                    xr& x = c.to_xr();                    
                    if (x[1].var() == l.var()) {
                        x.swap(0, 1);
                    }
                    VERIFY(x[0].var() == l.var());
                    for (unsigned i = 1; i < x.size(); ++i) {
                        literal lit(value(x[i]) == l_true ? x[i] : ~x[i]);
                        inc_parity(lit.var());
                        if (lvl(lit) == level) {
                            TRACE("ba", tout << "mark: " << lit << "\n";);
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
            bool found = false;
            while (num_marks > 0) {
                l = s().m_trail[index];
                v = l.var();
                unsigned n = get_parity(v);
                if (n > 0 && lvl(l) == level) {
                    reset_parity(v);
                    num_marks -= n;
                    if (n % 2 == 1) {
                        found = true;
                        break;
                    }
                }
                --index;
            }
            if (!found) {
                break;
            }
            --index;
            js = s().m_justification[v];
        }

        // now walk the defined literals 

        for (literal lit : m_parity_trail) {
            if (get_parity(lit.var()) % 2 == 1) {
                r.push_back(lit);
            }
            else {
                // IF_VERBOSE(2, verbose_stream() << "skip even parity: " << lit << "\n";);
            }
            reset_parity(lit.var());
        }
        m_parity_trail.reset();
        TRACE("ba", tout << r << "\n";);
    }

    void ba_solver::pre_simplify() {
        VERIFY(s().at_base_lvl());
        if (s().inconsistent())
            return;
        m_constraint_removed = false;
        xor_finder xf(s());
        for (unsigned sz = m_constraints.size(), i = 0; i < sz; ++i) pre_simplify(xf, *m_constraints[i]);
        for (unsigned sz = m_learned.size(), i = 0; i < sz; ++i) pre_simplify(xf, *m_learned[i]);   
        bool change = m_constraint_removed;
        cleanup_constraints();
        if (change) {
            // remove non-used variables.
            init_use_lists();
            remove_unused_defs();
            set_non_external();
        }
    }


    void ba_solver::simplify(xr& x) {
        if (x.learned()) {
            x.set_removed();
            m_constraint_removed = true;            
        }
    }

    void ba_solver::get_antecedents(literal l, xr const& x, literal_vector& r) {
        if (x.lit() != null_literal) r.push_back(x.lit());
        // TRACE("ba", display(tout << l << " ", x, true););
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

    lbool ba_solver::eval(xr const& x) const {
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

    lbool ba_solver::eval(model const& m, xr const& x) const {
        bool odd = false;
        
        for (auto l : x) {
            switch (value(m, l)) {
            case l_true: odd = !odd; break;
            case l_false: break;
            default: return l_undef;
            }
        }
        return odd ? l_true : l_false;
    }

    void ba_solver::pre_simplify(xor_finder& xf, constraint& c) {
        if (c.is_xr() && c.size() <= xf.max_xor_size()) {
            unsigned sz = c.size();
            literal_vector lits;
            bool parity = false;
            xr const& x = c.to_xr();
            for (literal lit : x) {
                parity ^= lit.sign();
            }

            // IF_VERBOSE(0, verbose_stream() << "blast: " << c << "\n");
            for (unsigned i = 0; i < (1ul << sz); ++i) {
                if (xf.parity(sz, i) == parity) {
                    lits.reset();
                    for (unsigned j = 0; j < sz; ++j) {
                        lits.push_back(literal(x[j].var(), (0 != (i & (1 << j)))));
                    }
                    // IF_VERBOSE(0, verbose_stream() << lits << "\n");
                    s().mk_clause(lits);
                }
            }
            c.set_removed();
            m_constraint_removed = true;
        }
    }

    bool ba_solver::clausify(xr& x) {
        return false;
    }

    // merge xors that contain cut variable
    void ba_solver::merge_xor() {
        unsigned sz = s().num_vars();
        for (unsigned i = 0; i < sz; ++i) {
            literal lit(i, false);
            unsigned index = lit.index();
            if (m_cnstr_use_list[index].size() == 2) {
                constraint& c1 = *m_cnstr_use_list[index][0];
                constraint& c2 = *m_cnstr_use_list[index][1];
                if (c1.is_xr() && c2.is_xr() && 
                    m_clause_use_list.get(lit).empty() && 
                    m_clause_use_list.get(~lit).empty()) {
                    bool unique = true;
                    for (watched w : get_wlist(lit)) {
                        if (w.is_binary_clause()) unique = false;                        
                    }
                    for (watched w : get_wlist(~lit)) {
                        if (w.is_binary_clause()) unique = false;                        
                    }
                    if (!unique) continue;
                    xr const& x1 = c1.to_xr();
                    xr const& x2 = c2.to_xr();
                    literal_vector lits, dups;
                    bool parity = false;
                    init_visited();
                    for (literal l : x1) {
                        mark_visited(l.var());
                        lits.push_back(l);
                    }
                    for (literal l : x2) {
                        if (is_visited(l.var())) {
                            dups.push_back(l);
                        }
                        else {
                            lits.push_back(l);
                        }
                    }
                    init_visited();
                    for (literal l : dups) mark_visited(l);
                    unsigned j = 0;
                    for (unsigned i = 0; i < lits.size(); ++i) {
                        literal l = lits[i];
                        if (is_visited(l)) {
                            // skip
                        }
                        else if (is_visited(~l)) {
                            parity ^= true;
                        }
                        else {
                            lits[j++] = l;
                        }
                    }
                    lits.shrink(j);
                    if (!parity) lits[0].neg();
                    IF_VERBOSE(1, verbose_stream() << "binary " << lits << " : " << c1 << " " << c2 << "\n");
                    c1.set_removed();
                    c2.set_removed();
                    add_xr(lits, !c1.learned() && !c2.learned());
                    m_constraint_removed = true;
                }
            }
        }
    }

    void ba_solver::extract_xor() {
        xor_finder xf(s());
        std::function<void (literal_vector const&)> f = [this](literal_vector const& l) { add_xr(l, false); };
        xf.set(f);
        clause_vector clauses(s().clauses());
        xf(clauses);
        for (clause* cp : xf.removed_clauses()) {
            cp->set_removed(true);
            m_clause_removed = true;
        }
    }

    void ba_solver::display(std::ostream& out, xr const& x, bool values) const {
        out << "xr: ";
        for (literal l : x) {
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

    bool ba_solver::validate_unit_propagation(xr const& x, literal alit) const {
        if (value(x.lit()) != l_true) return false;
        for (unsigned i = 1; i < x.size(); ++i) {
            if (value(x[i]) == l_undef) return false;
        }
        return true;
    }

}
