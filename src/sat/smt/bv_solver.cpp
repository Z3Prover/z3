/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_solver.cpp

Abstract:

    Solving utilities for bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-02
    based on smt/theory_bv

--*/

#include "ast/ast_ll_pp.h"
#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "tactic/tactic_exception.h"

namespace bv {

    class solver::bit_trail : public trail {
        solver& s;
        solver::var_pos vp;
        sat::literal lit;
    public:
        bit_trail(solver& s, var_pos vp) : s(s), vp(vp), lit(s.m_bits[vp.first][vp.second]) {}

        void undo() override {
            s.m_bits[vp.first][vp.second] = lit;
        }
    };

    class solver::bit_occs_trail : public trail {
        atom& a;
        var_pos_occ* m_occs;

    public:
        bit_occs_trail(solver& s, atom& a): a(a), m_occs(a.m_occs) {}
        
        void undo() override {
            a.m_occs = m_occs;
        }
    };

    solver::solver(euf::solver& ctx, theory_id id) :
        euf::th_euf_solver(ctx, symbol("bv"), id),
        bv(m),
        m_autil(m),
        m_ackerman(*this),
        m_bb(m, get_config()),
        m_find(*this) {
        m_bb.set_flat(false);
    }

    void solver::fixed_var_eh(theory_var v1) {
        numeral val1, val2;
        VERIFY(get_fixed_value(v1, val1));
        euf::enode* n1 = var2enode(v1);
        unsigned sz = m_bits[v1].size();
        value_sort_pair key(val1, sz);
        theory_var v2;
        if (ctx.watches_fixed(n1)) {
            expr_ref value(bv.mk_numeral(val1, sz), m);
            ctx.assign_fixed(n1, value, m_bits[v1]);
        }
        bool is_current =
            m_fixed_var_table.find(key, v2) &&
            v2 < static_cast<int>(get_num_vars()) &&
            is_bv(v2) &&
            m_bits[v2].size() == sz &&
            get_fixed_value(v2, val2) && val1 == val2;
        if (!is_current)
            m_fixed_var_table.insert(key, v1);
        else if (n1->get_root() != var2enode(v2)->get_root()) {
            SASSERT(get_bv_size(v1) == get_bv_size(v2));
            TRACE("bv", tout << "detected equality: v" << v1 << " = v" << v2 << "\n" << pp(v1) << pp(v2););
            m_stats.m_num_bit2eq++;
            add_fixed_eq(v1, v2);
            ctx.propagate(n1, var2enode(v2), mk_bit2eq_justification(v1, v2));
        }
    }

    void solver::add_fixed_eq(theory_var v1, theory_var v2) {
        if (!get_config().m_bv_eq_axioms)
            return;
        m_ackerman.used_eq_eh(v1, v2);
    }

    bool solver::get_fixed_value(theory_var v, numeral& result) const {
        result.reset();
        unsigned i = 0;
        for (literal b : m_bits[v]) {
            if (b == ~m_true) 
                ;
            else if (b == m_true) 
                result += power2(i);
            else {
                switch (ctx.s().value(b)) {
                case l_false:
                    break;
                case l_undef:
                    return false;
                case l_true:
                    result += power2(i);
                    break;
                }
            }
            ++i;
        }
        return true;
    }

    /**
       \brief Find an unassigned bit for m_wpos[v], if such bit cannot be found invoke fixed_var_eh
    */
    void solver::find_wpos(theory_var v) {
        literal_vector const& bits = m_bits[v];
        unsigned sz = bits.size();
        unsigned& wpos = m_wpos[v];
        for (unsigned i = 0; i < sz; ++i) {
            unsigned idx = (i + wpos) % sz;
            if (s().value(bits[idx]) == l_undef) {
                wpos = idx;
                TRACE("bv", tout << "moved wpos of v" << v << " to " << wpos << "\n";);
                return;
            }
        }
        TRACE("bv", tout << "v" << v << " is a fixed variable.\n";);
        fixed_var_eh(v);
    }

    /**
     *\brief v[idx] = ~v'[idx], then v /= v' is a theory axiom.
    */
    void solver::find_new_diseq_axioms(atom& a, theory_var v, unsigned idx) {
        if (!get_config().m_bv_eq_axioms)
            return;
        literal l = m_bits[v][idx];
        l.neg();
        for (auto vp : a) {
            theory_var v2 = vp.first;
            unsigned   idx2 = vp.second;
            if (idx == idx2 && m_bits[v2].size() == m_bits[v].size() && m_bits[v2][idx2] == l )
                mk_new_diseq_axiom(v, v2, idx);
        }
    }

    /**
       \brief v1[idx] = ~v2[idx], then v1 /= v2 is a theory axiom.
    */
    void solver::mk_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx) {
        SASSERT(m_bits[v1][idx] == ~m_bits[v2][idx]);
        TRACE("bv", tout << "found new diseq axiom\n" << pp(v1) << pp(v2););
        m_stats.m_num_diseq_static++;
        expr_ref eq = mk_var_eq(v1, v2);
        add_unit(~ctx.internalize(eq, false, false, m_is_redundant));
    }

    std::ostream& solver::display(std::ostream& out, theory_var v) const {
        expr* e = var2expr(v);
        out << "v";
        out.width(4);
        out << std::left << v;
        out << " ";
        out.width(4);
        out << e->get_id() << " -> ";
        out.width(4);
        out << var2enode(find(v))->get_expr_id();
        out << std::right;
        out.flush();
        atom* a = nullptr;
        if (is_bv(v)) {
            numeral val;
            if (get_fixed_value(v, val))
                out << " (= " << val << ")";
            for (literal lit : m_bits[v]) {
                out << " " << lit << ":" << mk_bounded_pp(literal2expr(lit), m, 1);
            }
        }
        else if (m.is_bool(e) && (a = m_bool_var2atom.get(expr2literal(e).var(), nullptr))) {
            for (var_pos vp : *a)
                out << " " << var2enode(vp.first)->get_expr_id() << "[" << vp.second << "]";
        }
        else
            out << " " << mk_bounded_pp(e, m, 1);
        out << "\n";
        return out;
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        force_push();
        TRACE("bv", tout << "new eq " << mk_bounded_pp(var2expr(eq.v1()), m) << " == " << mk_bounded_pp(var2expr(eq.v2()), m) << "\n";);
        if (is_bv(eq.v1())) {
            m_find.merge(eq.v1(), eq.v2());
            VERIFY(eq.is_eq());
        }
    }

    void solver::new_diseq_eh(euf::th_eq const& ne) {
        theory_var v1 = ne.v1(), v2 = ne.v2();
        if (!is_bv(v1))
            return;
        if (s().is_probing())
            return;
        
        TRACE("bv", tout << "diff: " << v1 << " != " << v2 << " @" << s().scope_lvl() << "\n";);
        unsigned sz = m_bits[v1].size();
        if (sz == 1)
            return;
        unsigned num_undef = 0;
        int undef_idx = 0;
        for (unsigned i = 0; i < sz; ++i) {
            sat::literal a = m_bits[v1][i];
            sat::literal b = m_bits[v2][i];
            if (a == ~b)                
                return;
            auto va = s().value(a);
            auto vb = s().value(b);
            if (va != l_undef && vb != l_undef && va != vb)
                return;
            if (va == l_undef) {
                ++num_undef;
                undef_idx = i + 1;
            }
            if (vb == l_undef) {
                ++num_undef;
                undef_idx = -static_cast<int>(i + 1);
            }
            if (num_undef > 1 && get_config().m_bv_eq_axioms)
                return;
        }
        if (num_undef == 0)
            return;
        else if (num_undef == 1) {
            if (undef_idx < 0) {
                undef_idx = -undef_idx;
                std::swap(v1, v2);
            }
            undef_idx--;
            sat::literal consequent = m_bits[v1][undef_idx];
            sat::literal b = m_bits[v2][undef_idx];
            sat::literal antecedent = ~expr2literal(ne.eq());
            SASSERT(s().value(antecedent) == l_true);
            SASSERT(s().value(consequent) == l_undef);
            SASSERT(s().value(b) != l_undef);
            if (s().value(b) == l_true)
                consequent.neg();
            ++m_stats.m_num_ne2bit;
            s().assign(consequent, mk_ne2bit_justification(undef_idx, v1, v2, consequent, antecedent));
        }
        else if (s().at_search_lvl()) {
            force_push();
            assert_ackerman(v1, v2);
        }
        else 
            m_ackerman.used_diseq_eh(v1, v2);        
    }

    double solver::get_reward(literal l, sat::ext_constraint_idx idx, sat::literal_occs_fun& occs) const { return 0; }
    bool solver::is_extended_binary(sat::ext_justification_idx idx, literal_vector& r) { return false; }
    bool solver::is_external(bool_var v) { return true; }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& c = bv_justification::from_index(idx);
        TRACE("bv", display_constraint(tout, idx) << "\n";);
        switch (c.m_kind) {
        case bv_justification::kind_t::eq2bit:
            SASSERT(s().value(c.m_antecedent) == l_true);
            r.push_back(c.m_antecedent);
            ctx.add_antecedent(var2enode(c.m_v1), var2enode(c.m_v2));
            break;
        case bv_justification::kind_t::ne2bit: {
            r.push_back(c.m_antecedent);
            SASSERT(s().value(c.m_antecedent) == l_true);
            SASSERT(c.m_consequent == l);
            unsigned idx = c.m_idx;
            for (unsigned i = m_bits[c.m_v1].size(); i-- > 0; ) {
                sat::literal a = m_bits[c.m_v1][i];
                sat::literal b = m_bits[c.m_v2][i];
                SASSERT(a == b || s().value(a) != l_undef);
                SASSERT(i == idx || s().value(a) == s().value(b));
                if (a == b)
                    continue;
                if (i == idx) {
                    if (s().value(b) == l_false)
                        b.neg();
                    r.push_back(b);
                    
                    continue;
                }
                if (s().value(a) == l_false) {
                    a.neg();
                    b.neg();
                }
                r.push_back(a);
                r.push_back(b);
            }
            
            break;
        }
        case bv_justification::kind_t::bit2eq:
            SASSERT(m_bits[c.m_v1].size() == m_bits[c.m_v2].size());
            for (unsigned i = m_bits[c.m_v1].size(); i-- > 0; ) {
                sat::literal a = m_bits[c.m_v1][i];
                sat::literal b = m_bits[c.m_v2][i];
                SASSERT(a == b || s().value(a) != l_undef);
                SASSERT(s().value(a) == s().value(b));
                if (a == b)
                    continue;
                if (s().value(a) == l_false) {
                    a.neg();
                    b.neg();
                }
                r.push_back(a);
                r.push_back(b);
            }
            break;
        case bv_justification::kind_t::bit2ne: {
            SASSERT(c.m_consequent.sign());
            sat::bool_var v = c.m_consequent.var();
            expr* eq = bool_var2expr(v);
            SASSERT(m.is_eq(eq));
            euf::enode* n = expr2enode(eq);
            theory_var v1 = n->get_arg(0)->get_th_var(get_id());
            theory_var v2 = n->get_arg(1)->get_th_var(get_id());
            sat::literal a = m_bits[v1][c.m_idx];
            sat::literal b = m_bits[v2][c.m_idx];
            lbool val_a = s().value(a);
            lbool val_b = s().value(b);
            SASSERT(val_a != l_undef && val_b != l_undef && val_a != val_b);
            if (val_a == l_false) a.neg();
            if (val_b == l_false) b.neg();
            r.push_back(a);
            r.push_back(b);
            break;
        }
        }
        if (!probing && ctx.use_drat())
            log_drat(c);
    }

    void solver::log_drat(bv_justification const& c) {
        // introduce dummy literal for equality.
        sat::literal leq(s().num_vars() + 1, false);
        expr_ref eq(m);
        if (c.m_kind != bv_justification::kind_t::bit2ne) {
            expr* e1 = var2expr(c.m_v1);
            expr* e2 = var2expr(c.m_v2);
            eq = m.mk_eq(e1, e2);       
            ctx.drat_eq_def(leq, eq);
        }

        sat::literal_vector lits;
        switch (c.m_kind) {
        case bv_justification::kind_t::eq2bit:
            lits.push_back(~leq);
            lits.push_back(~c.m_antecedent);
            lits.push_back(c.m_consequent);
            break;
        case bv_justification::kind_t::ne2bit:
            get_antecedents(c.m_consequent, c.to_index(), lits, true);
            lits.push_back(c.m_consequent);
            break;
        case bv_justification::kind_t::bit2eq:      
            get_antecedents(leq, c.to_index(), lits, true);
            for (auto& lit : lits)
                lit.neg();
            lits.push_back(leq);
            break;
        case bv_justification::kind_t::bit2ne: 
            get_antecedents(c.m_consequent, c.to_index(), lits, true);
            for (auto& lit : lits)
                lit.neg();
            lits.push_back(c.m_consequent);            
            break;
        }
        ctx.get_drat().add(lits, status());
        // TBD, a proper way would be to delete the lemma after use.
    }

    void solver::asserted(literal l) {
        
        atom* a = get_bv2a(l.var());
        TRACE("bv", tout << "asserted: " << l << "\n";);
        if (a) {
            force_push();
            m_prop_queue.push_back(propagation_item(a));            
            for (auto p : a->m_bit2occ) {
                del_eq_occurs(p.first, p.second);
            }
        }
    }

    bool solver::unit_propagate() {
        if (m_prop_queue_head == m_prop_queue.size())
            return false;
        force_push();
        ctx.push(value_trail<unsigned>(m_prop_queue_head));
        for (; m_prop_queue_head < m_prop_queue.size() && !s().inconsistent(); ++m_prop_queue_head) {
            auto const p = m_prop_queue[m_prop_queue_head];
            if (p.m_atom) {
                for (auto vp : *p.m_atom)
                    propagate_bits(vp);
                for (eq_occurs const& eq : p.m_atom->eqs()) 
                    propagate_eq_occurs(eq);                
            }
            else 
                propagate_bits(p.m_vp);            
        }
        // check_missing_propagation();
        return true;
    }

    bool solver::propagate_eq_occurs(eq_occurs const& occ) {
        auto lit = occ.m_literal;

        if (s().value(lit) != l_undef) {
            IF_VERBOSE(20, verbose_stream() << "assigned " << lit << " " << s().value(lit) << "\n");
            return false;
        }
        literal bit1 = m_bits[occ.m_v1][occ.m_idx];
        literal bit2 = m_bits[occ.m_v2][occ.m_idx];
        lbool val2 = s().value(bit2);
        
        if (val2 == l_undef) {
            IF_VERBOSE(20, verbose_stream() << "add " << occ.m_bv2 << " " << occ.m_v2 << "\n");
            eq_internalized(occ.m_bv2, occ.m_bv1, occ.m_idx, occ.m_v2, occ.m_v1, occ.m_literal, occ.m_node);
            return false;
        }
        lbool val1 = s().value(bit1);
        SASSERT(val1 != l_undef);
        if (val1 != val2 && val2 != l_undef) {
            ++m_stats.m_num_bit2ne;
            IF_VERBOSE(20, verbose_stream() << "assign " << ~lit << "\n");
            s().assign(~lit, mk_bit2ne_justification(occ.m_idx, ~lit));
            return true;
        }
        IF_VERBOSE(20, verbose_stream() << "eq " << lit << "\n");
        return false;
    }

    bool solver::propagate_bits(var_pos entry) {
        theory_var v1 = entry.first;
        unsigned idx = entry.second;
        SASSERT(idx < m_bits[v1].size());
        if (m_wpos[v1] == idx)
            find_wpos(v1);

        literal bit1 = m_bits[v1][idx];
        lbool   val = s().value(bit1);
        TRACE("bv", tout << "propagating v" << v1 << " #" << var2enode(v1)->get_expr_id() << "[" << idx << "] = " << val << "\n";);
        if (val == l_undef)
            return false;

        if (val == l_false)
            bit1.neg();

        unsigned num_bits = 0, num_assigned = 0;
        for (theory_var v2 = m_find.next(v1); v2 != v1; v2 = m_find.next(v2)) {
            literal bit2 = m_bits[v2][idx];
            SASSERT(m_bits[v1][idx] != ~m_bits[v2][idx]);
            TRACE("bv", tout << "propagating #" << var2enode(v2)->get_expr_id() << "[" << idx << "] = " << s().value(bit2) << "\n";);

            if (val == l_false)
                bit2.neg();
            ++num_bits;
            if (num_bits > 3 && num_assigned == 0)
                break;
            if (s().value(bit2) == l_true) 
                continue;
            ++num_assigned;
            if (!assign_bit(bit2, v1, v2, idx, bit1, false))
                break;
        }
        return num_assigned > 0;
    }

    /**
    * Check each delay internalized bit-vector operation for compliance.
    * 
    * TBD: add model-repair attempt after cheap propagation axioms have been added
    */
    sat::check_result solver::check() {
        force_push();
        SASSERT(m_prop_queue.size() == m_prop_queue_head);
        bool ok = true;
        svector<std::pair<expr*, internalize_mode>> delay;
        for (auto kv : m_delay_internalize)
            delay.push_back(std::make_pair(kv.m_key, kv.m_value));
        flet<bool> _cheap1(m_cheap_axioms, true);
        for (auto kv : delay) 
            if (!check_delay_internalized(kv.first))
                ok = false;
        if (!ok)
            return sat::check_result::CR_CONTINUE;

        // if (repair_model()) return sat::check_result::DONE;

        flet<bool> _cheap2(m_cheap_axioms, false);
        for (auto kv : delay) 
            if (!check_delay_internalized(kv.first))
                ok = false;
        
        if (!ok)
            return sat::check_result::CR_CONTINUE;
        return sat::check_result::CR_DONE;
    }

    void solver::push_core() {
        TRACE("bv", tout << "push: " << get_num_vars() << "@" << m_prop_queue_lim.size() << "\n";);
        th_euf_solver::push_core();
        m_prop_queue_lim.push_back(m_prop_queue.size());
    }

    void solver::pop_core(unsigned n) {
        SASSERT(m_num_scopes == 0);
        unsigned old_sz = m_prop_queue_lim.size() - n;
        m_prop_queue.shrink(m_prop_queue_lim[old_sz]);
        m_prop_queue_lim.shrink(old_sz);
        th_euf_solver::pop_core(n);
        old_sz = get_num_vars();        
        m_bits.shrink(old_sz);
        m_wpos.shrink(old_sz);
        m_zero_one_bits.shrink(old_sz);
        TRACE("bv", tout << "num vars " << old_sz << "@" << m_prop_queue_lim.size() << "\n";);
    }

    void solver::simplify() {
        m_ackerman.propagate();
    }

    bool solver::set_root(literal l, literal r) {
        return false;
        atom* a = get_bv2a(l.var());
        if (!a)
            return true;
        for (auto vp : *a) {            
            sat::literal l2 = m_bits[vp.first][vp.second];
            if (l2.var() == r.var())
                continue;
            SASSERT(l2.var() == l.var());
            VERIFY(l2.var() == l.var());
            sat::literal r2 = (l.sign() == l2.sign()) ? r : ~r;
            ctx.push(vector2_value_trail<bits_vector, sat::literal>(m_bits, vp.first, vp.second));
            m_bits[vp.first][vp.second] = r2;
            set_bit_eh(vp.first, r2, vp.second);
        }
        ctx.push(bit_occs_trail(*this, *a));
        a->m_occs = nullptr;
        // validate_atoms();
        return true;
    }

    /**
    * Instantiate Ackerman axioms for bit-vectors that have become equal after roots have been added.
    */
    void solver::flush_roots() {
        struct eq {
            solver& s;
            eq(solver& s) :s(s) {}
            bool operator()(theory_var v1, theory_var v2) const {
                return s.m_bits[v1] == s.m_bits[v2];
            }
        };
        struct hash {
            solver& s;
            hash(solver& s) :s(s) {}
            bool operator()(theory_var v) const {
                literal_vector const& a = s.m_bits[v];
                return string_hash(reinterpret_cast<char*>(a.data()), a.size() * sizeof(sat::literal), 3);
            }
        };
        eq eq_proc(*this);
        hash hash_proc(*this);
        map<theory_var, theory_var, hash, eq> table(hash_proc, eq_proc);
        for (theory_var v = 0; v < static_cast<theory_var>(get_num_vars()); ++v) {
            if (!m_bits[v].empty()) {
                theory_var w = table.insert_if_not_there(v, v);
                if (v != w && m_find.find(v) != m_find.find(w))
                    assert_ackerman(v, w);
            }
        }    
        TRACE("bv", tout << "infer new equations for bit-vectors that are now equal\n";);
    }

    void solver::clauses_modifed() {}
    lbool solver::get_phase(bool_var v) { return l_undef; }
    std::ostream& solver::display(std::ostream& out) const {
        unsigned num_vars = get_num_vars();
        if (num_vars > 0)
            out << "bv-solver:\n";
        for (unsigned v = 0; v < num_vars; v++)
            out << pp(v);
        return out;
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        return display_constraint(out, idx);
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        auto& c = bv_justification::from_index(idx);
        theory_var v1 = c.m_v1;
        theory_var v2 = c.m_v2;
        unsigned cidx = c.m_idx;
        switch (c.m_kind) {
        case bv_justification::kind_t::eq2bit:
            return out << "bv <- " << c.m_antecedent << " v" << v1 << " == v" << v2;
        case bv_justification::kind_t::bit2eq:
            return out << "bv " << m_bits[v1] << " == " << m_bits[v2] << " -> v" << v1 << " == v" << v2;
        case bv_justification::kind_t::bit2ne: {
            expr* e = bool_var2expr(c.m_consequent.var());
            SASSERT(m.is_eq(e));
            euf::enode* n = expr2enode(e);
            v1 = n->get_arg(0)->get_th_var(get_id());
            v2 = n->get_arg(1)->get_th_var(get_id());            
            return out << "bv <- v" << v1 << "[" << cidx << "] != v" << v2 << "[" << cidx << "] " << m_bits[v1][cidx] << " != " << m_bits[v2][cidx];
        }
        case bv_justification::kind_t::ne2bit: 
            return out << "bv <- " << m_bits[v1] << " != " << m_bits[v2] << " @" << cidx;                                                 
        default:
            UNREACHABLE();
            break;
        }
        return out;
    }

    std::ostream& solver::display(std::ostream& out, atom const& a) const {
        out << a.m_bv << "\n";
        for (auto vp : a) 
            out << vp.first << "[" << vp.second << "]\n";
        for (auto e : a.eqs())
            out << e.m_bv1 << " " << e.m_bv2 << "\n";
        return out;
    }


    void solver::collect_statistics(statistics& st) const {
        st.update("bv conflicts", m_stats.m_num_conflicts);
        st.update("bv diseqs", m_stats.m_num_diseq_static);
        st.update("bv dynamic diseqs", m_stats.m_num_diseq_dynamic);
        st.update("bv eq2bit", m_stats.m_num_eq2bit);
        st.update("bv ne2bit", m_stats.m_num_ne2bit);
        st.update("bv bit2eq", m_stats.m_num_bit2eq);
        st.update("bv bit2ne", m_stats.m_num_bit2ne);
        st.update("bv ackerman", m_stats.m_ackerman);
    }

    sat::extension* solver::copy(sat::solver* s) { UNREACHABLE(); return nullptr; }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        bv::solver* result = alloc(bv::solver, ctx, get_id());
        ast_translation tr(m, ctx.get_manager());
        for (unsigned i = 0; i < get_num_vars(); ++i) {
            expr* e1 = var2expr(i);
            expr* e2 = tr(e1);
            euf::enode* n2 = ctx.get_enode(e2);
            SASSERT(n2);
            result->mk_var(n2);
            result->m_bits[i].append(m_bits[i]);
            result->m_zero_one_bits[i].append(m_zero_one_bits[i]);
        }
        result->set_solver(&ctx.s());
        for (theory_var i = 0; i < static_cast<theory_var>(get_num_vars()); ++i)
            if (find(i) != i)
                result->m_find.set_root(i, find(i));
        result->m_prop_queue.append(m_prop_queue);
        for (unsigned i = 0; i < m_bool_var2atom.size(); ++i) {
            atom* a = m_bool_var2atom[i];
            if (!a)
                continue;

            atom* new_a = new (result->get_region()) atom(i);
            result->m_bool_var2atom.setx(i, new_a, nullptr);
            for (auto vp : *a)
                new_a->m_occs = new (result->get_region()) var_pos_occ(vp.first, vp.second, new_a->m_occs);
            for (eq_occurs const& occ : a->eqs()) {
                expr* e = occ.m_node->get_expr();
                expr_ref e2(tr(e), tr.to());
                euf::enode* n = ctx.get_enode(e2);
                new_a->m_eqs = new (result->get_region()) eq_occurs(occ.m_bv1, occ.m_bv2, occ.m_idx, occ.m_v1, occ.m_v2, occ.m_literal, n, new_a->m_eqs);
            }
            new_a->m_def = a->m_def;
            new_a->m_var = a->m_var;
            // validate_atoms();
        }
        return result;
    }

    void solver::pop_reinit() {}
    bool solver::validate() { return true; }
    void solver::init_use_list(sat::ext_use_list& ul) {}
    bool solver::is_blocked(literal l, sat::ext_constraint_idx) { return false; }
    bool solver::check_model(sat::model const& m) const { return true; }
    void solver::finalize_model(model& mdl) {}

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(bv.is_bv(n->get_expr()));
        if (bv.is_numeral(n->get_expr())) {
            values[n->get_root_id()] = n->get_expr();
            return;
        }
        theory_var v = n->get_th_var(get_id());
        rational val;
        unsigned i = 0;
        for (auto l : m_bits[v]) {
            switch (s().value(l)) {
            case l_true:
                val += power2(i);
                break;
            default:
                break;
            }
            ++i;
        }
        values[n->get_root_id()] = bv.mk_numeral(val, m_bits[v].size());
    }

    trail_stack& solver::get_trail_stack() {
        return ctx.get_trail_stack();
    }

    void solver::merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {

        TRACE("bv", tout << "merging: v" << v1 << " #" << var2enode(v1)->get_expr_id() << " v" << v2 << " #" << var2enode(v2)->get_expr_id() << "\n";);
        if (!merge_zero_one_bits(r1, r2)) {
            TRACE("bv", tout << "conflict detected\n";);
            return; // conflict was detected
        }
        SASSERT(m_bits[v1].size() == m_bits[v2].size());
        unsigned sz = m_bits[v1].size();
        if (sz == 1)
            return;
        for (unsigned idx = 0; !s().inconsistent() && idx < sz; idx++) {
            literal bit1 = m_bits[v1][idx];
            literal bit2 = m_bits[v2][idx];
            CTRACE("bv", bit1 == ~bit2, tout << pp(v1) << pp(v2) << "idx: " << idx << "\n";);
            if (bit1 == ~bit2) {
                mk_new_diseq_axiom(v1, v2, idx);
                return;
            }
            SASSERT(bit1 != ~bit2);
            lbool val1 = s().value(bit1);
            lbool val2 = s().value(bit2);
            TRACE("bv", tout << "merge v" << v1 << " " << bit1 << ":= " << val1 << " " << bit2 << ":= " << val2 << "\n";);
            if (val1 == val2)
                continue;
            CTRACE("bv", (val1 != l_undef && val2 != l_undef), tout << "inconsistent "; tout << pp(v1) << pp(v2) << "idx: " << idx << "\n";);
            if (val1 == l_false)
                assign_bit(~bit2, v1, v2, idx, ~bit1, true);
            else if (val1 == l_true)
                assign_bit(bit2, v1, v2, idx, bit1, true);
            else if (val2 == l_false)
                assign_bit(~bit1, v2, v1, idx, ~bit2, true);
            else if (val2 == l_true)
                assign_bit(bit1, v2, v1, idx, bit2, true);
        }
    }

    sat::justification solver::mk_eq2bit_justification(theory_var v1, theory_var v2, sat::literal c, sat::literal a) {
        void* mem = get_region().allocate(bv_justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) bv_justification(v1, v2, c, a);
        return sat::justification::mk_ext_justification(s().scope_lvl(), constraint->to_index());
    }

    sat::ext_justification_idx solver::mk_bit2eq_justification(theory_var v1, theory_var v2) {
        void* mem = get_region().allocate(bv_justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) bv_justification(v1, v2);
        return constraint->to_index();
    }

    sat::justification solver::mk_bit2ne_justification(unsigned idx, sat::literal c) {
        void* mem = get_region().allocate(bv_justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) bv_justification(idx, c);
        return sat::justification::mk_ext_justification(s().scope_lvl(), constraint->to_index());
    }

    sat::justification solver::mk_ne2bit_justification(unsigned idx, theory_var v1, theory_var v2, sat::literal c, sat::literal a) {
        void* mem = get_region().allocate(bv_justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) bv_justification(idx, v1, v2, c, a);
        return sat::justification::mk_ext_justification(s().scope_lvl(), constraint->to_index());
    }

    bool solver::assign_bit(literal consequent, theory_var v1, theory_var v2, unsigned idx, literal antecedent, bool propagate_eqc) {
        m_stats.m_num_eq2bit++;
        SASSERT(ctx.s().value(antecedent) == l_true);
        SASSERT(m_bits[v2][idx].var() == consequent.var());
        SASSERT(consequent.var() != antecedent.var());
        s().assign(consequent, mk_eq2bit_justification(v1, v2, consequent, antecedent));
        if (s().value(consequent) == l_false) {
            m_stats.m_num_conflicts++;
            SASSERT(s().inconsistent());
            return false;
        }
        else {
            if (m_wpos[v2] == idx)
                find_wpos(v2);
            bool_var cv = consequent.var();
            atom* a = get_bv2a(cv);
            force_push();
            if (a)
                for (auto curr : *a)
                    if (propagate_eqc || find(curr.first) != find(v2) || curr.second != idx) 
                        m_prop_queue.push_back(propagation_item(curr));  
            return true;
        }
    }

    void solver::unmerge_eh(theory_var v1, theory_var v2) {
        // v1 was the root of the equivalence class
        // I must remove the zero_one_bits that are from v2.
        zero_one_bits& bits = m_zero_one_bits[v1];
        if (bits.empty())
            return;
        for (unsigned j = bits.size(); j-- > 0; ) {
            zero_one_bit& bit = bits[j];
            if (find(bit.m_owner) == v1) {
                bits.shrink(j + 1);
                return;
            }
        }
        bits.shrink(0);
    }

    bool solver::merge_zero_one_bits(theory_var r1, theory_var r2) {
        zero_one_bits& bits2 = m_zero_one_bits[r2];
        if (bits2.empty())
            return true;
        zero_one_bits& bits1 = m_zero_one_bits[r1];
        unsigned bv_size = get_bv_size(r1);
        SASSERT(bv_size == get_bv_size(r2));
        m_merge_aux[0].reserve(bv_size + 1, euf::null_theory_var);
        m_merge_aux[1].reserve(bv_size + 1, euf::null_theory_var);

        struct scoped_reset {
            solver& s;
            zero_one_bits& bits1;
            scoped_reset(solver& s, zero_one_bits& bits1) :s(s), bits1(bits1) {}
            ~scoped_reset() {
                for (auto& zo : bits1)
                    s.m_merge_aux[zo.m_is_true][zo.m_idx] = euf::null_theory_var;
            }
        };
        scoped_reset _sr(*this, bits1);

        DEBUG_CODE(for (unsigned i = 0; i < bv_size; i++) SASSERT(m_merge_aux[0][i] == euf::null_theory_var || m_merge_aux[1][i] == euf::null_theory_var););

        // save info about bits1
        for (auto& zo : bits1)
            m_merge_aux[zo.m_is_true][zo.m_idx] = zo.m_owner;
        // check if bits2 is consistent with bits1, and copy new bits to bits1
        for (auto& zo : bits2) {
            theory_var v2 = zo.m_owner;
            theory_var v1 = m_merge_aux[!zo.m_is_true][zo.m_idx];
            if (v1 != euf::null_theory_var) {
                // conflict was detected ... v1 and v2 have complementary bits
                SASSERT(m_bits[v1][zo.m_idx] == ~(m_bits[v2][zo.m_idx]));
                SASSERT(m_bits[v1].size() == m_bits[v2].size());
                mk_new_diseq_axiom(v1, v2, zo.m_idx);
                return false;
            }
            // copy missing variable to bits1
            if (m_merge_aux[zo.m_is_true][zo.m_idx] == euf::null_theory_var)
                bits1.push_back(zo);
        }
        // reset m_merge_aux vector
        DEBUG_CODE(for (unsigned i = 0; i < bv_size; i++) { SASSERT(m_merge_aux[0][i] == euf::null_theory_var || m_merge_aux[1][i] == euf::null_theory_var); });
        return true;
    }

    rational const& solver::power2(unsigned i) const {
        while (m_power2.size() <= i)
            m_power2.push_back(m_bb.power(m_power2.size()));
        return m_power2[i];
    }

}
