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

    class solver::bit_trail : public trail<euf::solver> {
        solver& s;
        solver::var_pos vp;
        sat::literal lit;
    public:
        bit_trail(solver& s, var_pos vp) : s(s), vp(vp), lit(s.m_bits[vp.first][vp.second]) {}

        virtual void undo(euf::solver& euf) {
            s.m_bits[vp.first][vp.second] = lit;
        }
    };

    solver::solver(euf::solver& ctx, theory_id id) :
        euf::th_euf_solver(ctx, id),
        bv(m),
        m_autil(m),
        m_ackerman(*this),
        m_bb(m, get_config()),
        m_find(*this) {
    }

    void solver::fixed_var_eh(theory_var v1) {
        numeral val1, val2;
        VERIFY(get_fixed_value(v1, val1));
        unsigned sz = m_bits[v1].size();
        value_sort_pair key(val1, sz);
        theory_var v2;
        bool is_current =
            m_fixed_var_table.find(key, v2) &&
            v2 < static_cast<int>(get_num_vars()) &&
            is_bv(v2) &&
            get_bv_size(v2) == sz &&
            get_fixed_value(v2, val2) && val1 == val2;

        if (!is_current)
            m_fixed_var_table.insert(key, v1);
        else if (var2enode(v1)->get_root() != var2enode(v2)->get_root()) {
            SASSERT(get_bv_size(v1) == get_bv_size(v2));
            TRACE("bv", tout << "detected equality: v" << v1 << " = v" << v2 << "\n" << pp(v1) << pp(v2););
            m_stats.m_num_th2core_eq++;
            add_fixed_eq(v1, v2);
            ctx.propagate(var2enode(v1), var2enode(v2), mk_bit2bv_justification(v1, v2));
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
            switch (ctx.s().value(b)) {
            case l_false:
                break;
            case l_undef:
                return false;
            case l_true:
                result += power2(i);
                break;
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
    void solver::find_new_diseq_axioms(bit_atom& a, theory_var v, unsigned idx) {
        if (!get_config().m_bv_eq_axioms)
            return;
        literal l = m_bits[v][idx];
        l.neg();
        for (auto vp : a) {
            theory_var v2 = vp.first;
            unsigned   idx2 = vp.second;
            if (idx == idx2 && m_bits[v2][idx2] == l && get_bv_size(v2) == get_bv_size(v))
                mk_new_diseq_axiom(v, v2, idx);
        }
    }

    /**
       \brief v1[idx] = ~v2[idx], then v1 /= v2 is a theory axiom.
    */
    void solver::mk_new_diseq_axiom(theory_var v1, theory_var v2, unsigned idx) {
        if (!get_config().m_bv_eq_axioms)
            return;

        // TBD: disabled until new literal creation is supported
        return;
        SASSERT(m_bits[v1][idx] == ~m_bits[v2][idx]);
        TRACE("bv", tout << "found new diseq axiom\n" << pp(v1) << pp(v2););
        m_stats.m_num_diseq_static++;
        expr_ref eq(m.mk_eq(var2expr(v1), var2expr(v2)), m);
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
            if (a->is_bit()) {
                for (var_pos vp : a->to_bit())
                    out << " " << var2enode(vp.first)->get_expr_id() << "[" << vp.second << "]";
            }
            else
                out << "def-atom";
        }
        else
            out << " " << mk_bounded_pp(e, m, 1);
        out << "\n";
        return out;
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        TRACE("bv", tout << "new eq " << eq.m_v1 << " == " << eq.m_v2 << "\n";);
        if (is_bv(eq.m_v1))
            m_find.merge(eq.m_v1, eq.m_v2);
    }

    double solver::get_reward(literal l, sat::ext_constraint_idx idx, sat::literal_occs_fun& occs) const { return 0; }
    bool solver::is_extended_binary(sat::ext_justification_idx idx, literal_vector& r) { return false; }
    bool solver::is_external(bool_var v) { return true; }
    bool solver::propagate(literal l, sat::ext_constraint_idx idx) { return false; }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& c = bv_justification::from_index(idx);
        TRACE("bv", display_constraint(tout, idx););
        switch (c.m_kind) {
        case bv_justification::kind_t::bv2bit:
            r.push_back(c.m_antecedent);
            ctx.add_antecedent(var2enode(c.m_v1), var2enode(c.m_v2));
            break;
        case bv_justification::kind_t::bit2bv:
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
        }
        if (!probing && ctx.use_drat())
            log_drat(c);
    }

    void solver::log_drat(bv_justification const& c) {
        // this has a side-effect so changes provability:
        expr_ref eq(m.mk_eq(var2expr(c.m_v1), var2expr(c.m_v2)), m);
        sat::literal leq = ctx.internalize(eq, false, false, false);
        sat::literal_vector lits;
        auto add_bit = [&](sat::literal lit) {
            if (s().value(lit) == l_true)
                lit.neg();
            lits.push_back(lit);
        };
        switch (c.m_kind) {
        case bv_justification::kind_t::bv2bit:
            lits.push_back(~leq);
            lits.push_back(~c.m_antecedent);
            lits.push_back(c.m_consequent);
            break;
        case bv_justification::kind_t::bit2bv:
            lits.push_back(leq);
            for (unsigned i = m_bits[c.m_v1].size(); i-- > 0; ) {
                sat::literal a = m_bits[c.m_v1][i];
                sat::literal b = m_bits[c.m_v2][i];
                if (a != b) {
                    add_bit(a);
                    add_bit(b);
                }
            }
            break;
        }
        ctx.get_drat().add(lits, status());
    }

    void solver::asserted(literal l) {
        atom* a = get_bv2a(l.var());
        TRACE("bv", tout << "asserted: " << l << "\n";);
        if (a->is_bit())
            for (auto vp : a->to_bit())
                m_prop_queue.push_back(vp);
    }

    bool solver::unit_propagate() {
        if (m_prop_queue_head == m_prop_queue.size())
            return false;
        ctx.push(value_trail<euf::solver, unsigned>(m_prop_queue_head));
        for (; m_prop_queue_head < m_prop_queue.size() && !s().inconsistent(); ++m_prop_queue_head)
            propagate_bits(m_prop_queue[m_prop_queue_head]);
        return true;
    }

    void solver::propagate_bits(var_pos entry) {
        theory_var v1 = entry.first;
        unsigned idx = entry.second;
        SASSERT(idx < m_bits[v1].size());
        if (m_wpos[v1] == idx)
            find_wpos(v1);

        literal bit1 = m_bits[v1][idx];
        lbool   val = s().value(bit1);
        TRACE("bv", tout << "propagating v" << v1 << " #" << var2enode(v1)->get_expr_id() << "[" << idx << "] = " << val << "\n";);
        if (val == l_undef)
            return;

        if (val == l_false)
            bit1.neg();

        for (theory_var v2 = m_find.next(v1); v2 != v1 && !s().inconsistent(); v2 = m_find.next(v2)) {
            literal bit2 = m_bits[v2][idx];
            SASSERT(m_bits[v1][idx] != ~m_bits[v2][idx]);
            TRACE("bv", tout << "propagating #" << var2enode(v2)->get_expr_id() << "[" << idx << "] = " << s().value(bit2) << "\n";);

            if (val == l_false)
                bit2.neg();
            if (l_true != s().value(bit2))
                assign_bit(bit2, v1, v2, idx, bit1, false);
        }
    }

    sat::check_result solver::check() {
        SASSERT(m_prop_queue.size() == m_prop_queue_head);
        return sat::check_result::CR_DONE;
    }

    void solver::push() {
        th_euf_solver::lazy_push();
        m_prop_queue_lim.push_back(m_prop_queue.size());
    }

    void solver::pop(unsigned n) {
        unsigned old_sz = m_prop_queue_lim.size() - n;
        m_prop_queue.shrink(m_prop_queue_lim[old_sz]);
        m_prop_queue_lim.shrink(old_sz);
        n = lazy_pop(n);
        if (n > 0) {
            old_sz = get_num_vars();
            m_bits.shrink(old_sz);
            m_wpos.shrink(old_sz);
            m_zero_one_bits.shrink(old_sz);
        }
    }

    void solver::pre_simplify() {}

    void solver::simplify() {
        m_ackerman.propagate();
    }

    bool solver::set_root(literal l, literal r) {
        atom* a = get_bv2a(l.var());
        if (!a || !a->is_bit())
            return true;
        for (auto vp : a->to_bit()) {
            sat::literal l2 = m_bits[vp.first][vp.second];
            sat::literal r2 = (l.sign() == l2.sign()) ? r : ~r;
            SASSERT(l2.var() == l.var());
            ctx.push(bit_trail(*this, vp));
            m_bits[vp.first][vp.second] = r2;
            set_bit_eh(vp.first, r2, vp.second);
        }
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
                return string_hash(reinterpret_cast<char*>(a.c_ptr()), a.size() * sizeof(sat::literal), 3);
            }
        };
        eq eq_proc(*this);
        hash hash_proc(*this);
        map<theory_var, theory_var, hash, eq> table(hash_proc, eq_proc);
        for (unsigned v = 0; v < get_num_vars(); ++v) {
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
        switch (c.m_kind) {
        case bv_justification::kind_t::bv2bit:
            return out << c.m_consequent << " <= " << c.m_antecedent << " v" << c.m_v1 << " == v" << c.m_v2 << "\n";
        case bv_justification::kind_t::bit2bv:
            return out << m_bits[c.m_v1] << " == " << m_bits[c.m_v2] << " => v" << c.m_v1 << " == v" << c.m_v2 << "\n";
        default:
            UNREACHABLE();
            break;
        }
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("bv conflicts", m_stats.m_num_conflicts);
        st.update("bv diseqs", m_stats.m_num_diseq_static);
        st.update("bv dynamic diseqs", m_stats.m_num_diseq_dynamic);
        st.update("bv bit2core", m_stats.m_num_bit2core);
        st.update("bv->core eq", m_stats.m_num_th2core_eq);
        st.update("bv ackerman", m_stats.m_ackerman);
    }

    sat::extension* solver::copy(sat::solver* s) { UNREACHABLE(); return nullptr; }

    euf::th_solver* solver::fresh(sat::solver* s, euf::solver& ctx) {
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
        for (unsigned i = 0; i < get_num_vars(); ++i)
            if (find(i) != i)
                result->m_find.merge(i, find(i));
        result->m_prop_queue.append(m_prop_queue);
        for (unsigned i = 0; i < m_bool_var2atom.size(); ++i) {
            atom* a = m_bool_var2atom[i];
            if (!a)
                continue;

            if (a->is_bit()) {
                bit_atom* new_a = new (result->get_region()) bit_atom();
                m_bool_var2atom.setx(i, new_a, nullptr);
                for (auto vp : a->to_bit())
                    new_a->m_occs = new (result->get_region()) var_pos_occ(vp.first, vp.second, new_a->m_occs);
            }
            else {
                def_atom* new_a = new (result->get_region()) def_atom(a->to_def().m_var, a->to_def().m_def);
                m_bool_var2atom.setx(i, new_a, nullptr);
            }
        }
        return result;
    }

    void solver::pop_reinit() {}
    bool solver::validate() { return true; }
    void solver::init_use_list(sat::ext_use_list& ul) {}
    bool solver::is_blocked(literal l, sat::ext_constraint_idx) { return false; }
    bool solver::check_model(sat::model const& m) const { return true; }
    unsigned solver::max_var(unsigned w) const { return w; }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(bv.is_bv(n->get_expr()));
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

    trail_stack<euf::solver>& solver::get_trail_stack() {
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
        for (unsigned idx = 0; !s().inconsistent() && idx < sz; idx++) {
            literal bit1 = m_bits[v1][idx];
            literal bit2 = m_bits[v2][idx];
            CTRACE("bv", bit1 == ~bit2, tout << pp(v1) << pp(v2) << "idx: " << idx << "\n";);
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

    sat::justification solver::mk_bv2bit_justification(theory_var v1, theory_var v2, sat::literal c, sat::literal a) {
        void* mem = get_region().allocate(bv_justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) bv_justification(v1, v2, c, a);
        return sat::justification::mk_ext_justification(s().scope_lvl(), constraint->to_index());
    }

    sat::ext_justification_idx solver::mk_bit2bv_justification(theory_var v1, theory_var v2) {
        void* mem = get_region().allocate(bv_justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) bv_justification(v1, v2);
        return constraint->to_index();
    }

    void solver::assign_bit(literal consequent, theory_var v1, theory_var v2, unsigned idx, literal antecedent, bool propagate_eqc) {
        m_stats.m_num_bit2core++;
        SASSERT(ctx.s().value(antecedent) == l_true);
        SASSERT(m_bits[v2][idx].var() == consequent.var());
        SASSERT(consequent.var() != antecedent.var());
        s().assign(consequent, mk_bv2bit_justification(v1, v2, consequent, antecedent));
        if (s().value(consequent) == l_false) {
            m_stats.m_num_conflicts++;
            SASSERT(s().inconsistent());
        }
        else {
            if (get_config().m_bv_eq_axioms && false) {
                // TODO - enable when pop_reinit is available
                expr_ref eq(m.mk_eq(var2expr(v1), var2expr(v2)), m);
                flet<bool> _is_redundant(m_is_redundant, true);
                literal eq_lit = ctx.internalize(eq, false, false, m_is_redundant);
                add_clause(~antecedent, ~eq_lit, consequent);
                add_clause(antecedent, ~eq_lit, ~consequent);
            }

            if (m_wpos[v2] == idx)
                find_wpos(v2);
            bool_var cv = consequent.var();
            atom* a = get_bv2a(cv);
            if (a && a->is_bit())
                for (auto curr : a->to_bit())
                    if (propagate_eqc || find(curr.first) != find(v2) || curr.second != idx) 
                        m_prop_queue.push_back(curr);                    
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

    /**
        \brief Check whether m_zero_one_bits is an accurate summary of the bits in the
        equivalence class rooted by v.
        \remark The method does nothing if v is not the root of the equivalence class.
    */
    bool solver::check_zero_one_bits(theory_var v) {
        if (s().inconsistent())
            return true; // property is only valid if the context is not in a conflict.
        if (!is_root(v) || !is_bv(v))
            return true;
        bool_vector bits[2];
        unsigned      num_bits = 0;
        unsigned      bv_sz = get_bv_size(v);
        bits[0].resize(bv_sz, false);
        bits[1].resize(bv_sz, false);

        theory_var curr = v;
        do {
            literal_vector const& lits = m_bits[curr];
            for (unsigned i = 0; i < lits.size(); i++) {
                literal l = lits[i];
                if (s().value(l) != l_undef) {
                    unsigned is_true = s().value(l) == l_true;
                    if (bits[!is_true][i]) {
                        // expect a conflict later on.
                        return true;
                    }
                    if (!bits[is_true][i]) {
                        bits[is_true][i] = true;
                        num_bits++;
                    }
                }
            }
            curr = m_find.next(curr);
        } while (curr != v);

        zero_one_bits const& _bits = m_zero_one_bits[v];
        SASSERT(_bits.size() == num_bits);
        bool_vector already_found;
        already_found.resize(bv_sz, false);
        for (auto& zo : _bits) {
            SASSERT(find(zo.m_owner) == v);
            SASSERT(bits[zo.m_is_true][zo.m_idx]);
            SASSERT(!already_found[zo.m_idx]);
            already_found[zo.m_idx] = true;
        }
        return true;
    }
}
