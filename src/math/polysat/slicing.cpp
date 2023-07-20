/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polysat slicing

Author:

    Jakob Rath 2023-06-01

--*/




/*

Example:
(1)     x = y
(2)     z = y[3:0]
(3)     explain(x[3:0] == z)? should be { (1), (2) }

                    (1)
        x ========================> y
       / \                         / \          (2)
  x[7:4] x[3:0]               y[7:4] y[3:0] ===========> z


TODO:
- track fixed bits along with enodes
- notify solver about equalities discovered by congruence
- implement query functions
- when solver assigns value of a variable v, add equations with v substituted by its value?

*/


#include "ast/reg_decl_plugins.h"
#include "math/polysat/slicing.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "util/tptr.h"

namespace {

    template <typename>
    [[maybe_unused]]
    inline constexpr bool always_false_v = false;

}

namespace polysat {

    unsigned slicing::dep_t::to_uint() const {
        return std::visit([](auto arg) -> unsigned {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return UINT_MAX;
            else if constexpr (std::is_same_v<T, sat::literal>)
                return (arg.to_uint() << 1);
            else if constexpr (std::is_same_v<T, pvar>)
                return (arg << 1) + 1;
            else
                static_assert(always_false_v<T>, "non-exhaustive visitor!");
        }, m_data);
    }

    slicing::dep_t slicing::dep_t::from_uint(unsigned x) {
        if (x == UINT_MAX)
            return dep_t();
        else if ((x & 1) == 0)
            return dep_t(sat::to_literal(x >> 1));
        else
            return dep_t(static_cast<pvar>(x >> 1));
    }

    std::ostream& slicing::dep_t::display(std::ostream& out) {
        if (is_null())
            out << "null";
        else if (is_var())
            out << "v" << var();
        else if (is_lit())
            out << "lit(" << lit() << ")";
        return out;
    }

    void* slicing::encode_dep(dep_t d) {
        void* p = box<void>(d.to_uint());
        SASSERT_EQ(d, decode_dep(p));
        return p;
    }

    slicing::dep_t slicing::decode_dep(void* p) {
        return dep_t::from_uint(unbox<unsigned>(p));
    }

    void slicing::display_dep(std::ostream& out, void* d) {
        out << decode_dep(d);
    }

    slicing::slicing(solver& s):
        m_solver(s),
        m_egraph(m_ast)
    {
        reg_decl_plugins(m_ast);
        m_bv = alloc(bv_util, m_ast);
        m_egraph.set_display_justification(display_dep);
        m_egraph.set_on_propagate([&](enode* lit, enode* ante) { egraph_on_propagate(lit, ante); });
    }

    slicing::slice_info& slicing::info(euf::enode* n) {
        return const_cast<slice_info&>(std::as_const(*this).info(n));
    }

    slicing::slice_info const& slicing::info(euf::enode* n) const {
        SASSERT(!n->is_equality());
        slice_info const& i = m_info[n->get_id()];
        return i.is_slice() ? i : info(i.slice);
    }

    unsigned slicing::width(enode* s) const {
        SASSERT(!s->is_equality());
        return m_bv->get_bv_size(s->get_expr());
    }

    func_decl* slicing::mk_concat_decl(ptr_vector<expr> const& args) {
        SASSERT(args.size() >= 2);
        ptr_vector<sort> domain;
        unsigned sz = 0;
        for (expr* e : args) {
            domain.push_back(e->get_sort());
            sz += m_bv->get_bv_size(e);
        }
        sort* range = m_bv->mk_sort(sz);
        return m_ast.mk_func_decl(symbol("slice-concat"), domain.size(), domain.data(), range);
    }

    void slicing::push_scope() {
        SASSERT(!is_conflict());
        if (can_propagate())
            propagate();
        m_scopes.push_back(m_trail.size());
        m_egraph.push();
        SASSERT(m_needs_congruence.empty());
    }

    void slicing::pop_scope(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        unsigned const lvl = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned const target_lvl = lvl - num_scopes;
        unsigned const target_size = m_scopes[target_lvl];
        m_scopes.shrink(target_lvl);
        while (m_trail.size() > target_size) {
            switch (m_trail.back()) {
            case trail_item::add_var:       undo_add_var();     break;
            case trail_item::split_core:    undo_split_core();  break;
            case trail_item::mk_extract:    undo_mk_extract();  break;
            default: UNREACHABLE();
            }
            m_trail.pop_back();
        }
        m_egraph.pop(num_scopes);
        m_needs_congruence.reset();
        m_disequality_conflict = nullptr;
    }

    void slicing::add_var(unsigned bit_width) {
        pvar const v = m_var2slice.size();
        enode* s = alloc_slice(bit_width, v);
        m_var2slice.push_back(s);
    }

    void slicing::undo_add_var() {
        m_var2slice.pop_back();
    }

    slicing::enode* slicing::find_or_alloc_disequality(enode* x, enode* y, sat::literal lit) {
        expr_ref eq(m_ast.mk_eq(x->get_expr(), y->get_expr()), m_ast);
        enode* eqn = m_egraph.find(eq);
        if (eqn)
            return eqn;
        auto args = {x, y};
        eqn = m_egraph.mk(eq, 0, args.size(), args.begin());
        auto j = euf::justification::external(encode_dep(lit));
        m_egraph.set_value(eqn, l_false, j);
        SASSERT(eqn->is_equality());
        SASSERT_EQ(eqn->value(), l_false);
        return eqn;
    }

    slicing::enode* slicing::alloc_enode(expr* e, unsigned num_args, enode* const* args, pvar var) {
        SASSERT(!m_egraph.find(e));
        euf::enode* n = m_egraph.mk(e, 0, num_args, args);  // NOTE: the egraph keeps a strong reference to 'e'
        m_info.reserve(n->get_id() + 1);
        slice_info& i = info(n);
        i.reset();
        i.var = var;
        return n;
    }

    slicing::enode* slicing::find_or_alloc_enode(expr* e, unsigned num_args, enode* const* args, pvar var) {
        enode* n = m_egraph.find(e);
        if (n) {
            SASSERT_EQ(info(n).var, var);
            return n;
        }
        return alloc_enode(e, num_args, args, var);
    }

    slicing::enode* slicing::alloc_slice(unsigned width, pvar var) {
        SASSERT(width > 0);
        app* a = m_ast.mk_fresh_const("s", m_bv->mk_sort(width), false);
        return alloc_enode(a, 0, nullptr, var);
    }

    void slicing::add_congruence(pvar v) {
        enode_vector& base = m_tmp2;
        SASSERT(base.empty());
        enode* sv = var2slice(v);
        get_base(sv, base);
        // Add equation v == concat(s1, ..., sn)
        ptr_vector<expr> args;
        for (enode* n : base)
            args.push_back(n->get_expr());
        app* a = m_ast.mk_app(mk_concat_decl(args), args);
        enode* concat = find_or_alloc_enode(a, base.size(), base.data(), null_var);
        info(concat).slice = sv;
        base.clear();
        m_egraph.merge(sv, concat, encode_dep(dep_t()));
    }

    void slicing::add_congruence_if_needed(pvar v) {
        if (!m_needs_congruence.contains(v))
            return;
        m_needs_congruence.remove(v);
        add_congruence(v);
    }

    void slicing::update_var_congruences() {
        for (pvar v : m_needs_congruence)
            add_congruence(v);
        m_needs_congruence.reset();
    }

    // split a single slice without updating any equivalences
    void slicing::split_core(enode* s, unsigned cut) {
        SASSERT(!has_sub(s));
        SASSERT(info(s).sub_hi == nullptr && info(s).sub_lo == nullptr);
        SASSERT(width(s) > cut + 1);
        unsigned const width_hi = width(s) - cut - 1;
        unsigned const width_lo = cut + 1;
        enode* sub_hi;
        enode* sub_lo;
        if (has_value(s)) {
            rational const val = get_value(s);
            sub_hi = mk_value_slice(machine_div2k(val, width_lo), width_hi);
            sub_lo = mk_value_slice(mod2k(val, width_lo), width_lo);
        }
        else {
            sub_hi = alloc_slice(width_hi);
            sub_lo = alloc_slice(width_lo);
            info(sub_hi).parent = s;
            info(sub_lo).parent = s;
        }
        info(s).set_cut(cut, sub_hi, sub_lo);
        m_trail.push_back(trail_item::split_core);
        m_split_trail.push_back(s);
        for (enode* n = s; n != nullptr; n = parent(n)) {
            pvar const v = slice2var(n);
            if (v == null_var)
                continue;
            if (m_needs_congruence.contains(v)) {
                SASSERT(invariant_needs_congruence());
                break;  // added parents already previously
            }
            m_needs_congruence.insert(v);
        }
    }

    bool slicing::invariant_needs_congruence() const {
        for (pvar v : m_needs_congruence)
            for (enode* s = var2slice(v); s != nullptr; s = parent(s))
                if (slice2var(s) != null_var) {
                    VERIFY(m_needs_congruence.contains(slice2var(s)));
                }
        return true;
    }

    void slicing::undo_split_core() {
        enode* s = m_split_trail.back();
        m_split_trail.pop_back();
        info(s).set_cut(null_cut, nullptr, nullptr);
    }

    void slicing::split(enode* s, unsigned cut) {
        // split all slices in the equivalence class
        for (euf::enode* n : euf::enode_class(s))
            split_core(n, cut);
        // propagate the proper equivalences
        for (euf::enode* n : euf::enode_class(s)) {
            euf::enode* target = n->get_target();
            if (!target)
                continue;
            euf::justification j = n->get_justification();
            SASSERT(j.is_external());  // cannot be a congruence since the slice wasn't split before.
            m_egraph.merge(sub_hi(n), sub_hi(target), j.ext<void>());
            m_egraph.merge(sub_lo(n), sub_lo(target), j.ext<void>());
        }
    }

    void slicing::mk_slice(enode* src, unsigned const hi, unsigned const lo, enode_vector& out, bool output_full_src, bool output_base) {
        SASSERT(hi >= lo);
        SASSERT(width(src) > hi);  // extracted range must be fully contained inside the src slice
        auto output_slice = [this, output_base, &out](enode* s) {
            if (output_base)
                get_base(s, out);
            else
                out.push_back(s);
        };
        if (lo == 0 && width(src) - 1 == hi) {
            output_slice(src);
            return;
        }
        if (has_sub(src)) {
            // src is split into [src.width-1, cut+1] and [cut, 0]
            unsigned const cut = info(src).cut;
            if (lo >= cut + 1) {
                // target slice falls into upper subslice
                mk_slice(sub_hi(src), hi - cut - 1, lo - cut - 1, out, output_full_src, output_base);
                if (output_full_src)
                    output_slice(sub_lo(src));
                return;
            }
            else if (cut >= hi) {
                // target slice falls into lower subslice
                if (output_full_src)
                    output_slice(sub_hi(src));
                mk_slice(sub_lo(src), hi, lo, out, output_full_src, output_base);
                return;
            }
            else {
                SASSERT(hi > cut && cut >= lo);
                // desired range spans over the cutpoint, so we get multiple slices in the result
                mk_slice(sub_hi(src), hi - cut - 1, 0, out, output_full_src, output_base);
                mk_slice(sub_lo(src), cut, lo, out, output_full_src, output_base);
                return;
            }
        }
        else {
            // [src.width-1, 0] has no subdivision yet
            if (width(src) - 1 > hi) {
                split(src, hi);
                SASSERT(!has_sub(sub_hi(src)));
                if (output_full_src)
                    out.push_back(sub_hi(src));
                mk_slice(sub_lo(src), hi, lo, out, output_full_src, output_base);  // recursive call to take care of case lo > 0
                return;
            }
            else {
                SASSERT(lo > 0);
                split(src, lo - 1);
                out.push_back(sub_hi(src));
                SASSERT(!has_sub(sub_lo(src)));
                if (output_full_src)
                    out.push_back(sub_lo(src));
                return;
            }
        }
        UNREACHABLE();
    }

    slicing::enode* slicing::mk_value_slice(rational const& val, unsigned bit_width) {
        SASSERT(0 <= val && val < rational::power_of_two(bit_width));
        app* a = m_bv->mk_numeral(val, bit_width);
        enode* s = find_or_alloc_enode(a, 0, nullptr, null_var);
        s->mark_interpreted();
        SASSERT(s->interpreted());
        SASSERT_EQ(get_value(s), val);
        return s;
    }

    rational slicing::get_value(enode* s) const {
        SASSERT(s->interpreted());
        rational val;
        VERIFY(try_get_value(s, val));
        return val;
    }

    bool slicing::try_get_value(enode* s, rational& val) const {
        return m_bv->is_numeral(s->get_expr(), val);
    }

    void slicing::begin_explain() {
        SASSERT(m_marked_lits.empty());
        SASSERT(m_marked_vars.empty());
    }

    void slicing::end_explain() {
        m_marked_lits.reset();
        m_marked_vars.reset();
    }

    void slicing::push_dep(void* dp, sat::literal_vector& out_lits, unsigned_vector& out_vars) {
        dep_t d = decode_dep(dp);
        if (d.is_var()) {
            pvar v = d.var();
            if (m_marked_vars.contains(v))
                return;
            m_marked_vars.insert(v);
            out_vars.push_back(v);
        }
        else if (d.is_lit()) {
            sat::literal lit = d.lit();
            if (m_marked_lits.contains(lit))
                return;
            m_marked_lits.insert(lit);
            out_lits.push_back(lit);
        }
        else {
            SASSERT(d.is_null());
        }
    }

    void slicing::explain_class(enode* x, enode* y, sat::literal_vector& out_lits, unsigned_vector& out_vars) {
        SASSERT_EQ(x->get_root(), y->get_root());
        SASSERT(m_tmp_justifications.empty());
        m_egraph.begin_explain();
        m_egraph.explain_eq(m_tmp_justifications, nullptr, x, y);
        m_egraph.end_explain();
        for (void* dp : m_tmp_justifications)
            push_dep(dp, out_lits, out_vars);
        m_tmp_justifications.reset();
    }

    void slicing::explain_equal(enode* x, enode* y, sat::literal_vector& out_lits, unsigned_vector& out_vars) {
        SASSERT(is_equal(x, y));
        enode_vector& xs = m_tmp2;
        enode_vector& ys = m_tmp3;
        SASSERT(xs.empty());
        SASSERT(ys.empty());
        xs.push_back(x);
        ys.push_back(y);
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            enode* const x = xs.back(); xs.pop_back();
            enode* const y = ys.back(); ys.pop_back();
            if (x == y)
                continue;
            if (width(x) == width(y)) {
                enode* const rx = x->get_root();
                enode* const ry = y->get_root();
                if (rx == ry)
                    explain_class(x, y, out_lits, out_vars);
                else {
                    xs.push_back(sub_hi(rx));
                    xs.push_back(sub_lo(rx));
                    ys.push_back(sub_hi(ry));
                    ys.push_back(sub_lo(ry));
                }
            }
            else if (width(x) > width(y)) {
                enode* const rx = x->get_root();
                xs.push_back(sub_hi(rx));
                xs.push_back(sub_lo(rx));
                ys.push_back(y);
            }
            else {
                SASSERT(width(x) < width(y));
                xs.push_back(x);
                enode* const ry = y->get_root();
                ys.push_back(sub_hi(ry));
                ys.push_back(sub_lo(ry));
            }
        }
        SASSERT(ys.empty());
    }

    void slicing::explain_equal(pvar x, pvar y, sat::literal_vector& out_lits, unsigned_vector& out_vars) {
        begin_explain();
        explain_equal(var2slice(x), var2slice(y), out_lits, out_vars);
        end_explain();
    }

    void slicing::explain(sat::literal_vector& out_lits, unsigned_vector& out_vars) {
        SASSERT(is_conflict());
        begin_explain();
        SASSERT(m_tmp_justifications.empty());
        m_egraph.begin_explain();
        if (m_disequality_conflict) {
            enode* eqn = m_disequality_conflict;
            SASSERT(eqn->is_equality());
            SASSERT_EQ(eqn->value(), l_false);
            SASSERT(eqn->get_lit_justification().is_external());
            SASSERT(m_ast.is_eq(eqn->get_expr()));
            SASSERT_EQ(eqn->get_arg(0)->get_root(), eqn->get_arg(1)->get_root());
            m_egraph.explain_eq(m_tmp_justifications, nullptr, eqn->get_arg(0), eqn->get_arg(1));
            push_dep(eqn->get_lit_justification().ext<void>(), out_lits, out_vars);
        }
        else {
            SASSERT(m_egraph.inconsistent());
            m_egraph.explain(m_tmp_justifications, nullptr);
        }
        m_egraph.end_explain();
        for (void* dp : m_tmp_justifications)
            push_dep(dp, out_lits, out_vars);
        m_tmp_justifications.reset();
        end_explain();
    }

    void slicing::egraph_on_propagate(enode* lit, enode* ante) {
        // ante may be set when symmetric equality is added by congruence
        if (ante)
            return;
        // on_propagate may be called before set_value
        if (lit->value() == l_undef)
            return;
        SASSERT(lit->is_equality());
        SASSERT_EQ(lit->value(), l_false);
        SASSERT(lit->get_lit_justification().is_external());
        m_disequality_conflict = lit;
    }

    bool slicing::can_propagate() const {
        return !m_needs_congruence.empty() || m_egraph.can_propagate();
    }

    void slicing::propagate() {
        // m_egraph.propagate();
        if (is_conflict())
            return;
        update_var_congruences();
        m_egraph.propagate();
    }

    bool slicing::merge_base(enode* s1, enode* s2, dep_t dep) {
        SASSERT_EQ(width(s1), width(s2));
        SASSERT(!has_sub(s1));
        SASSERT(!has_sub(s2));
        m_egraph.merge(s1, s2, encode_dep(dep));
        return !is_conflict();
    }

    bool slicing::merge(enode_vector& xs, enode_vector& ys, dep_t dep) {
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            enode* x = xs.back();
            enode* y = ys.back();
            xs.pop_back();
            ys.pop_back();
            if (has_sub(x)) {
                get_base(x, xs);
                x = xs.back();
                xs.pop_back();
            }
            if (has_sub(y)) {
                get_base(y, ys);
                y = ys.back();
                ys.pop_back();
            }
            SASSERT(!has_sub(x));
            SASSERT(!has_sub(y));
            if (width(x) == width(y)) {
                if (!merge_base(x, y, dep))
                    return false;
            }
            else if (width(x) > width(y)) {
                // need to split x according to y
                mk_slice(x, width(y) - 1, 0, xs, true);
                ys.push_back(y);
            }
            else {
                SASSERT(width(y) > width(x));
                // need to split y according to x
                mk_slice(y, width(x) - 1, 0, ys, true);
                xs.push_back(x);
            }
        }
        SASSERT(ys.empty());
        return true;
    }

    bool slicing::merge(enode_vector& xs, enode* y, dep_t dep) {
        enode_vector& ys = m_tmp2;
        SASSERT(ys.empty());
        ys.push_back(y);
        return merge(xs, ys, dep);  // will clear xs and ys
    }

    bool slicing::merge(enode* x, enode* y, dep_t dep) {
        SASSERT_EQ(width(x), width(y));
        if (!has_sub(x) && !has_sub(y))
            return merge_base(x, y, dep);
        enode_vector& xs = m_tmp2;
        enode_vector& ys = m_tmp3;
        SASSERT(xs.empty());
        SASSERT(ys.empty());
        xs.push_back(x);
        ys.push_back(y);
        return merge(xs, ys, dep);  // will clear xs and ys
    }

    bool slicing::is_equal(enode* x, enode* y) {
        SASSERT_EQ(width(x), width(y));
        x = x->get_root();
        y = y->get_root();
        if (x == y)
            return true;
        enode_vector& xs = m_tmp2;
        enode_vector& ys = m_tmp3;
        SASSERT(xs.empty());
        SASSERT(ys.empty());
        get_root_base(x, xs);
        get_root_base(y, ys);
        SASSERT(all_of(xs, [](enode* s) { return s->is_root(); }));
        SASSERT(all_of(ys, [](enode* s) { return s->is_root(); }));
        bool result = (xs == ys);
        xs.clear();
        ys.clear();
        return result;
    }

    template <bool should_get_root>
    void slicing::get_base_core(enode* src, enode_vector& out_base) const {
        enode_vector& todo = m_tmp1;
        SASSERT(todo.empty());
        todo.push_back(src);
        while (!todo.empty()) {
            enode* s = todo.back();
            todo.pop_back();
            if constexpr (should_get_root) {
                s = s->get_root();
            }
            if (!has_sub(s))
                out_base.push_back(s);
            else {
                todo.push_back(sub_lo(s));
                todo.push_back(sub_hi(s));
            }
        }
        SASSERT(todo.empty());
    }

    void slicing::get_base(enode* src, enode_vector& out_base) const {
        get_base_core<false>(src, out_base);
    }

    void slicing::get_root_base(enode* src, enode_vector& out_base) const {
        get_base_core<true>(src, out_base);
    }

    pvar slicing::mk_extract(enode* src, unsigned hi, unsigned lo) {
        enode_vector& slices = m_tmp3;
        SASSERT(slices.empty());
        mk_slice(src, hi, lo, slices, false, true);
        pvar v = null_var;
        // try to re-use variable of an existing slice
        if (slices.size() == 1)
            v = slice2var(slices[0]);
        // allocate new variable if we cannot reuse it
        if (v == null_var)
            v = m_solver.add_var(hi - lo + 1);
#if 0
        // slice didn't have a variable yet; so we can re-use it for the new variable
        // (we end up with a "phantom" enode that was first created for the variable)
        if (slices.size() == 1) {
            enode* s = slices[0];
            SASSERT_EQ(info(s).var, null_var);
            info(m_var2slice[v]).var = null_var;  // disconnect the "phantom" enode
            info(s).var = v;
            m_var2slice[v] = s;
        }
#endif
        // connect new variable
        VERIFY(merge(slices, var2slice(v), dep_t()));
        slices.reset();
        return v;
    }

    pvar slicing::mk_extract(pvar src, unsigned hi, unsigned lo) {
        extract_args args{src, hi, lo};
        auto it = m_extract_dedup.find_iterator(args);
        if (it != m_extract_dedup.end())
            return it->m_value;
        pvar const v = mk_extract(var2slice(src), hi, lo);
        m_extract_dedup.insert(args, v);
        m_extract_trail.push_back(args);
        m_trail.push_back(trail_item::mk_extract);
        return v;
    }

    void slicing::undo_mk_extract() {
        extract_args args = m_extract_trail.back();
        m_extract_trail.pop_back();
        m_extract_dedup.remove(args);
    }

    pvar slicing::mk_concat(unsigned num_args, pvar const* args) {
        NOT_IMPLEMENTED_YET();
        return null_var;
#if 0
        // v := p ++ q      (new variable of size |p| + |q|)
        // v[:|q|] = p
        // v[|q|:] = q
        unsigned const p_sz = p.power_of_2();
        unsigned const q_sz = q.power_of_2();
        unsigned const v_sz = p_sz + q_sz;
        if (p.is_val() && q.is_val()) {
            rational const val = p.val() * rational::power_of_two(q_sz) + q.val();
            return m_solver.sz2pdd(v_sz).mk_val(val);
        }
        if (p.is_val()) {
        }
        if (q.is_val()) {
        }
        pvar const v = m_solver.add_var(v_sz);
        enode_vector tmp;
        tmp.push_back(pdd2slice(p));
        tmp.push_back(pdd2slice(q));
        VERIFY(merge(tmp, var2slice(v), dep_t()));
        return m_solver.var(v);
#endif
    }

    pvar slicing::mk_concat(std::initializer_list<pvar> args) {
        return mk_concat(args.size(), args.begin());
    }

    void slicing::add_constraint(signed_constraint c) {
        SASSERT(!is_conflict());
        if (!c->is_eq())
            return;
        pdd const& p = c->to_eq();
        auto& m = p.manager();
        for (auto& [a, x] : p.linear_monomials()) {
            if (a != 1 && a != m.max_value())
                continue;
            pdd const body = a.is_one() ? (m.mk_var(x) - p) : (m.mk_var(x) + p);
            // c is either x = body or x != body, depending on polarity
            LOG("Equation from lit(" << c.blit() << ")  " << c << ":  v" << x << " = " << body);
            if (!add_equation(x, body, c.blit())) {
                SASSERT(is_conflict());
                return;
            }
            // without this check, when p = x - y we would handle both x = y and y = x separately
            if (body.is_unary())
                break;
        }
    }

    bool slicing::add_equation(pvar x, pdd const& body, sat::literal lit) {
        enode* const sx = var2slice(x);
        if (!lit.sign() && body.is_val()) {
            LOG("    simple assignment");
            // Simple assignment x = value
            enode* const sval = mk_value_slice(body.val(), body.power_of_2());
            return merge(sx, sval, lit);
        }
        pvar const y = m_solver.m_names.get_name(body);
        if (y == null_var) {
            LOG("    skip for now (unnamed body)");
            // TODO: register name trigger (if a name for value 'body' is created later, then merge x=y at that time)
            //      could also count how often 'body' was registered and introduce name when more than once.
            //      maybe better: register x as an existing name for 'body'? question is how to track the dependency on c.
            return true;
        }
        enode* const sy = var2slice(y);
        if (!lit.sign())
            return merge(sx, sy, lit);
        else {
            enode* n = find_or_alloc_disequality(sy, sx, lit);
            if (!m_disequality_conflict && is_equal(sx, sy)) {
                add_congruence_if_needed(x);
                add_congruence_if_needed(y);
                m_disequality_conflict = n;
                return false;
            }
        }
        return true;
    }

    void slicing::add_value(pvar v, rational const& val) {
        SASSERT(!is_conflict());
        enode* const sv = var2slice(v);
        enode* const sval = mk_value_slice(val, width(sv));
        (void)merge(sv, sval, v);
    }

    std::ostream& slicing::display(std::ostream& out) const {
        enode_vector base;
        for (pvar v = 0; v < m_var2slice.size(); ++v) {
            out << "v" << v << ":";
            base.reset();
            enode* const vs = var2slice(v);
            get_root_base(vs, base);
            for (enode* s : base)
                display(out << " ", s);
            if (has_value(vs->get_root()))
                out << "    [root_value: " << get_value(vs->get_root()) << "]";
            out << "\n";
        }
        return out;
    }

    std::ostream& slicing::display_tree(std::ostream& out) const {
        for (pvar v = 0; v < m_var2slice.size(); ++v) {
            out << "v" << v << ":\n";
            enode* const s = var2slice(v);
            display_tree(out, s, 4, width(s) - 1, 0);
        }
        out << m_egraph << "\n";
        return out;
    }

    std::ostream& slicing::display_tree(std::ostream& out, enode* s, unsigned indent, unsigned hi, unsigned lo) const {
        out << std::string(indent, ' ') << "[" << hi << ":" << lo << "]";
        out << " id=" << s->get_id();
        out << " w=" << width(s);
        if (!s->is_root())
            out << " root=" << s->get_root_id();
        if (has_value(s->get_root()))
            out << " root_value=" << get_value(s->get_root());
        out << "\n";
        if (has_sub(s)) {
            unsigned cut = info(s).cut;
            display_tree(out, sub_hi(s), indent + 4, hi, cut + 1 + lo);
            display_tree(out, sub_lo(s), indent + 4, cut + lo, lo);
        }
        return out;
    }

    std::ostream& slicing::display(std::ostream& out, enode* s) const {
        out << "{id:" << s->get_id() << ",w:" << width(s) << "}";
        return out;
    }

    bool slicing::invariant() const {
        VERIFY(m_tmp1.empty());
        VERIFY(m_tmp2.empty());
        VERIFY(m_tmp3.empty());
        for (enode* s : m_egraph.nodes()) {
            // we use equality enodes only to track disequalities
            if (s->is_equality())
                continue;
            // if the slice is equivalent to a variable, then the variable's slice is in the equivalence class
            pvar const v = slice2var(s);
            if (v != null_var) {
                VERIFY_EQ(var2slice(v)->get_root(), s->get_root());
            }
            // if slice has a value, it should be propagated to its sub-slices
            if (has_value(s)) {
                VERIFY(s->is_root());
                if (has_sub(s)) {
                    VERIFY(has_value(sub_hi(s)));
                    VERIFY(has_value(sub_lo(s)));
                }
            }
            // properties below only matter for representatives
            if (!s->is_root())
                continue;
            enode_vector s_base;
            get_base(s, s_base);
            for (enode* n : euf::enode_class(s)) {
                // equivalence class only contains slices of equal length
                VERIFY_EQ(width(s), width(n));
                // bases of equivalent nodes are equivalent
                enode_vector n_base;
                get_base(n, n_base);
                VERIFY_EQ(s_base.size(), n_base.size());
                for (unsigned i = s_base.size(); i-- > 0; ) {
                    VERIFY_EQ(s_base[i]->get_root(), n_base[i]->get_root());
                }
            }
        }
        return true;
    }

}
