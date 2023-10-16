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
- About the sub-slice sharing among equivalent nodes:
  - When extracting a variable y := x[h:l], we always need to create a new slice for y.
  - Merge slices for x[h:l] with y; store as dependency 'x[h:l]' (rather than 'null_dep' as we do now).
    - when merging, we must avoid that the new variable becomes the root of the equivalence class,
      because when finding dependencies for 'y := x[h:l]', such extraction-dependencies would be false/unnecessary.
      (alternatively, just ignore them. but we never *have* to have them as root, so just don't do it. but add assertions for 1. new var is not root, 2. no extraction-dependency when walking from 'x' to 'x[h:l]'.)
  - When encountering this dependency, need to start at slice for 'x' and walk towards 'x[h:l]',
    collecting dependencies whenever we move to a representative.
- when solver assigns value of a variable v, add equations with v substituted by its value?
    - since we only track equations over variables/names, this might not lead to many further additions
    - a question is how to track/handle the dependency on the assignment
- check Algorithm 2 of "Solving Bitvectors with MCSAT"; what is the difference to what we are doing now?
- track equalities such as x = -y ?
- on_merge could propagate values upwards:
    if slice has value but parent has no value, then check if sub_other(parent(s)) [sibling(s)?] has a value.
    if yes, can propagate value upwards. (add a congruence term to track deps properly?).
    we have to check the whole equivalence class, because the parents may be in different classes.
    it is enough to propagate values to variables. we could count (in the variable slice) the number of its base slices that are still unassigned.

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

    void* slicing::dep_t::encode() const {
        void* p = std::visit([](auto arg) -> void* {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, std::monostate>)
                return nullptr;
            else if constexpr (std::is_same_v<T, sat::literal>)
                return box<void>(arg.to_uint(), 1);
            else if constexpr (std::is_same_v<T, unsigned>)
                return box<void>(arg, 2);
            else
                static_assert(always_false_v<T>, "non-exhaustive visitor!");
        }, m_data);
        SASSERT(*this == decode(p));
        return p;
    }

    slicing::dep_t slicing::dep_t::decode(void* p) {
        if (!p)
            return {};
        unsigned tag = get_tag(p);
        SASSERT(tag == 1 || tag == 2);
        if (tag == 1)
            return dep_t(sat::to_literal(unbox<unsigned>(p)));
        else
            return dep_t(unbox<unsigned>(p));
    }

    std::ostream& slicing::display(std::ostream& out, dep_t d) const {
        if (d.is_null())
            out << "null";
        else if (d.is_value()) {
            out << "value(v" << get_dep_var(d) << " on slice " << get_dep_slice(d)->get_id();
            if (get_dep_lit(d) != sat::null_literal)
                out << " by literal " << get_dep_lit(d);
            out << ")";
        }
        else if (d.is_lit())
            out << "lit(" << d.lit() << ")";
        return out;
    }

    slicing::dep_t slicing::mk_var_dep(pvar v, enode* s, sat::literal lit) {
        SASSERT_EQ(m_dep_var.size(), m_dep_slice.size());
        SASSERT_EQ(m_dep_var.size(), m_dep_lit.size());
        unsigned const idx = m_dep_var.size();
        m_dep_var.push_back(v);
        m_dep_lit.push_back(lit);
        m_dep_slice.push_back(s);
        return dep_t(idx);
    }

    slicing::slicing(solver& s):
        m_solver(s),
        m_egraph(m_ast)
    {
        reg_decl_plugins(m_ast);
        m_bv = alloc(bv_util, m_ast);
        m_egraph.set_display_justification([&](std::ostream& out, void* dp) { display(out, dep_t::decode(dp)); });
        m_egraph.set_on_merge([&](enode* root, enode* other) { egraph_on_merge(root, other); });
        m_egraph.set_on_propagate([&](enode* lit, enode* ante) { egraph_on_propagate(lit, ante); });
        // m_egraph.set_on_make([&](enode* n) { egraph_on_make(n); });
    }

    slicing::slice_info& slicing::info(enode* n) {
        return const_cast<slice_info&>(std::as_const(*this).info(n));
    }

    slicing::slice_info const& slicing::info(enode* n) const {
        SASSERT(n);
        SASSERT(!n->is_equality());
        SASSERT(m_bv->is_bv_sort(n->get_sort()));
        slice_info const& i = m_info[n->get_id()];
        return i.slice ? info(i.slice) : i;
    }

    bool slicing::is_slice(enode* n) const {
        if (n->is_equality())
            return false;
        SASSERT(m_bv->is_bv_sort(n->get_sort()));
        slice_info const& i = m_info[n->get_id()];
        return !i.slice;
    }

    bool slicing::is_concat(enode* n) const {
        if (n->is_equality())
            return false;
        return !is_slice(n);
    }

    unsigned slicing::width(enode* s) const {
        SASSERT(!s->is_equality());
        return m_bv->get_bv_size(s->get_expr());
    }

    slicing::enode* slicing::sibling(enode* s) const {
        enode* p = parent(s);
        SASSERT(p);
        SASSERT(sub_lo(p) == s || sub_hi(p) == s);
        if (s != sub_hi(p))
            return sub_hi(p);
        else
            return sub_lo(p);
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
        LOG("push_scope");
        if (can_propagate())
            propagate();
        m_scopes.push_back(m_trail.size());
        m_egraph.push();
        m_dep_size_trail.push_back(m_dep_var.size());
        SASSERT(!use_var_congruences() || m_needs_congruence.empty());
    }

    void slicing::pop_scope(unsigned num_scopes) {
        LOG("pop_scope(" << num_scopes << ")");
        if (num_scopes == 0)
            return;
        unsigned const lvl = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned const target_lvl = lvl - num_scopes;
        unsigned const target_size = m_scopes[target_lvl];
        m_scopes.shrink(target_lvl);
        svector<trail_item> replay_trail;
        unsigned_vector replay_add_var_trail;
        svector<std::pair<extract_args, pvar>> replay_extract_trail;
        svector<concat_info> replay_concat_trail;
        unsigned num_replay_concat = 0;
        for (unsigned i = m_trail.size(); i-- > target_size; ) {
            switch (m_trail[i]) {
            case trail_item::add_var:
                replay_trail.push_back(trail_item::add_var);
                replay_add_var_trail.push_back(width(m_var2slice.back()));
                undo_add_var();
                break;
            case trail_item::split_core:
                undo_split_core();
                break;
            case trail_item::mk_extract: {
                replay_trail.push_back(trail_item::mk_extract);
                extract_args const& args = m_extract_trail.back();
                replay_extract_trail.push_back({args, m_extract_dedup[args]});
                undo_mk_extract();
                break;
            }
            case trail_item::mk_concat:
                replay_trail.push_back(trail_item::mk_concat);
                num_replay_concat++;
                break;
            case trail_item::set_value_node:
                undo_set_value_node();
                break;
            default:
                UNREACHABLE();
            }
        }
        m_egraph.pop(num_scopes);
        m_needs_congruence.reset();
        m_disequality_conflict = nullptr;
        m_dep_var.shrink(m_dep_size_trail[target_lvl]);
        m_dep_lit.shrink(m_dep_size_trail[target_lvl]);
        m_dep_slice.shrink(m_dep_size_trail[target_lvl]);
        m_dep_size_trail.shrink(target_lvl);
        m_trail.shrink(target_size);
        // replay add_var/mk_extract/mk_concat in the same order
        // (only until polysat::solver supports proper garbage collection of variables)
        unsigned add_var_idx = replay_add_var_trail.size();
        unsigned extract_idx = replay_extract_trail.size();
        unsigned concat_idx = m_concat_trail.size() - num_replay_concat;
        for (auto it = replay_trail.rbegin(); it != replay_trail.rend(); ++it) {
            switch (*it) {
            case trail_item::add_var: {
                unsigned const sz = replay_add_var_trail[--add_var_idx];
                add_var(sz);
                break;
            }
            case trail_item::mk_extract: {
                auto const [args, v] = replay_extract_trail[--extract_idx];
                replay_extract(args, v);
                break;
            }
            case trail_item::mk_concat: {
                NOT_IMPLEMENTED_YET();
                auto const ci = m_concat_trail[concat_idx++];
                num_replay_concat++;
                replay_concat(ci.num_args, &m_concat_args[ci.args_idx], ci.v);
                break;
            }
            default:
                UNREACHABLE();
            }
        }
        SASSERT(invariant());
    }

    void slicing::add_var(unsigned bit_width) {
        pvar const v = m_var2slice.size();
        enode* s = alloc_slice(bit_width, v);
        m_var2slice.push_back(s);
        m_trail.push_back(trail_item::add_var);
        LOG_V(10, "add_var: v" << v << " -> " << slice_pp(*this, s));
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
        auto j = euf::justification::external(dep_t(lit).encode());
        m_egraph.set_value(eqn, l_false, j);
        SASSERT(eqn->is_equality());
        SASSERT_EQ(eqn->value(), l_false);
        return eqn;
    }

    void slicing::egraph_on_make(enode* n) {
        LOG("on_make: " << e_pp(n));
    }

    slicing::enode* slicing::alloc_enode(expr* e, unsigned num_args, enode* const* args, pvar var) {
        SASSERT(!m_egraph.find(e));
        // NOTE: sometimes egraph::mk already triggers a merge due to congruence.
        //       in this case we have to make sure to allocate m_info early enough.
        unsigned const id = e->get_id();
        m_info.reserve(id + 1);
        slice_info& i = m_info[id];
        i.reset();
        i.var = var;
        enode* n = m_egraph.mk(e, 0, num_args, args);  // NOTE: the egraph keeps a strong reference to 'e'
        LOG_V(10, "alloc_enode: " << slice_pp(*this, n) << " " << e_pp(n));
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
        app_ref a(m_ast.mk_fresh_const("s", m_bv->mk_sort(width), false), m_ast);
        return alloc_enode(a, 0, nullptr, var);
    }

    slicing::enode* slicing::mk_concat_node(enode_vector const& slices) {
        return mk_concat_node(slices.size(), slices.data());
    }

    slicing::enode* slicing::mk_concat_node(unsigned num_slices, enode* const* slices) {
        ptr_vector<expr> args;
        for (unsigned i = 0; i < num_slices; ++i)
            args.push_back(slices[i]->get_expr());
        app_ref a(m_ast.mk_app(mk_concat_decl(args), args), m_ast);
        return find_or_alloc_enode(a, num_slices, slices, null_var);
    }

    void slicing::add_concat_node(enode* s, enode* concat) {
        SASSERT(slice2var(s) != null_var);  // all concat nodes should point to a variable node
        SASSERT(is_app(concat->get_expr()));
        slice_info& concat_info = m_info[concat->get_id()];
        if (s->get_root() == concat->get_root()) {
            SASSERT_EQ(s, concat_info.slice);
            return;
        }
        SASSERT(!concat_info.slice);  // not yet set
        concat_info.slice = s;
        egraph_merge(s, concat, dep_t());
    }

    void slicing::add_var_congruence(pvar v) {
        enode_vector& base = m_tmp2;
        SASSERT(base.empty());
        enode* sv = var2slice(v);
        get_base(sv, base);
        // Add equation v == concat(s1, ..., sn)
        add_concat_node(sv, mk_concat_node(base));
        base.clear();
    }

    void slicing::add_var_congruence_if_needed(pvar v) {
        if (!m_needs_congruence.contains(v))
            return;
        m_needs_congruence.remove(v);
        add_var_congruence(v);
    }

    void slicing::update_var_congruences() {
        if (!use_var_congruences())
            return;
        // TODO: this is only needed once per equivalence class
        //          (mark root of var2slice to detect duplicates?)
        for (pvar v : m_needs_congruence)
            add_var_congruence(v);
        m_needs_congruence.reset();
    }

    bool slicing::use_var_congruences() const {
        return m_solver.config().m_slicing_congruence;
    }

    // split a single slice without updating any equivalences
    void slicing::split_core(enode* s, unsigned cut) {
        SASSERT(is_slice(s));  // this action only makes sense for slices
        SASSERT(!has_sub(s));
        SASSERT(info(s).sub_hi == nullptr && info(s).sub_lo == nullptr);
        SASSERT(width(s) > cut + 1);
        unsigned const width_hi = width(s) - cut - 1;
        unsigned const width_lo = cut + 1;
        enode* sub_hi;
        enode* sub_lo;
        if (is_value(s)) {
            rational const val = get_value(s);
            sub_hi = mk_value_slice(machine_div2k(val, width_lo), width_hi);
            sub_lo = mk_value_slice(mod2k(val, width_lo), width_lo);
        }
        else {
            sub_hi = alloc_slice(width_hi);
            sub_lo = alloc_slice(width_lo);
        }
        SASSERT(!parent(sub_hi));
        SASSERT(!parent(sub_lo));
        info(sub_hi).parent = s;
        info(sub_lo).parent = s;
        info(s).set_cut(cut, sub_hi, sub_lo);
        m_trail.push_back(trail_item::split_core);
        m_enode_trail.push_back(s);
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
        enode* s = m_enode_trail.back();
        m_enode_trail.pop_back();
        info(s).set_cut(null_cut, nullptr, nullptr);
    }

    void slicing::split(enode* s, unsigned cut) {
        // this action only makes sense for base slices.
        // a base slice is never equivalent to a congruence node.
        SASSERT(is_slice(s));
        SASSERT(!has_sub(s));
        SASSERT(cut != null_cut);
        // split all slices in the equivalence class
        for (enode* n : euf::enode_class(s))
            split_core(n, cut);
        // propagate equivalences to subslices
        for (enode* n : euf::enode_class(s)) {
            enode* target = n->get_target();
            if (!target)
                continue;
            euf::justification const j = n->get_justification();
            SASSERT(j.is_external());  // cannot be a congruence since the slice wasn't split before.
            dep_t const d = dep_t::decode(j.ext<void>());
            egraph_merge(sub_hi(n), sub_hi(target), d);
            egraph_merge(sub_lo(n), sub_lo(target), d);
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
        SASSERT(bit_width > 0);
        SASSERT(0 <= val && val < rational::power_of_two(bit_width));
        sort* bv_sort = m_bv->mk_sort(bit_width);
        func_decl_ref f(m_ast.mk_fresh_func_decl("val", nullptr, 1, &bv_sort, bv_sort, false), m_ast);
        app_ref a(m_ast.mk_app(f, m_bv->mk_numeral(val, bit_width)), m_ast);
        enode* s = alloc_enode(a, 0, nullptr, null_var);
        set_value_node(s, s);
        SASSERT_EQ(get_value(s), val);
        return s;
    }

    slicing::enode* slicing::mk_interpreted_value_node(enode* s) {
        SASSERT(is_value(s));
        // NOTE: how this is used now, the node will not yet be contained in the egraph.
        enode* n = alloc_enode(s->get_app()->get_arg(0), 0, nullptr, null_var);
        info(n).value_node = s;
        n->mark_interpreted();
        SASSERT(n->interpreted());
        SASSERT_EQ(get_value_node(n), s);
        return n;
    }

    bool slicing::is_value(enode* n) const {
        SASSERT(is_app(n->get_expr()));  // we only create app nodes at the moment; if this fails just return false here.
        app* a = n->get_app();
        return a->get_num_args() == 1 && m_bv->is_numeral(a->get_arg(0));
    }

    rational slicing::get_value(enode* s) const {
        SASSERT(is_value(s));
        rational val;
        VERIFY(try_get_value(s, val));
        return val;
    }

    bool slicing::try_get_value(enode* s, rational& val) const {
        if (!s)
            return false;
        app* a = s->get_app();
        if (a->get_num_args() != 1)
            return false;
        bool const ok = m_bv->is_numeral(a->get_arg(0), val);
        SASSERT_EQ(ok, is_value(s));
        return ok;
    }

    void slicing::explain_class(enode* x, enode* y, ptr_vector<void>& out_deps) {
        SASSERT_EQ(x->get_root(), y->get_root());
        m_egraph.begin_explain();
        m_egraph.explain_eq(out_deps, nullptr, x, y);
        m_egraph.end_explain();
    }

    void slicing::explain_equal(enode* x, enode* y, ptr_vector<void>& out_deps) {
        SASSERT(is_equal(x, y));
        SASSERT_EQ(width(x), width(y));
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
                    explain_class(x, y, out_deps);
                else {
                    xs.push_back(sub_hi(x));
                    xs.push_back(sub_lo(x));
                    ys.push_back(sub_hi(y));
                    ys.push_back(sub_lo(y));
                }
            }
            else if (width(x) > width(y)) {
                xs.push_back(sub_hi(x));
                xs.push_back(sub_lo(x));
                ys.push_back(y);
            }
            else {
                SASSERT(width(x) < width(y));
                xs.push_back(x);
                ys.push_back(sub_hi(y));
                ys.push_back(sub_lo(y));
            }
        }
        SASSERT(ys.empty());
    }

    void slicing::explain_equal(pvar x, pvar y, ptr_vector<void>& out_deps) {
        explain_equal(var2slice(x), var2slice(y), out_deps);
    }

    void slicing::explain_equal(pvar x, pvar y, std::function<void(sat::literal)> const& on_lit) {
        SASSERT(m_marked_lits.empty());
        SASSERT(m_tmp_deps.empty());
        explain_equal(x, y, m_tmp_deps);
        for (void* dp : m_tmp_deps) {
            dep_t const d = dep_t::decode(dp);
            if (d.is_null())
                continue;
            if (d.is_lit()) {
                sat::literal lit = d.lit();
                if (m_marked_lits.contains(lit))
                    continue;
                m_marked_lits.insert(lit);
                on_lit(d.lit());
            }
            else {
                // equivalence between to variables cannot be due to value assignment
                UNREACHABLE();
            }
        }
        m_marked_lits.reset();
        m_tmp_deps.reset();
    }

    void slicing::explain(ptr_vector<void>& out_deps) {
        SASSERT(is_conflict());
        m_egraph.begin_explain();
        if (m_disequality_conflict) {
            LOG("Disequality conflict: " << m_disequality_conflict);
            enode* eqn = m_disequality_conflict;
            SASSERT(eqn->is_equality());
            SASSERT_EQ(eqn->value(), l_false);
            SASSERT(eqn->get_lit_justification().is_external());
            SASSERT(m_ast.is_eq(eqn->get_expr()));
            SASSERT_EQ(eqn->get_arg(0)->get_root(), eqn->get_arg(1)->get_root());
            m_egraph.explain_eq(out_deps, nullptr, eqn->get_arg(0), eqn->get_arg(1));
            out_deps.push_back(eqn->get_lit_justification().ext<void>());
        }
        else {
            SASSERT(m_egraph.inconsistent());
            m_egraph.explain(out_deps, nullptr);
        }
        m_egraph.end_explain();
    }

    clause_ref slicing::build_conflict_clause() {
        LOG_H1("slicing: build_conflict_clause");
        // display_tree(std::cerr);
        SASSERT(invariant());
        SASSERT(is_conflict());
        SASSERT(m_marked_lits.empty());
        SASSERT(m_tmp_deps.empty());
        explain(m_tmp_deps);
        clause_builder cb(m_solver, "slicing");
        pvar x = null_var; enode* sx = nullptr;
        pvar y = null_var; enode* sy = nullptr;
        for (void* dp : m_tmp_deps) {
            dep_t const d = dep_t::decode(dp);
            if (d.is_null())
                continue;
            if (d.is_lit()) {
                sat::literal const lit = d.lit();
                if (m_marked_lits.contains(lit))
                    continue;
                m_marked_lits.insert(lit);
                LOG("Premise:    " << lit_pp(m_solver, lit));
                cb.insert(~lit);
            }
            else {
                SASSERT(d.is_value());
                pvar const v = get_dep_var(d);
                enode* const sv = get_dep_slice(d);
                if (x == null_var)
                    x = v, sx = sv;
                else if (y == null_var)
                    y = v, sy = sv;
                else {
                    // pvar justifications are only introduced by add_value, i.e., when a variable is assigned in the solver.
                    // thus there can be at most two pvar justifications in a single conflict.
                    UNREACHABLE();
                }
                sat::literal lit = get_dep_lit(d);
                if (lit != sat::null_literal) {
                    LOG("Premise:    " << lit_pp(m_solver, lit));
                    cb.insert(~lit);
                }
            }
        }
        m_marked_lits.reset();
        m_tmp_deps.reset();
        if (x != null_var) LOG("Variable v" << x << " with slice " << slice_pp(*this, sx));
        if (y != null_var) LOG("Variable v" << y << " with slice " << slice_pp(*this, sy));
        // SASSERT(x != null_var || y == null_var);
        // SASSERT(y != null_var || x == null_var);

        // Algorithm 1 in BitvectorsMCSAT
        signed_constraint c;
        if (x == null_var) {
            /* nothing to do */
            SASSERT_EQ(y, null_var);
        }
        else if (y == null_var) {
            SASSERT(get_value_node(sx));
            unsigned hi, lo;
            VERIFY(find_range_in_ancestor(sx, var2slice(x), hi, lo));
            LOG("Variable v" << x << " has solver-value " << m_solver.get_value(x));
            LOG("Subslice v" << x << "[" << hi << ":" << lo << "] has value " << get_value(get_value_node(sx)));
            UNREACHABLE();
            /*
            // the egraph has derived that x (or a sub-slice thereof) must have value b that differs from the currently assigned value of x.
            // the explanation is:      lits ==> x[...] = b
            enode* const xn = var2slice(x)->get_root();
            if (false && is_value(xn)) {
                // TODO: clause may be unsound if the premises only imply equality of subslices; may need a separate explain-query here.
                c = m_solver.eq(m_solver.var(x), get_value(xn));
            }
            else {
                // The conflict is only for a sub-slice x[hi:lo].
                // We need to create some literal that sets the bits x[hi:lo] to b.
                SASSERT(!is_value(xn));
                unsigned hi, lo;
                VERIFY(find_range_in_ancestor(sx, var2slice(x), hi, lo));
                LOG("Variable v" << x << " has solver-value " << m_solver.get_value(x));
                LOG("Subslice v" << x << "[" << hi << ":" << lo << "] has value " << get_value(get_value_node(sx)));
                rational const b = get_value(get_value_node(sx));
                // TODO: problematic case when this assertion is violated:
                // 1. v3 := v2[0:0]
                // 2. propagate value assignment v2 := 1 from some other constraints.
                // 3. propagate constraint v3 == 0.
                // In this case we want the value from the constraint v3==0 rather from sx (how to access it?)
                // (maybe constraints like v3 == 0 should be handled more like assignments?)
                SASSERT(b != mod2k(machine_div2k(m_solver.get_value(x), lo), hi - lo + 1));
                if (!lo) {
                    // x[hi:0] = b
                    // <==>
                    // 2^(N-1-hi) x = 2^(N-1-hi) b      where N = |x|
                    unsigned const N = m_solver.var2pdd(x).power_of_2();
                    rational const coeff = rational::power_of_two(N - 1 - hi);
                    c = m_solver.eq(coeff * m_solver.var(x), coeff * b);
                }
                else {
                    pvar const xx = mk_extract(x, hi, lo);
                    SASSERT_EQ(sx->get_root(), var2slice(xx)->get_root());
                    c = m_solver.eq(m_solver.var(xx), b);
                    // TODO: how does this clause actually help with search?
                    //      ==> need a constraint that will set the corresponding fixed bits of x.
                    //          for this, we need to track/propagate fixed bits across equivalence classes.
                    //          (could also introduce a constraint type that assigns a sub-range of a variable?)
                    //          otherwise, we will generate tautologies in this branch.
                }
            }
            */
        }
        else {
            display_tree(std::cout);
            SASSERT(y != null_var);
            SASSERT(x != y);
            SASSERT(get_value_node(sx));
            SASSERT(get_value_node(sy));
            unsigned x_hi, x_lo, y_hi, y_lo;
            VERIFY(find_range_in_ancestor(sx, var2slice(x), x_hi, x_lo));
            VERIFY(find_range_in_ancestor(sy, var2slice(y), y_hi, y_lo));
            LOG("find_range_in_ancestor: v" << x << "[" << x_hi << ":" << x_lo << "] = " << slice_pp(*this, sx) << ", slice-value " << get_value(get_value_node(sx)));
            LOG("find_range_in_ancestor: v" << y << "[" << y_hi << ":" << y_lo << "] = " << slice_pp(*this, sy) << ", slice-value " << get_value(get_value_node(sy)));
            if (m_solver.is_assigned(x)) {
                rational sval = mod2k(machine_div2k(m_solver.get_value(x), x_lo), x_hi - x_lo + 1);
                LOG("Variable v" << x << " has solver-value " << m_solver.get_value(x) << ", i.e., v" << x << "[" << x_hi << ":" << x_lo << "] = " << sval);
            }
            if (m_solver.is_assigned(y)) {
                rational sval = mod2k(machine_div2k(m_solver.get_value(y), y_lo), y_hi - y_lo + 1);
                LOG("Variable v" << y << " has solver-value " << m_solver.get_value(y) << ", i.e., v" << y << "[" << y_hi << ":" << y_lo << "] = " << sval);
            }

            std::abort();
            // below is TODO


            // LOG("Slice sx=" << slice_pp(*this, sx) << " has value " << get_value(get_value_node(sx)));
            // LOG("Slice sy=" << slice_pp(*this, sy) << " has value " << get_value(get_value_node(sy)));
            // the egraph has derived that x (or a subslice of x) must be equal to y (or a subslice of y),
            // but the currently assigned values differ.
            // the explanation is:      lits ==> x[...] = y[...]
            if (false && is_equal(var2slice(x), var2slice(y))) {
                // don't need to introduce subslices if the variables themselves are already equal
                // TODO: but clause may be unsound if the premises only imply equality of subslices; may need a separate explain-query here.
                c = m_solver.eq(m_solver.var(x), m_solver.var(y));
            }
            else if (sx == sy) {
                // two assignments to the same slice but coming from different variables.
                // TODO: this case is impossible once we properly track/propagate fixed bits on slices, because viable-with-fixed-bits will exclude conflicting values upfront.
                //      (it is also hard and probably not useful to handle otherwise)

                // we handle one special case for now
                if (sx->get_root() == var2slice(x)->get_root() && m_solver.get_value(x) != get_value(get_value_node(var2slice(x)))) {
                    LOG("Variable v" << x << " has solver-value " << m_solver.get_value(x) << " and slicing-value " << get_value(get_value_node(var2slice(x))));
                    // here, the learned clause should be   y = value(y)  ==>  x = slicing-value(x)
                    signed_constraint d = m_solver.eq(m_solver.var(y), m_solver.get_value(y));
                    LOG("Premise:    " << lit_pp(m_solver, d));
                    cb.insert_eval(~d);
                    c = m_solver.eq(m_solver.var(x), get_value(get_value_node(sx)));
                }
            }
            else {
                unsigned x_hi, x_lo, y_hi, y_lo;
                VERIFY(find_range_in_ancestor(sx, var2slice(x), x_hi, x_lo));
                VERIFY(find_range_in_ancestor(sy, var2slice(y), y_hi, y_lo));
                pvar const xx = mk_extract(x, x_hi, x_lo);
                pvar const yy = mk_extract(y, y_hi, y_lo);
                SASSERT_EQ(sx->get_root(), var2slice(xx)->get_root());
                SASSERT_EQ(sy->get_root(), var2slice(yy)->get_root());
                LOG("find_range_in_ancestor: v" << x << "[" << x_hi << ":" << x_lo << "] = " << slice_pp(*this, sx) << "   --> represented by variable v" << xx);
                LOG("find_range_in_ancestor: v" << y << "[" << y_hi << ":" << y_lo << "] = " << slice_pp(*this, sy) << "   --> represented by variable v" << yy);
                SASSERT(xx != yy);
                c = m_solver.eq(m_solver.var(xx), m_solver.var(yy));
            }
        }
        SASSERT(x == null_var || c);
        if (c) {
            LOG("Conclusion: " << lit_pp(m_solver, c));
            cb.insert_eval(c);
        } else {
            LOG("Conclusion: <conflict>");
        }

        std::abort();
        return cb.build();
    }

    void slicing::explain_value(enode* s, std::function<void(sat::literal)> const& on_lit, std::function<void(pvar)> const& on_var) {
        SASSERT(invariant());
        SASSERT(m_marked_lits.empty());

        enode* n = get_value_node(s);
        SASSERT(is_value(n));

        SASSERT(m_tmp_deps.empty());
        explain_equal(s, n, m_tmp_deps);

        for (void* dp : m_tmp_deps) {
            dep_t const d = dep_t::decode(dp);
            if (d.is_null())
                continue;
            if (d.is_lit())
                on_lit(d.lit());
            else {
                SASSERT(d.is_value());
                if (get_dep_lit(d) == sat::null_literal)
                    on_var(get_dep_var(d));
                else
                    on_lit(get_dep_lit(d));
            }
        }
        m_tmp_deps.reset();
    }

    void slicing::explain_value(pvar v, std::function<void(sat::literal)> const& on_lit, std::function<void(pvar)> const& on_var) {
        explain_value(var2slice(v), on_lit, on_var);
    }

    bool slicing::find_range_in_ancestor(enode* s, enode* a, unsigned& out_hi, unsigned& out_lo) {
        out_hi = width(s) - 1;
        out_lo = 0;
        while (true) {
            if (s == a)
                return true;
            enode* p = parent(s);
            if (!p)
                return false;
            if (s == sub_hi(p)) {
                unsigned offset = 1 + info(p).cut;
                out_hi += offset;
                out_lo += offset;
            }
            else {
                SASSERT_EQ(s, sub_lo(p));
                /* range stays unchanged */
            }
            s = p;
        }
    }

    bool slicing::is_extract(pvar x, pvar src, unsigned& out_hi, unsigned& out_lo) {
        return find_range_in_ancestor(var2slice(x), var2slice(src), out_hi, out_lo);
    }

    void slicing::egraph_on_merge(enode* root, enode* other) {
        LOG("on_merge: root " << slice_pp(*this, root) << "other " << slice_pp(*this, other));
        if (root->interpreted())
            return;
        SASSERT(!other->interpreted());  // by convention, interpreted nodes are always chosen as root
        SASSERT(root != other);
        SASSERT_EQ(root, root->get_root());
        SASSERT_EQ(root, other->get_root());

        enode* v1 = info(root).value_node;   // root is the root
        enode* v2 = info(other).value_node;  // 'other' was its own root before the merge
        if (v1 && v2 && get_value(v1) != get_value(v2)) {
            // we have a conflict. add interpreted enodes to make the egraph realize it.
            enode* i1 = mk_interpreted_value_node(v1);
            enode* i2 = mk_interpreted_value_node(v2);
            m_egraph.merge(i1, v1, dep_t().encode());
            m_egraph.merge(i2, v2, dep_t().encode());
            SASSERT(is_conflict());
            return;
        }

        if (v1 || v2) {
            if (!v1) set_value_node(root, v2);
            if (!v2) set_value_node(other, v1);
            rational const val = get_value(v1 ? v1 : v2);
            for (enode* n : euf::enode_class(other)) {
                pvar const v = slice2var(n);
                if (v == null_var)
                    continue;
                if (m_solver.is_assigned(v))
                    continue;
                LOG("on_merge: v" << v << " := " << val);
                m_solver.assign_propagate_by_slicing(v, val);
            }
        }
    }

    void slicing::set_value_node(enode* s, enode* value_node) {
        SASSERT(!info(s).value_node);
        SASSERT(is_value(value_node));
        info(s).value_node = value_node;
        if (s != value_node) {
            m_trail.push_back(trail_item::set_value_node);
            m_enode_trail.push_back(s);
        }
    }

    void slicing::undo_set_value_node() {
        enode* s = m_enode_trail.back();
        m_enode_trail.pop_back();
        info(s).value_node = nullptr;
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
        if (use_var_congruences() && !m_needs_congruence.empty())
            return true;
        return m_egraph.can_propagate();
    }

    void slicing::propagate() {
        // m_egraph.propagate();
        if (is_conflict())
            return;
        update_var_congruences();
        m_egraph.propagate();
    }

    bool slicing::egraph_merge(enode* s1, enode* s2, dep_t dep) {
        LOG("egraph_merge: " << slice_pp(*this, s1) << " and " << slice_pp(*this, s2));
        SASSERT_EQ(width(s1), width(s2));
        enode* v1 = get_value_node(s1);
        enode* v2 = get_value_node(s2);
        if (v1 && v2 && get_value(v1) == get_value(v2)) {
            // optimization: if s1, s2 are already equivalent to the same value,
            // then they could have been merged already and we do not need to record 'dep'.
            // merge the value slices instead.
            m_egraph.merge(v1, v2, dep_t().encode());
            return !is_conflict();
        }
        if (dep.is_value()) {
            if (is_value(s1))
                std::swap(s1, s2);
            SASSERT(is_value(s2));
            SASSERT(!is_value(s1));  // we never merge two value slices directly
            if (get_dep_slice(dep) != s1)
                dep = mk_var_dep(get_dep_var(dep), s1, get_dep_lit(dep));
        }
        m_egraph.merge(s1, s2, dep.encode());
        return !is_conflict();
    }

    bool slicing::merge_base(enode* s1, enode* s2, dep_t dep) {
        SASSERT(!has_sub(s1));
        SASSERT(!has_sub(s2));
        return egraph_merge(s1, s2, dep);
    }

    bool slicing::merge(enode_vector& xs, enode_vector& ys, dep_t dep) {
        while (!xs.empty()) {
            SASSERT(!ys.empty());
            enode* const x = xs.back();
            enode* const y = ys.back();
            xs.pop_back();
            ys.pop_back();
            if (x == y)
                continue;
            if (x->get_root() == y->get_root()) {
                DEBUG_CODE({
                    // invariant: parents merged => base slices merged
                    enode_vector const x_base = get_base(x);
                    enode_vector const y_base = get_base(y);
                    SASSERT_EQ(x_base.size(), y_base.size());
                    for (unsigned i = x_base.size(); i-- > 0; ) {
                        SASSERT_EQ(x_base[i]->get_root(), y_base[i]->get_root());
                    }
                });
                continue;
            }
#if 0
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
                if (!merge_base(x, y, dep)) {
                    xs.clear();
                    ys.clear();
                    return false;
                }
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
#else
            if (width(x) == width(y)) {
                // We may merge slices if at least one of them doesn't have a subslice yet,
                // because in that case all intermediate cut points will be aligned.
                // NOTE: it is necessary to merge intermediate slices for value nodes, to ensure downward propagation of assignments.
                bool const should_merge = (!has_sub(x) || !has_sub(y));
                // If either slice has a subdivision, we have to cut the other and advance to subslices
                if (has_sub(x) || has_sub(y)) {
                    if (!has_sub(x))
                        split(x, get_cut(y));
                    if (!has_sub(y))
                        split(y, get_cut(x));
                    xs.push_back(sub_hi(x));
                    xs.push_back(sub_lo(x));
                    ys.push_back(sub_hi(y));
                    ys.push_back(sub_lo(y));
                }
                // We may only merge intermediate nodes after we're done with splitting (since we currently split the whole equivalence class at once)
                if (should_merge) {
                    if (!egraph_merge(x, y, dep)) {
                        xs.clear();
                        ys.clear();
                        return false;
                    }
                }
            }
            else if (width(x) > width(y)) {
                if (!has_sub(x))
                    split(x, width(y) - 1);
                    // split(x, has_sub(y) ? get_cut(y) : (width(y) - 1));
                xs.push_back(sub_hi(x));
                xs.push_back(sub_lo(x));
                ys.push_back(y);
            }
            else {
                SASSERT(width(y) > width(x));
                if (!has_sub(y))
                    split(y, width(x) - 1);
                    // split(y, has_sub(x) ? get_cut(x) : (width(x) - 1));
                ys.push_back(sub_hi(y));
                ys.push_back(sub_lo(y));
                xs.push_back(x);
            }
#endif
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
        LOG("merge: " << slice_pp(*this, x) << " and " << slice_pp(*this, y));
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
        on_scope_exit clear_vectors([&xs, &ys](){
            xs.clear();
            ys.clear();
        });
        // TODO: we don't always have to collect the full base if intermediate nodes are already equal
        get_base(x, xs);
        get_base(y, ys);
        if (xs.size() != ys.size())
            return false;
        for (unsigned i = xs.size(); i-- > 0; )
            if (xs[i]->get_root() != ys[i]->get_root())
                return false;
        return true;
    }

    void slicing::get_base(enode* src, enode_vector& out_base) const {
        enode_vector& todo = m_tmp1;
        SASSERT(todo.empty());
        todo.push_back(src);
        while (!todo.empty()) {
            enode* s = todo.back();
            todo.pop_back();
            if (!has_sub(s))
                out_base.push_back(s);
            else {
                todo.push_back(sub_lo(s));
                todo.push_back(sub_hi(s));
            }
        }
        SASSERT(todo.empty());
    }

    slicing::enode_vector slicing::get_base(enode* src) const {
        enode_vector out;
        get_base(src, out);
        return out;
    }

    pvar slicing::mk_extract(enode* src, unsigned hi, unsigned lo, pvar replay_var) {
        LOG("mk_extract: src=" << slice_pp(*this, src) << " hi=" << hi << " lo=" << lo);
        enode_vector& slices = m_tmp3;
        SASSERT(slices.empty());
        mk_slice(src, hi, lo, slices, false, false);
        pvar v = null_var;
        // try to re-use variable of an existing slice
        if (slices.size() == 1)
            v = slice2var(slices[0]);
        if (replay_var != null_var && v != replay_var) {
            // replayed variable should be 'fresh', unless it was a re-used variable
            enode* s = var2slice(replay_var);
            SASSERT(s->is_root());
            SASSERT_EQ(s->class_size(), 1);
            SASSERT(!has_sub(s));
            SASSERT_EQ(width(s), hi - lo + 1);
            v = replay_var;
        }
        // allocate new variable if we cannot reuse it
        if (v == null_var) {
            v = m_solver.add_var(hi - lo + 1, pvar_kind::internal);
#if 1
            // slice didn't have a variable yet; so we can re-use it for the new variable
            // (we end up with a "phantom" enode that was first created for the variable)
            if (slices.size() == 1) {
                enode* s = slices[0];
                LOG("re-using slice " << slice_pp(*this, s) << " for new variable v" << v);
                // display_tree(std::cerr, s, 0, hi, lo);
                SASSERT_EQ(info(s).var, null_var);
                info(m_var2slice[v]).var = null_var;  // disconnect the "phantom" enode
                info(s).var = v;
                m_var2slice[v] = s;
            }
#endif
        }
        // connect new variable
        VERIFY(merge(slices, var2slice(v), dep_t()));
        slices.reset();
        return v;
    }

    void slicing::replay_extract(extract_args const& args, pvar r) {
        LOG("replay_extract");
        SASSERT(r != null_var);
        SASSERT(!m_extract_dedup.contains(args));
        VERIFY_EQ(mk_extract(var2slice(args.src), args.hi, args.lo, r), r);
        m_extract_dedup.insert(args, r);
        m_extract_trail.push_back(args);
        m_trail.push_back(trail_item::mk_extract);
    }

    pvar slicing::mk_extract(pvar src, unsigned hi, unsigned lo) {
        LOG_H3("mk_extract: v" << src << "[" << hi << ":" << lo << "]     size(v" << src << ") = " << m_solver.size(src));
        if (m_solver.size(src) == hi - lo + 1)
            return src;
        extract_args args{src, hi, lo};
        auto it = m_extract_dedup.find_iterator(args);
        if (it != m_extract_dedup.end())
            return it->m_value;
        pvar const v = mk_extract(var2slice(src), hi, lo);
        m_extract_dedup.insert(args, v);
        m_extract_trail.push_back(args);
        m_trail.push_back(trail_item::mk_extract);
        LOG("mk_extract: v" << src << "[" << hi << ":" << lo << "] = v" << v);
        return v;
    }

    void slicing::undo_mk_extract() {
        extract_args args = m_extract_trail.back();
        m_extract_trail.pop_back();
        m_extract_dedup.remove(args);
    }

    pvar slicing::mk_concat(unsigned num_args, pvar const* args, pvar replay_var) {
        enode_vector& slices = m_tmp3;
        SASSERT(slices.empty());
        unsigned total_width = 0;
        for (unsigned i = 0; i < num_args; ++i) {
            enode* s = var2slice(args[i]);
            slices.push_back(s);
            total_width += width(s);
        }
        // NOTE: we use concat nodes to deduplicate (syntactically equal) concat expressions.
        //       we might end up reusing variables that are not introduced by mk_concat (if we enable the variable re-use optimization in mk_extract),
        //       but because such congruence nodes are only added over direct descendants, we do not get unwanted dependencies from this re-use.
        //       (but note that the nodes from mk_concat are not only over direct descendants)
        enode* concat = mk_concat_node(slices);
        pvar v = slice2var(concat);
        if (v != null_var)
            return v;
        if (replay_var != null_var) {
            // replayed variable should be 'fresh'
            enode* s = var2slice(replay_var);
            SASSERT(s->is_root());
            SASSERT_EQ(s->class_size(), 1);
            SASSERT(!has_sub(s));
            SASSERT_EQ(width(s), total_width);
            v = replay_var;
        }
        else
            v = m_solver.add_var(total_width, pvar_kind::internal);
        enode* sv = var2slice(v);
        VERIFY(merge(slices, sv, dep_t()));
        // NOTE: add_concat_node must be done after merge to preserve the invariant: "a base slice is never equivalent to a congruence node".
        add_concat_node(sv, concat);
        slices.reset();

        // don't mess with the concat_trail during replay
        if (replay_var == null_var) {
            concat_info ci;
            ci.v = v;
            ci.num_args = num_args;
            ci.args_idx = m_concat_args.size();
            m_concat_trail.push_back(ci);
            for (unsigned i = 0; i < num_args; ++i)
                m_concat_args.push_back(args[i]);
        }
        m_trail.push_back(trail_item::mk_concat);

        return v;
    }

    void slicing::replay_concat(unsigned num_args, pvar const* args, pvar r) {
        SASSERT(r != null_var);
        VERIFY_EQ(mk_concat(num_args, args, r), r);
    }

    pvar slicing::mk_concat(std::initializer_list<pvar> args) {
        return mk_concat(args.size(), args.begin());
    }

    void slicing::add_constraint(signed_constraint c) {
        LOG(c);
        SASSERT(!is_conflict());
        if (!add_fixed_bits(c))
            return;
        if (c->is_eq())
            add_constraint_eq(c->to_eq(), c.blit());
    }

    bool slicing::add_fixed_bits(signed_constraint c) {
        // TODO: what is missing here:
        // - we don't prioritize constraints that set larger bit ranges
        //   e.g., c1 sets 3 lower bits, and c2 sets 5 lower bits.
        //   slicing may have both {c1,c2} in justifications while previously we always prefer c2.
        // - instead of prioritizing constraints (which is annoying to do incrementally), let subsumption take care of this issue.
        //   if constraint C subsumes constraint D, then we might even want to completely deactivate D in the solver? (not easy if D is on higher level than C).
        // - (we could wait until propagate() to add fixed bits to the egraph. but that would only work on a single decision level.)
        if (c->vars().size() != 1)
            return true;
        fixed_bits fb;
        if (!get_fixed_bits(c, fb))
            return true;
        pvar const x = c->vars()[0];
        return add_fixed_bits(x, fb.hi, fb.lo, fb.value, c.blit());
    }

    bool slicing::add_fixed_bits(pvar x, unsigned hi, unsigned lo, rational const& value, sat::literal lit) {
        LOG("add_fixed_bits: v" << x << "[" << hi << ":" << lo << "] = " << value << " by " << lit_pp(m_solver, lit));
        enode_vector& xs = m_tmp3;
        SASSERT(xs.empty());
        mk_slice(var2slice(x), hi, lo, xs, false, false);
        enode* const sval = mk_value_slice(value, hi - lo + 1);
        // 'xs' will be cleared by 'merge'.
        // NOTE: the 'nullptr' argument will be fixed by 'egraph_merge'
        return merge(xs, sval, mk_var_dep(x, nullptr, lit));
    }

    bool slicing::add_constraint_eq(pdd const& p, sat::literal lit) {
        auto& m = p.manager();
        for (auto& [a, x] : p.linear_monomials()) {
            if (a != 1 && a != m.max_value())
                continue;
            pdd const body = a.is_one() ? (m.mk_var(x) - p) : (m.mk_var(x) + p);
            // c is either x = body or x != body, depending on polarity
            if (!add_equation(x, body, lit)) {
                SASSERT(is_conflict());
                return false;
            }
            // without this check, when p = x - y we would handle both x = y and y = x separately
            if (body.is_unary())
                break;
        }
        return true;
    }

    // TODO: handle equations 2^k x = 2^k y? (lower n-k bits of x and y are equal)
    bool slicing::add_equation(pvar x, pdd const& body, sat::literal lit) {
        LOG("Equation from lit(" << lit << "):  v" << x << (lit.sign() ? " != " : " = ") << body);
        if (!lit.sign() && body.is_val()) {
            LOG("    simple assignment");
            // Simple assignment x = value
            return add_value(x, body.val(), lit);
        }
        enode* const sx = var2slice(x);
        pvar const y = m_solver.m_names.get_name(body);
        if (y == null_var) {
            if (!body.is_val()) {
                // TODO: register name trigger (if a name for value 'body' is created later, then merge x=y at that time)
                //      could also count how often 'body' was registered and introduce name when more than once.
                //      maybe better: register x as an existing name for 'body'? question is how to track the dependency on c.
                LOG("    skip for now (unnamed body)");
            } else
                LOG("    skip for now (disequality with constant)");
            return true;
        }
        enode* const sy = var2slice(y);
        if (!lit.sign()) {
            LOG("    merge v" << x << " and v" << y);
            return merge(sx, sy, lit);
        }
        else {
            LOG("    store disequality v" << x << " != v" << y);
            enode* n = find_or_alloc_disequality(sx, sy, lit);
            if (!m_disequality_conflict && is_equal(sx, sy)) {
                add_var_congruence_if_needed(x);
                add_var_congruence_if_needed(y);
                m_disequality_conflict = n;
                return false;
            }
        }
        return true;
    }

    bool slicing::add_value(pvar v, rational const& value, sat::literal lit) {
        enode* const sv = var2slice(v);
        if (get_value_node(sv) && get_value(get_value_node(sv)) == value)
            return true;
        enode* const sval = mk_value_slice(value, width(sv));
        return merge(sv, sval, mk_var_dep(v, sv, lit));
    }

    void slicing::add_value(pvar v, rational const& value) {
        LOG("v" << v << " := " << value);
        SASSERT(!is_conflict());
        (void)add_value(v, value, sat::null_literal);
    }

    void slicing::collect_simple_overlaps(pvar v, pvar_vector& out) {
        unsigned const first_out = out.size();
        enode* const sv = var2slice(v);
        unsigned const v_width = width(sv);
        enode_vector& v_base = m_tmp2;
        SASSERT(v_base.empty());
        get_base(var2slice(v), v_base);

        SASSERT(all_of(m_egraph.nodes(), [](enode* n) { return !n->is_marked1(); }));

        // Collect direct sub-slices of v and their equivalences
        // (these don't need any extra checks)
        for (enode* s = sv; s != nullptr; s = has_sub(s) ? sub_lo(s) : nullptr) {
            for (enode* n : euf::enode_class(s)) {
                if (!is_proper_slice(n))
                    continue;
                pvar const w = slice2var(n);
                if (w == null_var)
                    continue;
                SASSERT(!n->is_marked1());
                n->mark1();
                out.push_back(w);
            }
        }

        // lowermost base slice of v
        enode* const v_base_lo = v_base.back();

        svector<std::pair<enode*,pvar>> candidates;
        // Collect all other candidate variables,
        // i.e., those who share the lowermost base slice with v.
        for (enode* n : euf::enode_class(v_base_lo)) {
            if (!is_proper_slice(n))
                continue;
            if (n == v_base_lo)
                continue;
            enode* const n0 = n;
            pvar w2 = null_var;  // the highest variable we care about from this equivalence class
            // examine parents to find variables
            SASSERT(!has_sub(n));
            while (true) {
                pvar const w = slice2var(n);
                if (w != null_var && !n->is_marked1())
                    w2 = w;
                enode* p = parent(n);
                if (!p)
                    break;
                if (sub_lo(p) != n)     // we only care about lowermost slices of variables
                    break;
                if (width(p) > v_width)
                    break;
                n = p;
            }
            if (w2 != null_var)
                candidates.push_back({n0, w2});
        }

        // Check candidates
        for (auto const& [n0, w2] : candidates) {
            // unsigned v_next = v_base.size();
            auto v_it = v_base.rbegin();
            enode* n = n0;
            SASSERT_EQ(n->get_root(), (*v_it)->get_root());
            ++v_it;
            while (true) {
                // here: base of n is equivalent to lower portion of base of v
                pvar const w = slice2var(n);
                if (w != null_var && !n->is_marked1()) {
                    n->mark1();
                    out.push_back(w);
                }
                if (w == w2)
                    break;
                //
                enode* const p = parent(n);
                SASSERT(p);
                SASSERT_EQ(sub_lo(p), n);   // otherwise not a candidate
                // check if base of sub_hi(p) matches the base of v
                enode_vector& p_hi_base = m_tmp3;
                get_base(sub_hi(p), p_hi_base);
                auto p_it = p_hi_base.rbegin();
                bool ok = true;
                while (ok && p_it != p_hi_base.rend()) {
                    if (v_it == v_base.rend())
                        ok = false;
                    else if ((*p_it)->get_root() != (*v_it)->get_root())
                        ok = false;
                    else {
                        ++p_it;
                        ++v_it;
                    }
                }
                p_hi_base.reset();
                if (!ok)
                    break;
                n = p;
            }
        }

        v_base.reset();
        for (unsigned i = out.size(); i-- > first_out; ) {
            enode* n = var2slice(out[i]);
            SASSERT(n->is_marked1());
            n->unmark1();
        }
        SASSERT(all_of(m_egraph.nodes(), [](enode* n) { return !n->is_marked1(); }));
    }

    void slicing::collect_fixed(pvar v, justified_fixed_bits_vector& out) {
        enode_vector& base = m_tmp2;
        SASSERT(base.empty());
        get_base(var2slice(v), base);
        rational a;
        unsigned lo = 0;
        for (auto it = base.rbegin(); it != base.rend(); ++it) {
            enode* const n = *it;
            enode* const nv = get_value_node(n);
            unsigned const w = width(n);
            unsigned const hi = lo + w - 1;
            if (try_get_value(nv, a))
                out.push_back({hi, lo, a, n});
            lo += w;
        }
        base.reset();
    }

    void slicing::explain_fixed(euf::enode* const n, std::function<void(sat::literal)> const& on_lit, std::function<void(pvar)> const& on_var) {
        explain_value(n, on_lit, on_var);
    }

    pvar_vector slicing::equivalent_vars(pvar v) const {
        pvar_vector xs;
        for (enode* n : euf::enode_class(var2slice(v))) {
            pvar const x = slice2var(n);
            if (x != null_var)
                xs.push_back(x);
        }
        return xs;
    }

    std::ostream& slicing::display(std::ostream& out) const {
        enode_vector base;
        for (pvar v = 0; v < m_var2slice.size(); ++v) {
            out << "v" << v << ":";
            base.reset();
            enode* const vs = var2slice(v);
            get_base(vs, base);
            for (enode* s : base)
                display(out << " ", s);
            if (enode* vnode = get_value_node(vs))
                out << "    [root_value: " << get_value(vnode) << "]";
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
        if (slice2var(s) != null_var)
            out << " var=v" << slice2var(s);
        if (parent(s))
            out << " parent=" << parent(s)->get_id();
        if (!s->is_root())
            out << " root=" << s->get_root_id();
        if (enode* n = get_value_node(s))
            out << " value=" << get_value(n);
        // if (is_proper_slice(s))
        //     out << " <slice>";
        if (is_value(s))
            out << " <value>";
        if (is_concat(s))
            out << " <concat>";
        if (is_equality(s))
            out << " <equality>";
        out << "\n";
        if (has_sub(s)) {
            unsigned cut = info(s).cut;
            display_tree(out, sub_hi(s), indent + 4, hi, cut + 1 + lo);
            display_tree(out, sub_lo(s), indent + 4, cut + lo, lo);
        }
        return out;
    }

    std::ostream& slicing::display(std::ostream& out, enode* s) const {
        out << "{id:" << s->get_id();
        out << ",w:" << width(s);
        out << ",root:" << s->get_root_id();
        if (slice2var(s) != null_var)
            out << ",var:v" << slice2var(s);
        if (is_value(s))
            out << ",value:" << get_value(s);
        if (s->interpreted())
            out << ",<interpreted>";
        if (is_concat(s))
            out << ",<concat>";
        if (is_equality(s))
            out << ",<equality>";
        out << "}";
        return out;
    }

    bool slicing::invariant() const {
        VERIFY(m_tmp1.empty());
        VERIFY(m_tmp2.empty());
        VERIFY(m_tmp3.empty());
        if (is_conflict())  // if we break a loop early on conflict, we can't guarantee that all properties are satisfied
            return true;
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
            if (get_value_node(s) && has_sub(s)) {
                VERIFY(get_value_node(sub_hi(s)));
                VERIFY(get_value_node(sub_lo(s)));
            }
            // a base slice is never equivalent to a congruence node
            if (is_slice(s) && !has_sub(s)) {
                VERIFY(all_of(euf::enode_class(s), [&](enode* n) { return is_slice(n); }));
            }
            if (is_concat(s)) {
                // all concat nodes point to a variable slice
                VERIFY(slice2var(s) != null_var);
                enode* sv = var2slice(slice2var(s));  // the corresponding variable slice
                VERIFY(s != sv);
                VERIFY(is_slice(sv));
                VERIFY(s->num_args() >= 2);
            }
            /////////////////////////////////////////////////////////////////
            // class properties (i.e., skip non-representatives)
            if (!s->is_root())
                continue;
            bool const sub = has_sub(s);
            enode_vector const s_base = get_base(s);
            for (enode* n : euf::enode_class(s)) {
                // equivalence class only contains slices of equal length
                VERIFY_EQ(width(s), width(n));
                // either all nodes in the class have subslices or none do
                SASSERT_EQ(sub, has_sub(n));
                // bases of equivalent nodes are equivalent
                enode_vector const n_base = get_base(n);
                VERIFY_EQ(s_base.size(), n_base.size());
                for (unsigned i = s_base.size(); i-- > 0; ) {
                    VERIFY_EQ(s_base[i]->get_root(), n_base[i]->get_root());
                }
            }
        }
        return true;
    }

}
