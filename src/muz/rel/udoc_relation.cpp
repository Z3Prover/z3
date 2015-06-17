/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    udoc_relation.cpp

Abstract:

    Relation based on union of DOCs.

Author:

    Nuno Lopes (a-nlopes) 2013-03-01
    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:

    Revised version of dl_hassel_diff facilities.

Notes:

--*/
#include "udoc_relation.h"
#include "dl_relation_manager.h"
#include "qe_util.h"
#include "ast_util.h"
#include "smt_kernel.h"


namespace datalog {

    udoc_relation::udoc_relation(udoc_plugin& p, relation_signature const& sig):
        relation_base(p, sig),
        dm(p.dm(p.num_signature_bits(sig))) {
        unsigned column = 0;
        for (unsigned i = 0; i < sig.size(); ++i) {
            m_column_info.push_back(column);
            column += p.num_sort_bits(sig[i]);
        }
        m_column_info.push_back(column);
    }
    udoc_relation::~udoc_relation() {
        reset();
    }
    void udoc_relation::reset() {
        m_elems.reset(dm);
    }
    void udoc_relation::expand_column_vector(unsigned_vector& v, const udoc_relation* other) const {
        unsigned_vector orig;
        orig.swap(v);
        for (unsigned i = 0; i < orig.size(); ++i) {
            unsigned col, limit;
            if (orig[i] < get_num_cols()) {
                col = column_idx(orig[i]);
                limit = col + column_num_bits(orig[i]);
            } else {
                unsigned idx = orig[i] - get_num_cols();
                col = get_num_bits() + other->column_idx(idx);
                limit = col + other->column_num_bits(idx);
            }
            for (; col < limit; ++col) {
                v.push_back(col);
            }
        }
    }

    doc* udoc_relation::fact2doc(const relation_fact & f) const {
        doc* d = dm.allocate0();
        for (unsigned i = 0; i < f.size(); ++i) {
            unsigned bv_size;
            rational val;
            VERIFY(get_plugin().is_numeral(f[i], val, bv_size));
            SASSERT(bv_size == column_num_bits(i));
            unsigned lo = column_idx(i);
            unsigned hi = column_idx(i + 1);
            dm.tbvm().set(d->pos(),val, hi-1, lo);
        }
        return d;
    }
    void udoc_relation::add_fact(const relation_fact & f) {
        doc* d = fact2doc(f);
        m_elems.insert(dm, d);
    }
    void udoc_relation::add_new_fact(const relation_fact & f) {
        m_elems.push_back(fact2doc(f));
    }
    bool udoc_relation::empty() const {
        return m_elems.is_empty_complete(get_plugin().m, dm);
    }
    bool udoc_relation::contains_fact(const relation_fact & f) const {
        doc_ref d(dm, fact2doc(f));
        return m_elems.contains(dm, *d);
    }
    udoc_relation * udoc_relation::clone() const {
        udoc_relation* result = udoc_plugin::get(get_plugin().mk_empty(get_signature()));
        for (unsigned i = 0; i < m_elems.size(); ++i) {
            result->m_elems.push_back(dm.allocate(m_elems[i]));
        }
        return result;
    }
    udoc_relation * udoc_relation::complement(func_decl* f) const {
        udoc_relation* result = udoc_plugin::get(get_plugin().mk_empty(get_signature()));
        m_elems.complement(dm, result->m_elems);
        return result;
    }
    void udoc_relation::to_formula(expr_ref& fml) const {
        ast_manager& m = fml.get_manager();
        expr_ref_vector disj(m);
        for (unsigned i = 0; i < m_elems.size(); ++i) {
            disj.push_back(to_formula(m_elems[i]));
        }
        fml = mk_or(m, disj.size(), disj.c_ptr());
    }
    expr_ref udoc_relation::to_formula(doc const& d) const {
        ast_manager& m = get_plugin().get_ast_manager();
        expr_ref result(m);
        expr_ref_vector conjs(m);
        conjs.push_back(to_formula(d.pos()));
        for (unsigned i = 0; i < d.neg().size(); ++i) {
            conjs.push_back(m.mk_not(to_formula(d.neg()[i])));
        }
        result = mk_and(m, conjs.size(), conjs.c_ptr());
        return result;
    }
    expr_ref udoc_relation::to_formula(tbv const& t) const {
        udoc_plugin& p = get_plugin();
        ast_manager& m = p.get_ast_manager();
        expr_ref result(m);
        expr_ref_vector conjs(m);
        for (unsigned i = 0; i < get_num_cols(); ++i) {
            var_ref v(m);
            v = m.mk_var(i, get_signature()[i]);
            unsigned lo = column_idx(i);
            unsigned hi = column_idx(i+1);
            rational r(0);
            unsigned lo1 = lo;
            bool is_x = true;
            for (unsigned j = lo; j < hi; ++j) {
                switch(t[j]) {
                case BIT_0:
                    if (is_x) is_x = false, lo1 = j, r.reset();
                    break;
                case BIT_1:
                    if (is_x) is_x = false, lo1 = j, r.reset();
                    r += rational::power_of_two(j - lo1);
                    break;
                case BIT_x:
                    if (!is_x) {
                        SASSERT(p.bv.is_bv_sort(get_signature()[i]));
                        conjs.push_back(m.mk_eq(p.bv.mk_extract(j-1-lo,lo1-lo,v),
                                                p.bv.mk_numeral(r,j-lo1)));
                    }
                    is_x = true;
                    break;
                default:
                    UNREACHABLE();
                }
            }
            if (!is_x) {
                expr_ref num(m);
                if (lo1 == lo) {
                    num = p.mk_numeral(r, get_signature()[i]);
                    conjs.push_back(m.mk_eq(v, num));
                }
                else {
                    num = p.bv.mk_numeral(r, hi-lo1);
                    conjs.push_back(m.mk_eq(p.bv.mk_extract(hi-1-lo,lo1-lo,v), num));
                }
            }
        }
        result = mk_and(m, conjs.size(), conjs.c_ptr());
        return result;
    }

    udoc_plugin& udoc_relation::get_plugin() const {
        return static_cast<udoc_plugin&>(relation_base::get_plugin());
    }

    void udoc_relation::display(std::ostream& out) const {
        m_elems.display(dm, out); out << "\n";
    }

    unsigned udoc_relation::get_size_estimate_bytes() const {
        return sizeof(*this) + m_elems.get_size_estimate_bytes(dm);
    }

    // -------------

    udoc_plugin::udoc_plugin(relation_manager& rm):
        relation_plugin(udoc_plugin::get_name(), rm),
        m(rm.get_context().get_manager()),
        bv(m),
        dl(m),
        m_disable_fast_pass(false) {
    }
    udoc_plugin::~udoc_plugin() {
        u_map<doc_manager*>::iterator it = m_dms.begin(), end = m_dms.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
    }
    udoc_relation& udoc_plugin::get(relation_base& r) {
        return dynamic_cast<udoc_relation&>(r);
    }
    udoc_relation* udoc_plugin::get(relation_base* r) {
        return r?dynamic_cast<udoc_relation*>(r):0;
    }
    udoc_relation const & udoc_plugin::get(relation_base const& r) {
        return dynamic_cast<udoc_relation const&>(r);        
    }

    doc_manager& udoc_plugin::dm(relation_signature const& sig) {
        return dm(num_signature_bits(sig));
    }

    doc_manager& udoc_plugin::dm(unsigned n) {
        doc_manager* r;
        if (!m_dms.find(n, r)) {
            r = alloc(doc_manager, n);
            m_dms.insert(n, r);
        }
        return *r;
    }
    bool udoc_relation::is_var_range(expr* e, unsigned& hi, unsigned& lo, unsigned& v) const {
        udoc_plugin& p = get_plugin();
        if (is_var(e)) {
            v = to_var(e)->get_idx();
            hi = p.num_sort_bits(e)-1;
            lo = 0;
            return true;
        }
        expr* e2;
        if (p.bv.is_extract(e, lo, hi, e2) && is_var(e2)) {
            v = to_var(e2)->get_idx();
            SASSERT(lo <= hi);
            return true;
        }
        return false;
    }

    expr* udoc_plugin::mk_numeral(rational const& r, sort* s) {
        if (bv.is_bv_sort(s)) {
            return bv.mk_numeral(r, s);
        }
        if (m.is_bool(s)) {
            if (r.is_zero()) return m.mk_false();
            return m.mk_true();
        }
        SASSERT(dl.is_finite_sort(s));
        return dl.mk_numeral(r.get_uint64(), s);
    }
    bool udoc_plugin::is_numeral(expr* e, rational& r, unsigned& num_bits) {
        if (bv.is_numeral(e, r, num_bits)) return true;
        if (m.is_true(e)) {
            r = rational(1);
            num_bits = 1;
            return true;
        }
        if (m.is_false(e)) {
            r = rational(0);
            num_bits = 1;
            return true;
        }
        uint64 n, sz;
        ast_manager& m = get_ast_manager();
        if (dl.is_numeral(e, n) && dl.try_get_size(m.get_sort(e), sz)) {
            num_bits = 0;
            while (sz > 0) ++num_bits, sz = sz/2;
            r = rational(n, rational::ui64());
            return true;
        }
        return false;
    }
    unsigned udoc_plugin::num_sort_bits(sort* s) const {
        unsigned num_bits = 0;
        if (bv.is_bv_sort(s))
            return bv.get_bv_size(s);
        if (m.is_bool(s)) 
            return 1;
        uint64 sz;
        if (dl.try_get_size(s, sz)) {
            while (sz > 0) ++num_bits, sz /= 2;
            return num_bits;
        }
        UNREACHABLE();
        return 0;
    }
    unsigned udoc_plugin::num_signature_bits(relation_signature const& sig) { 
        unsigned result = 0;
        for (unsigned i = 0; i < sig.size(); ++i) {
            result += num_sort_bits(sig[i]);
        }
        return result;
    }

    bool udoc_plugin::is_finite_sort(sort* s) const {
        return bv.is_bv_sort(s) || dl.is_finite_sort(s);
    }


    bool udoc_plugin::can_handle_signature(const relation_signature & sig) {
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (!is_finite_sort(sig[i]))
                return false;
        }
        return true;
    }
    relation_base * udoc_plugin::mk_empty(const relation_signature & sig) {
        return alloc(udoc_relation, *this, sig);
    }
    relation_base * udoc_plugin::mk_full(func_decl* p, const relation_signature & s) {
        udoc_relation* r = get(mk_empty(s));
        r->get_udoc().push_back(dm(s).allocateX());
        return r;
    }
    class udoc_plugin::join_fn : public convenient_relation_join_fn {
        doc_manager& dm;
        doc_manager& dm1;
        doc_manager& dm2;
    public:
        join_fn(udoc_plugin& p, udoc_relation const& t1, udoc_relation const& t2, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2),
              dm(p.dm(get_result_signature())),
              dm1(t1.get_dm()),
              dm2(t2.get_dm()) {
            t1.expand_column_vector(m_cols1);
            t2.expand_column_vector(m_cols2);
        }

        virtual relation_base * operator()(const relation_base & _r1, const relation_base & _r2) {
            udoc_relation const& r1 = get(_r1);
            udoc_relation const& r2 = get(_r2);
            TRACE("doc", r1.display(tout << "r1:\n"); r2.display(tout  << "r2:\n"););
            udoc_plugin& p = r1.get_plugin();            
            relation_signature const& sig = get_result_signature();
            udoc_relation * result = alloc(udoc_relation, p, sig);
            udoc const& d1 = r1.get_udoc();
            udoc const& d2 = r2.get_udoc();
            udoc& r = result->get_udoc();
            r.join(d1, d2, dm, dm1, m_cols1, m_cols2);
            TRACE("doc", result->display(tout << "result:\n"););
            IF_VERBOSE(3, result->display(verbose_stream() << "join result:\n"););
            SASSERT(r.well_formed(result->get_dm()));
            return result;
        }
    };
    

    relation_join_fn * udoc_plugin::mk_join_fn(
        const relation_base & t1, const relation_base & t2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(t1) || !check_kind(t2)) {
            return 0;
        }
        return alloc(join_fn, *this, get(t1), get(t2), col_cnt, cols1, cols2);
    }

    class udoc_plugin::project_fn : public convenient_relation_project_fn {
        bit_vector m_to_delete;
    public:
        project_fn(udoc_relation const & t, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(t.get_signature(), removed_col_cnt, removed_cols) {
            t.expand_column_vector(m_removed_cols);
            unsigned n = t.get_dm().num_tbits();
            m_to_delete.resize(n, false);
            for (unsigned i = 0; i < m_removed_cols.size(); ++i) {
                m_to_delete.set(m_removed_cols[i], true);
            }
        }

        virtual relation_base * operator()(const relation_base & tb) {
            TRACE("doc", tb.display(tout << "src:\n"););
            udoc_relation const& t = get(tb);
            udoc_plugin& p = t.get_plugin();
            udoc_relation* r = udoc_plugin::get(p.mk_empty(get_result_signature()));
            doc_manager& dm1 = t.get_dm();
            doc_manager& dm2 = r->get_dm();
            doc_ref d2(dm2);
            udoc const& ud1 = t.get_udoc();
            udoc& ud2 = r->get_udoc();
            for (unsigned i = 0; i < ud1.size(); ++i) {
                d2 = dm1.project(dm2, m_to_delete, ud1[i]);
                ud2.push_back(d2.detach());
            }
            TRACE("doc", tout << "final size: " << r->get_size_estimate_rows() << '\n';);
            SASSERT(ud2.well_formed(dm2));
            return r;
        }
    };
    

    relation_transformer_fn * udoc_plugin::mk_project_fn(
        const relation_base & t, unsigned col_cnt, 
        const unsigned * removed_cols) {
        if (!check_kind(t))
            return 0;
        return alloc(project_fn, get(t), col_cnt, removed_cols);
    }

    class udoc_plugin::rename_fn : public convenient_relation_rename_fn {
        unsigned_vector m_permutation;
    public:
        rename_fn(udoc_relation const& t, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(t.get_signature(), cycle_len, cycle) {
            udoc_plugin& p = t.get_plugin();
            ast_manager& m = p.get_ast_manager();
            relation_signature const& sig1 = t.get_signature();
            relation_signature const& sig2 = get_result_signature();
            unsigned_vector permutation0, column_info;
            for (unsigned i = 0; i < t.get_num_bits(); ++i) {
                m_permutation.push_back(i);
            }
            for (unsigned i = 0; i < sig1.size(); ++i) {
                permutation0.push_back(i);
            }
            for (unsigned i = 0; i < cycle_len; ++i) {
                unsigned j = (i + 1)%cycle_len;
                unsigned col1 = cycle[i];
                unsigned col2 = cycle[j];
                permutation0[col2] = col1;
            }
            unsigned column = 0;
            for (unsigned i = 0; i < sig2.size(); ++i) {
                column_info.push_back(column);
                column += p.num_sort_bits(sig2[i]);
            }
            column_info.push_back(column);
            SASSERT(column == t.get_num_bits());

            TRACE("doc",
                  sig1.output(m, tout << "sig1: "); tout << "\n";
                  sig2.output(m, tout << "sig2: "); tout << "\n";
                  tout << "permute: ";
                  for (unsigned i = 0; i < permutation0.size(); ++i) {
                      tout << permutation0[i] << " ";
                  }
                  tout << "\n";
                  tout << "cycle: ";
                  for (unsigned i = 0; i < cycle_len; ++i) {
                      tout << cycle[i] << " ";
                  }
                  tout << "\n";
                  );
                  

            // 0 -> 2
            // [3:2:1] -> [1:2:3]
            // [3,4,5,1,2,0]

            for (unsigned i = 0; i < sig1.size(); ++i) {
                unsigned len  = t.column_num_bits(i);
                unsigned lo1  = t.column_idx(i);
                unsigned col2 = permutation0[i];
                unsigned lo2  = column_info[col2];
                SASSERT(lo2 + len <= t.get_num_bits());
                SASSERT(lo1 + len <= t.get_num_bits());
                for (unsigned k = 0; k < len; ++k) {
                    m_permutation[k + lo1] = k + lo2;
                }
            }
        }

        virtual relation_base * operator()(const relation_base & _r) {
            udoc_relation const& r = get(_r);
            TRACE("doc", r.display(tout << "r:\n"););
            udoc_plugin& p = r.get_plugin();            
            relation_signature const& sig = get_result_signature();
            udoc_relation* result = alloc(udoc_relation, p, sig);
            udoc const& src = r.get_udoc();
            udoc& dst = result->get_udoc();
            doc_manager& dm = r.get_dm();
            SASSERT(&result->get_dm() == &dm);
            for (unsigned i = 0; i < src.size(); ++i) {
                dst.push_back(dm.allocate(src[i], m_permutation.c_ptr()));
            }
            TRACE("doc", result->display(tout << "result:\n"););
            SASSERT(dst.well_formed(dm));
            return result;
        }
    };
    relation_transformer_fn * udoc_plugin::mk_rename_fn(
        const relation_base & r, 
        unsigned cycle_len, const unsigned * permutation_cycle) {
        if (check_kind(r)) {
            return alloc(rename_fn, get(r), cycle_len, permutation_cycle);
        }
        else {
            return 0;
        }
    }
    class udoc_plugin::union_fn : public relation_union_fn {
    public:
        union_fn() {}

        virtual void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) {
            TRACE("doc", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););
            udoc_relation& r = get(_r);
            udoc_relation const& src = get(_src);
            udoc_relation* d = get(_delta);
            doc_manager& dm = r.get_dm();
            udoc* d1 = 0;
            if (d) d1 = &d->get_udoc();
            IF_VERBOSE(3, r.display(verbose_stream() << "orig:  "););
            r.get_plugin().mk_union(dm, r.get_udoc(), src.get_udoc(), d1);
            SASSERT(r.get_udoc().well_formed(dm));
            SASSERT(!d1 || d1->well_formed(dm));
            TRACE("doc", _r.display(tout << "dst':\n"); );
            IF_VERBOSE(3, r.display(verbose_stream() << "union: "););
            IF_VERBOSE(3, if (d) d->display(verbose_stream() << "delta: "););
        }
    };
    void udoc_plugin::mk_union(doc_manager& dm, udoc& dst, udoc const& src, udoc* delta) {
        bool deltaempty = delta ? delta->is_empty() : false;

        if (dst.is_empty()) {
            for (unsigned i = 0; i < src.size(); ++i) {
                dst.push_back(dm.allocate(src[i]));
                if (delta) {
                    if (deltaempty)
                        delta->push_back(dm.allocate(src[i]));
                    else
                        delta->insert(dm, dm.allocate(src[i]));
                }
            }
        } else {
            for (unsigned i = 0; i < src.size(); ++i) {
                if (dst.insert(dm, dm.allocate(src[i])) && delta) {
                    if (deltaempty)
                        delta->push_back(dm.allocate(src[i]));
                    else
                        delta->insert(dm, dm.allocate(src[i]));
                }
            }
        }
    }
    relation_union_fn * udoc_plugin::mk_union_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return 0;
        }
        return alloc(union_fn);
    }
    relation_union_fn * udoc_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        return mk_union_fn(tgt, src, delta);
    }

    class udoc_plugin::filter_identical_fn : public relation_mutator_fn {
        unsigned_vector        m_cols;
        unsigned               m_size;
        bit_vector             m_empty_bv;
        union_find_default_ctx union_ctx;
        union_find<>           m_equalities;
    public:
        filter_identical_fn(const relation_base & _r, unsigned col_cnt, const unsigned *identical_cols)
            : m_cols(col_cnt), m_equalities(union_ctx) {
            udoc_relation const& r = get(_r);
            m_size = r.column_num_bits(identical_cols[0]);
            m_empty_bv.resize(r.get_num_bits(), false);            
            for (unsigned i = 0; i < col_cnt; ++i) {
                m_cols[i] = r.column_idx(identical_cols[i]);
            }            
            for (unsigned i = 0, e = m_empty_bv.size(); i < e; ++i) {
                m_equalities.mk_var();
            }
            for (unsigned i = 1; i < col_cnt; ++i) {
                for (unsigned j = 0; j < m_size; ++j) {
                    m_equalities.merge(m_cols[0]+j ,m_cols[i]+j);
                }
            }
        }
        
        virtual void operator()(relation_base & _r) {
            udoc_relation& r = get(_r);
            udoc& d = r.get_udoc();
            doc_manager& dm = r.get_dm();
            d.merge(dm, m_cols[0], m_size, m_equalities, m_empty_bv);
            SASSERT(d.well_formed(dm));
            TRACE("doc", tout << "final size: " << r.get_size_estimate_rows() << '\n';);
        }
    };
    relation_mutator_fn * udoc_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        return check_kind(t)?alloc(filter_identical_fn, t, col_cnt, identical_cols):0;
    }
    class udoc_plugin::filter_equal_fn : public relation_mutator_fn {
        doc_manager& dm;
        doc*         m_filter;
    public:
        filter_equal_fn(udoc_plugin& p, const udoc_relation & t, const relation_element val, unsigned col):
            dm(p.dm(t.get_signature())) {
            rational r;
            unsigned num_bits;
            VERIFY(p.is_numeral(val, r, num_bits));
            m_filter = dm.allocateX();
            unsigned lo = t.column_idx(col);
            unsigned hi = t.column_idx(col+1);
            SASSERT(num_bits == hi - lo);
            dm.tbvm().set(m_filter->pos(), r, hi-1, lo);
        }
        virtual ~filter_equal_fn() {
            dm.deallocate(m_filter);
        }        
        virtual void operator()(relation_base & tb) {
            udoc_relation & t = get(tb);
            t.get_udoc().intersect(dm, *m_filter);
            SASSERT(t.get_udoc().well_formed(t.get_dm()));
        }
    };
    relation_mutator_fn * udoc_plugin::mk_filter_equal_fn(
        const relation_base & t, const relation_element & value, unsigned col) {
        if (!check_kind(t))
            return 0;
        return alloc(filter_equal_fn, *this, get(t), value, col);
    }

    bool udoc_relation::is_guard(unsigned n, expr* const* gs) const {
        for (unsigned i = 0; i < n; ++i) {
            if (!is_guard(gs[i])) return false;
        }
        return true;
    }
    bool udoc_relation::is_guard(expr* g) const {
        udoc_plugin& p = get_plugin();
        ast_manager& m = p.get_ast_manager();
        bv_util& bv = p.bv;
        expr* e1, *e2;
        unsigned hi, lo, v;
        if (m.is_and(g) || m.is_or(g) || m.is_not(g) || m.is_true(g) || m.is_false(g)) {
            return is_guard(to_app(g)->get_num_args(), to_app(g)->get_args());
        }
        if (m.is_eq(g, e1, e2) && bv.is_bv(e1)) {
            if (is_var_range(e1, hi, lo, v) && is_ground(e2)) return true;
            if (is_var_range(e2, hi, lo, v) && is_ground(e1)) return true;
        }
        if (is_var(g)) {
            return true;
        }
        return false;
    }

    void udoc_relation::extract_guard(expr* cond, expr_ref& guard, expr_ref& rest) const {
        rest.reset();
        ast_manager& m = get_plugin().get_ast_manager();
        expr_ref_vector conds(m), guards(m), rests(m);
        conds.push_back(cond);
        qe::flatten_and(conds);
        for (unsigned i = 0; i < conds.size(); ++i) {
            expr* g = conds[i].get();
            if (is_guard(g)) {
                guards.push_back(g);
            }
            else {
                rests.push_back(g);
            }
        }
        guard = mk_and(m, guards.size(), guards.c_ptr());
        rest  = mk_and(m, rests.size(),  rests.c_ptr());        
    }
    void udoc_relation::extract_equalities(expr* g, expr_ref& rest, subset_ints& equalities,
                                           unsigned_vector& roots) const {
        rest.reset();
        ast_manager& m = get_plugin().get_ast_manager();
        expr_ref_vector conds(m);
        conds.push_back(g);
        qe::flatten_and(conds);
        expr* e1, *e2;
        for (unsigned i = 0; i < conds.size(); ++i) {
            expr* g = conds[i].get();
            if (m.is_eq(g, e1, e2)) {
                extract_equalities(e1, e2, conds, equalities, roots);
                conds[i] = conds.back();
                conds.pop_back();
            }
        }
        rest = mk_and(m, conds.size(), conds.c_ptr());
    }

    void udoc_relation::extract_equalities(
        expr* e1, expr* e2, expr_ref_vector& conds, 
        subset_ints& equalities, unsigned_vector& roots) const {        
        udoc_plugin& p = get_plugin();
        ast_manager& m  = p.get_ast_manager();
        bv_util& bv = p.bv;
        th_rewriter rw(m);
        unsigned hi, lo1, lo2, hi1, hi2, v1, v2;
        if (bv.is_concat(e2)) {
            std::swap(e1, e2);
        }
        if (bv.is_concat(e1)) {
            expr_ref e3(m);
            app* a1 = to_app(e1);
            hi = p.num_sort_bits(e1)-1;
            unsigned n = a1->get_num_args();
            for (unsigned i = 0; i < n; ++i) {
                expr* e = a1->get_arg(i);
                unsigned sz = p.num_sort_bits(e);
                e3 = bv.mk_extract(hi, hi-sz+1, e2);
                rw(e3);
                extract_equalities(e, e3, conds, equalities, roots);
                hi -= sz;
            }
            return;
        }
        if (is_var_range(e1, hi1, lo1, v1) && 
            is_var_range(e2, hi2, lo2, v2)) {
            unsigned col1 = column_idx(v1);
            lo1 += col1;
            hi1 += col1;
            unsigned col2 = column_idx(v2);
            lo2 += col2;
            hi2 += col2;
            for (unsigned j = 0; j <= hi1-lo1; ++j) {
                roots.push_back(lo1 + j);
                equalities.merge(lo1 + j, lo2 + j);
            }
            return;
        }   
        conds.push_back(m.mk_eq(e1, e2));
    }

    void udoc_relation::compile_guard(expr* g, udoc& d, bit_vector const& discard_cols) const {
        d.reset(dm);
        d.push_back(dm.allocateX()); 
        apply_guard(g, d, discard_cols);
    }
    void udoc_relation::apply_guard(expr* g, udoc& result, bit_vector const& discard_cols) const {
        // datastructure to store equalities with columns that will be projected out
        union_find_default_ctx union_ctx;
        subset_ints equalities(union_ctx);
        for (unsigned i = 0, e = discard_cols.size(); i < e; ++i) {
            equalities.mk_var();
        }        
        apply_guard(g, result, equalities, discard_cols);
    }
    bool udoc_relation::apply_ground_eq(doc_ref& d, unsigned v, unsigned hi, unsigned lo, expr* c) const {
        udoc_plugin& p = get_plugin();
        unsigned num_bits;
        rational r;
        unsigned col = column_idx(v);
        lo += col;
        hi += col;
        if (p.is_numeral(c, r, num_bits)) {
            d = dm.allocateX();
            dm.tbvm().set(d->pos(), r, hi, lo);
            return true;
        }
        // other cases?
        return false;
    }




    bool udoc_relation::apply_bv_eq(
        expr* e1, expr* e2, bit_vector const& discard_cols, udoc& result) const {
        udoc_plugin& p = get_plugin();
        ast_manager& m  = p.get_ast_manager();
        bv_util& bv = p.bv;
        th_rewriter rw(m);
        doc_ref d(get_dm());
        unsigned hi, lo, lo1, lo2, hi1, hi2, v, v1, v2;
        if (bv.is_concat(e2)) {
            std::swap(e1, e2);
        }
        if (bv.is_concat(e1)) {
            expr_ref e3(m);
            app* a1 = to_app(e1);
            hi = p.num_sort_bits(e1)-1;
            unsigned n = a1->get_num_args();
            for (unsigned i = 0; i < n; ++i) {
                expr* e = a1->get_arg(i);
                unsigned sz = p.num_sort_bits(e);
                e3 = bv.mk_extract(hi, hi-sz+1, e2);
                rw(e3);
                if (!apply_bv_eq(e, e3, discard_cols, result)) return false;
                hi -= sz;
            }
            return true;
        }
        if (is_ground(e1)) {
            std::swap(e1, e2);
        }
        if (is_var_range(e1, hi, lo, v) && is_ground(e2) &&
            apply_ground_eq(d, v, hi, lo, e2)) {
            result.intersect(dm, *d);
            return true;
        }
        if (is_var_range(e1, hi1, lo1, v1) && 
            is_var_range(e2, hi2, lo2, v2)) {
            unsigned idx1 = lo1 + column_idx(v1);
            unsigned idx2 = lo2 + column_idx(v2);
            unsigned length = hi1-lo1+1;
            result.merge(dm, idx1, idx2, length, discard_cols);
            return true;
        }   

        return false;
    }

    void udoc_relation::apply_guard(
        expr* g, udoc& result, subset_ints const& equalities, bit_vector const& discard_cols) const {
        ast_manager& m = get_plugin().get_ast_manager();
        bv_util& bv = get_plugin().bv;
        expr *e0, *e1, *e2;
        unsigned hi, lo, v;
        doc_ref d(get_dm());
        if (result.is_empty()) {
        }
        else if (m.is_true(g)) {
        }
        else if (m.is_false(g)) {
            result.reset(dm);
        }
        else if (m.is_and(g)) {
            for (unsigned i = 0; !result.is_empty() && i < to_app(g)->get_num_args(); ++i) {
                apply_guard(to_app(g)->get_arg(i), result, equalities, discard_cols);
            }
        }
        else if (m.is_not(g, e0) &&
                 m.is_eq(e0, e1, e2) && bv.is_bv(e1) &&
                 is_var_range(e1, hi, lo, v) && is_ground(e2) &&
                 apply_ground_eq(d, v, hi, lo, e2)) {
            result.subtract(dm, *d);
        }
        else if (m.is_not(g, e0) &&
                 m.is_eq(e0, e2, e1) && bv.is_bv(e1) &&
                 is_var_range(e1, hi, lo, v) && is_ground(e2) &&
                 apply_ground_eq(d, v, hi, lo, e2)) {
            result.subtract(dm, *d);
        }
        else if (m.is_not(g, e1)) {
            udoc sub;
            sub.push_back(dm.allocateX());
            // TODO: right now we state that no columns are discarded to avoid
            // silent column merging. This can be optimized if the set of merged
            // columns is returned so that here we remove different columns.
            bit_vector empty;
            empty.resize(discard_cols.size(), false);
            apply_guard(e1, sub, equalities, empty);
            result.subtract(dm, sub);
            result.simplify(dm);
            TRACE("doc",
                  result.display(dm, tout << "result0:") << "\n";
                  sub.display(dm, tout << "sub:") << "\n";);
            sub.reset(dm);
            TRACE("doc", result.display(dm, tout << "result:") << "\n";);
        }
        else if (m.is_or(g)) {
            udoc sub;
            sub.push_back(dm.allocateX());
            for (unsigned i = 0; !sub.is_empty() && i < to_app(g)->get_num_args(); ++i) {
                expr_ref arg(m);
                arg = mk_not(m, to_app(g)->get_arg(i));
                apply_guard(arg, sub, equalities, discard_cols);
            }
            TRACE("doc", result.display(dm, tout << "result0:") << "\n";);
            result.subtract(dm, sub);
            TRACE("doc", 
                  sub.display(dm, tout << "sub:") << "\n";
                  result.display(dm, tout << "result:") << "\n";);
            sub.reset(dm);
        }
        else if (is_var(g)) {
            SASSERT(m.is_bool(g));
            unsigned v = to_var(g)->get_idx();
            unsigned idx = column_idx(v);
            doc_ref d(dm);
            d = dm.allocateX();
            dm.set(*d, idx, BIT_1);
            result.intersect(dm, *d);
        }
        else if ((m.is_eq(g, e1, e2) || m.is_iff(g, e1, e2)) && m.is_bool(e1)) {
            udoc diff1, diff2;
            diff1.push_back(dm.allocateX());
            diff2.push_back(dm.allocateX());
            expr_ref f1(m), f2(m);
            f1 = mk_not(m, e1);
            f2 = mk_not(m, e2);
            apply_guard(e1, diff1, equalities, discard_cols);
            apply_guard(f2, diff1, equalities, discard_cols);
            result.subtract(dm, diff1);
            diff1.reset(dm);
            apply_guard(f1, diff2, equalities, discard_cols);
            apply_guard(e2, diff2, equalities, discard_cols);
            result.subtract(dm, diff2);
            diff2.reset(dm);
        }
        else if (m.is_eq(g, e1, e2) && bv.is_bv(e1)) {
            if (apply_bv_eq(e1, e2, discard_cols, result)) {
                // done
            }
            else {
                goto failure_case;
            }            
        }
        else {
        failure_case:
            std::ostringstream strm;
            strm << "Guard expression is not handled" << mk_pp(g, m);
            throw default_exception(strm.str()); 
        }
    }

    class udoc_plugin::filter_interpreted_fn : public relation_mutator_fn {
        union_find_default_ctx union_ctx;
        doc_manager& dm;
        expr_ref     m_original_condition;
        expr_ref     m_reduced_condition;
        udoc         m_udoc;
        bit_vector   m_empty_bv;
        subset_ints  m_equalities;

    public:
        filter_interpreted_fn(const udoc_relation & t, ast_manager& m, app *condition) :
            dm(t.get_dm()),
            m_original_condition(condition, m),
            m_reduced_condition(m),            
            m_equalities(union_ctx) {
            unsigned num_bits = t.get_num_bits();
            m_empty_bv.resize(num_bits, false);
            expr_ref guard(m);
            for (unsigned i = 0; i < num_bits; ++i) {
                m_equalities.mk_var();
            }        
            t.extract_guard(condition, guard, m_reduced_condition);            
            t.compile_guard(guard, m_udoc, m_empty_bv);

            TRACE("doc", 
                  tout << "original condition: " << mk_pp(condition, m) << "\n";
                  tout << "remaining condition: " << m_reduced_condition << "\n"; 
                  m_udoc.display(dm, tout) << "\n";);
        }

        virtual ~filter_interpreted_fn() {
            m_udoc.reset(dm);
        }
        
        virtual void operator()(relation_base & tb) {            
            udoc_relation & t = get(tb);
            udoc& u = t.get_udoc();
            SASSERT(u.well_formed(dm));
            u.intersect(dm, m_udoc);
            SASSERT(u.well_formed(dm));
            t.apply_guard(m_reduced_condition, u, m_equalities, m_empty_bv);
            SASSERT(u.well_formed(dm));            
            u.simplify(dm);
            SASSERT(u.well_formed(dm));
            TRACE("doc", tout << "final size: " << t.get_size_estimate_rows() << '\n';);
            IF_VERBOSE(3, t.display(verbose_stream()););
        }
    };
    relation_mutator_fn * udoc_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        return check_kind(t)?alloc(filter_interpreted_fn, get(t), get_ast_manager(), condition):0;
    }

    class udoc_plugin::join_project_fn : public convenient_relation_join_project_fn {
#if 0
        udoc_plugin::join_fn   m_joiner;
#endif
        bit_vector             m_to_delete; 

    public:
        join_project_fn(
            udoc_relation const& t1, udoc_relation const& t2, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2, 
            unsigned removed_col_cnt, unsigned const* rm_cols)
            : convenient_relation_join_project_fn(
                t1.get_signature(), t2.get_signature(), 
                col_cnt, cols1, cols2,
                removed_col_cnt, rm_cols)
#if 0
              , m_joiner(t1.get_plugin(), t1, t2, col_cnt, cols1, cols2)
#endif
        {
            unsigned num_bits1 = t1.get_num_bits();
            unsigned num_bits = num_bits1 + t2.get_num_bits();
            unsigned_vector removed_cols(removed_col_cnt, rm_cols);
            t1.expand_column_vector(removed_cols, &t2);
            t1.expand_column_vector(m_cols1);
            t2.expand_column_vector(m_cols2);
            m_to_delete.resize(num_bits, false);
            for (unsigned i = 0; i < removed_cols.size(); ++i) {
                m_to_delete.set(removed_cols[i], true);
            }
        }


        // TBD: replace this by "join" given below.
        virtual relation_base* operator()(relation_base const& t1, relation_base const& t2) {
#if 1
            return join(get(t1), get(t2));
#else
            udoc_relation *joined = get(m_joiner(t1, t2));
            relation_base* result = 0;
            if (joined->fast_empty()) {
                result = t1.get_plugin().mk_empty(get_result_signature());
            }
            else {
                project_fn projector(*joined, m_removed_cols.size(), m_removed_cols.c_ptr());
                result = projector(*joined);
            }
            joined->deallocate();
            return result;
#endif
        }           
    private:

        udoc_relation* join(udoc_relation const& t1, udoc_relation const& t2) {
            relation_signature prod_signature;
            prod_signature.append(t1.get_signature());
            prod_signature.append(t2.get_signature());
            udoc const& d1 = t1.get_udoc();
            udoc const& d2 = t2.get_udoc();
            doc_manager& dm1 = t1.get_dm();
            udoc_plugin& p = t1.get_plugin();
            doc_manager& dm_prod = p.dm(prod_signature);
            udoc_relation* result = get(p.mk_empty(get_result_signature()));
            udoc& res = result->get_udoc();
            doc_manager& dm_res  = result->get_dm();            

            for (unsigned i = 0; i < d1.size(); ++i) {
                for (unsigned j = 0; j < d2.size(); ++j) {
                    doc_ref d(dm_prod, dm_prod.join(d1[i], d2[j], dm1, m_cols1, m_cols2));
                    if (d) {
                        res.insert(dm_res, dm_prod.project(dm_res, m_to_delete, *d));
                        IF_VERBOSE(2, 
                                   if (res.size() > 0 && 0 == res.size() % 10000) {
                                       verbose_stream() << "result size: " << res.size() 
                                                        << " i:" << i << " j:" << j << " "
                                                        << 100*i/d1.size() << "% complete\n";
                                   });
                    }
                }
            }
            TRACE("doc", result->display(tout););
            return result;            
        }
    };


    class udoc_plugin::join_project_and_fn : public relation_join_fn {
    public:
      join_project_and_fn() {}

      virtual relation_base* operator()(relation_base const& t1, relation_base const& t2) {
          udoc_relation *result = get(t1.clone());
          result->get_udoc().intersect(result->get_dm(), get(t2).get_udoc());
          return result;
      }
    };

    relation_join_fn * udoc_plugin::mk_join_project_fn(
        relation_base const& t1, relation_base const& t2,
        unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
        unsigned removed_col_cnt, const unsigned * removed_cols) {    
        if (!check_kind(t1) || !check_kind(t2))
            return 0;
        // special case where we have h(X) :- f(X), g(X).
        if (joined_col_cnt == removed_col_cnt &&
            t1.get_signature().size() == joined_col_cnt &&
            t2.get_signature().size() == joined_col_cnt) {
            for (unsigned i = 0; i < removed_col_cnt; ++i) {
                if (removed_cols[i] != i || cols1[i] != cols2[i])
                    goto general_fn;
            }
            return alloc(join_project_and_fn);
        }

      general_fn:
        return alloc(join_project_fn, get(t1), get(t2),
                     joined_col_cnt, cols1, cols2,
                     removed_col_cnt, removed_cols);
    }


    //
    // Notes:
    // 1. this code could use some cleanup and simplification.
    // 2. It is also not very efficient in the copy routines. 
    //    They fall back to copying each bit instead of a chunk.
    // 3. Argument about correctness is needed as comments.
    // 4. Unit/stress test cases are needed.
    // 
    class udoc_plugin::negation_filter_fn : public relation_intersection_filter_fn {
        struct mk_remove_cols {
            mk_remove_cols(relation_base const& t1, relation_base const& t2, unsigned_vector& remove_cols) {
                unsigned sz1 = t1.get_signature().size();
                unsigned sz2 = t2.get_signature().size();
                for (unsigned i = 0; i < sz2; ++i) {
                    remove_cols.push_back(sz1 + i);
                }                
            }                
        };
        unsigned_vector m_t_cols;
        unsigned_vector m_neg_cols;
        unsigned_vector m_remove_cols;
        mk_remove_cols  m_mk_remove_cols;
        join_project_fn m_join_project;
        bool            m_is_subtract;
        //bool            m_is_aliased;
    public:
        negation_filter_fn(const udoc_relation & t, const udoc_relation & neg, unsigned joined_col_cnt,
                           const unsigned *t_cols, const unsigned *neg_cols)
            : m_t_cols(joined_col_cnt, t_cols), 
              m_neg_cols(joined_col_cnt, neg_cols),
              m_mk_remove_cols(t, neg, m_remove_cols),
              m_join_project(t, neg, joined_col_cnt, t_cols, neg_cols, 
                             m_remove_cols.size(), m_remove_cols.c_ptr()),
              m_is_subtract(false)//,
              /*m_is_aliased(true) */{
            SASSERT(joined_col_cnt > 0 || neg.get_signature().size() == 0);
            m_is_subtract = (joined_col_cnt == t.get_signature().size());
            m_is_subtract &= (joined_col_cnt == neg.get_signature().size());
            svector<bool> found(joined_col_cnt, false);
            for (unsigned i = 0; m_is_subtract && i < joined_col_cnt; ++i) {
                m_is_subtract = !found[t_cols[i]] && (t_cols[i] == neg_cols[i]);
                found[t_cols[i]] = true;
            }
            t.expand_column_vector(m_t_cols);
            neg.expand_column_vector(m_neg_cols);
        }
        
        virtual void operator()(relation_base& tb, const relation_base& negb) {
            udoc_relation& t = get(tb);
            udoc_relation const& n = get(negb);
            IF_VERBOSE(3, t.display(verbose_stream() << "dst:"););
            IF_VERBOSE(3, n.display(verbose_stream() << "neg:"););
            if (t.fast_empty() || n.fast_empty())
                return;

            /* TODO: double check
            if (!m_is_aliased && !p.m_disable_fast_pass) {
                // fast_pass(t, n);
            }
            */
            if (n.get_signature().empty())
                t.get_udoc().reset(t.get_dm());
            else if (m_is_subtract)
                t.get_udoc().subtract(t.get_dm(), n.get_udoc());
            else
                slow_pass(t, n);
        }

    private:
        /*
        void fast_pass(udoc_relation& t, const udoc_relation& n) {
            SASSERT(!m_is_aliased);
            udoc & dst = t.get_udoc();
            udoc const & neg = n.get_udoc();
            doc_manager& dmt = t.get_dm();
            doc_manager& dmn = n.get_dm();
            udoc result;
            for (unsigned i = 0; i < dst.size(); ++i) {
                bool subsumed = false;
                for (unsigned j = 0; j < neg.size(); ++j) {
                    if (dmn.contains(neg[j], m_neg_cols, dst[i], m_t_cols)) {
                        dmt.deallocate(&dst[i]);
                        subsumed = true;
                        break;
                    }
                }
                if (!subsumed)
                    result.push_back(&dst[i]);
            }
            std::swap(dst, result);
        }
        */

        void slow_pass(udoc_relation& t, udoc_relation const& n) {
            doc_manager& dmt = t.get_dm();
            udoc_relation* jp = get(m_join_project(t, n));
            if (!jp->fast_empty()) {
                t.get_udoc().subtract(dmt, jp->get_udoc());
            }
            TRACE("doc", t.display(tout); tout << "\n"; jp->display(tout); tout << "\n";);
            jp->deallocate();
        }
    };

    relation_intersection_filter_fn * udoc_plugin::mk_filter_by_negation_fn(
        const relation_base& t,
        const relation_base& neg, unsigned joined_col_cnt, const unsigned *t_cols,
        const unsigned *negated_cols) {
        if (!check_kind(t) || !check_kind(neg))
            return 0;
        return alloc(negation_filter_fn, get(t), get(neg), joined_col_cnt, t_cols, negated_cols);
    }



    class udoc_plugin::filter_proj_fn : public convenient_relation_project_fn {
        union_find_default_ctx union_ctx;
        doc_manager& dm;
        expr_ref     m_original_condition;
        expr_ref     m_reduced_condition;
        udoc         m_udoc;
        udoc         m_udoc2;
        bit_vector   m_to_delete; // map: col idx -> bool (whether the column is to be removed)
        subset_ints  m_equalities;
        unsigned_vector m_roots;

    public:
        filter_proj_fn(const udoc_relation & t, ast_manager& m, app *condition,
                       unsigned col_cnt, const unsigned * removed_cols) :
            convenient_relation_project_fn(t.get_signature(), col_cnt, removed_cols),
            dm(t.get_dm()),
            m_original_condition(condition, m),
            m_reduced_condition(m),
            m_equalities(union_ctx) {
            unsigned num_bits = t.get_num_bits();
            t.expand_column_vector(m_removed_cols);
            m_to_delete.resize(num_bits, false);
            for (unsigned i = 0; i < num_bits; ++i) {
                m_equalities.mk_var();
            }        
            for (unsigned i = 0; i < m_removed_cols.size(); ++i) {
                m_to_delete.set(m_removed_cols[i], true);
            }
            expr_ref guard(m), non_eq_cond(condition, m);
            t.extract_equalities(condition, non_eq_cond, m_equalities, m_roots);
            t.extract_guard(non_eq_cond, guard, m_reduced_condition);            
            t.compile_guard(guard, m_udoc, m_to_delete);
        }
        
        virtual ~filter_proj_fn() {
            m_udoc.reset(dm);
        }
        virtual relation_base* operator()(const relation_base & tb) {
            udoc_relation const & t = get(tb);
            udoc const& u1 = t.get_udoc();
            doc_manager& dm = t.get_dm();
            m_udoc2.copy(dm, u1);
            m_udoc2.intersect(dm, m_udoc);
            t.apply_guard(m_reduced_condition, m_udoc2, m_equalities, m_to_delete);
            m_udoc2.merge(dm, m_roots, m_equalities, m_to_delete);
            SASSERT(m_udoc2.well_formed(dm));  
            udoc_relation* r = get(t.get_plugin().mk_empty(get_result_signature()));
            doc_manager& dm2 = r->get_dm();
            for (unsigned i = 0; i < m_udoc2.size(); ++i) {
                doc* d = dm.project(dm2, m_to_delete, m_udoc2[i]);
                r->get_udoc().insert(dm2, d);
                SASSERT(r->get_udoc().well_formed(dm2));
            }
            m_udoc2.reset(dm);
            IF_VERBOSE(3, r->display(verbose_stream() << "filter project result:\n"););
            return r;
        }
    };
    relation_transformer_fn * udoc_plugin::mk_filter_interpreted_and_project_fn(
        const relation_base & t, app * condition,
        unsigned removed_col_cnt, const unsigned * removed_cols) {
        return check_kind(t)?alloc(filter_proj_fn, get(t), get_ast_manager(), condition, removed_col_cnt, removed_cols):0;
    }





}
