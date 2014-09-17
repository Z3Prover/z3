#include "udoc_relation.h"
#include "dl_relation_manager.h"
#include "qe_util.h"
#include "ast_util.h"

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
    void udoc_relation::expand_column_vector(unsigned_vector& v, udoc_relation* other) const {
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
            d->pos().set(val, hi, lo);
        }
        return d;
    }
    void udoc_relation::add_fact(const relation_fact & f) {
        doc* d = fact2doc(f);
        m_elems.insert(dm, d);
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
            unsigned lo0 = lo;
            bool is_x = true;
            for (unsigned j = lo; j < hi; ++j) {
                switch(t[j]) {
                case BIT_0:
                    if (is_x) is_x = false, lo0 = j, r.reset();
                    break;
                case BIT_1:
                    if (is_x) is_x = false, lo0 = j, r.reset();
                    r += rational::power_of_two(j - lo0);
                    break;
                case BIT_x:
                    if (!is_x) {
                        conjs.push_back(m.mk_eq(p.bv.mk_extract(j-1,lo0,v),
                                                p.bv.mk_numeral(r,j-lo0)));
                    }
                    is_x = true;
                    break;
                default:
                    UNREACHABLE();
                }
            }
            if (!is_x) {
                expr_ref num(m);
                if (lo0 == lo) {
                    num = p.mk_numeral(r, get_signature()[i]);
                    conjs.push_back(m.mk_eq(v, num));
                }
                else {
                    num = p.bv.mk_numeral(r, hi-lo0);
                    conjs.push_back(m.mk_eq(p.bv.mk_extract(hi-1,lo0,v), num));
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
        m_elems.display(dm, out);
    }

    // -------------

    udoc_plugin::udoc_plugin(relation_manager& rm):
        relation_plugin(udoc_plugin::get_name(), rm),
        m(rm.get_context().get_manager()),
        bv(m),
        dl(m) {
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
    expr* udoc_plugin::mk_numeral(rational const& r, sort* s) {
        if (bv.is_bv_sort(s)) {
            return bv.mk_numeral(r, s);
        }
        SASSERT(dl.is_finite_sort(s));
        return dl.mk_numeral(r.get_uint64(), s);
    }
    bool udoc_plugin::is_numeral(expr* e, rational& r, unsigned& num_bits) {
        if (bv.is_numeral(e, r, num_bits)) return true;
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

        void join(doc const& d1, doc const& d2, udoc& result) {
            doc* d = dm.allocateX();
            tbv& pos = d->pos();
            utbv& neg = d->neg();
            unsigned mid = dm1.num_tbits();
            unsigned hi  = dm.num_tbits();
            pos.set(d1.pos(), mid-1, 0);
            pos.set(d2.pos(), hi-1, mid);
            // first fix bits
            for (unsigned i = 0; i < m_cols1.size(); ++i) {
                unsigned idx1 = m_cols1[i];
                unsigned idx2 = mid + m_cols2[i];
                unsigned v1 = pos[idx1];
                unsigned v2 = pos[idx2];

                if (v1 == BIT_x) {
                    if (v2 != BIT_x)
                        pos.set(idx1, v2);
                } else if (v2 == BIT_x) {
                    pos.set(idx2, v1);
                } else if (v1 != v2) {
                    dm.deallocate(d);
                    // columns don't match
                    return;
                }
            }
            // fix equality of don't care columns
            for (unsigned i = 0; i < m_cols1.size(); ++i) {
                unsigned idx1 = m_cols1[i];
                unsigned idx2 = mid + m_cols2[i];
                unsigned v1 = pos[idx1];
                unsigned v2 = pos[idx2];
                
                if (v1 == BIT_x && v2 == BIT_x) {
                    // add to subtracted TBVs: 1xx0 and 0xx1
                    tbv* r = dm.tbv().allocate(pos);
                    r->set(idx1, BIT_0);
                    r->set(idx2, BIT_1);
                    neg.push_back(r);
                    
                    r = dm.tbv().allocate(pos);
                    r->set(idx1, BIT_1);
                    r->set(idx2, BIT_0);
                    neg.push_back(r);
                }
            }

            // handle subtracted TBVs:  1010 -> 1010xxx
            for (unsigned i = 0; i < d1.neg().size(); ++i) {
                tbv* t = dm.tbv().allocate();
                t->set(d1.neg()[i], mid-1, 0);
                t->set(d2.pos(), hi - 1, mid);
                neg.push_back(t);
            }
            for (unsigned i = 0; i < d2.neg().size(); ++i) {
                tbv* t = dm.tbv().allocate();
                t->set(d1.pos(), mid-1, 0);
                t->set(d2.neg()[i], hi - 1, mid);
                neg.push_back(t);
            }            
            result.insert(dm, d);
        }

        virtual relation_base * operator()(const relation_base & _r1, const relation_base & _r2) {
            udoc_relation const& r1 = get(_r1);
            udoc_relation const& r2 = get(_r2);
            udoc_plugin& p = r1.get_plugin();            
            relation_signature const& sig = get_result_signature();
            udoc_relation * result = alloc(udoc_relation, p, sig);
            udoc const& d1 = r1.get_udoc();
            udoc const& d2 = r2.get_udoc();
            udoc& r = result->get_udoc();
            for (unsigned i = 0; i < d1.size(); ++i) {
                for (unsigned j = 0; j < d2.size(); ++j) {
                    join(d1[i], d2[j], r);
                }
            }
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
    relation_transformer_fn * udoc_plugin::mk_project_fn(
        const relation_base & t, unsigned col_cnt, 
        const unsigned * removed_cols) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    class udoc_plugin::rename_fn : public convenient_relation_rename_fn {
        unsigned_vector m_permutation;
    public:
        rename_fn(udoc_relation const& t, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(t.get_signature(), cycle_len, cycle) {
            udoc_plugin& p = t.get_plugin();
            for (unsigned i = 0; i < t.get_num_bits(); ++i) {
                m_permutation.push_back(i);
            }
            unsigned len = t.column_num_bits(cycle[0]);
            for (unsigned i = 0; i < cycle_len; ++i) {
                unsigned j = (i + 1)%cycle_len;
                unsigned col1 = cycle[i];
                unsigned col2 = cycle[j];
                unsigned lo1 = t.column_idx(col1);
                unsigned lo2 = t.column_idx(col2);
                for (unsigned k = 0; k < len; ++k) {
                    m_permutation[k + lo1] = k + lo2;
                }
                SASSERT(column_num_bits(col1) == column_num_bits(col2));
            }
        }

        virtual relation_base * operator()(const relation_base & _r) {
            udoc_relation const& r = get(_r);
            udoc_plugin& p = r.get_plugin();            
            relation_signature const& sig = get_result_signature();
            udoc_relation* result = alloc(udoc_relation, p, sig);
            udoc const& src = r.get_udoc();
            udoc& dst = result->get_udoc();
            doc_manager& dm = r.get_dm();
            for (unsigned i = 0; i < src.size(); ++i) {
                dst.push_back(dm.allocate(src[i], m_permutation.c_ptr()));
            }
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

            TRACE("dl", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););

            udoc_relation& r = get(_r);
            udoc_relation const& src = get(_src);
            udoc_relation* d = get(_delta);
            udoc* d1 = 0;
            if (d) d1 = &d->get_udoc();
            r.get_plugin().mk_union(r.get_dm(), r.get_udoc(), src.get_udoc(), d1);
        }
    };
    void udoc_plugin::mk_union(doc_manager& dm, udoc& dst, udoc const& src, udoc* delta) {
        for (unsigned i = 0; i < src.size(); ++i) {
            doc* d = dm.allocate(src[i]);
            if (dst.insert(dm, d)) {
                if (delta) {
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
            doc_manager& dm = r.get_dm();
            unsigned num_bits = dm.num_tbits();
            m_size = r.column_num_bits(identical_cols[0]);
            m_empty_bv.resize(r.get_num_bits(), false);            
            for (unsigned i = 0; i < col_cnt; ++i) {
                m_cols[i] = r.column_idx(identical_cols[i]);
            }            
            for (unsigned i = 0, e = m_empty_bv.size(); i < e; ++i) {
                m_equalities.mk_var();
            }
        }
        
        virtual void operator()(relation_base & _r) {
            udoc_relation& r = get(_r);
            udoc& d = r.get_udoc();
            for (unsigned i = 1; i < m_cols.size(); ++i) {
                d.fix_eq_bits(m_cols[0], 0, m_cols[i], m_size, m_equalities, m_empty_bv);
            }
            TRACE("dl", tout << "final size: " << r.get_size_estimate_rows() << '\n';);
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
            m_filter->pos().set(r, hi-1, lo);
        }
        virtual ~filter_equal_fn() {
            dm.deallocate(m_filter);
        }        
        virtual void operator()(relation_base & tb) {
            udoc_relation & t = get(tb);
            t.get_udoc().intersect(dm, *m_filter);
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
        ast_manager& m = get_plugin().get_ast_manager();
        expr* e1, *e2;
        if (m.is_and(g) || m.is_or(g) || m.is_not(g) || m.is_true(g) || m.is_false(g)) {
            return is_guard(to_app(g)->get_num_args(), to_app(g)->get_args());
        }
        if (m.is_eq(g, e1, e2)) {
            if (is_var(e1) && is_var(e2)) return false;
            NOT_IMPLEMENTED_YET();
            // TBD
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
    bool udoc_relation::apply_eq(expr* g, udoc& result, var* v, unsigned hi, unsigned lo, expr* c) const {
        udoc_plugin& p = get_plugin();
        unsigned num_bits;
        rational r;
        unsigned idx = v->get_idx();
        unsigned col = column_idx(idx);
        lo += col;
        hi += col;
        if (p.is_numeral(c, r, num_bits)) {
            doc_ref d(dm, dm.allocateX());
            d->pos().set(r, hi, lo);
            result.intersect(dm, *d);
            return true;
        }
        // other cases?
        return false;
    }

    void udoc_relation::apply_guard(
        expr* g, udoc& result, 
        subset_ints& equalities, bit_vector const& discard_cols) const {
        ast_manager& m = get_plugin().get_ast_manager();
        bv_util& bv = get_plugin().bv;
        expr* e1, *e2;
        if (result.empty()) {
        }
        else if (m.is_and(g)) {
            for (unsigned i = 0; !result.empty() && i < to_app(g)->get_num_args(); ++i) {
                apply_guard(to_app(g)->get_arg(i), result, equalities, discard_cols);
            }
        }
        else if (m.is_not(g, e1)) {
            udoc sub;
            sub.push_back(dm.allocateX());
            apply_guard(e1, sub, equalities, discard_cols);
            result.subtract(dm, sub);
        }
        else if (m.is_or(g)) {
            udoc sub;
            sub.push_back(dm.allocateX());
            for (unsigned i = 0; !sub.empty() && i < to_app(g)->get_num_args(); ++i) {
                expr_ref arg(m);
                arg = mk_not(m, to_app(g)->get_arg(i));
                apply_guard(arg, result, equalities, discard_cols);
            }
            result.subtract(dm, sub);
        }
        else if (m.is_true(g)) {
        }
        else if (m.is_false(g)) {
            result.reset(dm);
        }
        else if (is_var(g)) {
            SASSERT(m.is_bool(g));
            unsigned v = to_var(g)->get_idx();
            unsigned idx = column_idx(v);
            doc_manager& dm1 = get_plugin().dm(1);
            tbv_ref bit1(dm1.tbv());
            bit1 = dm1.tbv().allocate1();
            result.fix_eq_bits(idx, bit1.get(), 0, 1, equalities, discard_cols);
        }
        else if (m.is_eq(g, e1, e2) && bv.is_bv(e1)) {
            unsigned hi, lo;
            expr* e3;
            if (is_var(e1) && is_ground(e2) && 
                apply_eq(g, result, to_var(e1), bv.get_bv_size(e1)-1, 0, e2)) {
            }
            else if (is_var(e2) && is_ground(e1) &&
                     apply_eq(g, result, to_var(e2), bv.get_bv_size(e2)-1, 0, e1)) {
            }
            else if (bv.is_extract(e1, lo, hi, e3) && is_var(e3) && is_ground(e2) &&
                     apply_eq(g, result, to_var(e3), hi, lo, e2)) {
            }
            else if (bv.is_extract(e2, lo, hi, e3) && is_var(e3) && is_ground(e1) &&
                     apply_eq(g, result, to_var(e3), hi, lo, e1)) {
            }
            else if (is_var(e1) && is_var(e2)) {
                NOT_IMPLEMENTED_YET();
                // TBD: equalities and discard_cols?                
                var* v1 = to_var(e1);
                var* v2 = to_var(e2);
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
        doc_manager& dm;
        expr_ref     m_condition;
        udoc         m_udoc;
        bit_vector   m_empty_bv;
    public:
        filter_interpreted_fn(const udoc_relation & t, ast_manager& m, app *condition) :
            dm(t.get_dm()),
            m_condition(m) {
            m_empty_bv.resize(t.get_num_bits(), false);
            expr_ref guard(m), rest(m);
            t.extract_guard(condition, guard, m_condition);            
            t.compile_guard(guard, m_udoc, m_empty_bv);
            if (m.is_true(m_condition)) {
                m_condition = 0;
            }
        }

        virtual ~filter_interpreted_fn() {
            m_udoc.reset(dm);
        }
        
        virtual void operator()(relation_base & tb) {
            udoc_relation & t = get(tb);
            udoc& u = t.get_udoc();
            u.intersect(dm, m_udoc);
            if (m_condition && !u.empty()) {
                t.apply_guard(m_condition, u, m_empty_bv);
            }
            TRACE("dl", tout << "final size: " << t.get_size_estimate_rows() << '\n';);
        }
    };
    relation_mutator_fn * udoc_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        return check_kind(t)?alloc(filter_interpreted_fn, get(t), get_ast_manager(), condition):0;
    }

    class udoc_plugin::negation_filter_fn : public relation_intersection_filter_fn {
        const unsigned_vector m_t_cols;
        const unsigned_vector m_neg_cols;
    public:
        negation_filter_fn(const udoc_relation & r, const udoc_relation & neg, unsigned joined_col_cnt,
                           const unsigned *t_cols, const unsigned *neg_cols)
            : m_t_cols(joined_col_cnt, t_cols), m_neg_cols(joined_col_cnt, neg_cols) {
            SASSERT(joined_col_cnt > 0);
        }
        
        virtual void operator()(relation_base& tb, const relation_base& negb) {
            udoc_relation& t = get(tb);
            udoc_relation const& neg = get(negb);
            NOT_IMPLEMENTED_YET();
            // t.m_bitsets.filter_negate(t, neg.m_bitsets, neg, m_t_cols, m_neg_cols);
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
        doc_manager& dm;
        expr_ref     m_condition;
        udoc         m_udoc;
        bit_vector   m_col_list; // map: col idx -> bool (whether the column is to be removed)
    public:
        filter_proj_fn(const udoc_relation & t, ast_manager& m, app *condition,
                       unsigned col_cnt, const unsigned * removed_cols) :
            convenient_relation_project_fn(t.get_signature(), col_cnt, removed_cols),
            dm(t.get_dm()),
            m_condition(m) {
            t.expand_column_vector(m_removed_cols);
            m_col_list.resize(t.get_num_bits(), false);
            for (unsigned i = 0; i < m_removed_cols.size(); ++i) {
                m_col_list.set(m_removed_cols[i]);
            }
            m_removed_cols.push_back(UINT_MAX);
            expr_ref guard(m), rest(m);
            t.extract_guard(condition, guard, m_condition);            
            t.compile_guard(guard, m_udoc, m_col_list);
            if (m.is_true(m_condition)) {
                m_condition = 0;
            }
        }
        
        virtual ~filter_proj_fn() {
            m_udoc.reset(dm);
        }
        virtual relation_base* operator()(const relation_base & tb) {
            udoc_relation const & t = get(tb);
            udoc const& u1 = t.get_udoc();
            udoc  u2;
            // copy u1 -> u2;
            NOT_IMPLEMENTED_YET();
            u2.intersect(dm, m_udoc);
            if (m_condition && !u2.empty()) {
                t.apply_guard(m_condition, u2, m_col_list);
            }
            udoc_relation* res = get(t.get_plugin().mk_empty(get_result_signature()));
            NOT_IMPLEMENTED_YET();
            // u2.project(m_removed_cols, res->get_dm(), res->get_udoc());
            return res;
        }
    };
    relation_transformer_fn * udoc_plugin::mk_filter_interpreted_and_project_fn(
        const relation_base & t, app * condition,
        unsigned removed_col_cnt, const unsigned * removed_cols) {
        return check_kind(t)?alloc(filter_proj_fn, get(t), get_ast_manager(), condition, removed_col_cnt, removed_cols):0;
    }


}
