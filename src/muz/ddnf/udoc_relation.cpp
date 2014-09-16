#include "udoc_relation.h"
#include "dl_relation_manager.h"

namespace datalog {

    udoc_relation::udoc_relation(udoc_plugin& p, relation_signature const& sig):
        relation_base(p, sig),
        dm(p.dm(num_signature_bits(p.bv, sig))) {
        unsigned column = 0;
        for (unsigned i = 0; i < sig.size(); ++i) {
            m_column_info.push_back(column);
            column += p.bv.get_bv_size(sig[i]);
        }
        m_column_info.push_back(column);
    }
    udoc_relation::~udoc_relation() {
        reset();
    }
    unsigned udoc_relation::num_signature_bits(bv_util& bv, relation_signature const& sig) { 
        unsigned result = 0;
        for (unsigned i = 0; i < sig.size(); ++i) {
            result += bv.get_bv_size(sig[i]);
        }
        return result;
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
            VERIFY(get_plugin().bv.is_numeral(f[i], val, bv_size));
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
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    udoc_relation * udoc_relation::complement(func_decl* f) const {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    void udoc_relation::to_formula(expr_ref& fml) const {
        NOT_IMPLEMENTED_YET();
    }
    udoc_plugin& udoc_relation::get_plugin() const {
        return static_cast<udoc_plugin&>(relation_base::get_plugin());
    }

    void udoc_relation::display(std::ostream& out) const {
        NOT_IMPLEMENTED_YET();
    }

    // -------------

    udoc_plugin::udoc_plugin(relation_manager& rm):
        relation_plugin(udoc_plugin::get_name(), rm),
        m(rm.get_context().get_manager()),
        bv(m) {
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

    doc_manager& udoc_plugin::dm(unsigned n) {
        doc_manager* r;
        if (!m_dms.find(n, r)) {
            r = alloc(doc_manager, n);
            m_dms.insert(n, r);
        }
        return *r;
    }
    bool udoc_plugin::can_handle_signature(const relation_signature & s) {
        NOT_IMPLEMENTED_YET();
        return false;
    }
    relation_base * udoc_plugin::mk_empty(const relation_signature & s) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    relation_base * udoc_plugin::mk_full(func_decl* p, const relation_signature & s) {
        NOT_IMPLEMENTED_YET();
        return 0;
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

                if (v1 == tbv::BIT_x) {
                    if (v2 != tbv::BIT_x)
                        pos.set(idx1, v2);
                } else if (v2 == tbv::BIT_x) {
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
                
                if (v1 == tbv::BIT_x && v2 == tbv::BIT_x) {
                    // add to subtracted TBVs: 1xx0 and 0xx1
                    tbv* r = dm.tbv().allocate(pos);
                    r->set(idx1, tbv::BIT_0);
                    r->set(idx2, tbv::BIT_1);
                    neg.push_back(r);
                    
                    r = dm.tbv().allocate(pos);
                    r->set(idx1, tbv::BIT_1);
                    r->set(idx2, tbv::BIT_0);
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
    relation_transformer_fn * udoc_plugin::mk_rename_fn(
        const relation_base & t, unsigned permutation_cycle_len, 
        const unsigned * permutation_cycle) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    relation_union_fn * udoc_plugin::mk_union_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    relation_union_fn * udoc_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    relation_mutator_fn * udoc_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, 
        const unsigned * identical_cols) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    relation_mutator_fn * udoc_plugin::mk_filter_equal_fn(
        const relation_base & t, const relation_element & value, unsigned col) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    relation_mutator_fn * udoc_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

}
