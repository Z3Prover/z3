/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    product_set.cpp

Abstract:

    Product set.

Author:

    Nikolaj Bjorner (nbjorner) 2014-08-23

Revision History:

--*/

#include "product_set.h"
#include "bv_decl_plugin.h"
#include "dl_relation_manager.h"
#include "bool_rewriter.h"

namespace datalog {

    product_set::product_set(
        product_set_plugin& p, relation_signature const& s, 
        bool is_empty, T const& t):
        vector_relation(p, s, is_empty, t), m_refs(0) {
        for (unsigned i = 0; i < s.size(); ++i) {
            (*this)[i] = bit_vector(p.set_size(s[i]));
        }
    }


    unsigned product_set::get_hash() const {
        unsigned hash = 0;
        for (unsigned i = 0; i < get_signature().size(); ++i) {
            hash ^= (*this)[i].get_hash();
        }
        return hash;
    }

    bool product_set::operator==(product_set const& p) const {
        for (unsigned i = 0; i < get_signature().size(); ++i) {
            if ((*this)[i] != p[i]) return false;
        }
        return true;            
    }

    bool product_set::contains(product_set const& p) const {
        for (unsigned i = 0; i < get_signature().size(); ++i) {
            if ((*this)[i].contains(p[i])) return false;
        }
        return true;            
    }

    void product_set::add_fact(const relation_fact & f) {
        UNREACHABLE();
    }
    bool product_set::contains_fact(const relation_fact & f) const {
        return false;
    }
    relation_base * product_set::clone() const {
        UNREACHABLE();
        return 0;
    }
    relation_base * product_set::complement(func_decl*) const {
        UNREACHABLE();
        return 0;
    }
    void product_set::to_formula(expr_ref& fml) const {
        ast_manager& m = fml.get_manager();
        bv_util bv(m);
        expr_ref_vector conjs(m), disjs(m);
        relation_signature const& sig = get_signature();
        if (m_empty) {
            fml = m.mk_false();
            return;
        }
        for (unsigned i = 0; i < sig.size(); ++i) {
            sort* ty = sig[i];
            expr_ref var(m.mk_var(i, ty), m);
            unsigned j = find(i);
            if (i != j) {
                conjs.push_back(m.mk_eq(var, m.mk_var(j, sig[j])));
                continue;
            }            
            T const& t = (*this)[i];
            disjs.reset();
            for (j = 0; j < t.size(); ++j) {
                if (t.get(j)) {
                    disjs.push_back(m.mk_eq(var, bv.mk_numeral(rational(j), ty)));
                }
            }
            if (disjs.empty()) {
                UNREACHABLE();
                fml = m.mk_false();
                return;
            }
            if (disjs.size() == 1) {
                conjs.push_back(disjs[0].get());
            }
            else {
                conjs.push_back(m.mk_or(disjs.size(), disjs.c_ptr()));
            }
        }
        bool_rewriter br(m);
        br.mk_and(conjs.size(), conjs.c_ptr(), fml);
    }    
    void product_set::display_index(unsigned i, const T& t, std::ostream& out) const {
        out << i << ":";
        t.display(out);
    }
    bool product_set::mk_intersect(unsigned idx, T const& t) {
        if (!m_empty) {
            (*this)[idx] &= t;
            m_empty = is_empty(idx, (*this)[idx]);
        }
        return !m_empty;
    }

    // product_set_relation


    product_set_relation::product_set_relation(product_set_plugin& p, relation_signature const& s):
        relation_base(p, s) {
    }

    product_set_relation::~product_set_relation() {
        product_sets::iterator it = m_elems.begin(), end = m_elems.end();
        for (; it != end; ++it) {
            (*it)->dec_ref();
        }
    }

    void product_set_relation::add_fact(const relation_fact & f) {
        ast_manager& m = get_plugin().get_ast_manager(); 
        bv_util bv(m);
        rational v;
        unsigned bv_size;
        product_set* s = alloc(product_set, get_plugin(), get_signature(), false);
        for (unsigned i = 0; i < f.size(); ++i) {
            VERIFY(bv.is_numeral(f[i], v, bv_size));
            SASSERT(v.is_unsigned());
            (*s)[i] = bit_vector(get_plugin().set_size(m.get_sort(f[i])));
            (*s)[i].set(v.get_unsigned(), true);
        }
        s->display(std::cout << "fact");
        if (m_elems.contains(s)) {
            dealloc(s);
        }
        else {
            s->inc_ref();
            m_elems.insert(s);
        }

    }
    bool product_set_relation::contains_fact(const relation_fact & f) const {
        std::cout << "contains fact\n";
        NOT_IMPLEMENTED_YET();
        return false;
    }
    product_set_relation * product_set_relation::clone() const {
        product_set_relation* r = alloc(product_set_relation, get_plugin(), get_signature());
        product_sets::iterator it = m_elems.begin(), end = m_elems.end();
        for (; it != end; ++it) {
            // TBD: have to copy because other operations are destructive.
            (*it)->inc_ref();
            r->m_elems.insert(*it);
        }
        return r;
    }
    product_set_relation * product_set_relation::complement(func_decl*) const {
        std::cout << "complement\n";
        NOT_IMPLEMENTED_YET();
        return 0;
    }
    void product_set_relation::to_formula(expr_ref& fml) const {
        product_sets::iterator it = m_elems.begin(), end = m_elems.end();
        ast_manager& m = get_plugin().get_manager().get_context().get_manager();
        expr_ref_vector disjs(m);
        for (; it != end; ++it) {
            (*it)->to_formula(fml);
            disjs.push_back(fml);
        }
        fml = m.mk_or(disjs.size(), disjs.c_ptr());
    }
    product_set_plugin& product_set_relation::get_plugin() const {
        return static_cast<product_set_plugin&>(relation_base::get_plugin());
    }

    void product_set_relation::display(std::ostream& out) const {
        product_sets::iterator it = m_elems.begin(), end = m_elems.end();
        for (; it != end; ++it) {
            (*it)->display(out);
        }
    }
    
    // product_set_plugin
    
    product_set_plugin::product_set_plugin(relation_manager& rm):
        relation_plugin(product_set_plugin::get_name(), rm) {
    }

    bool product_set_plugin::can_handle_signature(const relation_signature & sig) {
        bv_util bv(get_manager().get_context().get_manager());
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (!bv.is_bv_sort(sig[i])) return false;
        }
        return true;
    }

    product_set_relation& product_set_plugin::get(relation_base& r) {
        return dynamic_cast<product_set_relation&>(r);
    }
    product_set_relation* product_set_plugin::get(relation_base* r) {
        return r?dynamic_cast<product_set_relation*>(r):0;
    }
    product_set_relation const & product_set_plugin::get(relation_base const& r) {
        return dynamic_cast<product_set_relation const&>(r);        
    }
    relation_base * product_set_plugin::mk_empty(const relation_signature & s) {
        return alloc(product_set_relation, *this, s);
    }
    relation_base * product_set_plugin::mk_full(func_decl* p, const relation_signature & sig) {
        product_set_relation* result = alloc(product_set_relation, *this, sig);
        product_set* s = alloc(product_set, *this, sig, false);
        s->inc_ref();
        for (unsigned i = 0; i < sig.size(); ++i) {
            bit_vector& t = (*s)[i];
            t = bit_vector(set_size(sig[i]));
            for (unsigned j = 0; j < t.size(); ++j) {
                t.set(j, true);
            }
        }
        result->m_elems.insert(s);
        return result;
    }
    product_set* product_set_plugin::insert(product_set* s, product_set_relation* r) {
        if (s->empty()) {
            s->reset();
        }
        else if (r->m_elems.contains(s)) {
            s->reset();
        }
        else {
            s->inc_ref();
            r->m_elems.insert(s);
            s = alloc(product_set, *this, r->get_signature(), false);
        }
        return s;
    }

    unsigned product_set_plugin::set_size(sort* ty) {
        bv_util bv(get_ast_manager());
        unsigned bv_size = bv.get_bv_size(ty);
        SASSERT(bv_size <= 16);
        if (bv_size > 16) {
            throw default_exception("bit-vector based sets are not suitable for this domain size");
        }
        return 1 << bv_size;
    }

    class product_set_plugin::join_fn : public convenient_relation_join_fn {
    public:
        join_fn(const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2){
        }

        virtual relation_base * operator()(const relation_base & _r1, const relation_base & _r2) {
            product_set_relation const& r1 = get(_r1);
            product_set_relation const& r2 = get(_r2);
            product_set_plugin& p = r1.get_plugin();
            relation_signature const& sig = get_result_signature();
            product_set_relation * result = alloc(product_set_relation, p, sig);
            product_set* s = alloc(product_set, p, sig, false);
            product_sets::iterator it1 = r1.m_elems.begin(), end1 = r1.m_elems.end();
            for (; it1 != end1; ++it1) {
                product_sets::iterator it2 = r2.m_elems.begin(), end2 = r2.m_elems.end();
                for (; it2 != end2; ++it2) {
                    s->mk_join(*(*it1), *(*it2), m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
                    s = p.insert(s, result);
                }
            }
            dealloc(s);
            return result;
        }
    };
    relation_join_fn * product_set_plugin::mk_join_fn(
        const relation_base & r1, const relation_base & r2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(r1) || !check_kind(r2)) {
            return 0;
        }
        return alloc(join_fn, r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2);
    }

    class product_set_plugin::project_fn : public convenient_relation_project_fn {
    public:
        project_fn(const relation_signature & orig_sig, unsigned removed_col_cnt, 
                   const unsigned * removed_cols) 
            : convenient_relation_project_fn(orig_sig, removed_col_cnt, removed_cols) {
        }

        virtual relation_base * operator()(const relation_base & _r) {
            product_set_relation const& r = get(_r);
            product_set_plugin& p = r.get_plugin();
            relation_signature const& sig = get_result_signature();
            product_set_relation* result = alloc(product_set_relation, p, sig);
            product_set* s = alloc(product_set, p, sig, false);
            product_sets::iterator it = r.m_elems.begin(), end = r.m_elems.end();
            for (; it != end; ++it) {
                s->mk_project(*(*it), m_removed_cols.size(), m_removed_cols.c_ptr());
                s = p.insert(s, result);
            }
            dealloc(s);
            return result;
        }
    };
    relation_transformer_fn * product_set_plugin::mk_project_fn(
        const relation_base & r, unsigned col_cnt, 
        const unsigned * removed_cols) {
        if (check_kind(r)) {
            return alloc(project_fn, r.get_signature(), col_cnt, removed_cols);
        }
        else {
            return 0;
        }
    }
    class product_set_plugin::rename_fn : public convenient_relation_rename_fn {
    public:
        rename_fn(const relation_signature & orig_sig, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(orig_sig, cycle_len, cycle) {
        }

        virtual relation_base * operator()(const relation_base & _r) {
            product_set_relation const& r = get(_r);
            product_set_plugin& p = r.get_plugin();
            relation_signature const& sig = get_result_signature();
            product_set_relation* result = alloc(product_set_relation, p, sig);
            product_set* s = alloc(product_set, p, sig, false);
            product_sets::iterator it = r.m_elems.begin(), end = r.m_elems.end();
            for (; it != end; ++it) {
                s->mk_rename(*(*it), m_cycle.size(), m_cycle.c_ptr());
                s = p.insert(s, result);
            }
            dealloc(s);
            return result;
        }
    };

    relation_transformer_fn * product_set_plugin::mk_rename_fn(const relation_base & r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if (check_kind(r)) {
            return alloc(rename_fn, r.get_signature(), cycle_len, permutation_cycle);
        }
        else {
            return 0;
        }
    }

    class product_set_plugin::union_fn : public relation_union_fn {
    public:
        union_fn() {}

        virtual void operator()(relation_base & _r, const relation_base & _src, relation_base * _delta) {

            TRACE("dl", _r.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););

            product_set_relation& r = get(_r);
            product_set_relation const& src = get(_src);
            product_set_relation* d = get(_delta);
            product_sets::iterator it = src.m_elems.begin(), end = src.m_elems.end();
            for (; it != end; ++it) {
                product_set* ps = *it;
                if (!r.m_elems.contains(ps)) {
                    ps->inc_ref();
                    r.m_elems.insert(ps);
                    if (d) {
                        ps->inc_ref();
                        d->m_elems.insert(ps);
                    }
                }
            }
        }
    };
    relation_union_fn * product_set_plugin::mk_union_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return 0;
        }
        return alloc(union_fn);
    }
    relation_union_fn * product_set_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, 
        const relation_base * delta) {
        return mk_union_fn(tgt, src, delta);
    }


    class product_set_plugin::filter_identical_fn : public relation_mutator_fn {
        unsigned_vector m_identical_cols;
    public:
        filter_identical_fn(unsigned col_cnt, const unsigned * identical_cols) 
            : m_identical_cols(col_cnt, identical_cols) {}

        virtual void operator()(relation_base & _r) {
            product_set_relation & r = get(_r);
            product_set_plugin& p = r.get_plugin();
            ptr_vector<product_set> elems;
            product_sets::iterator it = r.m_elems.begin(), end = r.m_elems.end();
            for (; it != end; ++it) {
                elems.push_back(*it);
            }
            r.m_elems.reset();
            for (unsigned i = 0; i < elems.size(); ++i) {
                product_set* s = elems[i];
                if (equate(*s)) {
                    r.m_elems.insert(s);
                }
                else {
                    s->dec_ref();
                }                
            }
        }
    private:
        bool equate(product_set& dst) {
            for (unsigned i = 1; !dst.empty() && i < m_identical_cols.size(); ++i) {
                unsigned c1 = m_identical_cols[0];
                unsigned c2 = m_identical_cols[i];
                dst.equate(c1, c2);
            }
            return !dst.empty();
        }
    };
    relation_mutator_fn * product_set_plugin::mk_filter_identical_fn(
        const relation_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        return check_kind(t)?alloc(filter_identical_fn, col_cnt, identical_cols):0;
    }

    class product_set_plugin::filter_equal_fn : public relation_mutator_fn {
        unsigned   m_col;
        bit_vector m_value;
    public:
        filter_equal_fn(product_set_plugin& p, const relation_element & value, unsigned col, bool is_eq) 
            : m_col(col) {
            ast_manager& m = p.get_ast_manager();
            // m.get_context().get_manager()
            bv_util bv(m);
            rational v;
            unsigned bv_size;
            unsigned sz = p.set_size(m.get_sort(value));
            VERIFY(bv.is_numeral(value, v, bv_size));
            SASSERT(v.is_unsigned());
            unsigned w = v.get_unsigned();
            SASSERT(w < sz);
            m_value = bit_vector(sz);
            if (is_eq) {
                m_value.set(w, true);
            }
            else {
                for (unsigned i = 0; i < sz; ++i) {
                    m_value.set(i, i != w);
                }
            }
        }

        virtual void operator()(relation_base & _r) {
            product_set_relation & r = get(_r);
            product_set_plugin & p = r.get_plugin();

            ptr_vector<product_set> elems;
            product_sets::iterator it = r.m_elems.begin(), end = r.m_elems.end();
            for (; it != end; ++it) {
                elems.push_back(*it);
            }
            r.m_elems.reset();
            for (unsigned i = 0; i < elems.size(); ++i) {
                product_set* s = elems[i];
                
                if (s->mk_intersect(m_col, m_value)) {
                    r.m_elems.insert(s);
                }
                else {
                    s->dec_ref();
                }                
            }            
        }
    };

    relation_mutator_fn * product_set_plugin::mk_filter_equal_fn(const relation_base & r, 
        const relation_element & value, unsigned col) {
        return check_kind(r)?alloc(filter_equal_fn, *this, value, col, true):0;
    }

    relation_mutator_fn * product_set_plugin::mk_filter_interpreted_fn(
        const relation_base & t, app * condition) {
        ast_manager& m =get_manager().get_context().get_manager();
        std::cout << "filter interpreted '" << mk_pp(condition, m) << "'\n";            
        NOT_IMPLEMENTED_YET();
        return 0;
    }


};

