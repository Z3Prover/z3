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

    static unsigned s_ps_num_bits = 0;
    static unsigned s_num_ps = 0;

    product_set::product_set(
        product_set_plugin& p, relation_signature const& s, 
        initial_t init, T const& t):
        vector_relation<bit_vector>(p, s, false, t), m_refs(0) {
        unsigned delta = 0;
        for (unsigned i = 0; i < s.size(); ++i) {
            unsigned sz = p.set_size(s[i]);
            (*this)[i].resize(sz);
            if (init == FULL_t) {
                (*this)[i].neg();
            }
            delta += sz;
        }
        s_ps_num_bits += delta;
        s_num_ps ++;
        if ((s_num_ps % 1000) == 0) {
            std::cout << s_num_ps << " " << s_ps_num_bits << " " << delta << "\n";
        }
    }

    product_set::~product_set() {
        relation_signature const& s = get_signature();
        product_set_plugin& p = dynamic_cast<product_set_plugin&>(get_plugin());
        for (unsigned i = 0; i < s.size(); ++i) {
            unsigned sz = p.set_size(s[i]);
            s_ps_num_bits -= sz;
        }        
        --s_num_ps;
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
    void product_set::reset() {        
        for (unsigned i = 0; i < get_signature().size(); ++i) {
            (*this)[i].fill0();
        }        
    }
    void product_set::add_fact(const relation_fact & f) {
        UNREACHABLE();
    }
    bool product_set::contains_fact(const relation_fact & f) const {
        UNREACHABLE();
        return false;
    }
    relation_base * product_set::clone() const {
        product_set* result = alloc(product_set, dynamic_cast<product_set_plugin&>(get_plugin()), get_signature(), EMPTY_t);
        result->copy(*this);
        return result;
    }
    relation_base * product_set::complement(func_decl*) const {
        product_set* result = alloc(product_set, dynamic_cast<product_set_plugin&>(get_plugin()), get_signature(), EMPTY_t);
        result->copy(*this);
        result->complement();
        return result;
    }

    void product_set::complement() {
        for (unsigned i = 0; i < get_signature().size(); ++i) {
            (*this)[i].neg();
        }        
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
        reset();
    }

    class product_set_plugin::filter_interpreted_fn : public relation_mutator_fn {
        app_ref m_condition;
    public:
        filter_interpreted_fn(ast_manager& m, app* condition): m_condition(condition, m) {
            
        };
        virtual ~filter_interpreted_fn() {}
        
        virtual void operator()(relation_base & _r) {
            ast_manager& m = m_condition.get_manager();
            if (m.is_false(m_condition)) {
                product_set_relation & r = get(_r);
                r.reset();
                return;
            }
            if (m.is_true(m_condition)) {
                return;
            }
            product_set_relation & r = get(_r);
            product_set_plugin & p = r.get_plugin();
            NOT_IMPLEMENTED_YET();
        }
    };

    void product_set_relation::add_fact(const relation_fact & f) {
        ast_manager& m = get_plugin().get_ast_manager(); 
        bv_util bv(m);
        product_set* s = alloc(product_set, get_plugin(), get_signature(), product_set::EMPTY_t);
        rational v;
        unsigned bv_size;
        // the bit-vector sets are empty at this point so they need to be primed.
        for (unsigned i = 0; i < f.size(); ++i) {
            VERIFY(bv.is_numeral(f[i], v, bv_size));
            SASSERT(v.is_unsigned());
            (*s)[i].set(v.get_unsigned(), true);
        }
        // s->display(std::cout << "fact");
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
            product_set* ps = dynamic_cast<product_set*>((*it)->clone());
            ps->inc_ref();
            r->m_elems.insert(ps);
        }
        return r;
    }
    void product_set_relation::reset() {
        product_sets::iterator it = m_elems.begin(), end = m_elems.end();
        for (; it != end; ++it) {
            (*it)->dec_ref();
        }
        m_elems.reset();
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
        relation_plugin(product_set_plugin::get_name(), rm),
        m(rm.get_context().get_manager()),
        bv(m) {
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
        product_set* s = alloc(product_set, *this, sig, product_set::FULL_t);
        s->inc_ref();
        result->m_elems.insert(s);
        return result;
    }
    product_set* product_set_plugin::insert(product_set* s, product_set_relation* r) {
        if (s->empty()) {
            s->reset();
            s->complement();
        }
        else if (r->m_elems.contains(s)) {
            s->reset();
            s->complement();
        }
        else {
            s->inc_ref();
            r->m_elems.insert(s);
            s = alloc(product_set, *this, r->get_signature(), product_set::FULL_t);
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
            product_set* s = alloc(product_set, p, sig, product_set::FULL_t);
            product_sets::iterator it1 = r1.m_elems.begin(), end1 = r1.m_elems.end();
            for (; it1 != end1; ++it1) {
                product_sets::iterator it2 = r2.m_elems.begin(), end2 = r2.m_elems.end();
                for (; it2 != end2; ++it2) {
                    s->mk_join(*(*it1), *(*it2), m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
                    s = p.insert(s, result);
                }
            }
            dealloc(s);
            std::cout << "join " << result->m_elems.size() << "\n";
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
            product_set* s = alloc(product_set, p, sig, product_set::FULL_t);
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
            product_set* s = alloc(product_set, p, sig, product_set::FULL_t);
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
            r.get_plugin().mk_union(r, src, d);
            std::cout << "union: " << r.m_elems.size() << "\n";
        }
    };
    void product_set_plugin::mk_union(
        product_set_relation& dst, product_set_relation const& src, product_set_relation* delta) {
        product_sets::iterator it = src.m_elems.begin(), end = src.m_elems.end();
        for (; it != end; ++it) {
            product_set* ps = *it;
            if (!dst.m_elems.contains(ps)) {
                ps->inc_ref();
                dst.m_elems.insert(ps);
                if (delta) {
                    ps->inc_ref();
                    delta->m_elems.insert(ps);
                }
            }
        }
    }
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


    class product_set_plugin::filter_mask_fn : public relation_mutator_fn {
        unsigned   m_col;        
        bit_vector m_mask;
    public:
        filter_mask_fn(product_set_plugin& p, bit_vector const& mask, unsigned col) 
            : m_col(col), m_mask(mask) {
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
                
                if (s->mk_intersect(m_col, m_mask)) {
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
        bit_vector mask;
        expr* v = value;
        extract_mask(1, &v, mask);
        return check_kind(r)?alloc(filter_mask_fn, *this, mask, col):0;
    }

    class product_set_plugin::filter_by_union_fn : public relation_mutator_fn {
        ptr_vector<relation_mutator_fn> m_mutators;
    public:
        filter_by_union_fn(unsigned n, relation_mutator_fn ** mutators):
            m_mutators(n, mutators) {            
        }
        virtual ~filter_by_union_fn() {
            std::for_each(m_mutators.begin(), m_mutators.end(), delete_proc<relation_mutator_fn>());
        }
        
        virtual void operator()(relation_base& _r) {
            product_set_relation & r = get(_r);
            product_set_plugin & p = r.get_plugin();

            SASSERT(!m_mutators.empty());
            if (m_mutators.size() == 1) {
                (*(m_mutators[0]))(r);
                return;
            }
            product_set_relation src(p, r.get_signature());
            for (unsigned i = 1; i < m_mutators.size(); ++i) {
                product_set_relation* r1 = r.clone();
                (*(m_mutators[i]))(*r1);
                p.mk_union(src, *r1, 0);
                r1->deallocate();
            }
            (*(m_mutators[0]))(r);
            p.mk_union(r, src, 0);
        }
    };

    product_set_plugin::decomp_t product_set_plugin::decompose(expr* condition, expr_ref_vector& args, unsigned& col) {
        args.reset();
        expr* e1, *e2;
        app* value;
        if (m.is_not(condition, e1) && m.is_not(e1, e2)) {
            return decompose(e2, args, col);
        }
        if (m.is_not(condition, e1) && m.is_and(e1)) {
            expr_ref tmp(m);
            app* a = to_app(e1);
            unsigned sz = a->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                args.push_back(mk_not(a->get_arg(i)));
            }
            tmp = m.mk_or(args.size(), args.c_ptr());
            return decompose(tmp, args, col);
        }
        if (m.is_not(condition, e1) && m.is_or(e1)) {
            expr_ref tmp(m);
            app* a = to_app(e1);
            unsigned sz = a->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                args.push_back(mk_not(a->get_arg(i)));
            }
            tmp = m.mk_and(args.size(), args.c_ptr());
            return decompose(tmp, args, col);
        }
        if (m.is_and(condition)) {
            app* a = to_app(condition);
            unsigned sz = a->get_num_args();
            args.append(sz, a->get_args());
            return AND_d;
        }
        if (is_setof(condition, args, col)) {
            SASSERT(!args.empty());
            return SET_d;
        }
        if (m.is_or(condition)) {
            app* a = to_app(condition);
            unsigned sz = a->get_num_args();
            args.append(sz, a->get_args());
            return OR_d;
        }
        if (is_value_ne(condition, value, col)) {
            args.push_back(value);
            return NE_d;
        }
        if (is_value_eq(condition, value, col)) {
            args.push_back(value);
            return EQ_d;
        }
        if (m.is_not(condition, e1) && m.is_true(e1)) {
            return F_d;
        }
        if (m.is_false(condition)) {
            return F_d;
        }
        if (m.is_not(condition, e1) && m.is_false(e1)) {
            return T_d;
        }
        if (m.is_true(condition)) {
            return T_d;
        }
        return UNHANDLED_d;
    }

    bool product_set_plugin::mk_filter_interpreted(
        const relation_base & t, expr_ref_vector const& args,
        ptr_vector<relation_mutator_fn>& mutators) {
        unsigned sz = args.size();
        
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg = args[i];
            if (!is_app(arg)) {
                break;
            }
            relation_mutator_fn* mut = mk_filter_interpreted_fn(t, to_app(arg));
            if (!mut) {
                break;
            }
            mutators.push_back(mut);
        }
        if (mutators.size() < sz) {
            std::for_each(mutators.begin(), mutators.end(), delete_proc<relation_mutator_fn>());
            return false;
        }
        else {
            return true;
        }        
    }
    relation_mutator_fn * product_set_plugin::mk_filter_interpreted_fn(
        const relation_base & t, app * condition) {
        if (!check_kind(t)) return 0;
        unsigned col;
        ptr_vector<relation_mutator_fn> mutators;
        expr_ref_vector args(m);
        bit_vector mask;
        switch (decompose(condition, args, col)) {
        case NE_d:
            SASSERT(args.size() == 1);
            extract_mask(1, args.c_ptr(), mask);            
            mask.neg();
            return alloc(filter_mask_fn, *this, mask, col);
        case EQ_d:
            SASSERT(args.size() == 1);
            extract_mask(1, args.c_ptr(), mask);            
            return alloc(filter_mask_fn, *this, mask, col);
        case AND_d: 
            if (!mk_filter_interpreted(t, args, mutators)) {
                return 0;
            } 
            return get_manager().mk_apply_sequential_fn(mutators.size(), mutators.c_ptr());
        case OR_d: 
            if (!mk_filter_interpreted(t, args, mutators)) {
                return 0;
            } 
            return alloc(filter_by_union_fn, mutators.size(), mutators.c_ptr());
        case F_d:
            return alloc(filter_interpreted_fn, m, m.mk_false());
        case T_d:
            return alloc(filter_interpreted_fn, m, m.mk_true());
        case SET_d:
            extract_mask(args.size(), args.c_ptr(), mask);
            return alloc(filter_mask_fn, *this, mask, col);
        case UNHANDLED_d:
            std::cout << "filter interpreted unhandled '" << mk_pp(condition, m) << "'\n";            
            NOT_IMPLEMENTED_YET();
            return 0;
        default:
            UNREACHABLE();
        }
        return 0;
    }

    void product_set_plugin::extract_mask(unsigned n, expr* const* values, bit_vector& mask) {
        SASSERT(n > 0);
        unsigned sz = set_size(m.get_sort(values[0]));
        mask.resize(sz, false);
        rational v;
        unsigned bv_size;
        for (unsigned i = 0; i < n; ++i) {
            expr* value = values[i];
            VERIFY(bv.is_numeral(value, v, bv_size));
            SASSERT(v.is_unsigned());
            unsigned w = v.get_unsigned();
            SASSERT(w < sz);
            mask.set(w, true);
        }
    }

    bool product_set_plugin::is_setof(expr* condition, expr_ref_vector& values, unsigned & col) {
        if (!m.is_or(condition)) return false;
        unsigned sz = to_app(condition)->get_num_args();
        col = UINT_MAX;
        unsigned col1;
        if (sz == 0) return false;
        values.reset();
        app* value;
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg = to_app(condition)->get_arg(i);
            if (is_value_eq(arg, value, col1)) {
                if (col == UINT_MAX) {
                    col = col1;
                    values.push_back(value);
                }
                else if (col != col1) {
                    return false;
                }
                else {
                    values.push_back(value);
                }
            }
            else {
                return false;
            }
        }
        return true;
    }

    bool product_set_plugin::is_value_eq(expr* e, app*& value, unsigned& col) {
        expr* e1, *e2;
        rational val;
        unsigned bv_size;
        if (!m.is_eq(e, e1, e2)) return false;
        if (!is_var(e1)) std::swap(e1, e2);
        if (!is_var(e1)) return false;
        if (!bv.is_numeral(e2, val, bv_size)) return false;
        if (!val.is_unsigned()) return false;
        value = to_app(e2);
        col = to_var(e1)->get_idx();
        return true;
    }

    bool product_set_plugin::is_value_ne(expr* condition, relation_element& value, unsigned& col) {
        expr* e;
        if (m.is_not(condition, e)) {
            return is_value_eq(e, value, col);
        }
        else {
            return false;
        }
    }


};

