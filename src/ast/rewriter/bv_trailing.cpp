/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_trailing.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "ast/rewriter/bv_trailing.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"

// The analyzer gives up analysis after going TRAILING_DEPTH deep.
// This number shouldn't be too big.
#define  TRAILING_DEPTH 5

struct bv_trailing::imp {
    typedef rational numeral;
    typedef obj_map<expr, std::pair<unsigned,unsigned> > map;
    mk_extract_proc&     m_mk_extract;
    bv_util&             m_util;
    ast_manager&         m;

    // keep a cache for each depth, using the convention that m_count_cache[TRAILING_DEPTH] is top-level
    map*                 m_count_cache[TRAILING_DEPTH + 1];

    imp(mk_extract_proc& mk_extract)
        : m_mk_extract(mk_extract)
        , m_util(mk_extract.bvutil())
        , m(mk_extract.m()) {
        TRACE("bv-trailing", tout << "ctor\n";);

            for (unsigned i = 0; i <= TRAILING_DEPTH; ++i)
                m_count_cache[i] = nullptr;
    }

    virtual ~imp() {
        TRACE("bv-trailing", tout << "dtor\n";);
        reset_cache(0);
    }

    br_status eq_remove_trailing(expr * e1, expr * e2, expr_ref& result) {
        TRACE("bv-trailing", tout << mk_pp(e1, m) << "\n=\n" << mk_pp(e2, m) << "\n";);
        SASSERT(m_util.is_bv(e1) && m_util.is_bv(e2));
        SASSERT(m_util.get_bv_size(e1) == m_util.get_bv_size(e2));
        unsigned max1, min1, max2, min2;
        count_trailing(e1, min1, max1, TRAILING_DEPTH);
        count_trailing(e2, min2, max2, TRAILING_DEPTH);
        if (min1 > max2 || min2 > max1) { // bounds have empty intersection
            result = m.mk_false();
            return BR_DONE;
        }
        const unsigned min = std::min(min1, min2); // remove the minimum of the two lower bounds
        if (min == 0) { // nothing to remove
            return BR_FAILED;
        }
        const unsigned sz  = m_util.get_bv_size(e1);
        if (min == sz) { // everything removed, unlikely but we check anyhow for safety
            result = m.mk_true();
            return BR_DONE;
        }
        expr_ref out1(m);
        expr_ref out2(m);
        VERIFY(min == remove_trailing(e1, min, out1, TRAILING_DEPTH));
        VERIFY(min == remove_trailing(e2, min, out2, TRAILING_DEPTH));
        const bool are_eq = m.are_equal(out1, out2);
        result = are_eq ? m.mk_true() : m.mk_eq(out1, out2);
        return are_eq ? BR_DONE : BR_REWRITE2;
    }

    // This routine needs to be implemented carefully so that whenever it
    // returns a lower bound on trailing zeros min, the routine remove_trailing
    // must be capable of removing at least that many zeros from the expression.
    void count_trailing(expr * e, unsigned& min, unsigned& max, unsigned depth) {
        SASSERT(e && m_util.is_bv(e));
        if (is_cached(depth, e, min, max)) return;
        count_trailing_core(e, min, max, depth);
        TRACE("bv-trailing", tout << mk_pp(e, m) << "\n:" << min << " - " << max << "\n";);
        SASSERT(min <= max);
        SASSERT(max <= m_util.get_bv_size(e));
        cache(depth, e, min, max);  // store result into the cache
    }

    unsigned remove_trailing(expr * e, unsigned n, expr_ref& result, unsigned depth) {
        const unsigned retv = remove_trailing_core(e, n, result, depth);
        TRACE("bv-trailing", tout << mk_pp(e, m) << "\n--->\n" <<  retv << ": " << result  << "\n";);
        return retv;
    }

    // Assumes that count_trailing gives me a lower bound that we can also remove from each summand.
    unsigned remove_trailing_add(app * a, unsigned n, expr_ref& result, unsigned depth) {
        SASSERT(m_util.is_bv_add(a));
        if (depth <= 1) {
            result = a;
            return 0;
        }
        unsigned min, max;
        count_trailing(a, min, max, depth); // caching is important here
        const unsigned to_rm = std::min(min, n);
        if (to_rm == 0) {
            result = a;
            return 0;
        }

        const unsigned sz = m_util.get_bv_size(a);

        if (to_rm == sz) {
            result = nullptr;
            return sz;
        }

        expr_ref_vector new_args(m);
        expr_ref tmp(m);
        for (expr * curr : *a) {
            VERIFY(to_rm == remove_trailing(curr, to_rm, tmp, depth - 1));
            new_args.push_back(std::move(tmp));
        }
        result = m.mk_app(m_util.get_fid(), OP_BADD, new_args.size(), new_args.c_ptr());
        return to_rm;
    }

    unsigned remove_trailing_mul(app * a, unsigned n, expr_ref& result, unsigned depth) {
        SASSERT(m_util.is_bv_mul(a));
        const unsigned num  = a->get_num_args();
        if (depth <= 1 || !num) {
            result = a;
            return 0;
        }
        expr_ref tmp(m);
        expr * const coefficient = a->get_arg(0);
        const unsigned retv = remove_trailing(coefficient, n, tmp, depth - 1);
        SASSERT(retv <= n);
        if (retv == 0) {
            result = a;
            return 0;
        }
        const unsigned sz = m_util.get_bv_size(coefficient);
        const unsigned new_sz = sz - retv;
        SASSERT(m_util.get_bv_size(tmp) == new_sz);

        expr_ref_vector new_args(m);
        numeral c_val;
        unsigned c_sz;
        if (!m_util.is_numeral(tmp, c_val, c_sz) || !c_val.is_one())
            new_args.push_back(std::move(tmp));


        if (new_sz == 0) {
            result = nullptr;
            return retv;
        }


        for (unsigned i = 1; i < num; i++) {
            expr * const curr = a->get_arg(i);
            new_args.push_back(m_mk_extract(new_sz - 1, 0, curr));
        }
        switch (new_args.size()) {
        case 0: result = m_util.mk_numeral(1, new_sz); break;
        case 1: result = new_args.get(0); break;
        default: result = m.mk_app(m_util.get_fid(), OP_BMUL, new_args.size(), new_args.c_ptr());
        }
        return retv;
    }

    unsigned remove_trailing_concat(app * a, unsigned n, expr_ref& result, unsigned depth) {
        SASSERT(m_util.is_concat(a));
        if (depth <= 1) {
            result = a;
            return 0;
        }
        const unsigned num  = a->get_num_args();
        unsigned retv = 0;
        unsigned i = num;
        expr_ref new_last(nullptr, m);
        while (i && retv < n) {
            i--;
            expr * const curr = a->get_arg(i);
            const unsigned cur_rm = remove_trailing(curr, n, new_last, depth - 1);
            const unsigned curr_sz = m_util.get_bv_size(curr);
            retv += cur_rm;
            if (cur_rm < curr_sz) break;
        }
        if (retv == 0) {
            result = a;
            return 0;
        }

        if (!i && !new_last) {// all args eaten completely
            SASSERT(retv == m_util.get_bv_size(a));
            result = nullptr;
            return retv;
        }

        expr_ref_vector new_args(m);
        for (unsigned j = 0; j < i; ++j)
            new_args.push_back(a->get_arg(j));
        if (new_last) new_args.push_back(std::move(new_last));
        result = new_args.size() == 1 ? new_args.get(0)
                                      : m_util.mk_concat(new_args.size(), new_args.c_ptr());
        return retv;
    }

    unsigned remove_trailing(size_t max_rm, numeral& a) {
        numeral two(2);
        unsigned retv = 0;
        while (max_rm && a.is_even()) {
            div(a, two, a);
            ++retv;
            --max_rm;
        }
        return retv;
    }

    unsigned remove_trailing_core(expr * e, unsigned n, expr_ref& result, unsigned depth) {
        SASSERT(m_util.is_bv(e));
        if (!depth || !n) {
            return 0;
        }
        unsigned sz;
        unsigned retv = 0;
        numeral e_val;
        if (m_util.is_numeral(e, e_val, sz)) {
            retv = remove_trailing(std::min(n, sz), e_val);            
            const unsigned new_sz = sz - retv;
            result = new_sz ? (retv ? m_util.mk_numeral(e_val, new_sz) : e) : nullptr;
            return retv;
        }
        if (m_util.is_bv_mul(e))
            return remove_trailing_mul(to_app(e), n, result, depth);
        if (m_util.is_bv_add(e))
            return remove_trailing_add(to_app(e), n, result, depth);
        if (m_util.is_concat(e))
            return remove_trailing_concat(to_app(e), n, result, depth);
        return 0;
    }


    void count_trailing_concat(app * a, unsigned& min, unsigned& max, unsigned depth) {
        if (depth <= 1) {
            min = 0;
            max = m_util.get_bv_size(a);
        }
        max = min = 0; // treat empty concat as the empty string
        unsigned num = a->get_num_args();
        bool update_min = true;
        bool update_max = true;
        unsigned tmp_min, tmp_max;
        while (num-- && update_max) {
            expr * const curr = a->get_arg(num);
            const unsigned curr_sz = m_util.get_bv_size(curr);
            count_trailing(curr, tmp_min, tmp_max, depth - 1);
            SASSERT(curr_sz != tmp_min || curr_sz == tmp_max);
            max += tmp_max;
            if (update_min) min += tmp_min;
            //  continue updating only if eaten away completely
            update_min &= curr_sz == tmp_min;
            update_max &= curr_sz == tmp_max;
        }
    }

    void count_trailing_add(app * a, unsigned& min, unsigned& max, unsigned depth) {
        if (depth <= 1) {
            min = 0;
            max = m_util.get_bv_size(a);
        }
        const unsigned num = a->get_num_args();
        const unsigned sz = m_util.get_bv_size(a);
        min = max = sz; // treat empty addition as 0
        unsigned tmp_min;
        unsigned tmp_max;
        bool known_parity = true;
        bool is_odd = false;
        for (unsigned i = 0; i < num; ++i) {
            expr * const curr = a->get_arg(i);
            count_trailing(curr, tmp_min, tmp_max, depth - 1);
            min = std::min(min, tmp_min);
            known_parity = known_parity && (!tmp_max || tmp_min);
            if (known_parity && !tmp_max) is_odd = !is_odd;
            if (!known_parity && !min) break; // no more information can be gained
        }
        max = known_parity && is_odd ? 0 : sz; // max is known if parity is 1
    }

    void count_trailing_mul(app * a, unsigned& min, unsigned& max, unsigned depth) {
        if (depth <= 1) {
            min = 0;
            max = m_util.get_bv_size(a);
        }

        const unsigned num = a->get_num_args();
        if (!num) {
            max = min = 0; // treat empty multiplication as 1
            return;
        }
        // assume that numerals are pushed in the front, count only for the first element
        expr * const curr = a->get_arg(0);
        unsigned tmp_max;
        count_trailing(curr, min, tmp_max, depth - 1);
        max = num == 1 ? tmp_max : m_util.get_bv_size(a);
        return;
    }

    void count_trailing_core(expr * e, unsigned& min, unsigned& max, unsigned depth) {
        if (!depth) {
            min = 0;
            max = m_util.get_bv_size(e);
            return;
        }
        unsigned sz;
        numeral e_val;
        if (m_util.is_numeral(e, e_val, sz)) {
            min = max = 0;
            numeral two(2);
            while (sz-- && e_val.is_even()) {
                ++max;
                ++min;
                div(e_val, two, e_val);
            }
            return;
        }
        if (m_util.is_bv_mul(e)) count_trailing_mul(to_app(e), min, max, depth);
        else if (m_util.is_bv_add(e)) count_trailing_add(to_app(e), min, max, depth);
        else if (m_util.is_concat(e)) count_trailing_concat(to_app(e), min, max, depth);
        else {
            min = 0;
            max = m_util.get_bv_size(e);
        }
    }

    void cache(unsigned depth, expr * e, unsigned min, unsigned max) {
        SASSERT(depth <= TRAILING_DEPTH);
        if (depth == 0) return;
        if (m_count_cache[depth] == nullptr)
            m_count_cache[depth] = alloc(map);
        SASSERT(!m_count_cache[depth]->contains(e));
        m.inc_ref(e);
        m_count_cache[depth]->insert(e, std::make_pair(min, max));
        TRACE("bv-trailing", tout << "caching@" << depth <<": " << mk_pp(e, m) << '[' << m_util.get_bv_size(e) << "]\n: " << min << '-' << max << "\n";);
    }

    bool is_cached(unsigned depth, expr * e, unsigned& min, unsigned& max) {
        SASSERT(depth <= TRAILING_DEPTH);
        if (depth == 0) {
            min = 0;
            max = m_util.get_bv_size(e);
            return true;
        }
        if (m_count_cache[depth] == nullptr)
            return false;
        const map::obj_map_entry * const oe = m_count_cache[depth]->find_core(e);
        if (oe == nullptr) return false;
        min = oe->get_data().m_value.first;
        max = oe->get_data().m_value.second;
        TRACE("bv-trailing", tout << "cached@" << depth << ": " << mk_pp(e, m) << '[' << m_util.get_bv_size(e) << "]\n: " << min << '-' << max << "\n";);
        return true;
    }

    void reset_cache(const unsigned condition) {
        SASSERT(m_count_cache[0] == nullptr);
        for (unsigned i = 1; i <= TRAILING_DEPTH; ++i) {
            if (m_count_cache[i] == nullptr) continue;
            TRACE("bv-trailing", tout << "may reset cache " << i << " " << condition <<  "\n";);
            if (m_count_cache[i]->size() < condition) continue;
            TRACE("bv-trailing", tout << "reset cache " << i << "\n";);
            for (auto& kv : *m_count_cache[i]) {
                m.dec_ref(kv.m_key);
            }
            dealloc(m_count_cache[i]);
            m_count_cache[i] = nullptr;
        }
    }

};

bv_trailing::bv_trailing(mk_extract_proc& mk_extract) {
    m_imp = alloc(imp, mk_extract);
}

bv_trailing::~bv_trailing() {
    dealloc(m_imp);
}

br_status bv_trailing::eq_remove_trailing(expr * e1, expr * e2,  expr_ref& result) {
    return m_imp->eq_remove_trailing(e1, e2, result);
}

void bv_trailing::count_trailing(expr * e, unsigned& min, unsigned& max) {
     m_imp->count_trailing(e, min, max, TRAILING_DEPTH);
}

unsigned bv_trailing::remove_trailing(expr * e, unsigned n, expr_ref& result) {
    return m_imp->remove_trailing(e, n, result, TRAILING_DEPTH);
}

void bv_trailing::reset_cache(unsigned condition) {
    m_imp->reset_cache(condition);
}
