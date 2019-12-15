/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once
#include <functional>
#include "math/lp/nex.h"
#include "math/lp/nex_creator.h"

namespace nla {
class cross_nested {
    
    // fields
    nex *                                             m_e;
    std::function<bool (const nex*)>                  m_call_on_result;
    std::function<bool (unsigned)>                    m_var_is_fixed;
    std::function<unsigned ()>                        m_random;    
    bool                                              m_done;
    ptr_vector<nex>                                   m_b_split_vec;
    int                                               m_reported;
    bool                                              m_random_bit;
    std::function<nex_scalar*()>                      m_mk_scalar;
    nex_creator&                                      m_nex_creator;
#ifdef Z3DEBUG
    nex* m_e_clone;
#endif
public:
    
    nex_creator& get_nex_creator() { return m_nex_creator; }
    
    cross_nested(std::function<bool (const nex*)> call_on_result,
                 std::function<bool (unsigned)> var_is_fixed,
                 std::function<unsigned ()> random,
                 nex_creator& nex_cr) :
        m_call_on_result(call_on_result),
        m_var_is_fixed(var_is_fixed),
        m_random(random),
        m_done(false),
        m_reported(0),
        m_mk_scalar([this]{return m_nex_creator.mk_scalar(rational(1));}),
        m_nex_creator(nex_cr)
    {}

    
    void run(nex *e) {
        TRACE("nla_cn", tout << *e << "\n";);
        SASSERT(m_nex_creator.is_simplified(*e));
        m_e = e;
#ifdef Z3DEBUG
        m_e_clone = m_nex_creator.clone(m_e);
        TRACE("nla_cn", tout << "m_e_clone = " <<  * m_e_clone << "\n";);
        
#endif
        vector<nex**> front;
        explore_expr_on_front_elem(&m_e, front);
    }

    static nex** pop_front(vector<nex**>& front) {
        nex** c = front.back();
        TRACE("nla_cn", tout <<  **c << "\n";);
        front.pop_back();
        return c;
    }


    nex* extract_common_factor(nex* e) {
        nex_sum* c = to_sum(e);
        TRACE("nla_cn", tout << "c=" << *c << "\n"; tout << "occs:"; dump_occurences(tout, m_nex_creator.occurences_map()) << "\n";);
        unsigned size = c->size();
        bool have_factor = false;
        for (const auto & p : m_nex_creator.occurences_map()) {
            if (p.second.m_occs == size) {
                have_factor = true;
                break;
            }
        }
        if (have_factor == false) return nullptr;
        m_nex_creator.m_mk_mul.reset();
        for (const auto & p : m_nex_creator.occurences_map()) { // randomize here: todo
            if (p.second.m_occs == size) {
                m_nex_creator.m_mk_mul *= nex_pow(m_nex_creator.mk_var(p.first), p.second.m_power);
            }
        }
        return m_nex_creator.m_mk_mul.mk();
    }

    static bool has_common_factor(const nex_sum* c) {
        TRACE("nla_cn", tout << "c=" << *c << "\n";);
        auto & ch = *c;
        auto common_vars = get_vars_of_expr(ch[0]);
        for (lpvar j : common_vars) {
            bool divides_the_rest = true;
            for (unsigned i = 1; i < ch.size() && divides_the_rest; i++) {
                if (!ch[i]->contains(j))
                    divides_the_rest = false;
            }
            if (divides_the_rest) {
                TRACE("nla_cn_common_factor", tout << c << "\n";);
                return true;
            }
        }
        return false;
    }

    bool proceed_with_common_factor(nex** c, vector<nex**>& front) {
        TRACE("nla_cn", tout << "c=" << **c << "\n";);
        nex* f = extract_common_factor(*c);
        if (f == nullptr) {
            TRACE("nla_cn", tout << "no common factor\n"; );
            return false;
        }
        TRACE("nla_cn", tout << "common factor f=" << *f << "\n";);
        
        nex* c_over_f = m_nex_creator.mk_div(**c, *f);
        c_over_f = m_nex_creator.simplify(c_over_f);
        TRACE("nla_cn", tout << "c_over_f = " << *c_over_f << std::endl;);
        nex_mul* cm; 
        *c = cm = m_nex_creator.mk_mul(f, c_over_f);
        TRACE("nla_cn", tout << "common factor=" << *f << ", c=" << **c << "\ne = " << *m_e << "\n";);
        explore_expr_on_front_elem((*cm)[1].ee(),  front);
        return true;
    }

    static void push_to_front(vector<nex**>& front, nex** e) {
        TRACE("nla_cn", tout << **e << "\n";);
        front.push_back(e);
    }
    
    static vector<nex*> copy_front(const vector<nex**>& front) {
        vector<nex*> v;
        for (nex** n: front)
            v.push_back(*n);
        return v;
    }

    static void restore_front(const vector<nex*> &copy, vector<nex**>& front) {
        SASSERT(copy.size() == front.size());
        for (unsigned i = 0; i < front.size(); i++)
            *(front[i]) = copy[i];
    }

    void pop_allocated(unsigned sz) {
        m_nex_creator.pop(sz);
    }
    
    void explore_expr_on_front_elem_vars(nex** c, vector<nex**>& front, const svector<lpvar> & vars) {
        TRACE("nla_cn", tout << "save c=" << **c << "; front:"; print_front(front, tout) << "\n";);           
        nex* copy_of_c = *c;
        auto copy_of_front = copy_front(front);
        int alloc_size = m_nex_creator.size();
        for (lpvar j : vars) {
            if (m_var_is_fixed(j)) {
                // it does not make sense to explore fixed multupliers
                // because the interval products do not become smaller
                // after factoring those out
                continue;
            }
            explore_of_expr_on_sum_and_var(c, j, front);
            if (m_done)
                return;
            TRACE("nla_cn", tout << "before restore c=" << **c << "\nm_e=" << *m_e << "\n";);
            *c = copy_of_c;
            restore_front(copy_of_front, front);
            pop_allocated(alloc_size);
            TRACE("nla_cn", tout << "after restore c=" << **c << "\nm_e=" << *m_e << "\n";);   
        }
    }

    template <typename T>
    static std::ostream& dump_occurences(std::ostream& out, const T& occurences) {
        out << "{";
        for (const auto& p: occurences) {
            out << "(v" << p.first << "->" << p.second << ")";
        }
        out << "}" << std::endl;
        return out;
    }

    void calc_occurences(nex_sum* e) {
        clear_maps();
        for (const auto * ce : *e) {
            if (ce->is_mul()) {
                ce->to_mul().get_powers_from_mul(m_nex_creator.powers());
                update_occurences_with_powers();
            } else if (ce->is_var()) {
                add_var_occs(ce->to_var().var());
            }
        }
        remove_singular_occurences();
        TRACE("nla_cn_details", tout << "e=" << *e << "\noccs="; dump_occurences(tout, m_nex_creator.occurences_map()) << "\n";);
    }

    void fill_vars_from_occurences_map(svector<lpvar>& vars) {
        for (auto & p : m_nex_creator.occurences_map())
            vars.push_back(p.first);

        m_random_bit = m_random() % 2;
        TRACE("nla_cn", tout << "m_random_bit = " << m_random_bit << "\n";);
        std::sort(vars.begin(), vars.end(), [this](lpvar j, lpvar k)
                                            {
                                                auto it_j = m_nex_creator.occurences_map().find(j);
                                                auto it_k = m_nex_creator.occurences_map().find(k);
                                                

                                                const occ& a = it_j->second;
                                                const occ& b = it_k->second;
                                                if (a.m_occs > b.m_occs)
                                                    return true;
                                                if (a.m_occs < b.m_occs)
                                                    return false;
                                                if (a.m_power > b.m_power)
                                                    return true;
                                                if (a.m_power < b.m_power)
                                                    return false;
                                                
                                                return m_random_bit? j < k : j > k;
                                          });
 
    }    
    
    bool proceed_with_common_factor_or_get_vars_to_factor_out(nex** c, svector<lpvar>& vars, vector<nex**> front) {
        calc_occurences(to_sum(*c));
        if (proceed_with_common_factor(c, front))
            return true;

        fill_vars_from_occurences_map(vars);
        return false;
    }
    
    void explore_expr_on_front_elem(nex** c, vector<nex**>& front) {
        svector<lpvar> vars;
        if (proceed_with_common_factor_or_get_vars_to_factor_out(c, vars, front))
            return;

        TRACE("nla_cn", tout << "m_e=" << *m_e << "\nc=" << **c << ", c vars=";
              print_vector(vars, tout) << "; front:"; print_front(front, tout) << "\n";);
    
        if (vars.empty()) {
            if (front.empty()) {
                TRACE("nla_cn", tout << "got the cn form: =" << *m_e << "\n";);
                m_done = m_call_on_result(m_e) || ++m_reported > 100;
 #ifdef Z3DEBUG
                TRACE("nla_cn", tout << "m_e_clone " << *m_e_clone << "\n";);
                SASSERT(nex_creator::equal(m_e, m_e_clone));
 #endif
            } else {
                nex** f = pop_front(front);
                explore_expr_on_front_elem(f, front);     
            }
        } else {
            explore_expr_on_front_elem_vars(c, front, vars);
        }
    }

    std::ostream& print_front(const vector<nex**>& front, std::ostream& out) const {
        for (auto e : front) {
            out << **e << "\n";
        }
        return out;
    }
    // c is the sub expressiond which is going to be changed from sum to the cross nested form
    // front will be explored more
    void explore_of_expr_on_sum_and_var(nex** c, lpvar j, vector<nex**> front) {
        TRACE("nla_cn", tout << "m_e=" << *m_e << "\nc=" << **c << "\nj = " << nex_creator::ch(j) << "\nfront="; print_front(front, tout) << "\n";);
        if (!split_with_var(*c, j, front))
            return;
        TRACE("nla_cn", tout << "after split c=" << **c << "\nfront="; print_front(front, tout) << "\n";);
        if (front.empty()) {
#ifdef Z3DEBUG
            TRACE("nla_cn", tout << "got the cn form: =" << *m_e <<  ", clone = " << *m_e_clone << "\n";);
#endif
            m_done = m_call_on_result(m_e) || ++m_reported > 100;
#ifdef Z3DEBUG
            SASSERT(nex_creator::equal(m_e, m_e_clone));
#endif
            return;
        }
        auto n = pop_front(front);
        explore_expr_on_front_elem(n, front);
    }

    void add_var_occs(lpvar j) {
        auto it = m_nex_creator.occurences_map().find(j);
        if (it != m_nex_creator.occurences_map().end()) {
            it->second.m_occs++;
            it->second.m_power = 1;
        } else {            
            m_nex_creator.occurences_map().insert(std::make_pair(j, occ(1, 1)));
        }
    }    

    void update_occurences_with_powers() {
        for (auto & p : m_nex_creator.powers()) {
            lpvar j = p.first;
            unsigned jp = p.second;
            auto it = m_nex_creator.occurences_map().find(j);
            if (it == m_nex_creator.occurences_map().end()) {
                m_nex_creator.occurences_map()[j] = occ(1, jp);
            } else {
                it->second.m_occs++;
                it->second.m_power = std::min(it->second.m_power, jp);
            }
        }
        TRACE("nla_cn_details", tout << "occs="; dump_occurences(tout, m_nex_creator.occurences_map()) << "\n";);
    }    
    
    void remove_singular_occurences() {
        svector<lpvar> r;
        for (const auto & p : m_nex_creator.occurences_map()) {
            if (p.second.m_occs <= 1) {
                r.push_back(p.first);
            }
        }
        for (lpvar j : r)
            m_nex_creator.occurences_map().erase(j);
    }

    void clear_maps() {
        m_nex_creator.occurences_map().clear();
        m_nex_creator.powers().clear();
    }
    
    // j -> the number of expressions j appears in as a multiplier
    // The result is sorted by large number of occurences first
    vector<std::pair<lpvar, occ>> get_mult_occurences(const nex_sum* e) {
        clear_maps();
        for (const auto * ce : *e) {
            if (ce->is_mul()) {
                to_mul(ce)->get_powers_from_mul(m_nex_creator.powers());
                update_occurences_with_powers();
            } else if (ce->is_var()) {
                add_var_occs(to_var(ce)->var());
            }
        }
        remove_singular_occurences();
        TRACE("nla_cn_details", tout << "e=" << *e << "\noccs="; dump_occurences(tout, m_nex_creator.occurences_map()) << "\n";);
        vector<std::pair<lpvar, occ>> ret;
        for (auto & p : m_nex_creator.occurences_map())
            ret.push_back(p);
        std::sort(ret.begin(), ret.end(), [](const std::pair<lpvar, occ>& a, const std::pair<lpvar, occ>& b) {
                                              if (a.second.m_occs > b.second.m_occs)
                                                  return true;
                                              if (a.second.m_occs < b.second.m_occs)
                                                  return false;
                                              if (a.second.m_power > b.second.m_power)
                                                  return true;
                                              if (a.second.m_power < b.second.m_power)
                                                  return false;

                                              return a.first < b.first;
                                          });
        return ret;
    }

    static bool is_divisible_by_var(nex const* ce, lpvar j) {
        return (ce->is_mul() && to_mul(ce)->contains(j))
            || (ce->is_var() && to_var(ce)->var() == j);
    }
    // all factors of j go to a, the rest to b
    void pre_split(nex_sum * e, lpvar j, nex_sum const*& a, nex const*& b) {
        TRACE("nla_cn_details", tout << "e = " << * e << ", j = " << m_nex_creator.ch(j) << std::endl;);
        SASSERT(m_nex_creator.is_simplified(*e));
        nex_creator::sum_factory sf(m_nex_creator);
        m_b_split_vec.clear();
        for (nex const* ce: *e) {
            TRACE("nla_cn_details", tout << "ce = " << *ce << "\n";);
            if (is_divisible_by_var(ce, j)) {
                sf += m_nex_creator.mk_div(*ce , j);
            } else {
                m_b_split_vec.push_back(const_cast<nex*>(ce));
            }        
        }
        a = sf.mk();
        TRACE("nla_cn_details", tout << "a = " << *a << "\n";);
        SASSERT(a->size() >= 2 && m_b_split_vec.size());
        a = to_sum(m_nex_creator.simplify_sum(const_cast<nex_sum*>(a)));
        
        if (m_b_split_vec.size() == 1) {
            b = m_b_split_vec[0];
            TRACE("nla_cn_details", tout << "b = " << *b << "\n";);
        } else {
            SASSERT(m_b_split_vec.size() > 1);
            b = m_nex_creator.mk_sum(m_b_split_vec);
            TRACE("nla_cn_details", tout << "b = " << *b << "\n";);
        }
    }

    void update_front_with_split_with_non_empty_b(nex* &e, lpvar j, vector<nex**> & front, nex_sum const* a, nex const* b) {
        TRACE("nla_cn_details", tout << "b = " << *b << "\n";);
        e = m_nex_creator.mk_sum(m_nex_creator.mk_mul(m_nex_creator.mk_var(j), a), b); // e = j*a + b
        if (!a->is_linear()) {
            nex **ptr_to_a = e->to_sum()[0]->to_mul()[1].ee();
            push_to_front(front, ptr_to_a);
        }
        
        if (b->is_sum() && !to_sum(b)->is_linear()) {
            nex **ptr_to_a = &(e->to_sum()[1]);
            push_to_front(front, ptr_to_a);
        }
    }
    
   void update_front_with_split(nex* & e, lpvar j, vector<nex**> & front, nex_sum const* a, nex const* b) {
        if (b == nullptr) {
            e = m_nex_creator.mk_mul(m_nex_creator.mk_var(j), a);
            if (!to_sum(a)->is_linear())
                push_to_front(front, e->to_mul()[1].ee());
        } else {
            update_front_with_split_with_non_empty_b(e, j, front, a, b);
        }
    }
    // it returns true if the recursion brings a cross-nested form
    bool split_with_var(nex*& e, lpvar j, vector<nex**> & front) {
        SASSERT(e->is_sum());
        TRACE("nla_cn", tout << "e = " << *e << ", j=" << nex_creator::ch(j) << "\n";);
        nex_sum const* a; nex const* b;
        pre_split(to_sum(e), j, a, b);
        /*
          When we have e without a non-trivial common factor then
          there is a variable j such that e = jP + Q, where Q has all members
          of e that do not have j as a factor, and
          P also does not have a non-trivial common factor. It is enough
          to explore only such variables to create all cross-nested forms.
        */
        
        if (has_common_factor(a)) {
            return false;
        }
        update_front_with_split(e, j, front, a, b);
        return true;
    }

    
    ~cross_nested() {
        m_nex_creator.clear();
    }

    bool done() const { return m_done; }

#if Z3DEBUG
    nex * normalize_sum(nex_sum* a) {
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }

    nex * normalize_mul(nex_mul* a) {
        TRACE("nla_cn", tout << *a << "\n";);
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }    
    
    nex * normalize(nex* a) {
        if (a->is_elementary())
            return a;
        nex *r;
        if (a->is_mul()) {
            r = normalize_mul(to_mul(a));
        } else {
            r = normalize_sum(to_sum(a));
        }
        r->sort();
        return r;
    }
#endif
    
};
}
