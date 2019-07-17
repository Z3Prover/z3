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
#include "math/lp/nla_expr.h"
namespace nla {
class cross_nested {
    typedef nla_expr<rational> nex;
    nex& m_e;
    std::function<void (const nex&)> m_call_on_result;
    std::set<nex> m_reported;
public:
    cross_nested(nex &e, std::function<void (const nex&)> call_on_result): m_e(e), m_call_on_result(call_on_result) {}

    void run() {
        vector<nex*> front;
        cross_nested_of_expr_on_front_elem(&m_e, front);
    }

    static nex* pop_back(vector<nex*>& front) {
        nex* c = front.back();
        front.pop_back();
        return c;
    }

    struct occ {
        unsigned m_occs;
        unsigned m_power;
        occ() : m_occs(0), m_power(0) {}
        occ(unsigned k, unsigned p) : m_occs(k), m_power(p) {}
        // use the "name injection rule here"
        friend std::ostream& operator<<(std::ostream& out, const occ& c) {
            out << "(occs:" << c.m_occs <<", pow:" << c.m_power << ")";
            return out;
        }
    };

    bool proceed_with_common_factor(nex* c, vector<nex*>& front, const std::unordered_map<lpvar, occ> & occurences) {
        TRACE("nla_cn", tout << "c=" << *c << "\n";);
        SASSERT(c->is_sum());
        auto f = nex::mul();
        unsigned size = c->children().size();
        for(const auto & p : occurences) {
            if (p.second.m_occs == size) {
                unsigned pow = p.second.m_power;
                while (pow --) {
                    f *= nex::var(p.first);
                }
            }
        }
        if (f.children().size() == 0) return false;
        *c /= f;
        f.simplify();
        * c = nex::mul(f, *c);
        TRACE("nla_cn", tout << "common factor=" << f << ", c=" << *c << "\n";);
        cross_nested_of_expr_on_front_elem(&(c->children()[1]), front);
        return true;
    }
    
    void cross_nested_of_expr_on_front_elem_occs(nex* c, vector<nex*>& front, const std::unordered_map<lpvar, occ> & occurences) {
        if (proceed_with_common_factor(c, front, occurences))
            return;
        TRACE("nla_cn", tout << "save c=" << *c << "front:"; print_vector_of_ptrs(front, tout) << "\n";);           
        nex copy_of_c = *c;
        vector<nex> copy_of_front;
        for (nex* n: front)
            copy_of_front.push_back(*n);
        for(auto& p : occurences) {
            SASSERT(p.second.m_occs > 1);
            lpvar j = p.first;
            cross_nested_of_expr_on_sum_and_var(c, j, front);
            *c = copy_of_c;
            TRACE("nla_cn", tout << "restore c=" << *c << ", m_e=" << m_e << "\n";);   
            for (unsigned i = 0; i < front.size(); i++)
                *(front[i]) = copy_of_front[i];
        }
    }
    
    void cross_nested_of_expr_on_front_elem(nex* c, vector<nex*>& front) {
        SASSERT(c->is_sum());
        auto occurences = get_mult_occurences(*c);
        TRACE("nla_cn", tout << "m_e=" << m_e << "\nc=" << *c << "\noccurences="; print_vector(occurences, tout) << "\nfront:"; print_vector_of_ptrs(front, tout) << "\n";);
    
        if (occurences.empty()) {
            if(front.empty()) {
                TRACE("nla_cn_cn", tout << "got the cn form: m_e=" << m_e << "\n";);
                SASSERT(!can_be_cross_nested_more(m_e));
                auto e_to_report = m_e;
                e_to_report.simplify();
                e_to_report.sort();
                if (m_reported.find(e_to_report) == m_reported.end()) {
                    m_reported.insert(e_to_report);
                    m_call_on_result(e_to_report);
                } else {
                    TRACE("nla_cn", tout << "do not report " << e_to_report << "\n";);
                }
            } else {
                nex* c = pop_back(front);
                cross_nested_of_expr_on_front_elem(c, front);     
            }
        } else {
            cross_nested_of_expr_on_front_elem_occs(c, front, occurences);
        }
    }
    // e is the global expression, c is the sub expressiond which is going to changed from sum to the cross nested form
    void cross_nested_of_expr_on_sum_and_var(nex* c, lpvar j, vector<nex*> front) {
        TRACE("nla_cn", tout << "m_e=" << m_e << "\nc=" << *c << "\nj = v" << j << "\nfront="; print_vector_of_ptrs(front, tout) << "\n";);
        split_with_var(*c, j, front);
        TRACE("nla_cn", tout << "after split c=" << *c << "\nfront="; print_vector_of_ptrs(front, tout) << "\n";);    
        do {
            nex* n = pop_back(front);
            cross_nested_of_expr_on_front_elem(n, front);
        } while (!front.empty());
    }
   static void process_var_occurences(lpvar j, std::unordered_map<lpvar, occ>& occurences) {
        auto it = occurences.find(j);
        if (it != occurences.end()) {
            it->second.m_occs++;
            it->second.m_power = 1;
        } else {            
            occurences.insert(std::make_pair(j, occ(1, 1)));
        }
    }
    
    static void dump_occurences(std::ostream& out, const std::unordered_map<lpvar, occ>& occurences) {
        out << "{";
        for(const auto& p: occurences) {
            const occ& o = p.second;
            out << "(v" << p.first << "->" << o << ")";
        }
        out << "}" << std::endl;
    }


    static void update_occurences_with_powers(std::unordered_map<lpvar, occ>& occurences,
                                       const std::unordered_map<lpvar, int>& powers) {
        for (auto & p : powers) {
            lpvar j = p.first;
            unsigned jp = p.second;
            auto it = occurences.find(j);
            if (it == occurences.end()) {
                occurences[j] = occ(1, jp);
            } else {
                it->second.m_occs++;
                it->second.m_power = std::min(it->second.m_power, jp);
            }
        }
    }

    static void remove_singular_occurences(std::unordered_map<lpvar, occ>& occurences) {
        svector<lpvar> r;
        for (const auto & p : occurences) {
            if (p.second.m_occs <= 1) {
                r.push_back(p.first);
            }
        }
        for (lpvar j : r)
            occurences.erase(j);
    }
    // j -> the number of expressions j appears in as a multiplier, get the max degree as well
    static std::unordered_map<lpvar, occ> get_mult_occurences(const nex& e) {
        std::unordered_map<lpvar, occ> occurences;
        SASSERT(e.type() == expr_type::SUM);
        for (const auto & ce : e.children()) {
            std::unordered_set<lpvar> seen;
            if (ce.is_mul()) {
                auto powers = ce.get_powers_from_mul();
                update_occurences_with_powers(occurences, powers);
            } else if (ce.type() ==  expr_type::VAR) {
                process_var_occurences(ce.var(), occurences);
            }
        }
        remove_singular_occurences(occurences);
        TRACE("nla_cn_details", dump_occurences(tout, occurences););    
        return occurences;
    }
    bool can_be_cross_nested_more(const nex& e) const {
        switch (e.type()) {
        case expr_type::SCALAR:
            return false;
        case expr_type::SUM: {
            return !get_mult_occurences(e).empty();
        }
        case expr_type::MUL:
            {
                for (const auto & c: e.children()) {
                    if (can_be_cross_nested_more(c))
                        return true;
                }
                return false;
            }
        case expr_type::VAR:
            return false;
        default:
            TRACE("nla_cn_details", tout << e.type() << "\n";);
            SASSERT(false);
            return false;
        }
    }
    void split_with_var(nex& e, lpvar j, vector<nex*> & front) {
        TRACE("nla_cn_details", tout << "e = " << e << ", j = v" << j << "\n";);
        if (!e.is_sum())
            return;
        nex a, b;
        for (const nex & ce: e.children()) {
            if ((ce.is_mul() && ce.contains(j)) || (ce.is_var() && ce.var() == j)) {
                a.add_child(ce / j);
            } else {
                b.add_child(ce);
            }        
        }
        a.type() = expr_type::SUM;
        TRACE("nla_cn_details", tout << "a = " << a << "\n";);
        SASSERT(a.children().size() >= 2);
    
        if (b.children().size() == 1) {
            nex t = b.children()[0];
            b = t;      
        } else if (b.children().size() > 1) {
            b.type() = expr_type::SUM;        
        }

        if (b.is_undef()) {
            SASSERT(b.children().size() == 0);
            e = nex(expr_type::MUL);        
            e.add_child(nex::var(j));
            e.add_child(a);
            if (a.size() > 1) {
                front.push_back(&e.children().back());
                TRACE("nla_cn_details", tout << "push to front " << e.children().back() << "\n";);
            }
      
        } else {
            TRACE("nla_cn_details", tout << "b = " << b << "\n";);
            e = nex::sum(nex::mul(nex::var(j), a), b);
            if (a.is_sum()) {
                front.push_back(&(e.children()[0].children()[1]));
                TRACE("nla_cn_details", tout << "push to front " << e.children()[0].children()[1] << "\n";);
            }
            if (b.is_sum()) {
                front.push_back(&(e.children()[1]));
                TRACE("nla_cn_details", tout << "push to front " << e.children()[1] << "\n";);
            }
        }
    }
    std::set<lpvar> get_vars_of_expr(const nex &e ) const {
        std::set<lpvar> r;
        switch (e.type()) {
        case expr_type::SCALAR:
            return r;
        case expr_type::SUM:
        case expr_type::MUL:
            {
                for (const auto & c: e.children())
                    for ( lpvar j : get_vars_of_expr(c))
                        r.insert(j);
            }
            return r;
        case expr_type::VAR:
            r.insert(e.var());
            return r;
        default:
            TRACE("nla_cn_details", tout << e.type() << "\n";);
            SASSERT(false);
            return r;
        }

    }

};
}
