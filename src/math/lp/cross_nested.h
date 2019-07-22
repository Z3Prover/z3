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
public:
    cross_nested(nex &e, std::function<void (const nex&)> call_on_result): m_e(e), m_call_on_result(call_on_result) {}

    void run() {
        vector<nex*> front;
        explore_of_expr_on_front_elem(&m_e, front, true); // true for trivial form - no change
    }

    static nex* pop_back(vector<nex*>& front) {
        nex* c = front.back();
        TRACE("nla_cn", tout << *c << "\n";);
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

    static bool extract_common_factor(nex* c, nex& f, const std::unordered_map<lpvar, occ> & occurences) {
        TRACE("nla_cn", tout << "c=" << *c << "\n";);
        SASSERT(c->is_sum());
        f.type() = expr_type::MUL;
        SASSERT(f.children().empty());
        unsigned size = c->children().size();
        for(const auto & p : occurences) {
            if (p.second.m_occs == size) {
                unsigned pow = p.second.m_power;
                while (pow --) {
                    f *= nex::var(p.first);
                }
            }
        }
        return !f.children().empty();
    }

    bool proceed_with_common_factor(nex* c, vector<nex*>& front, const std::unordered_map<lpvar, occ> & occurences) {
        TRACE("nla_cn", tout << "c=" << *c << "\n";);
        SASSERT(c->is_sum());
        nex f;
        if (!extract_common_factor(c, f, occurences))
            return false;
        
        *c /= f;
        f.simplify();
        * c = nex::mul(f, *c);
        TRACE("nla_cn", tout << "common factor=" << f << ", c=" << *c << "\n";);
        explore_of_expr_on_front_elem(&(c->children()[1]), front, false);
        return true;
    }

    static void push(vector<nex*>& front, nex* e) {
        TRACE("nla_cn", tout << *e << "\n";);
        front.push_back(e);
    }
    
    static vector<nex> copy_front(const vector<nex*>& front) {
       vector<nex> v;
        for (nex* n: front)
            v.push_back(*n);
        return v;
    }

    static void restore_front(const vector<nex> &copy, vector<nex*>& front) {
        SASSERT(copy.size() == front.size());
        for (unsigned i = 0; i < front.size(); i++)
            *(front[i]) = copy[i];
    }
    
    void explore_of_expr_on_front_elem_occs(nex* c, vector<nex*>& front, const std::unordered_map<lpvar, occ> & occurences) {
        if (proceed_with_common_factor(c, front, occurences))
            return;
        TRACE("nla_cn", tout << "save c=" << *c << "; front:"; print_vector_of_ptrs(front, tout) << "\n";);           
        nex copy_of_c = *c;
        vector<nex> copy_of_front = copy_front(front);
        for(auto& p : occurences) {
            SASSERT(p.second.m_occs > 1);
            lpvar j = p.first;
            explore_of_expr_on_sum_and_var(c, j, front);
            *c = copy_of_c;
            TRACE("nla_cn", tout << "restore c=" << *c << ", m_e=" << m_e << "\n";);
            restore_front(copy_of_front, front);
            TRACE("nla_cn", tout << "restore c=" << *c << "\n";);
            TRACE("nla_cn", tout << "m_e=" << m_e << "\n";);   
        }
    }

    static std::ostream& dump_occurences(std::ostream& out, const std::unordered_map<lpvar, occ>& occurences) {
        out << "{";
        for(const auto& p: occurences) {
            const occ& o = p.second;
            out << "(" << (char)('a' + p.first) << "->" << o << ")";
        }
        out << "}" << std::endl;
        return out;
    }

    void explore_of_expr_on_front_elem(nex* c, vector<nex*>& front, bool trivial_form) {
        SASSERT(c->is_sum());
        auto occurences = get_mult_occurences(*c);
        TRACE("nla_cn", tout << "m_e=" << m_e << "\nc=" << *c << ", c occurences=";
              dump_occurences(tout, occurences) << "; front:"; print_vector_of_ptrs(front, tout) << "\ntrivial_form=" << trivial_form << "\n";);
    
        if (occurences.empty()) {
            if(front.empty()) {
                if (trivial_form)
                    return;
                TRACE("nla_cn", tout << "got the cn form: =" << m_e << "\n";);
                m_call_on_result(m_e);
            } else {
                nex* c = pop_back(front);
                explore_of_expr_on_front_elem(c, front, trivial_form);     
            }
        } else {
            explore_of_expr_on_front_elem_occs(c, front, occurences);
        }
    }
    static char ch(unsigned j) {
        return (char)('a'+j);
    }
    // e is the global expression, c is the sub expressiond which is going to changed from sum to the cross nested form
    void explore_of_expr_on_sum_and_var(nex* c, lpvar j, vector<nex*> front) {
        TRACE("nla_cn", tout << "m_e=" << m_e << "\nc=" << *c << "\nj = " << ch(j) << "\nfront="; print_vector_of_ptrs(front, tout) << "\n";);
        if (!split_with_var(*c, j, front))
            return;
        TRACE("nla_cn", tout << "after split c=" << *c << "\nfront="; print_vector_of_ptrs(front, tout) << "\n";);
        SASSERT(front.size());
        nex* n = pop_back(front); TRACE("nla_cn", tout << "n=" << *n <<"\n";);
        explore_of_expr_on_front_elem(n, front, false); // we got a non-trivial_form
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
        TRACE("nla_cn_details", tout << "occs="; dump_occurences(tout, occurences) << "\n";);
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
            if (ce.is_mul()) {
                auto powers = ce.get_powers_from_mul();
                update_occurences_with_powers(occurences, powers);
            } else if (ce.type() ==  expr_type::VAR) {
                process_var_occurences(ce.var(), occurences);
            }
        }
        remove_singular_occurences(occurences);
        TRACE("nla_cn_details", tout << "e=" << e << "\noccs="; dump_occurences(tout, occurences) << "\n";);    
        return occurences;
    }
    static bool can_be_cross_nested_more(const nex& s) {
        auto e = s;
        e.simplify();
        TRACE("nla_cn", tout << "simplified " << e << "\n";);
        switch (e.type()) {
        case expr_type::SCALAR:
            return false;
        case expr_type::SUM: 
            if ( !get_mult_occurences(e).empty()) {
                TRACE("nla_cn", tout << "true for " << e << "\n";);
                return true;
            }
            // fall through MUL
        case expr_type::MUL:
            {
                for (const auto & c: e.children()) {
                    if (can_be_cross_nested_more(c)) {
                        TRACE("nla_cn", tout << "true for " << e << "\n";);
                        return true;
                    }
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
    // all factors of j go to a, the rest to b
    static void pre_split(nex &e, lpvar j, nex &a, nex&b) {
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
        a.simplify();
        
        if (b.children().size() == 1) {
            nex t = b.children()[0];
            b = t;      
        } else if (b.children().size() > 1) {
            b.type() = expr_type::SUM;        
        }
    }

    // returns true if the recursion is done inside
    void update_front_with_split_with_non_empty_b(nex& e, lpvar j, vector<nex*> & front, nex& a, nex& b) {
        nex f;
        SASSERT(a.is_sum());
        
        TRACE("nla_cn_details", tout << "b = " << b << "\n";);
        e = nex::sum(nex::mul(nex::var(j), a), b);
        push(front, &(e.children()[0].children()[1])); // pushing 'a'
        TRACE("nla_cn", tout << "push to front " << e.children()[0].children()[1] << "\n";);
        
        if (b.is_sum()) {
            push(front, &(e.children()[1]));
            TRACE("nla_cn", tout << "push to front " << e.children()[1] << "\n";);
        }
    }
    
   void update_front_with_split(nex& e, lpvar j, vector<nex*> & front, nex& a, nex& b) {
        if (b.is_undef()) {
            SASSERT(b.children().size() == 0);
            e = nex(expr_type::MUL);        
            e.add_child(nex::var(j));
            e.add_child(a);
            if (a.size() > 1) {
                push(front, &e.children().back());
                TRACE("nla_cn_details", tout << "push to front " << e.children().back() << "\n";);
            }
        }
        update_front_with_split_with_non_empty_b(e, j, front, a, b);
    }
    // it returns true if the recursion brings a cross-nested form
    bool split_with_var(nex& e, lpvar j, vector<nex*> & front) {
        TRACE("nla_cn", tout << "e = " << e << ", j=" << ch(j) << "\n";);
        if (!e.is_sum()) return false;
        nex a, b;
        pre_split(e, j, a, b);
        nex f;
        if (extract_common_factor(&a, f, get_mult_occurences(a)))
            return false;
        update_front_with_split(e, j, front, a, b);
        return true;
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
