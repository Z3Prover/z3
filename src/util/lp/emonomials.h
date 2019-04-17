/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

     emonomials.h

  Abstract:

     table that associate monomials to congruence class representatives modulo a union find structure.

  Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

  Revision History:

    to replace rooted_mons.h and rooted_mon, rooted_mon_tabled

  --*/

#pragma once
#include "util/lp/lp_utils.h"
#include "util/lp/var_eqs.h"
#include "util/lp/monomial.h"
#include "util/region.h"

namespace nla {

    /**
       \brief class used to summarize the coefficients to a monomial after
       canonization with respect to current equalities.
    */
    class signed_vars {
        lpvar           m_var; // variable representing original monomial
        svector<lpvar>  m_vars;
        bool            m_sign;
    public:
        signed_vars() : m_sign(false) {}
        lpvar var() const { return m_var; }
        svector<lpvar> const& vars() const { return m_vars; }
        unsigned size() const { return m_vars.size(); }
        lpvar operator[](unsigned i) const { return m_vars[i]; }
        bool sign() const { return m_sign; }
        void set_sign(bool s) { m_sign = s; }
        void set_var(lpvar v) { m_var = v; }
        void set_vars(unsigned n, lpvar const* vars) {
            m_vars.reset();
            m_vars.append(n, vars);
            std::sort(m_vars.begin(), m_vars.end());
        }
        std::ostream& display(std::ostream& out) const {
            out << "v" << var() << " := ";
            if (sign()) out << "- ";
            for (lpvar v : vars()) out << "v" << v << " ";
            return out;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, signed_vars const& m) { return m.display(out); }


    class emonomials : public var_eqs_merge_handler {
        /**
           \brief private fields used by emonomials for maintaining state of canonized monomials.
        */
        class signed_vars_ts : public signed_vars {
        public:
            signed_vars_ts(): m_canonical(0), m_visited(0) {}
            unsigned m_canonical;
            unsigned m_visited;
        };

        /**
           \brief singly-lined cyclic list of monomial indices where variable occurs.
           Each variable points to the head and tail of the cyclic list.
           Initially, head and tail are nullptr.
           New elements are inserted in the beginning of the list.
           Two lists are merged when equivalence class representatives are merged, 
           and the merge is undone when the representative variables are unmerged.
         */
        struct cell {
            cell(unsigned mIndex, cell* c): m_next(c), m_index(mIndex) {}
            cell*        m_next;
            unsigned     m_index;
        };
        struct head_tail {
            head_tail(): m_head(nullptr), m_tail(nullptr) {}
            cell* m_head;
            cell* m_tail;
        };

        var_eqs&                m_ve;
        vector<monomial>        m_monomials;     // set of monomials
        unsigned_vector         m_lim;           // backtracking point
        unsigned_vector         m_var2index;     // var_mIndex -> mIndex
        unsigned                m_canonical;     // timestamp of last merge
        mutable unsigned        m_visited;       // timestamp of visited monomials during pf_iterator
        region                  m_region;        // region for allocating linked lists
        mutable vector<signed_vars_ts>  m_canonized;     // canonized versions of signed variables
        mutable svector<lpvar>       m_vars;          // temporary vector of variables
        mutable svector<head_tail>   m_use_lists;     // use list of monomials where variables occur.

        void inc_canonical();
        void inc_visited() const;

        void remove_var2monomials(lpvar v, unsigned mIndex);
        void insert_var2monomials(lpvar v, unsigned mIndex);
        void merge_var2monomials(lpvar root, lpvar other);
        void unmerge_var2monomials(lpvar root, lpvar other);

        cell* head(lpvar v) const;
        void set_visited(monomial const& m) const;
        bool is_visited(monomial const& m) const;
        
    public:
        /**
           \brief emonomials builds on top of var_eqs.
           push and pop on emonomials calls push/pop on var_eqs, so no 
           other calls to push/pop to the var_eqs should take place. 
         */
        emonomials(var_eqs& ve): m_ve(ve), m_canonical(1), m_visited(0) { m_ve.set_merge_handler(this); }

        /**
           \brief push/pop scopes. 
           The life-time of a merge is local within a scope.
        */
        void push();

        void pop(unsigned n);

        /**
           \brief create a monomial from an equality v := vs
        */
        void add(lpvar v, unsigned sz, lpvar const* vs);
        void add(lpvar v, svector<lpvar> const& vs) { add(v, vs.size(), vs.c_ptr()); }
        void add(lpvar v, lpvar x, lpvar y) { lpvar vs[2] = { x, y }; add(v, 2, vs); }
        void add(lpvar v, lpvar x, lpvar y, lpvar z) { lpvar vs[3] = { x, y, z }; add(v, 3, vs); }

        /**
           \brief retrieve monomial corresponding to variable v from definition v := vs
        */
        monomial const* var2monomial(lpvar v) const { unsigned idx = m_var2index.get(v, UINT_MAX); return idx == UINT_MAX ? nullptr : &m_monomials[idx]; }
        
        /**
           \brief obtain a canonized signed monomial
           corresponding to current equivalence class.
        */
        signed_vars const& canonize(monomial const& m) const;

        /**
           \brief determine if m1 divides m2 over the canonization obtained from merged variables.
         */
        bool canonize_divides(monomial const& m1, monomial const& m2) const;

        /**
           \brief produce explanation for monomial canonization.
        */
        void explain_canonized(monomial const& m, lp::explanation& exp);

        /**
           \brief iterator over monomials that are declared.
        */
        vector<monomial>::const_iterator begin() const { return m_monomials.begin(); }
        vector<monomial>::const_iterator end() const { return m_monomials.end(); }

        /**
           \brief iterators over monomials where an equivalent variable is used
        */
        class iterator {
            emonomials const& m;
            cell*       m_cell;
            bool        m_touched;            
        public:
            iterator(emonomials const& m, cell* c, bool at_end): m(m), m_cell(c), m_touched(at_end || c == nullptr) {}
            monomial const& operator*() { return m.m_monomials[m_cell->m_index]; }
            iterator& operator++() { m_touched = true; m_cell = m_cell->m_next; return *this; }
            iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
            bool operator==(iterator const& other) const { return m_cell == other.m_cell && m_touched == other.m_touched; }
            bool operator!=(iterator const& other) const { return m_cell != other.m_cell || m_touched != other.m_touched; }
        };
        
        class use_list {
            emonomials const& m;
            lpvar     m_var;
            cell*     head() { return m.head(m_var); } 
        public:
            use_list(emonomials const& m, lpvar v): m(m), m_var(v) {}
            iterator begin() { return iterator(m, head(), false); }
            iterator end() { return iterator(m, head(), true); }
        };

        use_list get_use_list(lpvar v) const { return use_list(*this, v); }


        /**
           \brief retrieve monomials m' where m is a proper factor of modulo current equalities.
        */
        class pf_iterator {
            emonomials const& m;
            monomial const&   m_mon; // canonized monomial
            iterator          m_it;  // iterator over the first variable occurs list, ++ filters out elements that are not factors.
            iterator          m_end;

            void fast_forward();
        public:
            pf_iterator(emonomials const& m, monomial const& mon, bool at_end);
            monomial const& operator*() { return *m_it; }
            pf_iterator& operator++() { ++m_it; fast_forward(); return *this; }
            pf_iterator operator++(int) { pf_iterator tmp = *this; ++*this; return tmp; }
            bool operator==(pf_iterator const& other) const { return m_it == other.m_it; }
            bool operator!=(pf_iterator const& other) const { return m_it != other.m_it; }
        };

        class factors_of {
            emonomials const& m;
            monomial const& mon;
        public:
            factors_of(emonomials const& m, monomial const& mon): m(m), mon(mon) {}
            pf_iterator begin() { return pf_iterator(m, mon, false); }
            pf_iterator end() { return pf_iterator(m, mon, true); }
        };

        factors_of get_factors_of(monomial const& m) const { inc_visited(); return factors_of(*this, m); }
        
        /**
           \brief display state of emonomials
        */
        std::ostream& display(std::ostream& out) const;

        /**
           \brief
           these are merge event handlers to interect the union-find handlers.
           r2 becomes the new root. r2 is the root of v2, r1 is the old root of v1
        */
        void merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) override;

        void after_merge_eh(signed_var r2, signed_var r1, signed_var v2, signed_var v1) override;

        void unmerge_eh(signed_var r2, signed_var r1) override;        

    };

    inline std::ostream& operator<<(std::ostream& out, emonomials const& m) { return m.display(out); }

}
