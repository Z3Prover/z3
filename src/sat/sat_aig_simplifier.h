/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_aig_simplifier.h

  Abstract:
   
    extract AIG definitions from clauses
    Perform cut-set enumeration to identify equivalences.

  Author:

    Nikolaj Bjorner 2020-01-02

  --*/

#pragma once

#include "sat/sat_aig_finder.h"
#include "sat/sat_cutset.h"

namespace sat {

    enum bool_op {
        var_op,
        and_op,
        ite_op,
        xor_op,
        no_op
    };

    class aig_cuts {
        // encodes one of var, and, !and, xor, !xor, ite, !ite.
        class node {
            bool     m_sign;
            bool_op  m_op;
            unsigned m_num_children;
            unsigned m_offset;
        public:
            node(): m_sign(false), m_op(no_op), m_num_children(UINT_MAX), m_offset(UINT_MAX) {}
            explicit node(unsigned v): m_sign(false), m_op(var_op), m_num_children(UINT_MAX), m_offset(v) {}
            explicit node(bool negate, bool_op op, unsigned num_children, unsigned offset): 
                m_sign(negate), m_op(op), m_num_children(num_children), m_offset(offset) {}
            bool is_valid() const { return m_offset != UINT_MAX; }
            bool_op op() const { return m_op; }
            bool is_var() const { return m_op == var_op; }
            bool is_and() const { return m_op == and_op; }
            bool is_xor() const { return m_op == xor_op; }
            bool is_ite() const { return m_op == ite_op; }
            unsigned var() const { SASSERT(is_var()); return m_offset; }
            bool sign() const { return m_sign; }
            unsigned num_children() const { SASSERT(!is_var()); return m_num_children; }
            unsigned offset() const { return m_offset; }
        };
        svector<node>         m_aig;        // vector of main aig nodes.
        vector<svector<node>> m_aux_aig;    // vector of auxiliary aig nodes.
        literal_vector     m_literals;
        region             m_region;
        unsigned           m_max_cut_size;
        unsigned           m_max_cutset_size;
        cut_set            m_cut_set1, m_cut_set2;
        vector<cut_set>    m_cuts;

        void insert_aux(unsigned v, node const& n);
        void init_cut_set(unsigned id);

        unsigned_vector filter_valid_nodes();
        void augment(unsigned_vector const& ids, vector<cut_set>& cuts);
        void augment_ite(node const& n, cut_set& cs, vector<cut_set>& cuts);
        void augment_aig0(node const& n, cut_set& cs, vector<cut_set>& cuts);
        void augment_aig1(node const& n, cut_set& cs, vector<cut_set>& cuts);
        void augment_aig2(node const& n, cut_set& cs, vector<cut_set>& cuts);
        void augment_aigN(node const& n, cut_set& cs, vector<cut_set>& cuts);

    public:
        aig_cuts(unsigned max_cut_size, unsigned max_cutset_size);
        void add_var(unsigned v);
        void add_node(literal head, bool_op op, unsigned sz, literal const* args);

        literal child(node const& n, unsigned idx) const { SASSERT(!n.is_var()); SASSERT(idx < n.num_children()); return m_literals[n.offset() + idx]; }
        vector<cut_set> const & get_cuts();
    };

    class aig_simplifier {
    public:
        struct stats {
            unsigned m_num_eqs, m_num_cuts, m_num_xors, m_num_ands, m_num_ites;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct config {
            unsigned m_max_cut_size;
            unsigned m_max_cutset_size;
            config(): m_max_cut_size(4), m_max_cutset_size(10) {}
        };
    private:
        solver& s;
        stats   m_stats;
        config  m_config;
        aig_cuts m_aig_cuts;
        unsigned m_trail_size;
        literal_vector m_lits;

        struct report;
        void clauses2aig();
        void aig2clauses();
    public:
        aig_simplifier(solver& s);
        ~aig_simplifier() {}                
        void operator()();
        void collect_statistics(statistics& st) const;

        void add_and(literal head, unsigned sz, literal const* args);
        void add_or(literal head, unsigned sz, literal const* args);
        void add_xor(literal head, unsigned sz, literal const* args);
        void add_ite(literal head, literal c, literal t, literal e);
        void add_iff(literal head, literal l1, literal l2);
    };
}


