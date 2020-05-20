/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_unicode.h

Abstract:

    Solver for unicode characters

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-16

--*/
#pragma once

#include "util/s_integer.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_theory.h"
#include "smt/diff_logic.h"

namespace smt {

    class seq_unicode {
        struct ext {
            static const bool m_int_theory = true;
            typedef s_integer numeral;
            typedef s_integer fin_numeral;
            numeral m_epsilon;
            typedef literal explanation;
            ext(): m_epsilon(1) {}            
        };

        class nc_functor {
            literal_vector m_literals;
        public:
            nc_functor() {}
            void operator()(literal const& l) {
                if (l != null_literal) m_literals.push_back(l);
            }
            literal_vector const& get_lits() const { return m_literals; }
            void new_edge(dl_var s, dl_var d, unsigned num_edges, edge_id const* edges) {}
        };

        struct var_value_hash {
            seq_unicode & m_th;
            var_value_hash(seq_unicode & th):m_th(th) {}
            unsigned operator()(theory_var v) const { return m_th.get_value(v); }
        };

        struct var_value_eq {
            seq_unicode & m_th;
            var_value_eq(seq_unicode & th):m_th(th) {}
            bool operator()(theory_var v1, theory_var v2) const { 
                return m_th.get_value(v1) == m_th.get_value(v2);
            }
        };

        typedef int_hashtable<var_value_hash, var_value_eq> var_value_table;

        theory&          th;
        ast_manager&     m;
        seq_util         seq;
        dl_graph<ext>    dl;
        unsigned         m_qhead;
        svector<edge_id> m_asserted_edges;
        nc_functor       m_nc_functor;
        var_value_hash   m_var_value_hash;
        var_value_eq     m_var_value_eq;
        var_value_table  m_var_value_table;
        std::function<void(literal, literal, literal)> m_add_axiom;

        context& ctx() const { return th.get_context(); }

        void propagate(edge_id edge);

        void add_axiom(literal a, literal b = null_literal, literal c = null_literal) {
            m_add_axiom(a, b, c);
        }

        void adapt_eq(theory_var v1, theory_var v2);

        literal mk_literal(expr* e);

    public:

        seq_unicode(theory& th);

        // <= atomic constraints on characters
        void assign_le(theory_var v1, theory_var v2, literal lit);

        // < atomic constraint on characters
        void assign_lt(theory_var v1, theory_var v2, literal lit);
        
        // = on characters
        void new_eq_eh(theory_var v1, theory_var v2);

        // != on characters
        void new_diseq_eh(theory_var v1, theory_var v2);

        // ensure coherence for character codes and equalities of shared symbols.
        bool final_check();

        unsigned get_value(theory_var v);

        void propagate();

        bool can_propagate() const { return m_qhead < m_asserted_edges.size(); }
        
    };

}

