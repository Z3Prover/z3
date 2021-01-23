/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_char.h

Abstract:

    Solver for characters

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-16

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/bit_blaster/bit_blaster.h"
#include "smt/smt_theory.h"

namespace smt {

    class seq_char {


        struct stats {
            unsigned m_num_ackerman;
            unsigned m_num_bounds;
            unsigned m_num_blast;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        theory&          th;
        ast_manager&     m;
        seq_util         seq;
        vector<literal_vector>  m_bits;
        vector<expr_ref_vector> m_ebits;
        unsigned_vector  m_var2value;
        svector<theory_var> m_value2var;
        bool             m_enabled { false };
        bit_blaster      m_bb;
        stats            m_stats;
        symbol           m_bits2char;

        struct reset_bits;

        context& ctx() const { return th.get_context(); }

        literal_vector const& get_bits(theory_var v);

        expr_ref_vector const& get_ebits(theory_var v);

        bool has_bits(theory_var v) const;

        void init_bits(theory_var v);

        bool get_value(theory_var v, unsigned& c);
        
        void enforce_ackerman(theory_var v, theory_var w);

        void enforce_value_bound(theory_var v);

        void enforce_bits();

    public:

        seq_char(theory& th);

        bool enabled() const { return m_enabled; }

        // <= atomic constraints on characters
        void assign_le(theory_var v1, theory_var v2, literal lit);

        // < atomic constraint on characters
        void assign_lt(theory_var v1, theory_var v2, literal lit);

        void new_const_char(theory_var v, unsigned c);
        
        // = on characters
        void new_eq_eh(theory_var v1, theory_var v2);

        // != on characters
        void new_diseq_eh(theory_var v1, theory_var v2);

        // ensure coherence for character codes and equalities of shared symbols.
        bool final_check();

        unsigned get_value(theory_var v);

        void internalize_le(literal lit, app* term);

        void collect_statistics(::statistics& st) const;
        
    };

}

