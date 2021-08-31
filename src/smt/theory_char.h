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

#include "ast/char_decl_plugin.h"
#include "ast/rewriter/bit_blaster/bit_blaster.h"
#include "model/char_factory.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_char : public theory {

        struct stats {
            unsigned m_num_ackerman;
            unsigned m_num_bounds;
            unsigned m_num_blast;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        seq_util                seq;
        vector<literal_vector>  m_bits;
        vector<expr_ref_vector> m_ebits;
        unsigned_vector         m_var2value;
        svector<theory_var>     m_value2var;
        bit_blaster             m_bb;
        stats                   m_stats;
        symbol                  m_bits2char;
        char_factory*           m_factory { nullptr };

        struct reset_bits;

        literal_vector const& get_bits(theory_var v);
        expr_ref_vector const& get_ebits(theory_var v);
        bool has_bits(theory_var v) const;
        void init_bits(theory_var v);
        bool get_char_value(theory_var v, unsigned& c);        
        void enforce_ackerman(theory_var v, theory_var w);
        void enforce_value_bound(theory_var v);
        void enforce_bits();

        bool final_check();
        void new_const_char(theory_var v, unsigned c);
        void new_char2int(theory_var v, expr* c);
        unsigned get_char_value(theory_var v);
        void internalize_le(literal lit, app* term);        
        void internalize_is_digit(literal lit, app* term);        

        theory_var mk_var(enode* n) override;

    public:

        theory_char(context& ctx);
        
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        theory * mk_fresh(context * new_ctx) override { return alloc(theory_char, *new_ctx); }
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void display(std::ostream& out) const override {}
        final_check_status final_check_eh() override { return final_check() ? FC_DONE : FC_CONTINUE; }
        void init_model(model_generator & mg) override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
        void collect_statistics(::statistics& st) const override;

    };

}

