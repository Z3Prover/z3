/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    polysat_solver.h

Abstract:

    Theory plugin for bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "math/dd/dd_pdd.h"
#include "sat/smt/polysat_core.h"

namespace euf {
    class solver;
}

namespace polysat {


    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef sat::literal literal;
        typedef sat::bool_var bool_var;
        typedef sat::literal_vector literal_vector;
        using pdd = dd::pdd;

        struct stats {
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };

        struct atom {
            bool_var                m_bv;
            signed_constraint       m_sc;
            atom(bool_var b) :m_bv(b) {}
            ~atom() { }
        };

        class polysat_proof : public euf::th_proof_hint {
        public:
            ~polysat_proof() override {}
            expr* get_hint(euf::solver& s) const override { return nullptr; }
        };

        friend class core;

        bv_util                  bv;
        arith_util               m_autil;
        stats                    m_stats;
        core                     m_core;
        polysat_proof            m_proof;

        vector<pdd>              m_var2pdd;                   // theory_var 2 pdd
        bool_vector              m_var2pdd_valid;             // valid flag
        unsigned_vector          m_pddvar2var;                // pvar -> theory_var
        ptr_vector<atom>         m_bool_var2atom;             // bool_var -> atom

        svector<std::pair<euf::theory_var, euf::theory_var>> m_var_eqs;
        unsigned                 m_var_eqs_head = 0;

        bool m_has_lemma = false;
        unsigned m_lemma_level = 0;
        expr_ref_vector m_lemma;

        // internalize
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        unsigned get_bv_size(euf::enode* n);
        unsigned get_bv_size(theory_var v);
        theory_var get_var(euf::enode* n);
        void fixed_var_eh(theory_var v);
        bool is_fixed(euf::theory_var v, expr_ref& val, sat::literal_vector& lits) override { return false; }
        bool is_bv(theory_var v) const { return bv.is_bv(var2expr(v)); }
        void register_true_false_bit(theory_var v, unsigned i);
        void add_bit(theory_var v, sat::literal lit);
        void eq_internalized(sat::bool_var b1, sat::bool_var b2, unsigned idx, theory_var v1, theory_var v2, sat::literal eq, euf::enode* n);

        void insert_bv2a(bool_var bv, atom* a) { m_bool_var2atom.setx(bv, a, nullptr); }
        void erase_bv2a(bool_var bv) { m_bool_var2atom[bv] = nullptr; }
        atom* get_bv2a(bool_var bv) const { return m_bool_var2atom.get(bv, nullptr); }
        class mk_atom_trail;
        atom* mk_atom(sat::bool_var bv);
        void set_bit_eh(theory_var v, literal l, unsigned idx);
        void init_bits(expr* e, expr_ref_vector const & bits);
        void mk_bits(theory_var v);
        void add_def(sat::literal def, sat::literal l);
        void internalize_unary(app* e, std::function<pdd(pdd)> const& fn);
        void internalize_binary(app* e, std::function<pdd(pdd, pdd)> const& fn);
        void internalize_binaryc(app* e, std::function<signed_constraint(pdd, pdd)> const& fn);
        void internalize_par_unary(app* e, std::function<pdd(pdd,unsigned)> const& fn);
        void internalize_novfl(app* n, std::function<void(unsigned, expr* const*, expr* const*, expr_ref&)>& fn);
        void internalize_interp(app* n, std::function<expr*(expr*, expr*)>& ibin, std::function<expr*(expr*)>& un);
        void internalize_num(app * n);       
        void internalize_concat(app * n);        
        void internalize_bv2int(app* n);
        void internalize_int2bv(app* n);
        void internalize_mkbv(app* n);
        void internalize_xor3(app* n);
        void internalize_carry(app* n);
        void internalize_sub(app* n);
        void internalize_extract(app* n);
        void internalize_repeat(app* n);
        void internalize_bit2bool(app* n);
        void internalize_udiv_i(app* n);
        template<bool Signed, bool Reverse, bool Negated>
        void internalize_le(app* n);
        void internalize_div_rem_i(app* e, bool is_div);
        void internalize_div_rem(app* e, bool is_div);
        void internalize_polysat(app* a);
        void assert_bv2int_axiom(app * n);
        void assert_int2bv_axiom(app* n);
        void internalize_bit2bool(atom* a, expr* e, unsigned idx);

        pdd expr2pdd(expr* e);
        pdd var2pdd(euf::theory_var v);
        void internalize_set(expr* e, pdd const& p);
        void internalize_set(euf::theory_var v, pdd const& p);

        // callbacks from core
        void add_eq_literal(pvar v, rational const& val);
        void set_conflict(dependency_vector const& core);
        void set_lemma(vector<signed_constraint> const& lemma, unsigned level, dependency_vector const& core);
        void propagate(signed_constraint sc, dependency_vector const& deps);
        void add_lemma(vector<signed_constraint> const& lemma);

        std::pair<sat::literal_vector, euf::enode_pair_vector> explain_deps(dependency_vector const& deps);
	       
    public:
        solver(euf::solver& ctx, theory_id id);
        void set_lookahead(sat::lookahead* s) override { }
        void init_search() override {}
        double get_reward(literal l, sat::ext_constraint_idx idx, sat::literal_occs_fun& occs) const override { return 0; }
        bool is_extended_binary(sat::ext_justification_idx idx, literal_vector& r) override { return false; }
        bool is_external(bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector & r, bool probing) override;
        void asserted(literal l) override;
        sat::check_result check() override;
        void simplify() override {}
        void clauses_modifed() override {}
        lbool get_phase(bool_var v) override { return l_undef; }
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override { throw default_exception("nyi"); }
        extension* copy(sat::solver* s) override { throw default_exception("nyi"); }
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override {}
        void gc() override {}
        void pop_reinit() override {}
        lbool resolve_conflict() override;
        bool validate() override { return true; }
        void init_use_list(sat::ext_use_list& ul) override {}
        bool is_blocked(literal l, sat::ext_constraint_idx) override { return false; }
        bool check_model(sat::model const& m) const override;
        void finalize_model(model& mdl) override;

        void new_eq_eh(euf::th_eq const& eq) override;
        void new_diseq_eh(euf::th_eq const& ne) override;
        bool use_diseqs() const override { return true; }
        bool unit_propagate() override;

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;

        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override { return false; }

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override { return false; }
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        void eq_internalized(euf::enode* n) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode * n, sort * s) override;
    };

}
