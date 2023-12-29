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
#include "sat/smt/polysat/core.h"
#include "sat/smt/intblast_solver.h"
#include "ast/euf/euf_bv_plugin.h"

namespace euf {
    class solver;
}

namespace polysat {


    class solver : public euf::th_euf_solver, public solver_interface {
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
            constraint_id           m_index;
            atom(bool_var b, constraint_id index) :m_bv(b), m_index(index) {}
            ~atom() { }
        };


        class polysat_proof : public euf::th_proof_hint {
            // assume name is statically allocated
            char const* name;
        public:
            polysat_proof(char const* name) : name(name) {}
            ~polysat_proof() override {}
            expr* get_hint(euf::solver& s) const override;
        };

        polysat_proof* mk_proof_hint(char const* name);

        bv_util                  bv;
        arith_util               m_autil;
        stats                    m_stats;
        core                     m_core;
        intblast::solver         m_intblast;

        vector<pdd>              m_var2pdd;                   // theory_var 2 pdd
        bool_vector              m_var2pdd_valid;             // valid flag
        unsigned_vector          m_pddvar2var;                // pvar -> theory_var
        ptr_vector<atom>         m_bool_var2atom;             // bool_var -> atom
        euf::bv_plugin* m_bv_plugin = nullptr;

        svector<std::pair<euf::theory_var, euf::theory_var>> m_var_eqs;
        unsigned                 m_var_eqs_head = 0;

        bool m_has_lemma = false;
        unsigned m_lemma_level = 0;
        expr_ref_vector m_lemma;

        sat::check_result intblast();

        void explain_slice(pvar v, pvar w, unsigned offset, std::function<void(euf::enode*, euf::enode*)>& consume);
        void explain_fixed(pvar v, unsigned lo, unsigned hi, rational const& value, std::function<void(euf::enode*, euf::enode*)>& consume_eq);

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
        void  mk_atom(sat::bool_var bv, signed_constraint& sc);
        void set_bit_eh(theory_var v, literal l, unsigned idx);
        void init_bits(expr* e, expr_ref_vector const & bits);
        void mk_bits(theory_var v);
        void add_def(sat::literal def, sat::literal l);
        void internalize_unary(app* e, std::function<pdd(pdd)> const& fn);
        void internalize_binary(app* e, std::function<pdd(pdd, pdd)> const& fn);
        void internalize_binary(app* e, std::function<expr*(expr*, expr*)> const& fn);
        void internalize_binary_predicate(app* e, std::function<signed_constraint(pdd, pdd)> const& fn);
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
        void internalize_bor(app* n);
        void internalize_bxor(app* n);
        void internalize_bnor(app* n);
        void internalize_bnand(app* n);
        void internalize_bxnor(app* n);
        void internalize_band(app* n);
        void internalize_lshr(app* n);
        void internalize_ashr(app* n);
        void internalize_shl(app* n);
        template<bool Signed, bool Reverse, bool Negated>
        void internalize_le(app* n);
        void internalize_zero_extend(app* n);
        void internalize_sign_extend(app* n);
        void internalize_udiv_i(app* e);
        void internalize_urem_i(app* e);
        void internalize_div_rem(app* e, bool is_div);
        void axiomatize_srem(app* e, expr* x, expr* y);
        void axiomatize_smod(app* e, expr* x, expr* y);
        void axiomatize_sdiv(app* e, expr* x, expr* y);
        void axiomatize_redand(app* e, expr* x);
        void axiomatize_redor(app* e, expr* x);
        void axiomatize_comp(app* e, expr* x, expr* y);
        void axiomatize_rotate_left(app* e, unsigned n, expr* x);
        void axiomatize_rotate_right(app* e, unsigned n, expr* x);
        void axiomatize_ext_rotate_left(app* e, expr* x, expr* y);
        void axiomatize_ext_rotate_right(app* e, expr* x, expr* y);
        void axiomatize_int2bv(app* e, unsigned sz, expr* x);
        void axiomatize_bv2int(app* e, expr* x);
        void axioms_for_extract(app* e);
        void axioms_for_concat(app* e);
        expr* rotate_left(app* e, unsigned n, expr* x);
        unsigned m_delayed_axioms_qhead = 0;
        ptr_vector<app> m_delayed_axioms;
        bool propagate_delayed_axioms();
        void internalize_polysat(app* a);
        void assert_bv2int_axiom(app * n);
        void assert_int2bv_axiom(app* n);

        pdd expr2pdd(expr* e);
        pdd var2pdd(euf::theory_var v);
        void internalize_set(expr* e, pdd const& p);
        void internalize_set(euf::theory_var v, pdd const& p);
        void quot_rem(expr* quot, expr* rem, expr* x, expr* y);

        vector<pdd> m_eqs;
        u_map<constraint_id> m_eq2constraint;
        struct undo_add_eq;
        constraint_id eq_constraint(pdd p, pdd q, dependency d);

        // callbacks from core
        lbool add_eq_literal(pvar v, rational const& val, dependency& d) override;
        void set_conflict(dependency_vector const& core, char const* hint) override;
        bool add_axiom(char const* name, constraint_or_dependency const* begin, constraint_or_dependency const* end, bool redundant) override;
        dependency propagate(signed_constraint sc, dependency_vector const& deps, char const* hint) override;
        void propagate(dependency const& d, bool sign, dependency_vector const& deps, char const* hint) override;
        trail_stack& trail() override;
        bool inconsistent() const override;
        void get_bitvector_sub_slices(pvar v, offset_slices& out) override;
        void get_bitvector_super_slices(pvar v, offset_slices& out) override;
        void get_bitvector_suffixes(pvar v, offset_slices& out) override;
        void get_fixed_bits(pvar v, fixed_bits_vector& fixed_bits) override;
        unsigned level(dependency const& d) override;
        dependency explain_slice(pvar v, pvar w, unsigned offset);

        bool add_axiom(char const* name, constraint_or_dependency_list const& clause, bool redundant) {
            return add_axiom(name, clause.begin(), clause.end(), redundant);
        }

        void add_axiom(char const* name, std::initializer_list<sat::literal> const& clause);
        void equiv_axiom(char const* name, sat::literal a, sat::literal b);

        void validate_propagate(sat::literal lit, sat::literal_vector const& core, euf::enode_pair_vector const& eqs);
        void validate_conflict(sat::literal_vector const& core, euf::enode_pair_vector const& eqs);
        void validate_axiom(sat::literal_vector const& clause);

        void explain_dep(dependency const& d, euf::enode_pair_vector& eqs, sat::literal_vector& lits);

        std::pair<sat::literal_vector, euf::enode_pair_vector> explain_deps(dependency_vector const& deps);

        expr_ref constraint2expr(signed_constraint const& sc);
        expr_ref pdd2expr(pdd const& p);

        struct scoped_eq_justification;
	       
    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override {}
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
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx, get_id()); }
        extension* copy(sat::solver* s) override { throw default_exception("polysat copy nyi"); }
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override {}
        void gc() override {}
        void pop_reinit() override {}
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
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

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
