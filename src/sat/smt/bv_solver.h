/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_solver.h

Abstract:

    Theory plugin for bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30

--*/
#pragma once

#include "sat/smt/sat_th.h"

namespace bv {

    class solver : public euf::th_euf_solver {
        typedef rational numeral;
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef sat::literal literal;
        typedef sat::bool_var bool_var;
        typedef sat::literal_vector literal_vector;
        typedef svector<euf::theory_var> vars;
        typedef std::pair<numeral, unsigned> value_sort_pair;
        typedef pair_hash<obj_hash<numeral>, unsigned_hash> value_sort_pair_hash;
        typedef map<value_sort_pair, theory_var, value_sort_pair_hash, default_eq<value_sort_pair> > value2var;
        typedef union_find<solver>  th_union_find;

        /**
           \brief Structure used to store the position of a bitvector variable that
           contains the true_literal/false_literal.
           
           Remark: the implementation assumes that bitvector variables containing
           complementary bits are never merged. I assert a disequality (not (= x y))
           whenever x and y contain complementary bits. However, this is too expensive
           when the bit is the true_literal or false_literal. The number of disequalities
           is too big. To avoid this problem, each equivalence class has a set
           of its true_literal and false_literal bits in the form of svector<zero_one_bit>.
           
           Before merging two classes we just check if the merge is valid by traversing these
           vectors.
        */
        struct zero_one_bit {
            theory_var m_owner;    //!< variable that owns the bit: useful for backtracking
            unsigned   m_idx:31;
            unsigned   m_is_true:1;
            zero_one_bit(theory_var v = euf::null_theory_var, unsigned idx = UINT_MAX, bool is_true = false):
                m_owner(v), m_idx(idx), m_is_true(is_true) {}
        };

        typedef svector<zero_one_bit> zero_one_bits;

        class atom {
        public:
            virtual ~atom() {}
            virtual bool is_bit() const = 0;
        };

        struct var_pos_occ {
            theory_var    m_var;
            unsigned      m_idx;
            var_pos_occ * m_next;
            var_pos_occ(theory_var v = euf::null_theory_var, unsigned idx = 0, var_pos_occ * next = nullptr):m_var(v), m_idx(idx), m_next(next) {}
        };

        struct bit_atom : public atom {
            var_pos_occ * m_occs;
            bit_atom():m_occs(nullptr) {}
            ~bit_atom() override {}
            bool is_bit() const override { return true; }
        };

        struct le_atom : public atom {
            literal    m_var;
            literal    m_def;
            le_atom(literal v, literal d):m_var(v), m_def(d) {}
            ~le_atom() override {}
            bool is_bit() const override { return false; }
        };

        euf::solver&             ctx;
        bv_util                  m_util;
        arith_util               m_autil;
//        bit_blaster              m_bb;
        th_union_find            m_find;
        vector<literal_vector>   m_bits;     // per var, the bits of a given variable.
        ptr_vector<expr>         m_bits_expr;
        svector<unsigned>        m_wpos;     // per var, watch position for fixed variable detection. 
        vector<zero_one_bits>    m_zero_one_bits; // per var, see comment in the struct zero_one_bit
//        bool_var2atom            m_bool_var2atom;
        sat::solver* m_solver;
        svector<sat::eframe>     m_stack;
        bool                     m_is_redundant{ false };

        bool visit(expr* e);
        bool visited(expr* e);
    public:
        solver(euf::solver& ctx);
        ~solver() override {}
        void set_solver(sat::solver* s) override { m_solver = s; }
        void set_lookahead(sat::lookahead* s) override { }
        void init_search() override {}
        double get_reward(literal l, sat::ext_constraint_idx idx, sat::literal_occs_fun& occs) const override;
        bool is_extended_binary(sat::ext_justification_idx idx, literal_vector& r) override;
        bool is_external(bool_var v) override;
        bool propagate(literal l, sat::ext_constraint_idx idx) override;
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector & r) override;
        void asserted(literal l) override;
        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        void pre_simplify() override;
        void simplify() override;
        void clauses_modifed() override;
        lbool get_phase(bool_var v) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        extension* copy(sat::solver* s) override;       
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override {}
        void gc() override {}
        void pop_reinit() override;
        bool validate() override;
        void init_use_list(sat::ext_use_list& ul) override;
        bool is_blocked(literal l, sat::ext_constraint_idx) override;
        bool check_model(sat::model const& m) const override;
        unsigned max_var(unsigned w) const override;

        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override { return false; }

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override { return false; }
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        euf::theory_var mk_var(euf::enode* n) override;

    };


}
