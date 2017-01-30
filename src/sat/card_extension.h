/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    card_extension.h

Abstract:

    Cardinality extensions.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/
#ifndef CARD_EXTENSION_H_
#define CARD_EXTENSION_H_

#include"sat_extension.h"
#include"sat_solver.h"

namespace sat {

    class card_extension : public extension {
        struct stats {
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        class card {
            unsigned       m_index;
            literal        m_lit;
            unsigned       m_k;
            unsigned       m_size;
            literal_vector m_lits;
        public:
            card(unsigned index, literal lit, literal_vector const& lits, unsigned k);
            unsigned index() const { return m_index; }
            literal lit() const { return m_lit; }
            literal operator[](unsigned i) const { return m_lits[i]; }
            unsigned k() const { return m_k; }
            unsigned size() const { return m_size; }
            void swap(unsigned i, unsigned j) { std::swap(m_lits[i], m_lits[j]); }
            void negate();                       
        };

        typedef ptr_vector<card> watch;
        struct var_info {
            watch* m_lit_watch[2];
            card*  m_card;
            var_info(): m_card(0) {
                m_lit_watch[0] = 0;
                m_lit_watch[1] = 0;
            }
            void reset() {
                dealloc(m_card);
                dealloc(m_lit_watch[0]);
                dealloc(m_lit_watch[1]);
            }
        };


        solver*             m_solver;
        stats               m_stats;        

        ptr_vector<card>    m_constraints;

        // watch literals
        svector<var_info>   m_var_infos;
        unsigned_vector     m_var_trail;
        unsigned_vector     m_var_lim;       

        // conflict resolution
        unsigned          m_num_marks;
        unsigned          m_conflict_lvl;
        svector<int>      m_coeffs;
        svector<bool_var> m_active_vars;
        int               m_bound;
        tracked_uint_set  m_active_var_set;
        literal_vector    m_conflict;
        literal_vector    m_literals;

        solver& s() const { return *m_solver; }
        void init_watch(card& c, bool is_true);
        void init_watch(bool_var v);
        void assign(card& c, literal lit);
        lbool add_assign(card& c, literal lit);
        void watch_literal(card& c, literal lit);
        void set_conflict(card& c, literal lit);
        void clear_watch(card& c);
        void reset_coeffs();

        void unwatch_literal(literal w, card* c);
        void remove(ptr_vector<card>& cards, card* c);

        void normalize_active_coeffs();
        void inc_coeff(literal l, int offset);
        int get_coeff(bool_var v) const;
        int get_abs_coeff(bool_var v) const;       

        literal_vector& get_literals() { m_literals.reset(); return m_literals; }
        literal get_asserting_literal(literal conseq);
        bool resolve_conflict(card& c, literal_vector const& conflict_clause);
        void process_antecedent(literal l, int offset);
        void process_card(card& c, int offset);
        void cut();

        // validation utilities
        bool validate_conflict(card& c);
        bool validate_assign(literal_vector const& lits, literal lit);
        bool validate_lemma();
        bool validate_unit_propagation(card const& c);
        bool validate_conflict(literal_vector const& lits);

        void display(std::ostream& out, card& c, bool values) const;
        void display_watch(std::ostream& out, bool_var v, bool sign) const;
    public:
        card_extension();
        virtual ~card_extension();
        void    set_solver(solver* s) { m_solver = s; }
        void    add_at_least(bool_var v, literal_vector const& lits, unsigned k);
        virtual void propagate(literal l, ext_constraint_idx idx, bool & keep);
        virtual void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r);
        virtual void asserted(literal l);
        virtual check_result check();
        virtual void push();
        virtual void pop(unsigned n);
        virtual void simplify();
        virtual void clauses_modifed();
        virtual lbool get_phase(bool_var v);
        virtual std::ostream& display(std::ostream& out) const;
        virtual void collect_statistics(statistics& st) const;
    };

};

#endif
