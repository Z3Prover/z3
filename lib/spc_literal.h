/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_literal.h

Abstract:

    Superposition Calculus literal

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef _SPC_LITERAL_H_
#define _SPC_LITERAL_H_

#include"ast.h"
#include"order.h"
#include"expr_stat.h"

namespace spc {
    typedef expr_stat literal_stat;

#define DEPTH_NUM_BITS 4
#define DEPTH_MAX ((1 << DEPTH_NUM_BITS) - 1)
#define CONST_COUNT_NUM_BITS 4    
#define CONST_COUNT_MAX ((1 << CONST_COUNT_NUM_BITS) - 1)
#define SYM_COUNT_NUM_BITS 16
#define SYM_COUNT_MAX ((1 << SYM_COUNT_NUM_BITS) - 1)

    /**
       \brief Superposition Calculus literal.
    */
    class literal {
        expr * m_atom;
        unsigned  m_sign:1;                           // true if a negative literal.
        unsigned  m_oriented:1;                       // true if it is an oriented equality.
        unsigned  m_left:1;                           // true if the largest term is on the left-hand-side of the equality (only meaningful if m_oriented == true).
        unsigned  m_selected:1;                       // true if it is a selected literal.
        unsigned  m_stats:1;                          // true if the following fields were initialized.
        unsigned  m_ground:1;                         // true if it is a ground literal
        unsigned  m_p_indexed:1;                      // true if the literal was inserted into the p (paramodulation) superposition index.
        unsigned  m_r_indexed:1;                      // true if the literal was inserted into the r (resolution) superposition index.
        unsigned  m_depth:DEPTH_NUM_BITS;             // approx. depth
        unsigned  m_const_count:CONST_COUNT_NUM_BITS; // approx. number of constants 
        unsigned  m_sym_count:SYM_COUNT_NUM_BITS;     // approx. size

        friend class clause;
        
        void set_selected(bool f) { 
            m_selected = f; 
        }
        
    public:
        literal():
            m_atom(0), 
            m_sign(false), 
            m_oriented(false), 
            m_left(false), 
            m_selected(false), 
            m_stats(false),
            m_ground(false),
            m_p_indexed(false),
            m_r_indexed(false),
            m_depth(0),
            m_const_count(0),
            m_sym_count(0) {
        }

        literal(expr * atom, bool sign = false):
            m_atom(atom), 
            m_sign(sign), 
            m_oriented(false), 
            m_left(false), 
            m_selected(false), 
            m_stats(false),    
            m_ground(false),
            m_p_indexed(false),
            m_r_indexed(false),
            m_depth(0),
            m_const_count(0),
            m_sym_count(0) {
        }

        bool sign() const { return m_sign; }
        bool pos() const { return !m_sign; }
        bool neg() const { return m_sign; }
        bool is_oriented() const { return m_oriented; }
        bool is_left() const { return m_left; }
        bool is_selected() const { return m_selected; }
        expr * atom() const { return m_atom; }
        expr * lhs() const { return to_app(m_atom)->get_arg(0); }
        expr * rhs() const { return to_app(m_atom)->get_arg(1); }
        unsigned get_id() const { return m_sign ? (to_app(m_atom)->get_id() << 1) + 1 : (to_app(m_atom)->get_id() << 1); }
        unsigned get_neg_id() const { return m_sign ? (to_app(m_atom)->get_id() << 1) : (to_app(m_atom)->get_id() << 1) + 1; }

        bool operator==(literal const & other) const { return m_atom == other.m_atom && m_sign == other.m_sign; }
        bool operator!=(literal const & other) const { return !operator==(other); }

        void set_p_indexed(bool f) { m_p_indexed = f; }
        void set_r_indexed(bool f) { m_r_indexed = f; }
        bool is_p_indexed() const { return m_p_indexed; }
        bool is_r_indexed() const { return m_r_indexed; }

        void try_to_orient(order & o);
        bool is_true(ast_manager & m) const {
            return 
                (!m_sign && m.is_true(m_atom)) || 
                (!m_sign && m.is_eq(m_atom) && to_app(m_atom)->get_arg(0) == to_app(m_atom)->get_arg(1)) ||
                (m_sign && m.is_false(m_atom));
        }
        bool is_false(ast_manager & m) const {
            return
                (m_sign && m.is_true(m_atom)) || 
                (m_sign && m.is_eq(m_atom) && to_app(m_atom)->get_arg(0) == to_app(m_atom)->get_arg(1)) ||
                (!m_sign && m.is_false(m_atom));
        }
        expr * to_expr(ast_manager & m) const;

        /**
           \brief Collect literal statistics
        */
        void get_stat(literal_stat & stat);
        void init_stat() { literal_stat st; get_stat(st); }
        bool has_stats() const { return m_stats; }
        bool is_ground() const { SASSERT(m_stats); return m_ground; }
        unsigned get_approx_depth() const { SASSERT(m_stats); return m_depth; }
        unsigned get_approx_const_count() const { SASSERT(m_stats); return m_const_count; }
        unsigned get_approx_sym_count() const { SASSERT(m_stats); return m_sym_count; }

        void display(std::ostream & out, ast_manager & m, bool detailed = false) const;
    };

    COMPILE_TIME_ASSERT(sizeof(expr*) != 4 || sizeof(literal) == sizeof(expr *) + sizeof(unsigned)); // 32 bit machine
    COMPILE_TIME_ASSERT(sizeof(expr*) != 8 || sizeof(literal) == sizeof(expr *) + sizeof(unsigned) + /* a structure must be aligned */ sizeof(unsigned)); // 64 bit machine

    void display(std::ostream & out, unsigned num_lists, literal * lits, ast_manager & m, bool detailed = false);

    order::result compare(order & o, literal const & l1, literal const & l2, unsigned offset = 0, substitution * s = 0);
    bool greater(order & o, literal const & l1, literal const & l2, unsigned offset = 0, substitution * s = 0);
    bool is_maximal(order & o, unsigned num_lists, literal * lits, literal const & l, unsigned offset = 0, substitution * s = 0);
    bool is_sel_maximal(order & o, unsigned num_lists, literal * lits, literal const & l, unsigned offset = 0, substitution * s = 0);

    /**
       \brief Set of found literals.

       This object is used to implement duplicate literal elimination, ans syntatic tautology.
    */
    class found_literals {
        bit_vector        m_marks;
        unsigned_vector   m_lit_ids;
    public:
        /**
           \brief Insert the given literal into the set.
        */
        void insert(literal const & l);
        
        /**
           \brief Return true if the set contains \c l.
        */
        bool contains(literal const & l) const;

        /**
           \brief Return true if the set contains the negation of \c l.
        */
        bool contains_neg(literal const & l) const;

        bool empty() const { return m_lit_ids.empty(); }

        /**
           \brief Remove all literals from the set.
        */
        void reset();
    };

    class literal_buffer {
        ast_manager &   m_manager;
        buffer<literal> m_lits;
    public:
        literal_buffer(ast_manager & m):
            m_manager(m) {
        }
        
        ~literal_buffer() {
            reset();
        }
        
        void push_back(literal const & l) { 
            m_manager.inc_ref(l.atom()); 
            m_lits.push_back(l); 
        }
        
        void reset();

        unsigned size() const {
            return m_lits.size();
        }

        literal * c_ptr() const {
            return m_lits.c_ptr();
        }
    };

    expr * mk_or(ast_manager & m, unsigned num_lists, literal * lits);
};

#endif /* _SPC_LITERAL_H_ */
