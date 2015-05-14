/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_clause.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-18.

Revision History:

--*/
#ifndef _SMT_CLAUSE_H_
#define _SMT_CLAUSE_H_

#include"ast.h"
#include"smt_literal.h"
#include"tptr.h"
#include"obj_hashtable.h"
#include"smt_justification.h"

namespace smt {

    class clause;

    /**
       \brief Abstract functor: clause deletion event handler.
    */
    class clause_del_eh {
    public:
        virtual ~clause_del_eh() {}
        virtual void operator()(ast_manager & m, clause * cls) = 0;
    };

    enum clause_kind {
        CLS_AUX,
        CLS_LEARNED,
        CLS_AUX_LEMMA 
    };
    
    /**
       \brief A SMT clause.
       
       A clause has several optional fields, I store space for them only if they are actually used.
    */
    class clause {
        unsigned m_num_literals;
        unsigned m_capacity:24;           //!< some of the clause literals can be simplified and removed, this field contains the original number of literals (used for GC).
        unsigned m_kind:2;                //!< kind
        unsigned m_reinit:1;              //!< true if the clause is in the reinit stack (only for learned clauses and aux_lemmas)
        unsigned m_reinternalize_atoms:1; //!< true if atoms must be reinitialized during reinitialization
        unsigned m_has_atoms:1;           //!< true if the clause has memory space for storing atoms.
        unsigned m_has_del_eh:1;          //!< true if must notify event handler when deleted.
        unsigned m_has_justification:1;   //!< true if the clause has a justification attached to it.
        unsigned m_deleted:1;             //!< true if the clause is marked for deletion by was not deleted yet because it is referenced by some data-structure (e.g., m_lemmas)
        literal  m_lits[0];

        static unsigned get_obj_size(unsigned num_lits, clause_kind k, bool has_atoms, bool has_del_eh, bool has_justification) {
            unsigned r = sizeof(clause) + sizeof(literal) * num_lits;
            if (k != CLS_AUX)
                r += sizeof(unsigned);
            /* dvitek: Fix alignment issues on 64-bit platforms.  The
             * 'if' statement below probably isn't worthwhile since
             * I'm guessing the allocator is probably going to round
             * up internally anyway.
             */
            //if (has_atoms || has_del_eh || has_justification)
            r = (r + (sizeof(void*)-1)) & ~(sizeof(void*)-1);
            if (has_atoms)
                r += sizeof(expr*) * num_lits;
            if (has_del_eh)
                r += sizeof(clause_del_eh *);
            if (has_justification)
                r += sizeof(justification *);
            return r;
        }

        unsigned const * get_activity_addr() const {
            return reinterpret_cast<unsigned const *>(m_lits + m_capacity);
        }

        unsigned * get_activity_addr() {
            return reinterpret_cast<unsigned *>(m_lits + m_capacity);
        }

        clause_del_eh * const * get_del_eh_addr() const {
            unsigned const * addr = get_activity_addr();
            if (is_lemma())
                addr ++;
            /* dvitek: It would be better to use uintptr_t than
             * size_t, but we need to wait until c++11 support is
             * really available.
             */
            size_t as_int = reinterpret_cast<size_t>(addr);
            as_int = (as_int + sizeof(void*)-1) & ~static_cast<size_t>(sizeof(void*)-1);
            return reinterpret_cast<clause_del_eh * const *>(as_int);
        }

        justification * const * get_justification_addr() const {
            clause_del_eh * const * addr = get_del_eh_addr();
            if (m_has_del_eh)
                addr ++;
            return reinterpret_cast<justification * const *>(addr);
        }

        expr * const * get_atoms_addr() const {
            justification * const * addr = get_justification_addr();
            if (m_has_justification)
                addr ++;
            return reinterpret_cast<expr * const *>(addr);
        }
        
        friend class context;

        void swap_lits(unsigned idx1, unsigned idx2) {
            literal tmp = get_literal(idx1);
            set_literal(idx1, get_literal(idx2));
            set_literal(idx2, tmp);
        }

        bool is_watch(literal l) const {
            return m_lits[0] == l || m_lits[1] == l;
        }

        void set_literal(unsigned idx, literal l) {
            m_lits[idx] = l;
        }

        void set_num_literals(unsigned n) {
            SASSERT(n <= m_num_literals);
            SASSERT(!m_reinit);
            m_num_literals = n;
        }

        void set_justification(justification * new_js) {
            SASSERT(m_has_justification);
            SASSERT(!m_reinit);
            SASSERT(!is_lemma() || new_js == 0 || !new_js->in_region());
            justification ** js_addr = const_cast<justification**>(get_justification_addr());
            *js_addr = new_js;
        }

        void release_atoms(ast_manager & m);
        
    public:
        static clause * mk(ast_manager & m, unsigned num_lits, literal * lits, clause_kind k, justification * js = 0, 
                           clause_del_eh * del_eh = 0, bool save_atoms = false, expr * const * bool_var2expr_map = 0);
        
        void deallocate(ast_manager & m);
        
        clause_kind get_kind() const {
            return static_cast<clause_kind>(m_kind);
        }

        bool is_lemma() const {
            return get_kind() != CLS_AUX;
        }

        bool is_learned() const {
            return get_kind() == CLS_LEARNED;
        }

        bool is_aux_lemma() const {
            return get_kind() == CLS_AUX_LEMMA;
        }

        bool in_reinit_stack() const { 
            return m_reinit;
        }

        bool reinternalize_atoms() const {
            return m_reinternalize_atoms;
        }
        
        unsigned get_num_literals() const {
            return m_num_literals;
        }

        literal get_literal(unsigned idx) const {
            SASSERT(idx < m_num_literals);
            return m_lits[idx];
        }

        literal & get_literal(unsigned idx) {
            SASSERT(idx < m_num_literals);
            return m_lits[idx];
        }

        literal * begin_literals() { return m_lits; }

        literal * end_literals() { return m_lits + m_num_literals; }

        literal const * begin_literals() const { return m_lits; }

        literal const * end_literals() const { return m_lits + m_num_literals; }

        unsigned get_activity() const {
            SASSERT(is_lemma());
            return *(get_activity_addr());
        }

        void set_activity(unsigned act) {
            SASSERT(is_lemma());
            *(get_activity_addr()) = act;
        }

        clause_del_eh * get_del_eh() const {
            return m_has_del_eh ? *(get_del_eh_addr()) : 0;
        }

        justification * get_justification() const {
            return m_has_justification ? *(get_justification_addr()) : 0;
        }

        unsigned get_num_atoms() const {
            return m_reinternalize_atoms ? m_num_literals : 0;
        }

        expr * get_atom(unsigned idx) const {
            SASSERT(idx < get_num_atoms());
            return UNTAG(expr*, get_atoms_addr()[idx]);
        }

        bool get_atom_sign(unsigned idx) const {
            SASSERT(idx < get_num_atoms());
            return GET_TAG(get_atoms_addr()[idx]) == 1;
        }

        bool erase_atom(unsigned idx);

        void inc_clause_activity() {
            SASSERT(is_lemma());
            set_activity(get_activity() + 1);
        }

        void display(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const;

        void display_compact(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const;

        unsigned hash() const {
            return get_ptr_hash(this); 
        }
        
        void mark_as_deleted(ast_manager & m) {
            SASSERT(!m_deleted);
            m_deleted = true;
            clause_del_eh * del_eh = get_del_eh();
            if (del_eh) {
                (*del_eh)(m, this);
                *(const_cast<clause_del_eh **>(get_del_eh_addr())) = 0;
            }
        }

        bool deleted() const { 
            return m_deleted; 
        }
    };

    typedef ptr_vector<clause> clause_vector;

    typedef obj_hashtable<clause> clause_set;
};

#endif /* _SMT_CLAUSE_H_ */

