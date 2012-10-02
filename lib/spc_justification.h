/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_justification.h

Abstract:

    Proof-like objects for tracking dependencies in the superposition
    calculus engine, and generating proofs.

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef _SPC_JUSTIFICATION_H_
#define _SPC_JUSTIFICATION_H_

#include"ast.h"
#include"spc_literal.h"
#include"spc_decl_plugin.h"

namespace spc {

    class clause;
    
    /**
       \brief Proof-like object use to track dependencies and produce
       proofs.

       \remark All justification objects must be allocated using the
       small_object_allocator in ast_manager.
    */
    class justification {
        clause * m_owner;
        unsigned m_ref_count:30;
        unsigned m_mark:1;
        unsigned m_assumption:1;
        
        friend class clause;
        void set_owner(clause * cls) { m_owner = cls; }

    public:
        justification(bool assumption = false):
            m_owner(0),
            m_ref_count(0),
            m_mark(false), 
            m_assumption(assumption) {
        }
        
        virtual ~justification() {}

        void inc_ref() { 
            m_ref_count++;
        }

        bool dec_ref() {
            SASSERT(m_ref_count > 0);
            m_ref_count--;
            return m_ref_count == 0;
        }
            
        unsigned get_ref_count() {
            return m_ref_count;
        }

        void set_mark(bool f) { m_mark = f; }
     
        bool is_marked() const { return m_mark; }

        /**
           \brief Return the clause justified by this object. 
           
           \remark for some justification objects that clause is
           supressed. Example: intermediate steps.
        */
        clause * get_clause() { return m_owner; }

        /**
           \brief Return the expr justified by this object. 
           This method returns a non null value only when
           proof generation is enabled. 
        */
        virtual expr * get_expr(ast_manager & m) { return 0; }

        /**
           \brief Return a non-zero value if the justification
           is wrapping a proof object.
        */
        virtual proof * get_proof() const { return 0; }

        /**
           \brief Return the parent justifications.
        */
        virtual void get_parents(ptr_buffer<justification> & parents) {}

        /**
           \brief Return the name of the rule used.
        */
        virtual spc_op_kind get_rule_id() = 0;
        
        /**
           \brief Return true if the justification is an external assumption.
        */
        bool assumption() const { return m_assumption; }

        void display(std::ostream & out);

        /**
           \brief This method is invoked before the object is deleted.
           Return the amount of memory consumed by this object.
        */
        virtual unsigned del_eh(ast_manager & m) = 0;
    };

    struct justification_stat {
        unsigned           m_proof_depth;
        unsigned           m_max_scope_lvl;
        ptr_buffer<clause> m_parent_clauses;
        justification_stat():
            m_proof_depth(0),
            m_max_scope_lvl(0) {
        }
    };

    void get_justification_stat(justification * p, justification_stat & stat);

    void dec_ref(justification * p, ast_manager & m);

    /**
       \brief Smart pointer for justification objects.
    */
    class justification_ref {
        justification * m_obj;
        ast_manager &   m_manager;
        void inc_ref() { if (m_obj) m_obj->inc_ref(); }
        void dec_ref() { if (m_obj) spc::dec_ref(m_obj, m_manager); }
    public:
        justification_ref(ast_manager & m):m_obj(0), m_manager(m) {}
        justification_ref(justification * j, ast_manager & m):
            m_obj(j), m_manager(m) {
            inc_ref();
        }
        ~justification_ref() {
            dec_ref();
        }
        operator justification*() const { return m_obj; }
        operator bool() const { return m_obj != 0; }
        bool operator!() const { return m_obj == 0; }
        justification * operator->() const { return m_obj; }
        justification const & operator*() const { return *m_obj; }
        justification_ref & operator=(justification * n) {
            if (n)
                n->inc_ref();
            dec_ref();
            m_obj = n;
            return *this;
        }
        justification_ref & operator=(justification_ref & n) {
            SASSERT(&m_manager == &n.m_manager);
            n.inc_ref();
            dec_ref();
            m_obj = n.m_obj;
            return *this;
        }
    };
    
    class justification_proof_wrapper : public justification {
        proof * m_proof;
        justification_proof_wrapper(proof * p, ast_manager & m):m_proof(p) { m.inc_ref(m_proof); }
    public:
        static justification * mk(proof * p, ast_manager & m);
        virtual ~justification_proof_wrapper() {}
        virtual proof * get_proof() const;
        virtual spc_op_kind get_rule_id() { return PR_SPC_ASSERTED; };
        virtual unsigned del_eh(ast_manager & m);
    };

    proof * mk_proof(ast_manager & m, family_id spc_fid, spc_op_kind pid, unsigned num_lits, literal * lits, proof * main_pr, unsigned num_auxs, 
                     proof * const * auxs);

    /**
       \brief Justification for rewriting steps: demodulation, duplicate literal deletion, resolved literal deletion.
    */
    class rewrite_justification : public justification {
        unsigned m_num_demodulators;
        void *   m_fields[0];
        static unsigned get_obj_size(unsigned num_demodulators, bool fine_grain) { 
            return sizeof(rewrite_justification) + (num_demodulators + (fine_grain ? 2 : 1)) * sizeof(void *); 
        }
        rewrite_justification(ast_manager & m, justification * head, 
                              unsigned num_demodulators, justification * const * demodulators, proof * pr);
    public:
        static justification * mk(ast_manager & m, justification * head, 
                                  unsigned num_demodulators, justification * const * demodulators, proof * pr = 0);
        virtual ~rewrite_justification() {}
        virtual proof * get_proof() const;
        virtual spc_op_kind get_rule_id() { return PR_SPC_REWRITE; }
        virtual void get_parents(ptr_buffer<justification> & parents);
        virtual unsigned del_eh(ast_manager & m);
    };

    proof * mk_rewrite_proof(ast_manager & m, family_id spc_fid, unsigned num_lits, literal * lits, proof * main_pr, unsigned num_auxs, 
                             proof * const * auxs);

    template<spc_op_kind Kind> 
    class unary_justification : public justification {
    protected:
        justification * m_parent;
        proof *         m_proof; 

        unary_justification(ast_manager & m, justification * p, proof * pr):
            m_parent(p),
            m_proof(pr) {
            p->inc_ref();
            SASSERT(m.fine_grain_proofs() == (pr != 0));
            if (m.fine_grain_proofs())
                m.inc_ref(pr);
        }

    public:
        virtual proof * get_proof() const {
            return m_proof;
        }

        virtual void get_parents(ptr_buffer<justification> & parents) {
            parents.push_back(m_parent);
        }
        
        virtual unsigned del_eh(ast_manager & m) {
            if (m.fine_grain_proofs()) 
                m.dec_ref(m_proof);
            return sizeof(unary_justification);
        }
        
        virtual spc_op_kind get_rule_id() {
            return Kind;
        }
        
        static justification * mk(ast_manager & m, family_id spc_fid, justification * p, unsigned num_lits, literal * lits) {
            proof * pr = 0;
            if (m.fine_grain_proofs())
                pr = mk_proof(m, spc_fid, Kind, num_lits, lits, p->get_proof(), 0, 0);
            void * mem = m.get_allocator().allocate(sizeof(unary_justification));
            return new (mem) unary_justification(m, p, pr);
        }
    };

    inline justification * mk_eq_res_justification(ast_manager & m, family_id spc_fid, justification * p, unsigned num_lits, literal * lits) {
        return unary_justification<PR_EQUALITY_RESOLUTION>::mk(m, spc_fid, p, num_lits, lits);
    }

    inline justification * mk_factoring_justification(ast_manager & m, family_id spc_fid, justification * p, unsigned num_lits, literal * lits) {
        return unary_justification<PR_FACTORING>::mk(m, spc_fid, p, num_lits, lits);
    }

    inline justification * mk_der_justification(ast_manager & m, family_id spc_fid, justification * p, unsigned num_lits, literal * lits) {
        return unary_justification<PR_SPC_DER>::mk(m, spc_fid, p, num_lits, lits);
    }

    template<spc_op_kind Kind> 
    class binary_justification : public justification {
    protected:
        justification * m_parent1;
        justification * m_parent2;
        proof *         m_proof; 

        binary_justification(ast_manager & m, justification * p1, justification * p2, proof * pr):
            m_parent1(p1),
            m_parent2(p2),
            m_proof(pr) {
            p1->inc_ref();
            p2->inc_ref();
            SASSERT(m.fine_grain_proofs() == (pr != 0));
            if (m.fine_grain_proofs())
                m.inc_ref(pr);
        }

    public:
        virtual proof * get_proof() const {
            return m_proof;
        }

        virtual void get_parents(ptr_buffer<justification> & parents) {
            parents.push_back(m_parent1);
            parents.push_back(m_parent2);
        }
        
        virtual unsigned del_eh(ast_manager & m) {
            if (m.fine_grain_proofs()) 
                m.dec_ref(m_proof);
            return sizeof(binary_justification);
        }
        
        virtual spc_op_kind get_rule_id() {
            return Kind;
        }
        
        static justification * mk(ast_manager & m, family_id spc_fid, justification * p1, justification * p2, unsigned num_lits, literal * lits,
                                  unsigned num_vars, var * const * vars) {
            proof * pr = 0;
            if (m.fine_grain_proofs()) {
                ptr_buffer<sort> sorts;
                sbuffer<symbol>  names;
                for (unsigned i = 0; i < num_vars; i++) {
                    sorts.push_back(vars[num_vars - i - 1]->get_sort());
                    names.push_back(symbol(num_vars - i - 1));
                }
                expr * body = mk_or(m, num_lits, lits);
                expr * new_fact = 0;
                if (num_vars == 0)
                    new_fact = body;
                else
                    new_fact = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), body);
                pr = m.mk_app(spc_fid, Kind, p1->get_proof(), p2->get_proof(), new_fact); 
            }
            void * mem = m.get_allocator().allocate(sizeof(binary_justification));
            return new (mem) binary_justification(m, p1, p2, pr);
        }
    };

    inline justification * mk_superposition_justification(ast_manager & m, family_id spc_fid, justification * p1, justification * p2,
                                                          unsigned num_lits, literal * lits, unsigned num_vars, var * const * vars) {
        return binary_justification<PR_SUPERPOSITION>::mk(m, spc_fid, p1, p2, num_lits, lits, num_vars, vars);
    }

    inline justification * mk_resolution_justification(ast_manager & m, family_id spc_fid, justification * p1, justification * p2,
                                                          unsigned num_lits, literal * lits, unsigned num_vars, var * const * vars) {
        return binary_justification<PR_SPC_RESOLUTION>::mk(m, spc_fid, p1, p2, num_lits, lits, num_vars, vars);
    }
};

#endif /* _SPC_JUSTIFICATION_H_ */
