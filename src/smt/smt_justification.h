/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_justification.h

Abstract:

    Proof-like objects for tracking dependencies in the SMT engine, and generating proofs.

Author:

    Leonardo de Moura (leonardo) 2008-02-18.

Revision History:

--*/
#ifndef SMT_JUSTIFICATION_H_
#define SMT_JUSTIFICATION_H_

#include"ast.h"
#include"smt_types.h"
#include"smt_literal.h"
#include"smt_eq_justification.h"

namespace smt {
    
    class conflict_resolution;

    typedef ptr_vector<justification> justification_vector;

    /**
       \brief Pseudo-proof objects. They are mainly used to track dependencies.
       When proof generation is enabled, they are also used to produce proofs.
       
       Justification objects are allocated using a stack based policy.
       Actually, there is one exception: justification of lemmas. 
       Lemmas created at scope level n may remain alive even after scope level n is backtracked.
       Lemmas are deleted by a GC that runs from time to time. So, a justification attached
       to a lemma will may remain alive after scope level n is backtracked.
       
       So, I allow justification objects to be allocated in regions and
       in the regular heap. The method in_region() should return true if the object is
       allocated in a region. 
    */
    class justification {
        unsigned m_mark:1;
        unsigned m_in_region:1; // true if the object was allocated in a region.
    public:
        justification(bool in_region = true):m_mark(false), m_in_region(in_region) {}
        virtual ~justification() {}

        /**
           \brief This method should return true if the method del_eh needs to be invoked 
           to free resources.
        */
        virtual bool has_del_eh() const {
            return false; 
        }

        /**
           \brief Free the resources allocated by this object.
        */
        virtual void del_eh(ast_manager & m) {
        }

        /**
           \brief Mark the antecedents the justification object.
           The antecedents are marked using the mark methods of the 
           conflict_resolution object.
        */
        virtual void get_antecedents(conflict_resolution & cr){
        }

        /**
           \brief Return the id of the theory that produced the proof object.
        */
        virtual theory_id get_from_theory() const {
            return null_theory_id;
        }

        void set_mark() { SASSERT(!m_mark); m_mark = true; }

        void unset_mark() { SASSERT(m_mark); m_mark = false; }

        bool is_marked() const { return m_mark; }
        
        unsigned hash() const { return get_ptr_hash(this); }

        virtual proof * mk_proof(conflict_resolution & cr) = 0;

        bool in_region() const { return m_in_region; }

        virtual char const * get_name() const { return "unknown"; }
        
        virtual void display_debug_info(conflict_resolution & cr, std::ostream & out) { /* do nothing */ }
    };

    class justification_proof_wrapper : public justification {
        proof * m_proof;
    public:
        justification_proof_wrapper(context & ctx, proof * pr, bool in_region = true);

        virtual bool has_del_eh() const {
            return true;
        }
        
        virtual void del_eh(ast_manager & m);
        
        virtual proof * mk_proof(conflict_resolution & cr);
        
        virtual char const * get_name() const { return "proof-wrapper"; }
    };

    class unit_resolution_justification : public justification {
        justification * m_antecedent;
        unsigned        m_num_literals;
        literal *       m_literals;
    public:
        unit_resolution_justification(region & r, justification * js, unsigned num_lits, literal const * lits);

        unit_resolution_justification(justification * js, unsigned num_lits, literal const * lits);

        ~unit_resolution_justification();

        virtual bool has_del_eh() const {
            return !in_region() && m_antecedent && m_antecedent->has_del_eh();
        }
        
        virtual void del_eh(ast_manager & m) {
            if (!in_region() && m_antecedent) m_antecedent->del_eh(m); 
        }

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "unit-resolution"; }
    };

    class eq_conflict_justification : public justification {
        enode *          m_node1;
        enode *          m_node2;
        eq_justification m_js;
    public:
        eq_conflict_justification(enode * n1, enode * n2, eq_justification js):
            m_node1(n1),
            m_node2(n2),
            m_js(js) {
        }

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "eq-conflict"; }
    };
    
    /**
       \brief Justification for m_node = root
    */
    class eq_root_propagation_justification : public justification {
        enode *         m_node;
    public:
        eq_root_propagation_justification(enode * n):m_node(n) {
        }

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "eq-root"; }
    };        

    /**
       \brief Justification for m_node1 = m_node2
    */
    class eq_propagation_justification : public justification {
        enode *         m_node1;
        enode *         m_node2;
    public:
        eq_propagation_justification(enode * n1, enode * n2):m_node1(n1), m_node2(n2) {
        }

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "eq-propagation"; }
    };        

    /**
       \brief Justification for p(x) <=> p(y), p(x)  ===>  p(y)
    */
    class mp_iff_justification : public justification {
        enode *         m_node1;  // p(x)
        enode *         m_node2;  // p(y)
    public:
        mp_iff_justification(enode * n1, enode * n2):m_node1(n1), m_node2(n2) {
        }

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "mp-iff"; }
    };

    /**
       \brief Abstract class for justifications that contains set of literals.
    */
    class simple_justification : public justification {
    protected:
        unsigned        m_num_literals;
        literal *       m_literals;
        
        bool antecedent2proof(conflict_resolution & cr, ptr_buffer<proof> & result);

    public:
        simple_justification(region & r, unsigned num_lits, literal const * lits);

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr) = 0;

        virtual char const * get_name() const { return "simple"; }

    };

    class simple_theory_justification : public simple_justification {
    protected:
        family_id      m_th_id;
        vector<parameter> m_params;
    public:
        simple_theory_justification(
            family_id fid, region & r, 
            unsigned num_lits, literal const * lits,
            unsigned num_params, parameter* params):
            simple_justification(r, num_lits, lits),
            m_th_id(fid), m_params(num_params, params) {}
        virtual ~simple_theory_justification() {}

        virtual bool has_del_eh() const { return !m_params.empty(); }

        virtual void del_eh(ast_manager & m) { m_params.reset(); }       

        virtual theory_id get_from_theory() const { return m_th_id; }
 
    };

    class theory_axiom_justification : public simple_theory_justification {
    public:

        theory_axiom_justification(family_id fid, region & r,                                    
                                   unsigned num_lits, literal const * lits, 
                                   unsigned num_params = 0, parameter* params = 0):
            simple_theory_justification(fid, r, num_lits, lits, num_params, params)  {}
        
        virtual void get_antecedents(conflict_resolution & cr) {}

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "theory-axiom"; }
    };

    class theory_propagation_justification : public simple_theory_justification {
        literal        m_consequent;
    public:
        theory_propagation_justification(family_id fid, region & r, unsigned num_lits, literal const * lits, literal consequent, 
                                         unsigned num_params = 0, parameter* params = 0):
            simple_theory_justification(fid, r, num_lits, lits, num_params, params), m_consequent(consequent) {}

        virtual proof * mk_proof(conflict_resolution & cr);


        virtual char const * get_name() const { return "theory-propagation"; }
        
    };
     
    class theory_conflict_justification : public simple_theory_justification {
    public:
        theory_conflict_justification(family_id fid, region & r, unsigned num_lits, literal const * lits, 
                                      unsigned num_params = 0, parameter* params = 0):
            simple_theory_justification(fid, r, num_lits, lits, num_params, params) {}

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "theory-conflict"; }
    };

    /**
       \brief Abstract class for justifications that contains set of literals and equalities.
    */
    class ext_simple_justification : public simple_justification {
    protected:
        unsigned        m_num_eqs;
        enode_pair *    m_eqs;
        
        bool antecedent2proof(conflict_resolution & cr, ptr_buffer<proof> & result);

    public:
        ext_simple_justification(region & r, unsigned num_lits, literal const * lits, 
                                 unsigned num_eqs, enode_pair const * eqs);

        virtual void get_antecedents(conflict_resolution & cr);

        virtual proof * mk_proof(conflict_resolution & cr) = 0;

        virtual char const * get_name() const { return "ext-simple"; }
    };

    /**
       \brief Abstract class for justifications that contains set of literals and equalities.
    */
    class ext_theory_simple_justification : public ext_simple_justification {
    protected:
        family_id m_th_id;
        vector<parameter> m_params;

    public:
        ext_theory_simple_justification(family_id fid, region & r, unsigned num_lits, literal const * lits, 
                                        unsigned num_eqs, enode_pair const * eqs, 
                                        unsigned num_params = 0, parameter* params = 0):
            ext_simple_justification(r, num_lits, lits, num_eqs, eqs), m_th_id(fid), m_params(num_params, params) {}
            
        virtual ~ext_theory_simple_justification() {}

        virtual bool has_del_eh() const { return !m_params.empty(); }

        virtual void del_eh(ast_manager & m) { m_params.reset(); }       

        virtual theory_id get_from_theory() const { return m_th_id; }
    };

    class ext_theory_propagation_justification : public ext_theory_simple_justification {
        literal        m_consequent;
    public:
        ext_theory_propagation_justification(family_id fid, region & r, 
                                             unsigned num_lits, literal const * lits, 
                                             unsigned num_eqs, enode_pair const * eqs,
                                             literal consequent,
                                             unsigned num_params = 0, parameter* params = 0):
            ext_theory_simple_justification(fid, r, num_lits, lits, num_eqs, eqs, num_params, params), 
            m_consequent(consequent) {}

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "ext-theory-propagation"; }
    };

    class ext_theory_conflict_justification : public ext_theory_simple_justification {
    public:
        ext_theory_conflict_justification(family_id fid, region & r, unsigned num_lits, literal const * lits, 
                                          unsigned num_eqs, enode_pair const * eqs,
                                          unsigned num_params = 0, parameter* params = 0):
            ext_theory_simple_justification(fid, r, num_lits, lits, num_eqs, eqs, num_params, params) {}

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "ext-theory-conflict"; }
    };

    class ext_theory_eq_propagation_justification : public ext_theory_simple_justification {
        enode *        m_lhs;
        enode *        m_rhs;
    public:
        ext_theory_eq_propagation_justification(
            family_id fid, region & r, 
            unsigned num_lits, literal const * lits, 
            unsigned num_eqs, enode_pair const * eqs,
            enode * lhs, enode * rhs,
            unsigned num_params = 0, parameter* params = 0):
            ext_theory_simple_justification(fid, r, num_lits, lits, num_eqs, eqs, num_params, params), m_lhs(lhs), m_rhs(rhs) {}

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "ext-theory-eq-propagation"; }
    };  

    /**
       \brief A theory lemma is similar to a theory axiom, but it is attached to a CLS_AUX_LEMMA clause instead of CLS_AUX.
       So, it cannot be stored in the heap, and it is unsafe to store literals, since it may be deleted during backtracking.
       Instead, they store a set of pairs (sign, expr). This pair is represented as a tagged pointer.
    */
    class theory_lemma_justification : public justification {
        family_id    m_th_id;
        vector<parameter> m_params;
        unsigned     m_num_literals;
        expr **      m_literals;
        
    public:
        theory_lemma_justification(family_id fid, context & ctx, unsigned num_lits, literal const * lits, 
                                   unsigned num_params = 0, parameter* params = 0);

        virtual ~theory_lemma_justification();

        virtual bool has_del_eh() const {
            return true;
        }
        
        virtual void del_eh(ast_manager & m);
        
        virtual void get_antecedents(conflict_resolution & cr) {}

        virtual proof * mk_proof(conflict_resolution & cr);

        virtual char const * get_name() const { return "theory-lemma"; }
    };
      
};

#endif /* SMT_JUSTIFICATION_H_ */

