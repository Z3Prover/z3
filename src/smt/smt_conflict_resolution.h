/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_conflict_resolution.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-25.

Revision History:

--*/
#ifndef SMT_CONFLICT_RESOLUTION_H_
#define SMT_CONFLICT_RESOLUTION_H_

#include"smt_literal.h"
#include"smt_bool_var_data.h"
#include"smt_justification.h"
#include"smt_enode.h"
#include"dyn_ack.h"
#include"obj_pair_hashtable.h"
#include"smt_params.h"
#include"obj_pair_hashtable.h"
#include"map.h"
#include"watch_list.h"
#include"obj_pair_set.h"

typedef approx_set_tpl<unsigned, u2u, unsigned> level_approx_set;

namespace smt {

    typedef std::pair<enode *, enode *> enode_pair;

    /**
       \brief Base conflict resolution class.
       It implements the FUIP strategy.
    */
    class conflict_resolution {
    protected:
        typedef obj_pair_set<enode, enode> enode_pair_set;

        ast_manager &                  m_manager;
        smt_params const &       m_params;
        context &                      m_ctx;
        dyn_ack_manager &              m_dyn_ack_manager;
        literal_vector const &         m_assigned_literals;
        
        unsigned                       m_conflict_lvl;
        
        literal_vector                 m_lemma;
        expr_ref_vector                m_lemma_atoms;
        unsigned                       m_new_scope_lvl;
        unsigned                       m_lemma_iscope_lvl;
        
        justification_vector           m_todo_js;
        unsigned                       m_todo_js_qhead;
        svector<enode_pair>            m_todo_eqs;
        enode_pair_set                 m_already_processed_eqs;
        
        literal_vector *               m_antecedents;

        // Reference for watch lists are used to implement subsumption resolution
        vector<watch_list> &           m_watches;     //!< per literal

        // ---------------------------
        //
        // Proof generation
        //
        // ---------------------------
        typedef obj_map<justification, proof *>                                js2proof;
        typedef obj_pair_map<enode, enode, proof *>                            eq2proof;
        typedef map<literal, proof *, obj_hash<literal>, default_eq<literal> > lit2proof;

        /**
           \brief Element for the todo-list used to build proofs.
        */
        struct tp_elem {
            enum {
                JUSTIFICATION,
                EQUALITY,
                LITERAL
            }                          m_kind;                          
            union {
                justification *        m_js;
                unsigned               m_lidx;
                struct {
                    enode *            m_lhs;
                    enode *            m_rhs;
                };
            };
            tp_elem(literal l):m_kind(LITERAL), m_lidx(l.index()) {}
            tp_elem(enode * lhs, enode * rhs):m_kind(EQUALITY), m_lhs(lhs), m_rhs(rhs) {}
            tp_elem(justification * js):m_kind(JUSTIFICATION), m_js(js) {}
        };

        svector<tp_elem>               m_todo_pr;
        js2proof                       m_js2proof;
        eq2proof                       m_eq2proof;
        lit2proof                      m_lit2proof;
        proof_ref_vector               m_new_proofs;
        proof_ref                      m_lemma_proof;

        literal_vector                 m_assumptions;

    public:
        void setup() {
        }

        void mark_justification(justification * js) {
            if (!js->is_marked()) {
                js->set_mark();
                m_todo_js.push_back(js);
            }
        }

        void mark_eq(enode * n1, enode * n2) {
            if (n1 != n2) {
                if (n1->get_owner_id() > n2->get_owner_id())
                    std::swap(n1, n2);
                enode_pair p(n1, n2);
                if (m_already_processed_eqs.insert_if_not_there(p)) {
                    TRACE("conflict_detail_verbose", tout << "marking eq #" << p.first->get_owner_id() << " = #" << 
                          p.second->get_owner_id() << "\n";);
                    m_todo_eqs.push_back(p);
                    SASSERT(m_already_processed_eqs.contains(p));
                }
            }
        }

        void mark_literal(literal l) {
            SASSERT(m_antecedents);
            m_antecedents->push_back(l);
        }

        void mark_justified_eq(enode * lhs, enode * rhs, eq_justification js) {
            eq_justification2literals(lhs, rhs, js);
        }

        proof * norm_eq_proof(enode * n1, enode * n2, proof * pr);

        proof * get_proof(enode_pair const & p);
        proof * get_proof(enode * n1, enode * n2);
        proof * get_proof(enode * n1, enode * n2, eq_justification js);
        proof * get_proof(literal l);
        proof * get_proof(literal l, b_justification js);
        proof * get_proof(justification * js);

        bool visit_b_justification(literal l, b_justification js);
        void mk_proof(literal l, b_justification js);
        bool visit_trans_proof(enode * lhs, enode * rhs);
        bool visit_eq_justications(enode * lhs, enode * rhs);
        void mk_proof(enode * lhs, enode * rhs, ptr_buffer<proof> & result);
        void mk_proof(enode * lhs, enode * rhs);
        void init_mk_proof();
        void mk_conflict_proof(b_justification conflict, literal not_l);

    protected:
        template<bool Set>
        void mark_enodes_in_trans(enode * n);
        enode * find_common_ancestor(enode * n1, enode * n2);
        void eq_justification2literals(enode * lhs, enode * rhs, eq_justification js);
        void eq_branch2literals(enode * n1, enode * n2);
        void eq2literals(enode * n1, enode * n2);
        void justification2literals_core(justification * js, literal_vector & result) ;
        void process_justifications();
        void unmark_justifications(unsigned old_js_qhead);

        literal_vector m_tmp_literal_vector;

        unsigned get_justification_max_lvl(justification * js);
        unsigned get_max_lvl(literal consequent, b_justification js);
        unsigned skip_literals_above_conflict_level();
        void process_antecedent(literal antecedent, unsigned & num_marks);
        void process_justification(justification * js, unsigned & num_marks);

        bool_var_vector m_unmark;
        bool_var_vector m_lemma_min_stack;
        level_approx_set m_lvl_set;
        level_approx_set get_lemma_approx_level_set();
        void reset_unmark(unsigned old_size);
        void reset_unmark_and_justifications(unsigned old_size, unsigned old_js_qhead);
        bool process_antecedent_for_minimization(literal antecedent);
        bool process_justification_for_minimization(justification * js);
        bool implied_by_marked(literal lit);
        void minimize_lemma();

        void structural_minimization();

        void process_antecedent_for_unsat_core(literal antecedent);
        void process_justification_for_unsat_core(justification * js);
        void mk_unsat_core(b_justification conflict, literal not_l);

        bool initialize_resolve(b_justification conflict, literal not_l, b_justification & js, literal & consequent);
        void finalize_resolve(b_justification conflict, literal not_l);
      
    public:
        conflict_resolution(ast_manager & m, 
                            context & ctx,
                            dyn_ack_manager & dack_manager,
                            smt_params const & params,
                            literal_vector const & assigned_literals,
                            vector<watch_list> & watches
                            );

        virtual ~conflict_resolution() {}

        virtual bool resolve(b_justification conflict, literal not_l);

        context & get_context() {
            return m_ctx;
        }

        ast_manager & get_manager() {
            return m_manager;
        }
        
        unsigned get_new_scope_lvl() const { 
            return m_new_scope_lvl;
        }

        unsigned get_lemma_intern_lvl() const {
            return m_lemma_iscope_lvl;
        }

        unsigned get_lemma_num_literals() const {
            return m_lemma.size();
        }

        literal * get_lemma_literals() {
            return m_lemma.c_ptr();
        }

        expr * * get_lemma_atoms() {
            return m_lemma_atoms.c_ptr();
        }

        void release_lemma_atoms() {
            m_lemma_atoms.reset();
        }
        
        proof * get_lemma_proof() {
            return m_lemma_proof;
        }

        literal_vector::const_iterator begin_unsat_core() const {
            return m_assumptions.begin();
        }

        literal_vector::const_iterator end_unsat_core() const {
            return m_assumptions.end();
        }

        void justification2literals(justification * js, literal_vector & result);

        void eq2literals(enode * n1, enode * n2, literal_vector & result);

    };

    inline void mark_literals(conflict_resolution & cr, unsigned sz, literal const * ls) {
        for (unsigned i = 0; i < sz; i++)
            cr.mark_literal(ls[i]);
    }

    conflict_resolution * mk_conflict_resolution(ast_manager & m, 
                                                 context & ctx,
                                                 dyn_ack_manager & dack_manager,
                                                 smt_params const & params,
                                                 literal_vector const & assigned_literals,  
                                                 vector<watch_list> & watches
                                                 );


};

#endif /* SMT_CONFLICT_RESOLUTION_H_ */

