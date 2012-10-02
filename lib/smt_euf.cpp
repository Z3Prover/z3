/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_euf.cpp

Abstract:

    Equality and uninterpreted functions

Author:

    Leonardo de Moura (leonardo) 2012-02-14.

Revision History:

--*/
#include"smt_euf.h"
#include"smt_context.h"
#include"ast_smt2_pp.h"

namespace smt {

    struct euf_manager::imp {
        context &                   m_context;
        ast_manager &               m_manager;
        region &                    m_region;
        expr_ref_vector             m_e_internalized_stack; // stack of the expressions already internalized as enodes. 
        ptr_vector<enode>           m_app2enode;    // app -> enode
        ptr_vector<enode>           m_enodes;
        vector<enode_vector>        m_decl2enodes;  // decl -> enode (for decls with arity > 0)
        cg_table                    m_cg_table; 
        dyn_ack_manager             m_dyn_ack_manager;
        struct new_eq {
            enode *                 m_lhs;
            enode *                 m_rhs;
            eq_justification        m_justification;
            new_eq() {}
            new_eq(enode * lhs, enode * rhs, eq_justification const & js):
                m_lhs(lhs), m_rhs(rhs), m_justification(js) {}
        };
        svector<new_eq>             m_eq_propagation_queue;
        struct new_th_eq {
            theory_id  m_th_id;
            theory_var m_lhs;
            theory_var m_rhs;
            new_th_eq():m_th_id(null_theory_id), m_lhs(null_theory_var), m_rhs(null_theory_var) {}
            new_th_eq(theory_id id, theory_var l, theory_var r):m_th_id(id), m_lhs(l), m_rhs(r) {}
        };
        svector<new_th_eq>          m_th_eq_propagation_queue;
        svector<new_th_eq>          m_th_diseq_propagation_queue;
        enode *                     m_is_diseq_tmp; // auxiliary enode used to find congruent equality atoms.
        tmp_enode                   m_tmp_enode;
        ptr_vector<almost_cg_table> m_almost_cg_tables; // temporary field for is_ext_diseq
        obj_map<expr, unsigned>     m_cached_generation;
        obj_hashtable<expr>         m_cache_generation_visited;
        friend class mk_enode_trail;
        class mk_enode_trail : public trail<context> {
            imp & m_owner;
        public:
            mk_enode_trail(imp & o):m_owner(o) {}
            virtual void undo(context & ctx) { m_owner.undo_mk_enode(); }
        };
        mk_enode_trail              m_mk_enode_trail;
        volatile bool               m_cancel_flag;

        // Statistics
        unsigned                    m_num_mk_enode;
        unsigned                    m_num_del_enode;

        void push_eq(enode * lhs, enode * rhs, eq_justification const & js) {
            SASSERT(lhs != rhs);
            m_eq_propagation_queue.push_back(new_eq(lhs, rhs, js));
        }

        void push_new_congruence(enode * n1, enode * n2, bool used_commutativity) {
            SASSERT(n1->m_cg == n2);
            push_eq(n1, n2, eq_justification::mk_cg(used_commutativity));
        }

        bool e_internalized(expr const * n) const {
            return m_app2enode.get(n->get_id(), 0) != 0;
        }

        void set_app2enode(expr const * n, enode * e) {
            m_app2enode.setx(n->get_id(), e, 0);
        }

        enode * mk_enode(app * n, bool suppress_args, bool merge_tf, bool cgc_enabled, unsigned generation) {
            TRACE("mk_enode_detail", 
                  tout << mk_ismt2_pp(n, m_manager) << "\n";
                  tout <<"suppress_args: " << suppress_args << ", merge_tf: " << merge_tf << ", cgc_enabled: " << cgc_enabled << "\n";);
            SASSERT(!e_internalized(n));
            unsigned scope_lvl   = m_context.get_scope_level();
            unsigned id          = n->get_id();
            unsigned _generation = 0;
            if (!m_cached_generation.empty() && m_cached_generation.find(n, _generation)) {
                generation = _generation;
            }
            enode * e            = enode::mk(m_manager, m_region, m_app2enode, n, generation, suppress_args, merge_tf, scope_lvl, cgc_enabled, true);
            TRACE("mk_enode_detail", tout << "e.get_num_args() = " << e->get_num_args() << "\n";);
            if (n->get_num_args() == 0 && m_manager.is_value(n))
                e->mark_as_interpreted();
            TRACE("mk_var_bug", tout << "mk_enode: " << id << "\n";);
            TRACE("generation", tout << "mk_enode: " << id << " " << generation << "\n";);
            set_app2enode(n, e);
            m_e_internalized_stack.push_back(n);
            m_context.push_trail_ptr(&m_mk_enode_trail);
            m_enodes.push_back(e);
            if (e->get_num_args() > 0) {
                if (e->is_true_eq()) {
                    /* 
                        bool_var v = enode2bool_var(e);
                        assign(literal(v), mk_justification(eq_propagation_justification(e->get_arg(0), e->get_arg(1))));
                        e->m_cg    = e;
                    */
                }
                else {
                    if (cgc_enabled) {
                        enode_bool_pair pair = m_cg_table.insert(e);
                        enode * e_prime      = pair.first;
                        if (e != e_prime) {
                            e->m_cg = e_prime;
                            bool used_commutativity = pair.second;
                            push_new_congruence(e, e_prime, used_commutativity);
                        }
                        else {
                            e->m_cg = e;
                        }
                    }
                    else {
                        e->m_cg = e;
                    }
                }
                if (!e->is_eq()) {
                    unsigned decl_id = n->get_decl()->get_decl_id();
                    if (decl_id >= m_decl2enodes.size())
                        m_decl2enodes.resize(decl_id+1);
                    m_decl2enodes[decl_id].push_back(e);
                }
            }
            SASSERT(e_internalized(n));
            m_num_mk_enode++;
            
            // #ifndef SMTCOMP
            // if (m_params.m_trace_stream != NULL)
            //    *m_params.m_trace_stream << "[attach-enode] #" << n->get_id() << " " << m_generation << "\n";        
            // #endif

            return e;
        }

        void undo_mk_enode() {
            SASSERT(!m_e_internalized_stack.empty());
            m_num_del_enode++;
            expr * n              = m_e_internalized_stack.back();
            TRACE("undo_mk_enode", tout << "undo_enode: #" << n->get_id() << "\n" << mk_ismt2_pp(n, m_manager) << "\n";);
            TRACE("mk_var_bug", tout << "undo_mk_enode: " << n->get_id() << "\n";);
            unsigned n_id         = n->get_id();
            SASSERT(is_app(n));
            enode * e             = m_app2enode[n_id];
            m_app2enode[n_id]     = 0;
            if (e->is_cgr() && !e->is_true_eq() && e->is_cgc_enabled()) {
                SASSERT(m_cg_table.contains_ptr(e));
                m_cg_table.erase(e);
            }
            if (e->get_num_args() > 0 && !e->is_eq()) {
                unsigned decl_id = to_app(n)->get_decl()->get_decl_id();
                SASSERT(decl_id < m_decl2enodes.size());
                SASSERT(m_decl2enodes[decl_id].back() == e);
                m_decl2enodes[decl_id].pop_back();
            }
            e->del_eh(m_manager);
            SASSERT(m_e_internalized_stack.size() == m_enodes.size());
            m_enodes.pop_back();
            m_e_internalized_stack.pop_back();
        }

    };

    euf_manager::euf_manager(context & ctx) {
    }
    
    euf_manager::~euf_manager() {
    }
};
