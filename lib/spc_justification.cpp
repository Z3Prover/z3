/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_justification.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#include"spc_justification.h"
#include"spc_clause.h"
#include"marker.h"

namespace spc {

    void get_justification_stat(justification * p, justification_stat & stat) {
        // Remark: justification objects that are not associated
        // with clauses may be shared. That is, they may be parent of
        // several different justification objects.
        marker<justification> m;
        ptr_buffer<justification> todo;
        todo.push_back(p);
        while (!todo.empty()) {
            justification * p = todo.back();
            todo.pop_back();
            if (!m.is_marked(p)) {
                m.mark(p);
                clause * cls = p->get_clause();
                if (cls) {
                    if (cls->get_proof_depth() > stat.m_proof_depth)
                        stat.m_proof_depth = cls->get_proof_depth();
                    if (cls->get_scope_lvl() > stat.m_max_scope_lvl)
                        stat.m_max_scope_lvl = cls->get_scope_lvl();
                    stat.m_parent_clauses.push_back(cls);
                }
                else {
                    p->get_parents(todo);
                }
            }
        }
    }

    void justification::display(std::ostream & out) {
        out << "[" << get_rule_id();
        ptr_buffer<justification> ps;
        get_parents(ps);
        unsigned sz = ps.size();
        for (unsigned i = 0; i < sz; i++) {
            out << " ";
            justification * js = ps[i];
            clause * cls = js->get_clause();
            if (cls)
                out << "#" << cls->get_id();
            else
                js->display(out);
        }
        out << "]";
    }

    justification * justification_proof_wrapper::mk(proof * p, ast_manager & m) {
        void * mem = m.get_allocator().allocate(sizeof(justification_proof_wrapper));
        return new (mem) justification_proof_wrapper(p, m);
    }

    proof * justification_proof_wrapper::get_proof() const { 
        return m_proof; 
    }

    unsigned justification_proof_wrapper::del_eh(ast_manager & m) { 
        m.dec_ref(m_proof); 
        return sizeof(justification_proof_wrapper);
    }

    void dec_ref(justification * p, ast_manager & m) {
        if (p->dec_ref()) {
            ptr_buffer<justification> to_delete;
            ptr_buffer<justification> parents;
            to_delete.push_back(p);
            while (!to_delete.empty()) {
                justification * p = to_delete.back();
                to_delete.pop_back();
                SASSERT(p->get_ref_count() == 0);
                parents.reset();
                p->get_parents(parents);
                ptr_buffer<justification>::iterator it  = parents.begin();
                ptr_buffer<justification>::iterator end = parents.end();
                for (; it != end; ++it) {
                    justification * parent = *it;
                    if (parent->dec_ref())
                        to_delete.push_back(parent);
                }
                unsigned sz = p->del_eh(m);
                p->~justification();
                m.get_allocator().deallocate(sz, p);
            }
        }
    }

    /**
       \brief Return a proof for a new clause formed by the literals lits[0] ... lits[num_lits - 1].
       This clause was produced using a main clause C, where the proof of C is \c main_pr,
       and the auxiliary proofs auxs[0] ... aux[num_auxs-1].
       
       \remark If fine_grain_proofs() is false, then 0 is returned.
    */
    proof * mk_proof(ast_manager & m, family_id spc_fid, spc_op_kind pid, unsigned num_lits, literal * lits, proof * main_pr, 
                     unsigned num_auxs, proof * const * auxs) {
        if (m.fine_grain_proofs()) {
            expr * new_fact_body = mk_or(m, num_lits, lits);
            
            SASSERT(main_pr);
            SASSERT(m.has_fact(main_pr));
            expr * fact     = m.get_fact(main_pr);
            expr * new_fact = 0;
            if (is_quantifier(fact))
                new_fact = m.update_quantifier(to_quantifier(fact), new_fact_body);
            else 
                new_fact = new_fact_body;

            ptr_buffer<expr> args;
            args.push_back(main_pr);
            args.append(num_auxs, (expr**) auxs);
            args.push_back(new_fact);
            
            return m.mk_app(spc_fid, pid, args.size(), args.c_ptr());
        }
        return 0;
    }

    justification * rewrite_justification::mk(ast_manager & m, justification * head, 
                                              unsigned num_demodulators, justification * const * demodulators, proof * pr) {
        void * mem = m.get_allocator().allocate(get_obj_size(num_demodulators, m.fine_grain_proofs()));
        return new (mem) rewrite_justification(m, head, num_demodulators, demodulators, pr);
    }

    rewrite_justification::rewrite_justification(ast_manager & m, justification * head, 
                                                 unsigned num_demodulators, justification * const * demodulators, proof * pr):
        m_num_demodulators(num_demodulators) {
        SASSERT(m.fine_grain_proofs() == (pr != 0));
        m_fields[0] = head;
        head->inc_ref();
        for (unsigned i = 0; i < num_demodulators; i++) {
            m_fields[i+1] = demodulators[i];
            demodulators[i]->inc_ref();
        }
        if (m.fine_grain_proofs()) {
            SASSERT(pr);
            m_fields[num_demodulators+1] = pr;
            m.inc_ref(pr);
        }
    }
            
    void rewrite_justification::get_parents(ptr_buffer<justification> & parents) {
        unsigned num_parents = m_num_demodulators+1;
        for (unsigned i = 0; i < num_parents; i++)
            parents.push_back(reinterpret_cast<justification*>(m_fields[i]));
    }

    proof * rewrite_justification::get_proof() const {
        return reinterpret_cast<proof*>(m_fields[m_num_demodulators+1]);
    }

    unsigned rewrite_justification::del_eh(ast_manager & m) {
        if (m.fine_grain_proofs()) {
            m.dec_ref(reinterpret_cast<proof*>(m_fields[m_num_demodulators+1]));
            return get_obj_size(m_num_demodulators, true);
        }
        return get_obj_size(m_num_demodulators, false);
    }

    proof * mk_rewrite_proof(ast_manager & m, family_id spc_fid, unsigned num_lits, literal * lits, proof * main_pr, 
                             unsigned num_auxs, proof * const * auxs) {
        return mk_proof(m, spc_fid, PR_SPC_REWRITE, num_lits, lits, main_pr, num_auxs, auxs);
    }
};
