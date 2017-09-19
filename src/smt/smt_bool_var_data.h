/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_bool_var_data.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-25.

Revision History:

--*/
#ifndef SMT_BOOL_VAR_DATA_H_
#define SMT_BOOL_VAR_DATA_H_

#include "smt/smt_b_justification.h"

namespace smt {

    struct bool_var_data {
    private:
        b_justification         m_justification;
    public:
        unsigned                m_scope_lvl:24;    //!< scope level of when the variable was assigned.
        unsigned                m_mark:1;
        unsigned                m_assumption:1;
        unsigned                m_phase_available:1;
        unsigned                m_phase:1;
    private:
        unsigned                m_eq:1;
        unsigned                m_true_first:1;   //!< If True, when case splitting try the true phase first. Otherwise, you default phase selection heuristic.
        unsigned                m_enode:1;        //!< has enode associated with it.
        unsigned                m_quantifier:1;   //!< true if bool var is attached to a quantifier
        unsigned                m_iscope_lvl:23;  //!< scope level of when the variable was internalized.
        unsigned                m_atom:1;         //!< logical or of m_eq, m_enode, m_quantifier, and m_notify_theory != 0
        unsigned                m_notify_theory:8;

        void update_atom_flag() {
            m_atom = m_eq || m_notify_theory != 0 || m_quantifier || m_enode;
        }
    public:
        
        unsigned get_intern_level() const { return m_iscope_lvl; }

        b_justification justification() const { return m_justification; }

        void set_axiom() { m_justification = b_justification::mk_axiom(); }

        void set_null_justification() { m_justification = null_b_justification; }

        void set_justification(b_justification const& j) { m_justification = j; }
        
        bool is_atom() const { return m_atom; }

        theory_id get_theory() const {
            return m_notify_theory == 0 ? null_theory_id : static_cast<theory_id>(m_notify_theory);
        }

        bool is_theory_atom() const { return m_notify_theory != 0; }

        void set_notify_theory(theory_id thid) {
            SASSERT(thid > 0 && thid <= 255);
            m_notify_theory = thid;
            m_atom          = true;
        }

        void reset_notify_theory() {
            m_notify_theory = 0;
            update_atom_flag();
        }

        bool is_enode() const { return m_enode; }

        void set_enode_flag() { 
            m_enode = true; 
            m_atom  = true;
        }

        void reset_enode_flag() { 
            m_enode = false; 
            update_atom_flag();
        }

        bool is_quantifier() const { return m_quantifier; }

        void set_quantifier_flag() {
            m_quantifier = true;
            m_atom  = true;
        }
        
        bool is_eq() const { return m_eq; }

        void set_eq_flag() {
            m_eq   = true;
            m_atom = true;
        }

        void reset_eq_flag() {
            m_eq   = false;
            update_atom_flag();
        }

        bool try_true_first() const { return m_true_first; }

        void set_true_first_flag() {
            m_true_first = true;
        }

        void reset_true_first_flag() {
            m_true_first = false;
        }

        void init(unsigned iscope_lvl) {
            m_justification   = null_b_justification;
            m_scope_lvl       = 0;
            m_mark            = false;
            m_assumption      = false;
            m_phase_available = false;
            m_phase           = false;
            m_iscope_lvl      = iscope_lvl;
            m_eq              = false;
            m_true_first      = false;
            m_notify_theory   = 0;
            m_enode           = false;
            m_quantifier      = false;
            m_atom            = false;
        }
    };
};

#endif /* SMT_BOOL_VAR_DATA_H_ */

