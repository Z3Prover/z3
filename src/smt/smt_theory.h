/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_theory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#ifndef SMT_THEORY_H_
#define SMT_THEORY_H_

#include "smt/smt_enode.h"
#include "util/obj_hashtable.h"
#include "util/statistics.h"
#include<typeinfo>

namespace smt {
    class model_generator;
    class model_value_proc;

    class theory {
        theory_id       m_id;
        context *       m_context;
        ast_manager *   m_manager;
        enode_vector    m_var2enode;
        unsigned_vector m_var2enode_lim;

        friend class context;
        friend class arith_value;
    protected:
        virtual void init(context * ctx);

        /* ---------------------------------------------------
        
        In the logical context, expressions are 'internalized'. That
        is, the logical context creates auxiliary data-structures
        (e.g., enodes) and attach them to the expressions. The logical
        context does not know the internals of each theory. So, during
        the internalization process, it notifies the theory (plugin)
        whenever it finds an application with a theory function
        symbol.

        A theory variable created at scope level n must be deleted
        when scope level n is backtracked.

        The logical context uses the method is_attached_to_var
        to decide whether an enode is already associated with a theory 
        variable or not.

        ------------------------------------------------------ */

        virtual theory_var mk_var(enode * n) {
            SASSERT(!is_attached_to_var(n));
            theory_var v = m_var2enode.size();
            m_var2enode.push_back(n);
            return v;
        }
        
    public:
        /**
           \brief Return ture if the given enode is attached to a
           variable of the theory.
           
           \remark The result is not equivalent to
           n->get_th_var(get_id()) != null_theory_var
           
           A theory variable v may be in the list of variables of n,
           but it may be inherited from another enode n' during an
           equivalence class merge. That is, get_enode(v) != n.
        */
        bool is_attached_to_var(enode const * n) const {
            theory_var v = n->get_th_var(get_id());
            return v != null_theory_var && get_enode(v) == n;
        }

    protected:
        /**
           \brief Return true if the theory uses default internalization:
           "the internalization of an application internalizes all arguments".
           Theories like arithmetic do not use default internalization.
           For example, in the application (+ a (+ b c)), no enode is created
           for (+ b c).
        */
        virtual bool default_internalizer() const {
            return true;
        }

        /**
           \brief This method is invoked by the logical context when
           atom is being internalized. The theory may return false if it 
           does not want to implement the given predicate symbol.

           After the execution of this method the given atom must be
           associated with a new boolean variable.
        */
        virtual bool internalize_atom(app * atom, bool gate_ctx) = 0;

        /**
           \brief This method is invoked by the logical context
           after the given equality atom is internalized.
        */
        virtual void internalize_eq_eh(app * atom, bool_var v) {
        }
                                    
        /**
           \brief This method is invoked by the logical context when
           the term is being internalized. The theory may return false
           if it does not want to implement the given function symbol.
           
           After the execution of this method the given term must be 
           associated with a new enode.
        */
        virtual bool internalize_term(app * term) = 0;

        /**
           \brief Apply (interpreted) sort constraints on the given enode.
        */
        virtual void apply_sort_cnstr(enode * n, sort * s) {
        }

        /**
           \brief This method is invoked when a truth value is 
           assigned to the given boolean variable.
        */
        virtual void assign_eh(bool_var v, bool is_true) {
        }

        /**
           \brief Equality propagation (v1 = v2): Core -> Theory
        */
        virtual void new_eq_eh(theory_var v1, theory_var v2) = 0;

        /**
           \brief Return true if the theory does something with the
           disequalities implied by the core.
        */
        virtual bool use_diseqs() const { 
            return true; 
        }

        /**
           \brief Disequality propagation (v1 /= v2): Core -> Theory
        */
        virtual void new_diseq_eh(theory_var v1, theory_var v2) = 0;

        /**
           \brief This method is invoked when the theory application n
           is marked as relevant.
         */
        virtual void relevant_eh(app * n) {
        }
        
        /**
           \brief This method is invoked when a new backtracking point
           is created.
        */
        virtual void push_scope_eh();

        /**
           \brief This method is invoked during backtracking.
        */
        virtual void pop_scope_eh(unsigned num_scopes);

        /**
           \brief This method is invoked when the logical context is being
           restarted.
        */
        virtual void restart_eh() {
        }

        /**
           \brief This method is called by smt_context before the search starts
           to get any extra assumptions the theory wants to use.
           (See theory_str for an example)
        */
        virtual void add_theory_assumptions(expr_ref_vector & assumptions) {
        }

        /**
           \brief This method is called from the smt_context when an unsat core is generated.
           The theory may change the answer to UNKNOWN by returning l_undef from this method.
        */
        virtual lbool validate_unsat_core(expr_ref_vector & unsat_core) {
            return l_false;
        }

        /**
           \brief This method is invoked before the search starts.
        */
        virtual void init_search_eh() {
        }

        /**
           \brief This method is invoked when the logical context assigned
           a truth value to all boolean variables and no inconsistency was 
           detected.
        */
        virtual final_check_status final_check_eh() {
            return FC_DONE;
        }

        /**
           \brief Parametric theories (e.g. Arrays) should implement this method.
           See example in context::is_shared
        */
        virtual bool is_shared(theory_var v) const {
            return false;
        }
    
        /**
           \brief Return true if the theory has something to propagate
        */
        virtual bool can_propagate() {
            return false;
        }
        
        /**
           \brief This method is invoked to give a theory a chance to perform
           theory propagation.
        */
        virtual void propagate() {
        }
        
        /**
           \brief This method allows a theory to contribute to
           disequality propagation.
        */
        virtual justification * why_is_diseq(theory_var v1, theory_var v2) {
            return nullptr;
        }

        /**
           \brief Just releases memory.
        */
        virtual void flush_eh() {
        }

        /**
           \brief This method is invoked when the logical context is being reset.
        */
        virtual void reset_eh();

        // ----------------------------------------------------
        //
        // Model validation (-vldt flag)
        //
        // ----------------------------------------------------

        virtual bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const {
            return true;
        }

        // ----------------------------------------------------
        //
        // Conflict resolution event handler
        //
        // ----------------------------------------------------
    public:
        /**
           \brief This method is invoked when a theory atom is used
           during conflict resolution. This allows the theory to bump
           the activity of the enodes contained in the given atom.
        */
        virtual void conflict_resolution_eh(app * atom, bool_var v) {
        }


    public:
        theory(family_id fid);
        virtual ~theory();
        
        virtual void setup() {
        }

        theory_id get_id() const {
            return m_id;
        }

        family_id get_family_id() const {
            return m_id;
        }

        context & get_context() const {
            SASSERT(m_context);
            return *m_context;
        }
        
        ast_manager & get_manager() const {
            SASSERT(m_manager);
            return *m_manager;
        }

        enode * get_enode(theory_var v) const {
            SASSERT(v < static_cast<int>(m_var2enode.size()));
            return m_var2enode[v];
        }

        /**
           \brief Return the equivalence class representative 
           of the given theory variable.
        */
        theory_var get_representative(theory_var v) const {
            SASSERT(v != null_theory_var);
            theory_var r = get_enode(v)->get_root()->get_th_var(get_id());
            SASSERT(r != null_theory_var);
            return r;
        }

        /** 
            \brief Return true if the theory variable is the representative
            of its equivalence class.
        */
        bool is_representative(theory_var v) const {
            return get_representative(v) == v;
        }
        
        unsigned get_num_vars() const {
            return m_var2enode.size();
        }

        unsigned get_old_num_vars(unsigned num_scopes) const {
            return m_var2enode_lim[m_var2enode_lim.size() - num_scopes];
        }
        
        virtual void display(std::ostream & out) const = 0;

        virtual void display_var2enode(std::ostream & out) const;
        
        virtual void collect_statistics(::statistics & st) const {
        }
        
        std::ostream& display_app(std::ostream & out, app * n) const;
        
        std::ostream& display_flat_app(std::ostream & out, app * n) const;
        
        std::ostream& display_var_def(std::ostream & out, theory_var v) const { return display_app(out, get_enode(v)->get_owner()); }
        
        std::ostream& display_var_flat_def(std::ostream & out, theory_var v) const { return display_flat_app(out, get_enode(v)->get_owner());  }

        /**
           \brief Assume eqs between variable that are equal with respect to the given table.
           Table is a hashtable indexed by the variable value.
           
           table.contains(v) should be true if there is v' in table such that assignment of
           v is equal to v'.

           This method assumes that class VarValueTable contains the methods:

           - void reset()
           - theory_var insert_if_not_there(theory_var v)
        */
        template<typename VarValueTable>
        bool assume_eqs(VarValueTable & table) {
            TRACE("assume_eqs", tout << "starting...\n";);
            table.reset();
            bool result   = false;
            int num       = get_num_vars();
            for (theory_var v = 0; v < num; v++) {
                enode * n        = get_enode(v);
                theory_var other = null_theory_var;
                TRACE("assume_eqs",
                      tout << "#" << n->get_owner_id() << " is_relevant_and_shared: " << is_relevant_and_shared(n) << "\n";);
                if (n != nullptr && is_relevant_and_shared(n)) {
                    other = table.insert_if_not_there(v);
                    if (other != v) {
                        enode * n2 = get_enode(other);
                        TRACE("assume_eqs", tout << "value(#" << n->get_owner_id() << ") = value(#" << n2->get_owner_id() << ")\n";);
                        if (assume_eq(n, n2)) {
                            TRACE("assume_eqs", tout << "new assumed eq\n";);
                            result = true;
                        }
                    }
                }
            }
            return result;
        }

        /**
           \brief When an eq atom n is created during the search, the default behavior is 
           to make sure that the n->get_arg(0)->get_id() < n->get_arg(1)->get_id().
           This may create some redundant atoms, since some theories/families use different
           convetions in their simplifiers. For example, arithmetic always force a numeral
           to be in the right hand side. So, this method should be redefined if the default
           behavior conflicts with a convention used by the theory/family.
        */
        virtual app * mk_eq_atom(expr * lhs, expr * rhs) {
            if (lhs->get_id() > rhs->get_id())
                std::swap(lhs, rhs);
            return get_manager().mk_eq(lhs, rhs);
        }

        literal mk_eq(expr * a, expr * b, bool gate_ctx);

        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------

        /**
           \brief Return true if theory support model construction
        */
        virtual bool build_models() const { 
            return true;
        }

        virtual void init_model(model_generator & m) {
        }

        virtual void finalize_model(model_generator & m) {
        }
        
        /**
           \brief Return a functor that can build the value (interpretation) for n.
        */
        virtual model_value_proc * mk_value(enode * n, model_generator & mg) {
            return nullptr;
        }

        virtual bool include_func_interp(func_decl* f) {
            return false;
        }

        // -----------------------------------
        //
        // Model checker
        //
        // -----------------------------------

        virtual bool get_value(enode * n, expr_ref & r) {
            return false;
        }

        virtual char const * get_name() const { return "unknown"; }

        // -----------------------------------
        //
        // Return a fresh new instance of the given theory.
        // This function is used to create a fresh context (new_ctx) containing the same theories of the context that owns this theory.
        //
        // We need the parameter new_ctx because of user_smt_theory :-(
        //
        // -----------------------------------
        virtual theory * mk_fresh(context * new_ctx) = 0;

    protected:
        // ----------------------------------------------------
        //
        // Auxiliary methods for assume_eqs
        //
        // smt::context is not defined at this point.
        //
        // ----------------------------------------------------

        bool is_relevant_and_shared(enode * n) const;

        bool assume_eq(enode * n1, enode * n2);
    };
    
};

#endif /* SMT_THEORY_H_ */

