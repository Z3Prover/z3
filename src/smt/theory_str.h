/*++
Module Name:

    theory_str.h

Abstract:

    String Theory Plugin

Author:

    Murphy Berzish (mtrberzi) 2015-09-03

Revision History:

--*/
#ifndef _THEORY_STR_H_
#define _THEORY_STR_H_

#include"smt_theory.h"
#include"trail.h"
#include"th_rewriter.h"
#include"value_factory.h"
#include"smt_model_generator.h"

namespace smt {

    class str_value_factory : public value_factory {
        // TODO
    };

    class theory_str : public theory {
        // TODO
    protected:
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);

        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);
        virtual theory* mk_fresh(context*) { return alloc(theory_str, get_manager()); }

        virtual void init_search_eh();

        virtual void relevant_eh(app * n);
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void push_scope_eh();

        virtual final_check_status final_check_eh();
    public:
        theory_str(ast_manager& m);
        virtual ~theory_str();
    protected:
        void attach_new_th_var(enode * n);
    };

};

#endif /* _THEORY_STR_H_ */
