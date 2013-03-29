/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_karr_invariants.h

Abstract:

    Extract integer linear invariants.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-08

Revision History:

--*/
#ifndef _DL_MK_KARR_INVARIANTS_H_
#define _DL_MK_KARR_INVARIANTS_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"arith_decl_plugin.h"
#include"hilbert_basis.h"

namespace datalog {

    /**
       \brief Rule transformer that strengthens bodies with invariants.
    */
    class mk_karr_invariants : public rule_transformer::plugin {

        struct matrix {
            vector<vector<rational> > A;
            vector<rational>          b;
            svector<bool>             eq;
            unsigned size() const { return A.size(); }
            void reset() { A.reset(); b.reset(); eq.reset(); }
            matrix& operator=(matrix const& other);
            void append(matrix const& other) { A.append(other.A); b.append(other.b); eq.append(other.eq); }
            void display(std::ostream& out) const;
            static void display_row(
                std::ostream& out, vector<rational> const& row, rational const& b, bool is_eq);
            static void display_ineq(
                std::ostream& out, vector<rational> const& row, rational const& b, bool is_eq);
        };
        class add_invariant_model_converter;

        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        arith_util      a;
        obj_map<func_decl, matrix*> m_constraints;
        obj_map<func_decl, matrix*> m_dual_constraints;
        hilbert_basis   m_hb;

        bool is_linear(expr* e, vector<rational>& row, rational& b, rational const& mul);
        bool is_eq(expr* e, var*& v, rational& n);
        bool get_transition_relation(rule const& r, matrix& M);
        void intersect_matrix(app* p, matrix const& Mp, unsigned num_columns, matrix& M);
        matrix* get_constraints(func_decl* p);   
        matrix& get_dual_constraints(func_decl* p);     
        void dualizeH(matrix& dst, matrix const& src);
        void dualizeI(matrix& dst, matrix const& src);
        void update_body(rule_set& rules, rule& r);

    public:
        mk_karr_invariants(context & ctx, unsigned priority);

        virtual ~mk_karr_invariants();

        virtual void cancel();
        
        rule_set * operator()(rule_set const & source);

    };

};

#endif /* _DL_MK_KARR_INVARIANTS_H_ */

