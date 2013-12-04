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

    class mk_karr_invariants : public rule_transformer::plugin {

        class add_invariant_model_converter;
        
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        context         m_inner_ctx;
        arith_util      a;
        obj_map<func_decl, expr*>      m_fun2inv;
        ast_ref_vector m_pinned;
        volatile bool  m_cancel;

        void get_invariants(rule_set const& src);

        void update_body(rule_set& result, rule& r);
        rule_set* update_rules(rule_set const& src);
    public:
        mk_karr_invariants(context & ctx, unsigned priority);

        virtual ~mk_karr_invariants();

        virtual void cancel();
        
        rule_set * operator()(rule_set const & source);

    };


};

#endif /* _DL_MK_KARR_INVARIANTS_H_ */

