#include "smt/theory_finite_set_lattice_refutation.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"
#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"

namespace smt {
    theory_finite_set_lattice_refutation::theory_finite_set_lattice_refutation(theory_finite_set& th): 
    m(th.m), ctx(th.ctx), th(th), u(m), bs(m), m_assumption(m) {}

    void theory_finite_set_lattice_refutation::add_equality(theory_var v1, theory_var v2){
        expr* arg1 = nullptr, *arg2 = nullptr;
        auto n1 = th.get_enode(v1);
        auto n2 = th.get_enode(v2);
        if(u.is_intersect(n2->get_expr(), arg1, arg2)){
            TRACE(finite_set, tout << "new_eq_eh_intersection: (v1:="<< n1->get_expr()<<") = (v2: intersect("<<arg1<<","<<arg2<<"))");
            if(arg1 == n1->get_expr()){
                // v2 = intersect(v2, v1) ==> v2\subseteq v1
                relations.push_back({arg1,arg2});
                ctx.push_trail(push_back_vector(relations));

            }
            else if(arg2 == n1->get_expr()){
                // v1 = intersect(v2, v1) ==> v1\subseteq v2
                relations.push_back({arg2,arg1});
                ctx.push_trail(push_back_vector(relations));
            }
        }
        else if(u.is_intersect(n1->get_expr(), arg1, arg2)){
            TRACE(finite_set, tout << "new_eq_eh_intersection2: (v2:="<< n2->get_expr()<<") = (v1: intersect("<<arg1<<","<<arg2<<"))");
            if(arg1 == n2->get_expr()){
                // v2 = intersect(v2, v1) ==> v2\subseteq v1
                relations.push_back({arg1,arg2});
                ctx.push_trail(push_back_vector(relations));

            }
            else if(arg2 == n2->get_expr()){
                // v1 = intersect(v2, v1) ==> v1\subseteq v2
                relations.push_back({arg2,arg1});
                ctx.push_trail(push_back_vector(relations));
            }
        }
    };

    void theory_finite_set_lattice_refutation::add_disequality(theory_var v1, theory_var v2){
        auto n1 = th.get_enode(v1);
        auto n2 = th.get_enode(v2);
        TRACE(finite_set, tout << "new_diseq_intersection: (v1:"<< n1->get_expr()<<") = (v2:"<< n2->get_expr() <<")");
    }
}