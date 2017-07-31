/*++

Module Name:

    dl_mk_array_eq_rewrite.h

Abstract:
    Selects a representative for array equivalence classes.

Author:

    Julien Braine

Revision History:

--*/


#include "dl_mk_array_eq_rewrite.h"
#include "dl_context.h"
#include "pattern_inference.h"
#include "dl_context.h"
#include "expr_safe_replace.h"
#include "expr_abstract.h"
#include"fixedpoint_params.hpp"
#include "../spacer/obj_equiv_class.h"

namespace datalog {

  mk_array_eq_rewrite::mk_array_eq_rewrite(
        context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        m_a(m)
  {
  }

  rule_set * mk_array_eq_rewrite::operator()(rule_set const & source)
  {
    src_set = &source;
    rule_set * result = alloc(rule_set, m_ctx);
    result->inherit_predicates(source);
    dst=result;
    unsigned nbrules = source.get_num_rules();
    src_manager = &source.get_rule_manager();
    for(unsigned i =0;i<nbrules;i++)
    {
      rule & r = *source.get_rule(i);
      instantiate_rule(r, *result);
    }
    return result;
  }

  void mk_array_eq_rewrite::instantiate_rule(const rule& r, rule_set & dest)
  {
    //Reset everything
    cnt = src_manager->get_counter().get_max_rule_var(r)+1;


    expr_ref_vector new_tail(m);
    unsigned nb_predicates = r.get_uninterpreted_tail_size();
    unsigned tail_size = r.get_tail_size();
    for(unsigned i=0;i<nb_predicates;i++)
    {
      new_tail.push_back(r.get_tail(i));
    }

    spacer::expr_equiv_class array_eq_classes(m);
    for(unsigned i=nb_predicates;i<tail_size;i++)
    {
      expr* cond = r.get_tail(i);
      expr* e1, *e2;
      if(m.is_eq(cond, e1, e2) && m_a.is_array(get_sort(e1)))
      {
        array_eq_classes.merge(e1, e2);
      }
      else
      {
        new_tail.push_back(cond);
      }
    }

    for(spacer::expr_equiv_class::equiv_iterator c_eq = array_eq_classes.begin();
        c_eq != array_eq_classes.end();++c_eq)
    {
      expr* representative = *(*c_eq).begin();
      for(spacer::expr_equiv_class::iterator it = (*c_eq).begin();
          it!=(*c_eq).end(); ++it)
      {
        if(!is_var(*it))
        {
          representative = *it;
          break;
        }
      }
      for(spacer::expr_equiv_class::iterator it = (*c_eq).begin();
          it!=(*c_eq).end(); ++it)
      {
        for(unsigned i=0;i<new_tail.size();i++)
          new_tail[i] = replace(new_tail[i].get(), representative, *it);
      }
      for(spacer::expr_equiv_class::iterator it = (*c_eq).begin();
          it!=(*c_eq).end(); ++it)
      {
        new_tail.push_back(m.mk_eq(*it, representative));
      }
    }
    params_ref select_over_store;
    select_over_store.set_bool("expand_select_store", true);
    th_rewriter t(m, select_over_store);
    expr_ref_vector res_conjs(m);
    for(unsigned i=0;i<new_tail.size();i++)
    {
      expr_ref tmp(m);
      t(new_tail[i].get(), tmp);
      res_conjs.push_back(tmp);
    }
    proof_ref pr(m);
    src_manager->mk_rule(m.mk_implies(m.mk_and(res_conjs.size(), res_conjs.c_ptr()), r.get_head()), pr, dest, r.name());
  }

  expr* mk_array_eq_rewrite::replace(expr* e, expr* new_val, expr* old_val)
  {
    if(e==old_val)
      return new_val;
    else if(!is_app(e))
    {
      return e;
    }
    app*f = to_app(e);
    ptr_vector<expr> n_args;
    for(unsigned i=0;i<f->get_num_args();i++)
    {
      n_args.push_back(replace(f->get_arg(i), new_val, old_val));
    }
    return m.mk_app(f->get_decl(), n_args.size(), n_args.c_ptr());
  }

}
