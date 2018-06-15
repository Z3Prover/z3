/*++

Module Name:

    dl_mk_array_instantiation.h

Abstract:

    Does array instantiation

Author:

    Julien Braine

Revision History:

--*/


#include "muz/transforms/dl_mk_array_instantiation.h"
#include "muz/base/dl_context.h"
#include "ast/pattern/pattern_inference.h"
#include "muz/base/dl_context.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/expr_abstract.h"
#include "muz/base/fp_params.hpp"

namespace datalog {

  mk_array_instantiation::mk_array_instantiation(
        context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        m_a(m),
        eq_classes(m),
        ownership(m)
  {
  }

  rule_set * mk_array_instantiation::operator()(rule_set const & source)
  {
    std::cout<<"Array Instantiation called with parameters :"
             <<" enforce="<<m_ctx.get_params().xform_instantiate_arrays_enforce()
             <<" nb_quantifier="<<m_ctx.get_params().xform_instantiate_arrays_nb_quantifier()
             <<" slice_technique="<<m_ctx.get_params().xform_instantiate_arrays_slice_technique()
             <<"\n";
    std::cout<<"Input rules = \n";
    source.display(std::cout);
    src_set = &source;
    rule_set * result = alloc(rule_set, m_ctx);
    dst=result;
    unsigned nbrules = source.get_num_rules();
    src_manager = &source.get_rule_manager();
    for(unsigned i =0;i<nbrules;i++)
    {
      rule & r = *source.get_rule(i);
      instantiate_rule(r, *result);
    }
    std::cout<<"\n\nOutput rules = \n";
    result->display(std::cout);
    return result;
  }

  void mk_array_instantiation::instantiate_rule(const rule& r, rule_set & dest)
  {
    //Reset everything
    selects.reset();
    eq_classes.reset();
    cnt = src_manager->get_counter().get_max_rule_var(r)+1;
    done_selects.reset();
    ownership.reset();

    expr_ref_vector phi(m);
    expr_ref_vector preds(m);
    expr_ref new_head = create_head(to_app(r.get_head()));
    unsigned nb_predicates = r.get_uninterpreted_tail_size();
    unsigned tail_size = r.get_tail_size();
    for(unsigned i=0;i<nb_predicates;i++)
    {
      preds.push_back(r.get_tail(i));
    }
    for(unsigned i=nb_predicates;i<tail_size;i++)
    {
      phi.push_back(r.get_tail(i));
    }

    //Retrieve selects
    for(unsigned i=0;i<phi.size();i++)
      retrieve_selects(phi[i].get());

    //Rewrite the predicates
    expr_ref_vector new_tail(m);
    for(unsigned i=0;i<preds.size();i++)
    {
      new_tail.append(instantiate_pred(to_app(preds[i].get())));
    }
    new_tail.append(phi);
    for(obj_map<expr, var*>::iterator it = done_selects.begin(); it!=done_selects.end(); ++it)
    {
      expr_ref tmp(m);
      tmp = &it->get_key();
      new_tail.push_back(m.mk_eq(it->get_value(), tmp));
    }
    proof_ref pr(m);
    src_manager->mk_rule(m.mk_implies(m.mk_and(new_tail.size(), new_tail.c_ptr()), new_head), pr, dest, r.name());
  }

  expr_ref mk_array_instantiation::create_head(app* old_head)
  {
     expr_ref_vector new_args(m);
     for(unsigned i=0;i<old_head->get_num_args();i++)
     {
       expr*arg = old_head->get_arg(i);
       if(m_a.is_array(get_sort(arg)))
       {
         for(unsigned k=0; k< m_ctx.get_params().xform_instantiate_arrays_nb_quantifier();k++)
         {
           expr_ref_vector dummy_args(m);
           dummy_args.push_back(arg);
           for(unsigned i=0;i<get_array_arity(get_sort(arg));i++)
           {
             dummy_args.push_back(m.mk_var(cnt, get_array_domain(get_sort(arg), i)));
             cnt++;
           }
           expr_ref select(m);
           select = m_a.mk_select(dummy_args.size(), dummy_args.c_ptr());
           new_args.push_back(select);
           selects.insert_if_not_there(arg, ptr_vector<expr>());
           selects[arg].push_back(select);
         }
         if(!m_ctx.get_params().xform_instantiate_arrays_enforce())
             new_args.push_back(arg);
       }
       else
        new_args.push_back(arg);
     }
     return create_pred(old_head, new_args);
  }


  void mk_array_instantiation::retrieve_selects(expr* e)
  {
    //If the expression is not a function application, we ignore it
    if (!is_app(e)) {
      return;
    }
    app*f=to_app(e);
    //Call the function recursively on all arguments
    unsigned nbargs = f->get_num_args();
    for(unsigned i=0;i<nbargs;i++)
    {
      retrieve_selects(f->get_arg(i));
    }
    //If it is a select, then add it to selects
    if(m_a.is_select(f))
    {
      SASSERT(!m_a.is_array(get_sort(e)));
      selects.insert_if_not_there(f->get_arg(0), ptr_vector<expr>());
      selects[f->get_arg(0)].push_back(e);
    }
    //If it is a condition between arrays, for example the result of a store, then add it to the equiv_classes
    if(m_a.is_store(f))
    {
      eq_classes.merge(e, f->get_arg(0));
    }
    else if(m.is_eq(f) && m_a.is_array(get_sort(f->get_arg(0))))
    {
      eq_classes.merge(f->get_arg(0), f->get_arg(1));
    }
  }


  expr_ref_vector mk_array_instantiation::getId(app*old_pred, const expr_ref_vector& n_args)
  {
    expr_ref_vector res(m);
    for(unsigned i=0;i<n_args.size(); i++)
    {
      if(m_a.is_select(n_args[i]))
      {
        app*select = to_app(n_args[i]);
        for(unsigned j=1;j<select->get_num_args();j++)
        {
          res.push_back(select->get_arg(j));
        }
      }
    }
    return res;
  }

  expr_ref mk_array_instantiation::create_pred(app*old_pred, expr_ref_vector& n_args)
  {
    expr_ref_vector new_args(m);
    new_args.append(n_args);
    new_args.append(getId(old_pred, n_args));
    for(unsigned i=0;i<new_args.size();i++)
    {
      if(m_a.is_select(new_args[i].get()))
      {
        new_args[i] = mk_select_var(new_args[i].get());
      }
    }
    sort_ref_vector new_sorts(m);
    for(unsigned i=0;i<new_args.size();i++)
      new_sorts.push_back(get_sort(new_args[i].get()));
    expr_ref res(m);
    func_decl_ref fun_decl(m);
    fun_decl = m.mk_func_decl(symbol((old_pred->get_decl()->get_name().str()+"!inst").c_str()), new_sorts.size(), new_sorts.c_ptr(), old_pred->get_decl()->get_range());
    m_ctx.register_predicate(fun_decl, false);
    if(src_set->is_output_predicate(old_pred->get_decl()))
      dst->set_output_predicate(fun_decl);
    res=m.mk_app(fun_decl,new_args.size(), new_args.c_ptr());
    return res;
  }

  var * mk_array_instantiation::mk_select_var(expr* select)
  {
    var*result;
    if(!done_selects.find(select, result))
    {
      ownership.push_back(select);
      result = m.mk_var(cnt, get_sort(select));
      cnt++;
      done_selects.insert(select, result);
    }
    return result;
  }

  expr_ref mk_array_instantiation::rewrite_select(expr*array, expr*select)
  {
    app*s = to_app(select);
    expr_ref res(m);
    expr_ref_vector args(m);
    args.push_back(array);
    for(unsigned i=1; i<s->get_num_args();i++)
    {
      args.push_back(s->get_arg(i));
    }
    res = m_a.mk_select(args.size(), args.c_ptr());
    return res;
  }

  expr_ref_vector mk_array_instantiation::retrieve_all_selects(expr*array)
  {
    expr_ref_vector all_selects(m);
    for(expr_equiv_class::iterator it = eq_classes.begin(array);
        it != eq_classes.end(array); ++it)
    {
      selects.insert_if_not_there(*it, ptr_vector<expr>());
      ptr_vector<expr>& select_ops = selects[*it];
      for(unsigned i=0;i<select_ops.size();i++)
      {
        all_selects.push_back(rewrite_select(array, select_ops[i]));
      }
    }
    if(all_selects.size()==0)
    {
      expr_ref_vector dummy_args(m);
      dummy_args.push_back(array);
      for(unsigned i=0;i<get_array_arity(get_sort(array));i++)
      {
        dummy_args.push_back(m.mk_var(cnt, get_array_domain(get_sort(array), i)));
        cnt++;
      }
      all_selects.push_back(m_a.mk_select(dummy_args.size(), dummy_args.c_ptr()));
    }
    return all_selects;
  }


  expr_ref_vector mk_array_instantiation::instantiate_pred(app*old_pred)
  {

    unsigned nb_old_args=old_pred->get_num_args();
    //Stores, for each old position, the list of a new possible arguments
    vector<expr_ref_vector> arg_correspondance;
    for(unsigned i=0;i<nb_old_args;i++)
    {
      expr_ref arg(old_pred->get_arg(i), m);
      if(m_a.is_array(get_sort(arg)))
      {
        vector<expr_ref_vector> arg_possibilities(m_ctx.get_params().xform_instantiate_arrays_nb_quantifier(), retrieve_all_selects(arg));
        arg_correspondance.append(arg_possibilities);
        if(!m_ctx.get_params().xform_instantiate_arrays_enforce())
        {
          expr_ref_vector tmp(m);
          tmp.push_back(arg);
          arg_correspondance.push_back(tmp);
        }
      }
      else
      {
        expr_ref_vector tmp(m);
        tmp.push_back(arg);
        arg_correspondance.push_back(tmp);
      }
    }
    //Now, we need to deal with every combination

    expr_ref_vector res(m);

    svector<unsigned> chosen(arg_correspondance.size(), 0u);
    while(1)
    {
      expr_ref_vector new_args(m);
      for(unsigned i=0;i<chosen.size();i++)
      {
          new_args.push_back(arg_correspondance[i][chosen[i]].get());
      }
      res.push_back(create_pred(old_pred, new_args));
      unsigned pos=-1;
      do
      {
        pos++;
        if(pos==chosen.size())
        {
          return res;
        }
      }while(chosen[pos]+1>=arg_correspondance[pos].size());
      chosen[pos]++;
    }
  }
}
