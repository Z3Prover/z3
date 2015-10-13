/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3checker.cpp

  Abstract:

  check correctness of interpolant

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#endif

#include "iz3base.h"
#include "iz3checker.h"

#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>
#include <iterator>


using namespace stl_ext;

struct iz3checker : iz3base {
  
    /* HACK: for tree interpolants, we assume that uninterpreted functions
       are global. This is because in the current state of the tree interpolation
       code, symbols that appear in sibling sub-trees have to be global, and
       we have no way to eliminate such function symbols. When tree interpoaltion is
       fixed, we can tree function symbols the same as constant symbols. */

    bool is_tree;

    void support(const ast &t, std::set<std::string> &res, hash_set<ast> &memo){
        if(memo.find(t) != memo.end()) return;
        memo.insert(t);
    
        int nargs = num_args(t);
        for(int i = 0; i < nargs; i++)
            support(arg(t,i),res,memo);
    
        switch(op(t)){
        case Uninterpreted:
            if(nargs == 0 || !is_tree) {
                std::string name = string_of_symbol(sym(t));
                res.insert(name);
            }
            break;
        case Forall:
        case Exists:
            support(get_quantifier_body(t),res,memo);
            break;
        default:;
        }
    }

    bool check(solver *s, std::ostream &err,
               const std::vector<ast> &cnsts,
               const std::vector<int> &parents,
               const std::vector<ast> &itp,
               const std::vector<ast> &theory){

        is_tree = !parents.empty();
        int num = cnsts.size();
        std::vector<std::vector<int> > children(num);
  
        for(int i = 0; i < num-1; i++){
            if(parents.size())
                children[parents[i]].push_back(i);
            else 
                children[i+1].push_back(i);
        }

        for(int i = 0; i < num; i++){
            s->push();
            for(unsigned j = 0; j < theory.size(); j++)
                s->assert_expr(to_expr(theory[j].raw()));
            s->assert_expr(to_expr(cnsts[i].raw()));
            std::vector<int> &cs = children[i];
            for(unsigned j = 0; j < cs.size(); j++)
                s->assert_expr(to_expr(itp[cs[j]].raw()));
            if(i != num-1)
                s->assert_expr(to_expr(mk_not(itp[i]).raw()));
            lbool result = s->check_sat(0,0);
            if(result != l_false){
                err << "interpolant " << i << " is incorrect";

                s->pop(1);
                for(unsigned j = 0; j < theory.size(); j++)
                    s->assert_expr(to_expr(theory[j].raw()));
                for(unsigned j = 0; j < cnsts.size(); j++)
                    if(in_range(j,range_downward(i)))
                        s->assert_expr(to_expr(cnsts[j].raw()));
                if(i != num-1)
                    s->assert_expr(to_expr(mk_not(itp[i]).raw()));
                lbool result = s->check_sat(0,0);
                if(result != l_false)
                    err << "interpolant " << i << " is not implied by its downeard closurn";

                return false;
            }
            s->pop(1);
        }

        std::vector<std::set<std::string> > supports(num);
        for(int i = 0; i < num; i++){
            hash_set<ast> memo;
            support(cnsts[i],supports[i],memo);
        }
        for(int i = 0; i < num-1; i++){
            std::vector<bool> Bside(num);
            for(int j = num-1; j >= 0; j--)
                Bside[j] = j != i;
            for(int j = num-1; j >= 0; j--)
                if(!Bside[j]){
                    std::vector<int> &cs = children[i];
                    for(unsigned k = 0; k < cs.size(); k++)
                        Bside[cs[k]] = false;
                }
            std::set<std::string> Asup, Bsup,common,Isup,bad;
            for(int j = num-1; j >= 0; j--){
                std::set<std::string> &side = Bside[j] ? Bsup : Asup;
                side.insert(supports[j].begin(),supports[j].end());
            }
            std::set_intersection(Asup.begin(),Asup.end(),Bsup.begin(),Bsup.end(),std::inserter(common,common.begin()));
            {
                hash_set<ast> tmemo;
                for(unsigned j = 0; j < theory.size(); j++)
                    support(theory[j],common,tmemo);                // all theory symbols allowed in interps
            }
            hash_set<ast> memo;
            support(itp[i],Isup,memo);
            std::set_difference(Isup.begin(),Isup.end(),common.begin(),common.end(),std::inserter(bad,bad.begin()));
            if(!bad.empty()){
                err << "bad symbols in interpolant " << i << ":";
                std::copy(bad.begin(),bad.end(),std::ostream_iterator<std::string>(err,","));
                return false;
            }
        }
        return true;
    }
  
    bool check(solver *s, std::ostream &err,
               const std::vector<ast> &_cnsts,
               const ast &tree,
               const std::vector<ast> &itp){

        std::vector<int> pos_map;
    
        // convert to the parents vector representation
    
        to_parents_vec_representation(_cnsts, tree, cnsts, parents, theory, pos_map);
    
        //use the parents vector representation to compute interpolant
        return check(s,err,cnsts,parents,itp,theory);
    }

    iz3checker(ast_manager &_m)
        : iz3base(_m) {
    }

    iz3checker(iz3mgr &_m)
        : iz3base(_m) {
    }

};  

template <class T>
std::vector<T> to_std_vector(const ::vector<T> &v){
    std::vector<T> _v(v.size());
    for(unsigned i = 0; i < v.size(); i++)
        _v[i] = v[i];
    return _v;
}


bool iz3check(ast_manager &_m_manager,
          solver *s,
          std::ostream &err,
          const ptr_vector<ast> &cnsts,
          const ::vector<int> &parents,
          const ptr_vector<ast> &interps,
          const ptr_vector<ast> &theory)
{
    iz3checker chk(_m_manager);
    return chk.check(s,err,chk.cook(cnsts),to_std_vector(parents),chk.cook(interps),chk.cook(theory));
}

bool iz3check(iz3mgr &mgr,
          solver *s,
          std::ostream &err,
          const std::vector<iz3mgr::ast> &cnsts,
          const std::vector<int> &parents,
          const std::vector<iz3mgr::ast> &interps,
          const std::vector<iz3mgr::ast> &theory)
{
    iz3checker chk(mgr);
    return chk.check(s,err,cnsts,parents,interps,theory);
}

bool iz3check(ast_manager &_m_manager,
          solver *s,
          std::ostream &err,
          const ptr_vector<ast> &_cnsts,
          ast *tree,
          const ptr_vector<ast> &interps)
{
    iz3checker chk(_m_manager);
    return chk.check(s,err,chk.cook(_cnsts),chk.cook(tree),chk.cook(interps));
}
