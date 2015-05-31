/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3proof.cpp

  Abstract:

  This class defines a simple interpolating proof system.

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

#include "iz3proof.h"
#include "iz3profiling.h"

#include<algorithm>
#include <iterator>
#include <iostream>
#include <sstream>

// #define FACTOR_INTERPS
// #define CHECK_PROOFS


void iz3proof::resolve(ast pivot, std::vector<ast> &cls1, const std::vector<ast> &cls2){
#ifdef CHECK_PROOFS
    std::vector<ast> orig_cls1 = cls1;
#endif  
    ast neg_pivot = pv->mk_not(pivot);
    bool found_pivot1 = false, found_pivot2 = false;
    for(unsigned i = 0; i < cls1.size(); i++){
        if(cls1[i] == neg_pivot){
            cls1[i] = cls1.back();
            cls1.pop_back();
            found_pivot1 = true;
            break;
        }
    }
    { 
        std::set<ast> memo;
        memo.insert(cls1.begin(),cls1.end());
        for(unsigned j = 0; j < cls2.size(); j++){
            if(cls2[j] == pivot)
                found_pivot2 = true;
            else
                if(memo.find(cls2[j]) == memo.end())
                    cls1.push_back(cls2[j]);
        }
    }
    if(found_pivot1 && found_pivot2)
        return;
 
#ifdef CHECK_PROOFS
    std::cerr << "resolution anomaly: " << nodes.size()-1 << "\n";
#if 0
    std::cerr << "pivot: "; {pv->print_lit(pivot); std::cout << "\n";}
    std::cerr << "left clause:\n";
    for(unsigned i = 0; i < orig_cls1.size(); i++)
        {pv->print_lit(orig_cls1[i]); std::cout << "\n";}
    std::cerr << "right clause:\n";
    for(unsigned i = 0; i < cls2.size(); i++)
        {pv->print_lit(cls2[i]); std::cout << "\n";}
    throw proof_error();
#endif
#endif
}

iz3proof::node iz3proof::make_resolution(ast pivot, node premise1, node premise2)
{
    if(nodes[premise1].rl == Hypothesis) return premise2; // resolve with hyp is noop
    if(nodes[premise2].rl == Hypothesis) return premise1;
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Resolution;
    n.aux = pivot;
    n.premises.resize(2);
    n.premises[0] = (premise1);
    n.premises[1] = (premise2);
#ifdef CHECK_PROOFS
    n.conclusion = nodes[premise1].conclusion;
    resolve(pivot,n.conclusion,nodes[premise2].conclusion);
    n.frame = 1;
#else
    n.frame = 0; // compute conclusion lazily
#endif
    return res;
}

iz3proof::node iz3proof::resolve_lemmas(ast pivot, node premise1, node premise2)
{
    std::vector<ast> lits(nodes[premise1].conclusion), itp; // no interpolant
    resolve(pivot,lits,nodes[premise2].conclusion);
    return make_lemma(lits,itp);
}


iz3proof::node iz3proof::make_assumption(int frame, const std::vector<ast> &assumption){
#if 0
    std::cout << "assumption: \n"; 
    for(unsigned i = 0; i < assumption.size(); i++)
        pv->show(assumption[i]);
    std::cout << "\n"; 
#endif
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Assumption;
    n.conclusion.resize(1);
    n.conclusion = assumption;
    n.frame = frame;
    return res;
}

iz3proof::node iz3proof::make_hypothesis(ast hypothesis){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Hypothesis;
    n.conclusion.resize(2);
    n.conclusion[0] = hypothesis;
    n.conclusion[1] = pv->mk_not(hypothesis);
    return res;
}

iz3proof::node iz3proof::make_theory(const std::vector<ast> &conclusion, std::vector<node> premises){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Theory;
    n.conclusion = conclusion;
    n.premises = premises;
    return res;
}

iz3proof::node iz3proof::make_axiom(const std::vector<ast> &conclusion){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Axiom;
    n.conclusion = conclusion;
    return res;
}

iz3proof::node iz3proof::make_contra(node prem, const std::vector<ast> &conclusion){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Contra;
    n.conclusion = conclusion;
#ifdef CHECK_PROOFS
    //if(!(conclusion == nodes[prem].conclusion)){
    //std::cerr << "internal error: proof error\n";
    //assert(0 && "proof error");
    //}
#endif
    n.premises.push_back(prem);
    return res;
}


iz3proof::node iz3proof::make_lemma(const std::vector<ast> &conclusion, const std::vector<ast> &interpolation){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Lemma;
    n.conclusion = conclusion;
    n.frame = interps.size();
    interps.push_back(interpolation);
    return res;
}

/** Make a Reflexivity node. This rule produces |- x = x */

iz3proof::node iz3proof::make_reflexivity(ast con){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Reflexivity;
    n.conclusion.push_back(con);
    return res;
}
  
/** Make a Symmetry node. This takes a derivation of |- x = y and
    produces | y = x */

iz3proof::node iz3proof::make_symmetry(ast con, node prem){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Reflexivity;
    n.conclusion.push_back(con);
    n.premises.push_back(prem);
    return res;
}

/** Make a transitivity node. This takes derivations of |- x = y
    and |- y = z produces | x = z */

iz3proof::node iz3proof::make_transitivity(ast con, node prem1, node prem2){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Transitivity;
    n.conclusion.push_back(con);
    n.premises.push_back(prem1);
    n.premises.push_back(prem2);
    return res;
}

  
/** Make a congruence node. This takes derivations of |- x_i = y_i
    and produces |- f(x_1,...,x_n) = f(y_1,...,y_n) */

iz3proof::node iz3proof::make_congruence(ast con, const std::vector<node> &prems){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = Congruence;
    n.conclusion.push_back(con);
    n.premises = prems;
    return res;
}


/** Make an equality contradicition node. This takes |- x = y
    and |- !(x = y) and produces false. */

iz3proof::node iz3proof::make_eqcontra(node prem1, node prem2){
    node res = make_node();
    node_struct &n = nodes[res];
    n.rl = EqContra;
    n.premises.push_back(prem1);
    n.premises.push_back(prem2);
    return res;
}

iz3proof::node iz3proof::copy_rec(stl_ext::hash_map<node,node> &memo, iz3proof &src, node n){
    stl_ext::hash_map<node,node>::iterator it = memo.find(n);
    if(it != memo.end()) return (*it).second;
    node_struct &ns = src.nodes[n];
    std::vector<node> prems(ns.premises.size());
    for(unsigned i = 0; i < prems.size(); i++)
        prems[i] = copy_rec(memo,src,ns.premises[i]);
    nodes.push_back(ns);
    nodes.back().premises.swap(prems);
    if(ns.rl == Lemma){
        nodes.back().frame = interps.size();
        interps.push_back(src.interps[ns.frame]);
    }
    int res = nodes.size()-1;
    memo[n] = res;
    return res;
}

iz3proof::node iz3proof::copy(iz3proof &src, node n){
    stl_ext::hash_map<node,node> memo;
    return copy_rec(memo, src, n);
}

bool iz3proof::pred_in_A(ast id){
    return weak
        ? pv->ranges_intersect(pv->ast_range(id),rng) :
        pv->range_contained(pv->ast_range(id),rng);
}
  
bool iz3proof::term_in_B(ast id){
    prover::range r = pv->ast_scope(id);
    if(weak) {
        if(pv->range_min(r) == SHRT_MIN)
            return !pv->range_contained(r,rng);
        else
            return !pv->ranges_intersect(r,rng);
    }
    else
        return !pv->range_contained(r,rng);
}
  
bool iz3proof::frame_in_A(int frame){
    return pv->in_range(frame,rng);
}

bool iz3proof::lit_in_B(ast lit){
    return
        b_lits.find(lit) != b_lits.end()
        || b_lits.find(pv->mk_not(lit)) != b_lits.end();
}

iz3proof::ast iz3proof::my_or(ast x, ast y){
    return pv->mk_not(pv->mk_and(pv->mk_not(x),pv->mk_not(y)));
}

iz3proof::ast iz3proof::get_A_lits(std::vector<ast> &cls){
    ast foo = pv->mk_false();
    for(unsigned i = 0; i < cls.size(); i++){
        ast lit = cls[i];
        if(b_lits.find(pv->mk_not(lit)) == b_lits.end()){
            if(pv->range_max(pv->ast_scope(lit)) == pv->range_min(pv->ast_scope(lit))){
                std::cout << "bad lit: " << pv->range_max(rng) << " : " << pv->range_max(pv->ast_scope(lit)) << " : " << (pv->ast_id(lit)) << " : ";
                pv->show(lit);
            }      
            foo = my_or(foo,lit);
        }
    }
    return foo;
}

iz3proof::ast iz3proof::get_B_lits(std::vector<ast> &cls){
    ast foo = pv->mk_false();
    for(unsigned i = 0; i < cls.size(); i++){
        ast lit = cls[i];
        if(b_lits.find(pv->mk_not(lit)) != b_lits.end())
            foo = my_or(foo,lit);
    }
    return foo;
}

void iz3proof::set_of_B_lits(std::vector<ast> &cls, std::set<ast> &res){
    for(unsigned i = 0; i < cls.size(); i++){
        ast lit = cls[i];
        if(b_lits.find(pv->mk_not(lit)) != b_lits.end())
            res.insert(lit);
    }
}

void iz3proof::set_of_A_lits(std::vector<ast> &cls, std::set<ast> &res){
    for(unsigned i = 0; i < cls.size(); i++){
        ast lit = cls[i];
        if(b_lits.find(pv->mk_not(lit)) == b_lits.end())
            res.insert(lit);
    }
}

void iz3proof::find_B_lits(){
    b_lits.clear();
    for(unsigned i = 0; i < nodes.size(); i++){
        node_struct &n = nodes[i];
        std::vector<ast> &cls = n.conclusion;
        if(n.rl == Assumption){
            if(weak) goto lemma;
            if(!frame_in_A(n.frame))
                for(unsigned j = 0; j < cls.size(); j++)
                    b_lits.insert(cls[j]);
        }
        else if(n.rl == Lemma) {
        lemma:
            for(unsigned j = 0; j < cls.size(); j++)
                if(term_in_B(cls[j]))
                    b_lits.insert(cls[j]);
        }
    }
}

iz3proof::ast iz3proof::disj_of_set(std::set<ast> &s){
    ast res = pv->mk_false();
    for(std::set<ast>::iterator it = s.begin(), en = s.end(); it != en; ++it)
        res = my_or(*it,res);
    return res;
}

void iz3proof::mk_and_factor(int p1, int p2, int i, std::vector<ast> &itps, std::vector<std::set<ast> > &disjs){
#ifdef FACTOR_INTERPS
    std::set<ast> &d1 = disjs[p1];
    std::set<ast> &d2 = disjs[p2];
    if(!weak){
        if(pv->is_true(itps[p1])){
            itps[i] = itps[p2];
            disjs[i] = disjs[p2];
        }
        else if(pv->is_true(itps[p2])){
            itps[i] = itps[p1];
            disjs[i] = disjs[p1];
        }
        else {
            std::set<ast> p1only,p2only;
            std::insert_iterator<std::set<ast> > p1o(p1only,p1only.begin());
            std::insert_iterator<std::set<ast> > p2o(p2only,p2only.begin());
            std::insert_iterator<std::set<ast> > dio(disjs[i],disjs[i].begin());
            std::set_difference(d1.begin(),d1.end(),d2.begin(),d2.end(),p1o);
            std::set_difference(d2.begin(),d2.end(),d1.begin(),d1.end(),p2o);
            std::set_intersection(d1.begin(),d1.end(),d2.begin(),d2.end(),dio);
            ast p1i = my_or(itps[p1],disj_of_set(p1only));
            ast p2i = my_or(itps[p2],disj_of_set(p2only));
            itps[i] = pv->mk_and(p1i,p2i);
        }
    }
    else {
        itps[i] = pv->mk_and(itps[p1],itps[p2]);
        std::insert_iterator<std::set<ast> > dio(disjs[i],disjs[i].begin());
        std::set_union(d1.begin(),d1.end(),d2.begin(),d2.end(),dio);
    }
#endif
}

void iz3proof::mk_or_factor(int p1, int p2, int i, std::vector<ast> &itps, std::vector<std::set<ast> > &disjs){
#ifdef FACTOR_INTERPS
    std::set<ast> &d1 = disjs[p1];
    std::set<ast> &d2 = disjs[p2];
    if(weak){
        if(pv->is_false(itps[p1])){
            itps[i] = itps[p2];
            disjs[i] = disjs[p2];
        }
        else if(pv->is_false(itps[p2])){
            itps[i] = itps[p1];
            disjs[i] = disjs[p1];
        }
        else {
            std::set<ast> p1only,p2only;
            std::insert_iterator<std::set<ast> > p1o(p1only,p1only.begin());
            std::insert_iterator<std::set<ast> > p2o(p2only,p2only.begin());
            std::insert_iterator<std::set<ast> > dio(disjs[i],disjs[i].begin());
            std::set_difference(d1.begin(),d1.end(),d2.begin(),d2.end(),p1o);
            std::set_difference(d2.begin(),d2.end(),d1.begin(),d1.end(),p2o);
            std::set_intersection(d1.begin(),d1.end(),d2.begin(),d2.end(),dio);
            ast p1i = pv->mk_and(itps[p1],pv->mk_not(disj_of_set(p1only)));
            ast p2i = pv->mk_and(itps[p2],pv->mk_not(disj_of_set(p2only)));
            itps[i] = my_or(p1i,p2i);
        }
    }
    else {
        itps[i] = my_or(itps[p1],itps[p2]);
        std::insert_iterator<std::set<ast> > dio(disjs[i],disjs[i].begin());
        std::set_union(d1.begin(),d1.end(),d2.begin(),d2.end(),dio);
    }
#endif
}

void iz3proof::interpolate_lemma(node_struct &n){
    if(interps[n.frame].size())
        return; // already computed
    pv->interpolate_clause(n.conclusion,interps[n.frame]);
}

iz3proof::ast iz3proof::interpolate(const prover::range &_rng, bool _weak
#ifdef CHECK_PROOFS
                                    , ast assump
                                    , std::vector<int> *parents
#endif
                                    ){
    // std::cout << "proof size: " << nodes.size() << "\n";
    rng = _rng;
    weak = _weak;
#ifdef CHECK_PROOFS
    if(nodes[nodes.size()-1].conclusion.size() != 0)
        std::cerr << "internal error: proof conclusion is not empty clause\n";
    if(!child_interps.size()){
        child_interps.resize(nodes.size());
        for(unsigned j = 0; j < nodes.size(); j++)
            child_interps[j] = pv->mk_true();
    }
#endif
    std::vector<ast> itps(nodes.size());
#ifdef FACTOR_INTERPS
    std::vector<std::set<ast> > disjs(nodes.size());
#endif
    profiling::timer_start("Blits");
    find_B_lits();
    profiling::timer_stop("Blits");
    profiling::timer_start("interp_proof");
    // strengthen();
    for(unsigned i = 0; i < nodes.size(); i++){
        node_struct &n = nodes[i];
        ast &q = itps[i];
        switch(n.rl){
        case Assumption: {

            if(frame_in_A(n.frame)){
                /* HypC-A */
                if(!weak) 
#ifdef FACTOR_INTERPS
                    {
                        q = pv->mk_false();
                        set_of_B_lits(n.conclusion,disjs[i]); 
                    }
#else
                q = get_B_lits(n.conclusion);
#endif
                else
                    q = pv->mk_false();
            }
            else {
                /* HypEq-B */
                if(!weak)
                    q = pv->mk_true();
                else
#ifdef FACTOR_INTERPS
                    {
                        q = pv->mk_true();
                        set_of_A_lits(n.conclusion,disjs[i]); 
                    }
#else
                q = pv->mk_not(get_A_lits(n.conclusion));
#endif
            }
            break;
        }
        case Resolution: {
            ast p = n.aux;
            p = pv->is_not(p) ? pv->mk_not(p) : p; // should be positive, but just in case
            if(lit_in_B(p))
#ifdef FACTOR_INTERPS
                mk_and_factor(n.premises[0],n.premises[1],i,itps,disjs);
#else
            q = pv->mk_and(itps[n.premises[0]],itps[n.premises[1]]);
#endif
            else
#ifdef FACTOR_INTERPS
                mk_or_factor(n.premises[0],n.premises[1],i,itps,disjs);
#else
            q = my_or(itps[n.premises[0]],itps[n.premises[1]]);
#endif
            break;
        }
        case Lemma: {
            interpolate_lemma(n); // make sure lemma interpolants have been computed
            q = interps[n.frame][pv->range_max(rng)];
            break;
        }
        case Contra: {
            q = itps[n.premises[0]];
#ifdef FACTOR_INTERPS
            disjs[i] = disjs[n.premises[0]];
#endif
            break;
        }
        default:
            assert(0 && "rule not allowed in interpolated proof");
        }
#ifdef CHECK_PROOFS
        int this_frame = pv->range_max(rng);
        if(0 && this_frame == 39) {
            std::vector<ast> alits;
            ast s = pv->mk_true();
            for(unsigned j = 0; j < n.conclusion.size(); j++)
                if(pred_in_A(n.conclusion[j])){
                    int scpmax = pv->range_max(pv->ast_scope(n.conclusion[j]));
                    if(scpmax == this_frame)
                        s = pv->mk_and(s,pv->mk_not(n.conclusion[j]));
                }
            ast ci = child_interps[i];
            s = pv->mk_and(pv->mk_and(s,pv->mk_and(assump,pv->mk_not(q))),ci);
            if(pv->is_sat(s)){
                std::cout << "interpolation invariant violated at step " << i << "\n";
                assert(0 && "interpolation invariant violated");
            }
        }
        if((*parents)[this_frame] == 39)
            child_interps[i] = pv->mk_and(child_interps[i],q);
#endif
    }
    ast &bar = itps[nodes.size()-1];
#ifdef FACTOR_INTERPS
    if(!weak)
        bar = my_or(bar,disj_of_set(disjs[nodes.size()-1]));
    else
        bar = pv->mk_and(bar,pv->mk_not(disj_of_set(disjs[nodes.size()-1])));
#endif
    profiling::timer_stop("interp_proof");
    profiling::timer_start("simplifying");
    bar = pv->simplify(bar);
    profiling::timer_stop("simplifying");
    return bar;
}


void iz3proof::print(std::ostream &s, int id){
    node_struct &n = nodes[id];
    switch(n.rl){
    case Assumption:
        s << "Assumption(";
        pv->print_clause(s,n.conclusion); 
        s << ")"; 
        break;
    case Hypothesis:
        s << "Hyp("; pv->print_expr(s,n.conclusion[0]); s << ")"; break;
    case Reflexivity:
        s << "Refl("; pv->print_expr(s,n.conclusion[0]); s << ")"; break;
    case Symmetry:
        s << "Symm("; print(s,n.premises[0]); s << ")"; break;
    case Transitivity:
        s << "Trans("; print(s,n.premises[0]); s << ","; print(s,n.premises[1]); s << ")"; break;
    case Congruence:
        s << "Cong("; pv->print_expr(s,n.conclusion[0]); 
        for(unsigned i = 0; i < n.premises.size(); i++){
            s << ",";
            print(s,n.premises[i]); 
        }
        s << ")"; break;
    case EqContra:
        s << "EqContra("; print(s,n.premises[0]); s << ","; print(s,n.premises[1]); s << ")"; break;
    case Resolution:
        s << "Res(";
        pv->print_expr(s,n.aux); s << ",";
        print(s,n.premises[0]); s << ","; print(s,n.premises[1]); s << ")"; 
        break;
    case Lemma:
        s << "Lemma(";
        pv->print_clause(s,n.conclusion); 
        for(unsigned i = 0; i < n.premises.size(); i++){
            s << ",";
            print(s,n.premises[i]);
        }
        s << ")"; 
        break;
    case Contra:
        s << "Contra(";
        print(s,n.premises[0]); 
        s << ")"; 
        break;
    default:;
    }
}


void iz3proof::show(int id){
    std::ostringstream ss;
    print(ss,id);
    iz3base::pretty_print(std::cout,ss.str());
    // std::cout << ss.str();
    std::cout << "\n";
}


