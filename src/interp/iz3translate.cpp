/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3translate.cpp

  Abstract:

  Translate a Z3 proof to in interpolated proof.

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

#include "iz3translate.h"
#include "iz3proof.h"
#include "iz3profiling.h"
#include "iz3interp.h"
#include "iz3proof_itp.h"

#include <assert.h>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>

//using std::vector;
using namespace stl_ext;



/* This translator goes directly from Z3 proofs to interpolated
   proofs without an intermediate representation. No secondary
   prover is used.
*/

class iz3translation_full : public iz3translation {
public:


    typedef iz3proof_itp Iproof;
  
    Iproof *iproof;

    /* Here we have lots of hash tables for memoizing various methods and
       other such global data structures.
    */

    typedef hash_map<ast,int> AstToInt;
    AstToInt locality;                        // memoizes locality of Z3 proof terms

    typedef std::pair<ast,ast> EquivEntry;
    typedef hash_map<ast,EquivEntry> EquivTab;
    EquivTab equivs;                          // maps non-local terms to equivalent local terms, with proof

    typedef hash_set<ast> AstHashSet;
    AstHashSet equivs_visited;                // proofs already checked for equivalences

    typedef std::pair<hash_map<ast,Iproof::node>, hash_map<ast,Iproof::node> > AstToIpf;
    AstToIpf translation;                     // Z3 proof nodes to Iproof nodes
  
    int frames;                               // number of frames

    typedef std::set<ast> AstSet;
    typedef hash_map<ast,AstSet> AstToAstSet;
    AstToAstSet hyp_map;                      // map proof terms to hypothesis set

    struct LocVar {                           // localization vars
        ast var;                                // a fresh variable
        ast term;                               // term it represents
        int frame;                              // frame in which it's defined
        LocVar(ast v, ast t, int f){var=v;term=t;frame=f;}
    };

    std::vector<LocVar> localization_vars;         // localization vars in order of creation
    typedef hash_map<ast,ast> AstToAst;
    AstToAst localization_map;                // maps terms to their localization vars

    typedef hash_map<ast,bool> AstToBool;
    AstToBool occurs_in_memo;                // memo of occurs_in function

    AstHashSet cont_eq_memo;                // memo of cont_eq function

    AstToAst subst_memo;                    // memo of subst function

    symb commute;

public:

 
#define from_ast(x) (x)

    // #define NEW_LOCALITY

#ifdef NEW_LOCALITY
    range rng; // the range of frames in the "A" part of the interpolant
#endif

    /* To handle skolemization, we have to scan the proof for skolem
       symbols and assign each to a frame. THe assignment is heuristic.
    */

    int scan_skolems_rec(hash_map<ast,int> &memo, const ast &proof, int frame){
        std::pair<ast,int> foo(proof,INT_MAX);
        std::pair<AstToInt::iterator, bool> bar = memo.insert(foo);
        int &res = bar.first->second;
        if(!bar.second) return res;
        pfrule dk = pr(proof);
        if(dk == PR_ASSERTED){
            ast ass = conc(proof);
            res = frame_of_assertion(ass);
        }
        else if(dk == PR_SKOLEMIZE){
            ast quanted = arg(conc(proof),0);
            if(op(quanted) == Not)
                quanted = arg(quanted,0);
            // range r = ast_range(quanted);
            // if(range_is_empty(r))
            range r = ast_scope(quanted);
            if(range_is_empty(r))
                throw iz3_exception("can't skolemize");
            if(frame == INT_MAX || !in_range(frame,r))
                frame = range_max(r); // this is desperation -- may fail
            if(frame >= frames) frame = frames - 1;
            add_frame_range(frame,arg(conc(proof),1));
            r = ast_scope(arg(conc(proof),1));
        }
        else if(dk==PR_MODUS_PONENS_OEQ){
            frame = scan_skolems_rec(memo,prem(proof,0),frame);
            scan_skolems_rec(memo,prem(proof,1),frame);
        }
        else {
            unsigned nprems = num_prems(proof);
            for(unsigned i = 0; i < nprems; i++){
                int bar = scan_skolems_rec(memo,prem(proof,i),frame);
                if(res == INT_MAX || res == bar) res = bar;
                else if(bar != INT_MAX) res = -1;
            }
        }
        return res;
    }

    void scan_skolems(const ast &proof){
        hash_map<ast,int> memo;
        scan_skolems_rec(memo,proof, INT_MAX);
    }

    // determine locality of a proof term
    // return frame of derivation if local, or -1 if not
    // result INT_MAX means the proof term is a tautology
    // memoized in hash_map "locality"

    int get_locality_rec(ast proof){
        std::pair<ast,int> foo(proof,INT_MAX);
        std::pair<AstToInt::iterator, bool> bar = locality.insert(foo);
        int &res = bar.first->second;
        if(!bar.second) return res;
        pfrule dk = pr(proof);
        if(dk == PR_ASSERTED){
            ast ass = conc(proof);
            res = frame_of_assertion(ass);
#ifdef NEW_LOCALITY
            if(in_range(res,rng))
                res = range_max(rng);
            else
                res = frames-1;
#endif
        }
        else if(dk == PR_QUANT_INST){
            std::vector<ast> lits;
            ast con = conc(proof);
            get_Z3_lits(con, lits);
            iproof->make_axiom(lits);
        }
#ifdef LOCALIZATION_KLUDGE
        else if(dk == PR_MODUS_PONENS && pr(prem(proof,0)) == PR_QUANT_INST
                && get_locality_rec(prem(proof,1)) == INT_MAX){
            std::vector<ast> lits;
            ast con = conc(proof);
            get_Z3_lits(con, lits);
            iproof->make_axiom(lits);
        }
#endif
        else {
            unsigned nprems = num_prems(proof);
            for(unsigned i = 0; i < nprems; i++){
                ast arg = prem(proof,i);
                int bar = get_locality_rec(arg);
                if(res == INT_MAX || res == bar) res = bar;
                else if(bar != INT_MAX) res = -1;
            }
        }
        return res;
    }


    int get_locality(ast proof){
        // if(lia_z3_axioms_only) return -1;
        int res = get_locality_rec(proof);
        if(res != -1){
            ast con = conc(proof);
            range rng = ast_scope(con);

            // hack: if a clause contains "true", it reduces to "true",
            // which means we won't compute the range correctly. we handle
            // this case by computing the ranges of the literals separately

            if(is_true(con)){
                std::vector<ast> lits;
                get_Z3_lits(conc(proof),lits);
                for(unsigned i = 0; i < lits.size(); i++)
                    rng = range_glb(rng,ast_scope(lits[i]));
            }
      
            if(!range_is_empty(rng)){
                AstSet &hyps = get_hyps(proof);
                for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it){
                    ast hyp = *it;
                    rng = range_glb(rng,ast_scope(hyp));
                }
            }

            if(res == INT_MAX){
                if(range_is_empty(rng))
                    res = -1;
                else res = range_max(rng);
            }
            else {
                if(!in_range(res,rng))
                    res = -1;
            }
        }
        return res;
    }


    AstSet &get_hyps(ast proof){
        std::pair<ast,AstSet > foo(proof,AstSet());
        std::pair<AstToAstSet::iterator, bool> bar = hyp_map.insert(foo);
        AstSet &res = bar.first->second;
        if(!bar.second) return res;
        pfrule dk = pr(proof);
        if(dk == PR_HYPOTHESIS){
            ast con = conc(proof);
            res.insert(con);
        }
        else {
            unsigned nprems = num_prems(proof);
            for(unsigned i = 0; i < nprems; i++){
                ast arg = prem(proof,i);
                AstSet &arg_hyps = get_hyps(arg);
                res.insert(arg_hyps.begin(),arg_hyps.end());
            }
            if(dk == PR_LEMMA){
                ast con = conc(proof);
                res.erase(mk_not(con));
                if(is_or(con)){
                    int clause_size = num_args(con);
                    for(int i = 0; i < clause_size; i++){
                        ast neglit = mk_not(arg(con,i));
                        res.erase(neglit);
                    }
                }        
            }
        }
#if 0
        AstSet::iterator it = res.begin(), en = res.end();
        if(it != en){
            AstSet::iterator old = it;
            ++it;
            for(; it != en; ++it, ++old)
                if(!(*old < *it))
                    std::cout << "foo!";
        }
#endif
        return res;
    }

    // Find all the judgements of the form p <-> q, where
    // p is local and q is non-local, recording them in "equivs"
    // the map equivs_visited is used to record the already visited proof terms

    void find_equivs(ast proof){
        if(equivs_visited.find(proof) != equivs_visited.end())
            return;
        equivs_visited.insert(proof);
        unsigned nprems = num_prems(proof);
        for(unsigned i = 0; i < nprems; i++) // do all the sub_terms
            find_equivs(prem(proof,i));
        ast con = conc(proof); // get the conclusion
        if(is_iff(con)){
            ast iff = con;
            for(int i = 0; i < 2; i++)
                if(!is_local(arg(iff,i)) && is_local(arg(iff,1-i))){
                    std::pair<ast,std::pair<ast,ast> > foo(arg(iff,i),std::pair<ast,ast>(arg(iff,1-i),proof));
                    equivs.insert(foo);
                }
        }
    }

    // get the lits of a Z3 clause
    void get_Z3_lits(ast t, std::vector<ast> &lits){
        opr dk = op(t);
        if(dk == False)
            return; // false = empty clause
        if(dk == Or){
            unsigned nargs = num_args(t);
            lits.resize(nargs);
            for(unsigned i = 0; i < nargs; i++) // do all the sub_terms
                lits[i] = arg(t,i);
        }
        else {
            lits.push_back(t);
        }
    }

    // resolve two clauses represented as vectors of lits. replace first clause
    void resolve(ast pivot, std::vector<ast> &cls1, std::vector<ast> &cls2){
        ast neg_pivot = mk_not(pivot);
        for(unsigned i = 0; i < cls1.size(); i++){
            if(cls1[i] == pivot){
                cls1[i] = cls1.back();
                cls1.pop_back();
                bool found_pivot2 = false;
                for(unsigned j = 0; j < cls2.size(); j++){
                    if(cls2[j] == neg_pivot)
                        found_pivot2 = true;
                    else
                        cls1.push_back(cls2[j]);
                }
                assert(found_pivot2);
                return;
            }
        }
        assert(0 && "resolve failed");
    }

    // get lits resulting from unit resolution up to and including "position"
    // TODO: this is quadratic -- fix it
    void do_unit_resolution(ast proof, int position, std::vector<ast> &lits){
        ast orig_clause = conc(prem(proof,0));
        get_Z3_lits(orig_clause,lits);
        for(int i = 1; i <= position; i++){
            std::vector<ast> unit(1);
            unit[0] = conc(prem(proof,i));
            resolve(mk_not(unit[0]),lits,unit);
        }
    }
  
#if 0
    // clear the localization variables
    void clear_localization(){
        localization_vars.clear();
        localization_map.clear();
    }
  
    // create a fresh variable for localization
    ast fresh_localization_var(ast term, int frame){
        std::ostringstream s;
        s << "%" << (localization_vars.size());
        ast var = make_var(s.str().c_str(),get_type(term));
        sym_range(sym(var)) = range_full(); // make this variable global
        localization_vars.push_back(LocVar(var,term,frame));
        return var;
    }
  

    // "localize" a term to a given frame range by 
    // creating new symbols to represent non-local subterms

    ast localize_term(ast e, const range &rng){
        if(ranges_intersect(ast_scope(e),rng))
            return e; // this term occurs in range, so it's O.K.
        AstToAst::iterator it = localization_map.find(e);
        if(it != localization_map.end())
            return it->second;

        // if is is non-local, we must first localize the arguments to
        // the range of its function symbol
    
        int nargs = num_args(e);
        if(nargs > 0 /*  && (!is_local(e) || flo <= hi || fhi >= lo) */){
            range frng = rng;
            if(op(e) == Uninterpreted){
                symb f = sym(e);
                range srng = sym_range(f);
                if(ranges_intersect(srng,rng)) // localize to desired range if possible
                    frng = range_glb(srng,rng);
            }
            std::vector<ast> largs(nargs);
            for(int i = 0; i < nargs; i++){
                largs[i] = localize_term(arg(e,i),frng);
                frng = range_glb(frng,ast_scope(largs[i]));
            }
            e = clone(e,largs);
            assert(is_local(e));
        }


        if(ranges_intersect(ast_scope(e),rng))
            return e; // this term occurs in range, so it's O.K.

        // choose a frame for the constraint that is close to range
        int frame = range_near(ast_scope(e),rng);

        ast new_var = fresh_localization_var(e,frame);
        localization_map[e] = new_var;
        ast cnst = make(Equal,new_var,e);
        // antes.push_back(std::pair<ast,int>(cnst,frame));
        return new_var;
    }

    // some patterm matching functions

    // match logical or with nargs arguments
    // assumes AIG form
    bool match_or(ast e, ast *args, int nargs){
        if(op(e) != Or) return false;
        int n = num_args(e);
        if(n != nargs) return false;
        for(int i = 0; i < nargs; i++)
            args[i] = arg(e,i);
        return true;
    }

    // match operator f with exactly nargs arguments
    bool match_op(ast e, opr f, ast *args, int nargs){
        if(op(e) != f) return false;
        int n = num_args(e);
        if(n != nargs) return false;
        for(int i = 0; i < nargs; i++)
            args[i] = arg(e,i);
        return true;
    }

    // see if the given formula can be interpreted as
    // an axiom instance (e.g., an array axiom instance).
    // if so, add it to "antes" in an appropriate frame.
    // this may require "localization"
  
    void get_axiom_instance(ast e){

        // "store" axiom
        // (or (= w q) (= (select (store a1 w y) q) (select a1 q)))
        // std::cout << "ax: "; show(e);
        ast lits[2],eq_ops_l[2],eq_ops_r[2],sel_ops[2], sto_ops[3], sel_ops2[2] ; 
        if(match_or(e,lits,2))
            if(match_op(lits[0],Equal,eq_ops_l,2))
                if(match_op(lits[1],Equal,eq_ops_r,2))
                    for(int i = 0; i < 2; i++){ // try the second equality both ways
                        if(match_op(eq_ops_r[0],Select,sel_ops,2))
                            if(match_op(sel_ops[0],Store,sto_ops,3))
                                if(match_op(eq_ops_r[1],Select,sel_ops2,2))
                                    for(int j = 0; j < 2; j++){ // try the first equality both ways
                                        if(eq_ops_l[0] == sto_ops[1]
                                           && eq_ops_l[1] == sel_ops[1]
                                           && eq_ops_l[1] == sel_ops2[1]
                                           && sto_ops[0] == sel_ops2[0])
                                            if(is_local(sel_ops[0])) // store term must be local
                                                {    
                                                    ast sto = sel_ops[0];
                                                    ast addr = localize_term(eq_ops_l[1],ast_scope(sto));
                                                    ast res = make(Or,
                                                                   make(Equal,eq_ops_l[0],addr),
                                                                   make(Equal,
                                                                        make(Select,sto,addr),
                                                                        make(Select,sel_ops2[0],addr)));
                                                    // int frame = range_min(ast_scope(res)); TODO
                                                    // antes.push_back(std::pair<ast,int>(res,frame));
                                                    return;
                                                }
                                        std::swap(eq_ops_l[0],eq_ops_l[1]);
                                    }
                        std::swap(eq_ops_r[0],eq_ops_r[1]);
                    }
    }

    // a quantifier instantation looks like (~ forall x. P) \/ P[z/x]
    // we need to find a time frame for P, then localize P[z/x] in this frame

    void get_quantifier_instance(ast e){
        ast disjs[2];
        if(match_or(e,disjs,2)){
            if(is_local(disjs[0])){
                ast res = localize_term(disjs[1], ast_scope(disjs[0]));
                // int frame = range_min(ast_scope(res)); TODO
                // antes.push_back(std::pair<ast,int>(res,frame));
                return;
            }
        }
    }

    ast get_judgement(ast proof){
        ast con = from_ast(conc(proof));
        AstSet &hyps = get_hyps(proof);
        std::vector<ast> hyps_vec;
        for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
            hyps_vec.push_back(*it);
        if(hyps_vec.size() == 0) return con;
        con = make(Or,mk_not(make(And,hyps_vec)),con);
        return con;
    }

    // does variable occur in expression?
    int occurs_in1(ast var, ast e){
        std::pair<ast,bool> foo(e,false);
        std::pair<AstToBool::iterator,bool> bar = occurs_in_memo.insert(foo);
        bool &res = bar.first->second;
        if(bar.second){
            if(e == var) res = true;
            int nargs = num_args(e);
            for(int i = 0; i < nargs; i++)
                res |= occurs_in1(var,arg(e,i));
        }
        return res;
    }

    int occurs_in(ast var, ast e){
        occurs_in_memo.clear();
        return occurs_in1(var,e);
    }
  
    // find a controlling equality for a given variable v in a term
    // a controlling equality is of the form v = t, which, being
    // false would force the formula to have the specifid truth value
    // returns t, or null if no such

    ast cont_eq(bool truth, ast v, ast e){
        if(is_not(e)) return cont_eq(!truth,v,arg(e,0));
        if(cont_eq_memo.find(e) != cont_eq_memo.end())
            return ast();
        cont_eq_memo.insert(e);
        if(!truth && op(e) == Equal){
            if(arg(e,0) == v) return(arg(e,1));
            if(arg(e,1) == v) return(arg(e,0));
        }
        if((!truth && op(e) == And) || (truth && op(e) == Or)){
            int nargs = num_args(e);
            for(int i = 0; i < nargs; i++){
                ast res = cont_eq(truth, v, arg(e,i));
                if(!res.null()) return res;
            }
        }
        return ast();
    }

    // substitute a term t for unbound occurrences of variable v in e
  
    ast subst(ast var, ast t, ast e){
        if(e == var) return t;
        std::pair<ast,ast> foo(e,ast());
        std::pair<AstToAst::iterator,bool> bar = subst_memo.insert(foo);
        ast &res = bar.first->second;
        if(bar.second){
            int nargs = num_args(e);
            std::vector<ast> args(nargs);
            for(int i = 0; i < nargs; i++)
                args[i] = subst(var,t,arg(e,i));
            opr f = op(e);
            if(f == Equal && args[0] == args[1]) res = mk_true();
            else res = clone(e,args);
        }
        return res;
    }

    // apply a quantifier to a formula, with some optimizations
    // 1) bound variable does not occur -> no quantifier
    // 2) bound variable must be equal to some term -> substitute

    ast apply_quant(opr quantifier, ast var, ast e){
        if(!occurs_in(var,e))return e;
        cont_eq_memo.clear();
        ast cterm = cont_eq(quantifier == Forall, var, e);
        if(!cterm.null()){
            subst_memo.clear();
            return subst(var,cterm,e);
        }
        std::vector<ast> bvs; bvs.push_back(var);
        return make_quant(quantifier,bvs,e);
    }

    // add quantifiers over the localization vars
    // to an interpolant for frames lo-hi

    ast add_quants(ast e, int lo, int hi){
        for(int i = localization_vars.size() - 1; i >= 0; i--){
            LocVar &lv = localization_vars[i];
            opr quantifier = (lv.frame >= lo && lv.frame <= hi) ? Exists : Forall; 
            e = apply_quant(quantifier,lv.var,e);
        }
        return e;
    }

    int get_lits_locality(std::vector<ast> &lits){
        range rng = range_full();
        for(std::vector<ast>::iterator it = lits.begin(), en = lits.end(); it != en; ++it){
            ast lit = *it;
            rng = range_glb(rng,ast_scope(lit));
        }
        if(range_is_empty(rng)) return -1;
    int hi = range_max(rng);
        if(hi >= frames) return frames - 1;
        return hi;
    }
#endif

    int num_lits(ast ast){
        opr dk = op(ast);
        if(dk == False)
            return 0;
        if(dk == Or){
            unsigned nargs = num_args(ast);
            int n = 0;
            for(unsigned i = 0; i < nargs; i++) // do all the sub_terms
                n += num_lits(arg(ast,i));
            return n;
        }
        else 
            return 1;
    }

    void symbols_out_of_scope_rec(hash_set<ast> &memo, hash_set<symb> &symb_memo, int frame, const ast &t){
        if(memo.find(t) != memo.end())
            return;
        memo.insert(t);
        if(op(t) == Uninterpreted){
            symb s = sym(t);
            range r = sym_range(s);
            if(!in_range(frame,r) && symb_memo.find(s) == symb_memo.end()){
                std::cout << string_of_symbol(s) << "\n";
                symb_memo.insert(s);
            }
        }
        int nargs = num_args(t);
        for(int i = 0; i < nargs; i++)
            symbols_out_of_scope_rec(memo,symb_memo,frame,arg(t,i));
    }

    void symbols_out_of_scope(int frame, const ast &t){
        hash_set<ast> memo;
        hash_set<symb> symb_memo;
        symbols_out_of_scope_rec(memo,symb_memo,frame,t);
    }

    void conc_symbols_out_of_scope(int frame, const ast &t){
        symbols_out_of_scope(frame,conc(t));
    }

    std::vector<ast> lit_trace;
    hash_set<ast> marked_proofs;

    bool proof_has_lit(const ast &proof, const ast &lit){
        AstSet &hyps = get_hyps(proof);
        if(hyps.find(mk_not(lit)) != hyps.end())
            return true;
        std::vector<ast> lits;
        ast con = conc(proof);
        get_Z3_lits(con, lits);
        for(unsigned i = 0; i < lits.size(); i++)
            if(lits[i] == lit)
                return true;
        return false;
    }


    void trace_lit_rec(const ast &lit, const ast &proof, AstHashSet &memo){
        if(memo.find(proof) == memo.end()){
            memo.insert(proof);
            AstSet &hyps = get_hyps(proof);
            std::vector<ast> lits;
            for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
                lits.push_back(mk_not(*it));
            ast con = conc(proof);
            get_Z3_lits(con, lits);
            for(unsigned i = 0; i < lits.size(); i++){
                if(lits[i] == lit){
                    print_expr(std::cout,proof);
                    std::cout << "\n";
                    marked_proofs.insert(proof);
                    pfrule dk = pr(proof);
                    if(dk == PR_UNIT_RESOLUTION || dk == PR_LEMMA){
                        unsigned nprems = num_prems(proof);
                        for(unsigned i = 0; i < nprems; i++){
                            ast arg = prem(proof,i);
                            trace_lit_rec(lit,arg,memo);
                        }
                    }
                    else
                        lit_trace.push_back(proof);
                }
            }
        }
    }
  
    ast traced_lit;

    int trace_lit(const ast &lit, const ast &proof){
        marked_proofs.clear();
        lit_trace.clear();
        traced_lit = lit;
        AstHashSet memo;
        trace_lit_rec(lit,proof,memo);
        return lit_trace.size();
    }

    bool is_literal_or_lit_iff(const ast &lit){
        if(my_is_literal(lit)) return true;
        if(op(lit) == Iff){
            return my_is_literal(arg(lit,0)) && my_is_literal(arg(lit,1));
        }
        return false;
    }

    bool my_is_literal(const ast &lit){
        ast abslit = is_not(lit) ? arg(lit,0) : lit;
        int f = op(abslit);
        return !(f == And || f == Or || f == Iff);
    }

    hash_map<int,ast> asts_by_id;

    void print_lit(const ast &lit){
        ast abslit = is_not(lit) ? arg(lit,0) : lit;
        if(!is_literal_or_lit_iff(lit)){
            if(is_not(lit)) std::cout << "~";
            int id = ast_id(abslit);
            asts_by_id[id] = abslit;
            std::cout << "[" << id << "]";
        }
        else
            print_expr(std::cout,lit);
    }

    void expand(int id){
        if(asts_by_id.find(id) == asts_by_id.end())
            std::cout << "undefined\n";
        else {
            ast lit = asts_by_id[id];
            std::string s = string_of_symbol(sym(lit));
            std::cout << "(" << s;
            unsigned nargs = num_args(lit);
            for(unsigned i = 0; i < nargs; i++){
                std::cout << " ";
                print_lit(arg(lit,i));
            }
            std::cout << ")\n";;
        }
    }

    void show_lit(const ast &lit){
        print_lit(lit);
        std::cout << "\n";
    }

    void print_z3_lit(const ast &a){
        print_lit(from_ast(a));
    }

    void show_z3_lit(const ast &a){
        print_z3_lit(a);
        std::cout << "\n";
    }

  
    void show_con(const ast &proof, bool brief){
        if(!traced_lit.null() && proof_has_lit(proof,traced_lit))
            std::cout << "(*) ";
        ast con = conc(proof);
        AstSet &hyps = get_hyps(proof);
        int count = 0;
        for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it){
            if(brief && ++count > 5){
                std::cout << "... ";
                break;
            }
            print_lit(*it);
            std::cout << " ";
        }
        std::cout << "|- ";
        std::vector<ast> lits;
        get_Z3_lits(con,lits);
        for(unsigned i = 0; i < lits.size(); i++){
            print_lit(lits[i]);
            std::cout << " ";
        }
        range r = ast_scope(con);
        std::cout << " {" << r.lo << "," << r.hi << "}";
        std::cout << "\n";
    }

    void show_step(const  ast &proof){
        std::cout << "\n";
        unsigned nprems = num_prems(proof);
        for(unsigned i = 0; i < nprems; i++){
            std::cout << "(" << i << ") ";
            ast arg = prem(proof,i);
            show_con(arg,true);
        }
        std::cout << "|------ ";
        std::cout << string_of_symbol(sym(proof)) << "\n";
        show_con(proof,false);
    }

    void show_marked( const ast &proof){
        std::cout << "\n";
        unsigned nprems = num_prems(proof);
        for(unsigned i = 0; i < nprems; i++){
            ast arg = prem(proof,i);
            if(!traced_lit.null() && proof_has_lit(arg,traced_lit)){
                std::cout << "(" << i << ") ";
                show_con(arg,true);
            }
        }
    }

    std::vector<ast> pfhist;
    int pfhist_pos;
  
    void pfgoto(const ast &proof){
        if(pfhist.size() == 0)
            pfhist_pos = 0;
        else pfhist_pos++;
        pfhist.resize(pfhist_pos);
        pfhist.push_back(proof);
        show_step(proof);
    }

  
    void pfback(){
        if(pfhist_pos > 0){
            pfhist_pos--;
            show_step(pfhist[pfhist_pos]);
        }
    }

    void pffwd(){
        if(pfhist_pos < ((int)pfhist.size()) - 1){
            pfhist_pos++;
            show_step(pfhist[pfhist_pos]);
        }
    }

    void pfprem(int i){
        if(pfhist.size() > 0){
            ast proof = pfhist[pfhist_pos];
            unsigned nprems = num_prems(proof);
            if(i >= 0 && i < (int)nprems)
                pfgoto(prem(proof,i));
        }
    }



    // translate a unit resolution sequence
    Iproof::node translate_ur(ast proof){
        ast prem0 = prem(proof,0);
        Iproof::node itp = translate_main(prem0,true);
        std::vector<ast> clause;
        ast conc0 = conc(prem0);
        int nprems = num_prems(proof);
        if(nprems == 2 && conc0 == mk_not(conc(prem(proof,1))))
            clause.push_back(conc0);
        else
            get_Z3_lits(conc0,clause);
        for(int position = 1; position < nprems; position++){
            ast ante =  prem(proof,position);
            ast pnode = conc(ante);
            ast pnode_abs = !is_not(pnode) ? pnode : mk_not(pnode);
            Iproof::node neg = itp;
            Iproof::node pos = translate_main(ante, false);
            if(is_not(pnode)){
                pnode = mk_not(pnode);
                std::swap(neg,pos);
            }
            std::vector<ast> unit(1);
            unit[0] = conc(ante);
            resolve(mk_not(conc(ante)),clause,unit);
            itp = iproof->make_resolution(pnode,clause,neg,pos);
        }
        return itp;
    }

    // get an inequality in the form 0 <= t where t is a linear term
    ast rhs_normalize_inequality(const ast &ineq){
        ast zero = make_int("0");
        ast thing = make(Leq,zero,zero);
        linear_comb(thing,make_int("1"),ineq);
        thing = simplify_ineq(thing);
        return thing;
    }

    bool check_farkas(const std::vector<ast> &prems, const ast &con){
        ast zero = make_int("0");
        ast thing = make(Leq,zero,zero);
        for(unsigned i = 0; i < prems.size(); i++)
            linear_comb(thing,make_int(rational(1)),prems[i]);
        linear_comb(thing,make_int(rational(-1)),con);
        thing = simplify_ineq(thing);
        return arg(thing,1) == make_int(rational(0));
    }

    // get an inequality in the form t <= c or t < c, there t is affine and c constant
    ast normalize_inequality(const ast &ineq){
        ast zero = make_int("0");
        ast thing = make(Leq,zero,zero);
        linear_comb(thing,make_int("1"),ineq);
        thing = simplify_ineq(thing);
        ast lhs = arg(thing,0);
        ast rhs = arg(thing,1);
        opr o = op(rhs);
        if(o != Numeral){
            if(op(rhs) == Plus){
                int nargs = num_args(rhs);
                ast const_term = zero;
                int i = 0;
                if(nargs > 0 && op(arg(rhs,0)) == Numeral){
                    const_term = arg(rhs,0);
                    i++;
                }
                if(i < nargs){
                    std::vector<ast> non_const;
                    for(; i < nargs; i++)
                        non_const.push_back(arg(rhs,i));
                    lhs = make(Sub,lhs,make(Plus,non_const));
                }
                rhs = const_term;
            }
            else {
                lhs = make(Sub,lhs,make(Plus,rhs));
                rhs = zero;
            }
            lhs = z3_simplify(lhs);
            rhs = z3_simplify(rhs);
            thing = make(op(thing),lhs,rhs);
        }
        return thing;
    }

    void get_linear_coefficients(const ast &t, std::vector<rational> &coeffs){
        if(op(t) == Plus){
            int nargs = num_args(t);
            for(int i = 0; i < nargs; i++)
                coeffs.push_back(get_coeff(arg(t,i)));
        }
        else
            coeffs.push_back(get_coeff(t));
    }

    /* given an affine term t, get the GCD of the coefficients in t. */
    ast gcd_of_coefficients(const ast &t){
        std::vector<rational> coeffs;
        get_linear_coefficients(t,coeffs);
        if(coeffs.size() == 0)
            return make_int("1"); // arbitrary
        rational d = abs(coeffs[0]);
        for(unsigned i = 1; i < coeffs.size(); i++){
            d = gcd(d,coeffs[i]);
        }
        return make_int(d);
    }

    ast get_bounded_variable(const ast &ineq, bool &lb){
        ast nineq = normalize_inequality(ineq);
        ast lhs = arg(nineq,0);
        switch(op(lhs)){
        case Uninterpreted: 
            lb = false;
            return lhs;
        case Times:
            if(arg(lhs,0) == make_int(rational(1)))
                lb = false;
            else if(arg(lhs,0) == make_int(rational(-1)))
                lb = true;
            else 
                throw unsupported();
            return arg(lhs,1);
        default:
            throw unsupported();
        }
    }

    rational get_term_coefficient(const ast &t1, const ast &v){
        ast t = arg(normalize_inequality(t1),0);
        if(op(t) == Plus){
            int nargs = num_args(t);
            for(int i = 0; i < nargs; i++){
                if(get_linear_var(arg(t,i)) == v)
                    return get_coeff(arg(t,i));
            }
        }
        else
            if(get_linear_var(t) == v)
                return get_coeff(t);
        return rational(0);
    }


    Iproof::node GCDtoDivRule(const ast &proof, bool pol, std::vector<rational> &coeffs, std::vector<Iproof::node> &prems, ast &cut_con){
        // gather the summands of the desired polarity
        std::vector<Iproof::node>  my_prems;
        std::vector<ast>  my_coeffs;
        std::vector<Iproof::node>  my_prem_cons;
        for(unsigned i = pol ? 0 : 1; i < coeffs.size(); i+= 2){
            rational &c = coeffs[i];
            if(c.is_pos()){
                my_prems.push_back(prems[i]);
                my_coeffs.push_back(make_int(c));
                my_prem_cons.push_back(conc(prem(proof,i)));
            }
            else if(c.is_neg()){
                int j = (i % 2 == 0) ? i + 1 : i - 1;
                my_prems.push_back(prems[j]);
                my_coeffs.push_back(make_int(-coeffs[j]));
                my_prem_cons.push_back(conc(prem(proof,j)));
            }
        }
        ast my_con = sum_inequalities(my_coeffs,my_prem_cons);

        // handle generalized GCD test. sadly, we dont' get the coefficients...
        if(coeffs[0].is_zero()){
            bool lb;
            int xtra_prem = 0;
            ast bv = get_bounded_variable(conc(prem(proof,0)),lb);
            rational bv_coeff = get_term_coefficient(my_con,bv);
            if(bv_coeff.is_pos() != lb)
                xtra_prem = 1;
            if(bv_coeff.is_neg())
                bv_coeff = -bv_coeff;

            my_prems.push_back(prems[xtra_prem]);
            my_coeffs.push_back(make_int(bv_coeff));
            my_prem_cons.push_back(conc(prem(proof,xtra_prem)));
            my_con = sum_inequalities(my_coeffs,my_prem_cons);
        }

        my_con = normalize_inequality(my_con);
        Iproof::node hyp = iproof->make_hypothesis(mk_not(my_con));
        my_prems.push_back(hyp);
        my_coeffs.push_back(make_int("1"));
        my_prem_cons.push_back(mk_not(my_con));
        Iproof::node res = iproof->make_farkas(mk_false(),my_prems,my_prem_cons,my_coeffs);

        ast t = arg(my_con,0);
        ast c = arg(my_con,1);
        ast d = gcd_of_coefficients(t);
        t = z3_simplify(mk_idiv(t,d));
        c = z3_simplify(mk_idiv(c,d));
        cut_con = make(op(my_con),t,c);
        return iproof->make_cut_rule(my_con,d,cut_con,res);
    }


    rational get_first_coefficient(const ast &t, ast &v){
        if(op(t) == Plus){
            unsigned best_id = UINT_MAX;
            rational best_coeff(0);
            int nargs = num_args(t);
            for(int i = 0; i < nargs; i++)
                if(op(arg(t,i)) != Numeral){
                    ast lv = get_linear_var(arg(t,i));
                    unsigned id = ast_id(lv);
                    if(id < best_id) {
                        v = lv;
                        best_id = id;
                        best_coeff = get_coeff(arg(t,i));
                    }
                }
            return best_coeff;
        }
        else
            if(op(t) != Numeral)
                return(get_coeff(t));
        return rational(0);
    }

    ast divide_inequalities(const ast &x, const ast&y){
        ast xvar, yvar;
        rational xcoeff = get_first_coefficient(arg(x,0),xvar);
        rational ycoeff = get_first_coefficient(arg(y,0),yvar);
        if(xcoeff == rational(0) || ycoeff == rational(0) || xvar != yvar)
            throw iz3_exception("bad assign-bounds lemma");
        rational ratio = xcoeff/ycoeff;
        if(denominator(ratio) != rational(1))
            throw iz3_exception("bad assign-bounds lemma");
        return make_int(ratio); // better be integer!
    }

    ast AssignBounds2Farkas(const ast &proof, const ast &con){
        std::vector<ast> farkas_coeffs;
        get_assign_bounds_coeffs(proof,farkas_coeffs);
        int nargs = num_args(con);
        if(nargs != (int)(farkas_coeffs.size()))
            throw iz3_exception("bad assign-bounds theory lemma");
#if 0
        if(farkas_coeffs[0] != make_int(rational(1)))
            farkas_coeffs[0] = make_int(rational(1));
#else
        std::vector<ast> lits, lit_coeffs;
        for(int i = 1; i < nargs; i++){
            lits.push_back(mk_not(arg(con,i)));
            lit_coeffs.push_back(farkas_coeffs[i]);
        }
        ast sum = normalize_inequality(sum_inequalities(lit_coeffs,lits));
        ast conseq = normalize_inequality(arg(con,0));
        ast d = divide_inequalities(sum,conseq);
#if 0
        if(d != farkas_coeffs[0])
            std::cout << "wow!\n";
#endif
        farkas_coeffs[0] = d;
#endif
        std::vector<ast> my_coeffs;
        std::vector<ast> my_cons;
        for(int i = 1; i < nargs; i++){
            my_cons.push_back(mk_not(arg(con,i)));
            my_coeffs.push_back(farkas_coeffs[i]);
        }
        ast farkas_con = normalize_inequality(sum_inequalities(my_coeffs,my_cons,true /* round_off */));
        my_cons.push_back(mk_not(farkas_con));
        my_coeffs.push_back(make_int("1"));
        std::vector<Iproof::node> my_hyps;
        for(int i = 0; i < nargs; i++)
            my_hyps.push_back(iproof->make_hypothesis(my_cons[i]));
        ast res = iproof->make_farkas(mk_false(),my_hyps,my_cons,my_coeffs);
        res = iproof->make_cut_rule(farkas_con,farkas_coeffs[0],arg(con,0),res);
        return res;
    }

    ast AssignBoundsRule2Farkas(const ast &proof, const ast &con, std::vector<Iproof::node> prems){
        std::vector<ast> farkas_coeffs;
        get_assign_bounds_rule_coeffs(proof,farkas_coeffs);
        int nargs = num_prems(proof)+1;
        if(nargs != (int)(farkas_coeffs.size()))
            throw iz3_exception("bad assign-bounds theory lemma");
#if 0
        if(farkas_coeffs[0] != make_int(rational(1)))
            farkas_coeffs[0] = make_int(rational(1));
#else
        std::vector<ast> lits, lit_coeffs;
        for(int i = 1; i < nargs; i++){
            lits.push_back(conc(prem(proof,i-1)));
            lit_coeffs.push_back(farkas_coeffs[i]);
        }
        ast sum = normalize_inequality(sum_inequalities(lit_coeffs,lits));
        ast conseq = normalize_inequality(con);
        ast d = divide_inequalities(sum,conseq);
#if 0
        if(d != farkas_coeffs[0])
            std::cout << "wow!\n";
#endif
        farkas_coeffs[0] = d;
#endif
        std::vector<ast> my_coeffs;
        std::vector<ast> my_cons;
        for(int i = 1; i < nargs; i++){
            my_cons.push_back(conc(prem(proof,i-1)));
            my_coeffs.push_back(farkas_coeffs[i]);
        }
        ast farkas_con = normalize_inequality(sum_inequalities(my_coeffs,my_cons,true /* round_off */));
        std::vector<Iproof::node> my_hyps;
        for(int i = 1; i < nargs; i++)
            my_hyps.push_back(prems[i-1]);
        my_cons.push_back(mk_not(farkas_con));
        my_coeffs.push_back(make_int("1"));
        my_hyps.push_back(iproof->make_hypothesis(mk_not(farkas_con)));    
        ast res = iproof->make_farkas(mk_false(),my_hyps,my_cons,my_coeffs);
        res = iproof->make_cut_rule(farkas_con,farkas_coeffs[0],conc(proof),res);
        return res;
    }

    ast GomoryCutRule2Farkas(const ast &proof, const ast &con, std::vector<Iproof::node> prems){
        std::vector<Iproof::node>  my_prems = prems;
        std::vector<ast>  my_coeffs;
        std::vector<Iproof::node>  my_prem_cons;
        get_gomory_cut_coeffs(proof,my_coeffs);
        int nargs = num_prems(proof);
        if(nargs != (int)(my_coeffs.size()))
            throw "bad gomory-cut theory lemma";
        for(int i = 0; i < nargs; i++)
            my_prem_cons.push_back(conc(prem(proof,i)));
        ast my_con = normalize_inequality(sum_inequalities(my_coeffs,my_prem_cons));
        Iproof::node hyp = iproof->make_hypothesis(mk_not(my_con));
        my_prems.push_back(hyp);
        my_coeffs.push_back(make_int("1"));
        my_prem_cons.push_back(mk_not(my_con));
        Iproof::node res = iproof->make_farkas(mk_false(),my_prems,my_prem_cons,my_coeffs);
        ast t = arg(my_con,0);
        ast c = arg(my_con,1);
        ast d = gcd_of_coefficients(t);
        t = z3_simplify(mk_idiv(t,d));
        c = z3_simplify(mk_idiv(c,d));
        ast cut_con = make(op(my_con),t,c);
        return iproof->make_cut_rule(my_con,d,cut_con,res);
    }

    Iproof::node RewriteClause(Iproof::node clause, const ast &rew){
        if(pr(rew) == PR_MONOTONICITY){
            int nequivs = num_prems(rew);
            for(int i = 0; i < nequivs; i++){
                Iproof::node equiv_pf = translate_main(prem(rew,i),false);
                ast equiv = conc(prem(rew,i));
                clause = iproof->make_mp(equiv,clause,equiv_pf);
            }
            return clause;
        }
        if(pr(rew) == PR_TRANSITIVITY){
            clause = RewriteClause(clause,prem(rew,0));
            clause = RewriteClause(clause,prem(rew,1));
            return clause;
        }
        if(pr(rew) == PR_REWRITE){
            return clause; // just hope the rewrite does nothing!
        }
        throw unsupported();
    }


    // Following code is for elimination of "commutativity" axiom

    Iproof::node make_commuted_modus_ponens(const ast &proof, const std::vector<Iproof::node> &args){
        ast pf = arg(args[1],0);
        ast comm_equiv = arg(args[1],1); // equivalence relation with possible commutations
        ast P = conc(prem(proof,0));
        ast Q = conc(proof);
        Iproof::node P_pf = args[0];
        ast P_comm = arg(comm_equiv,0);
        ast Q_comm = arg(comm_equiv,1);
        if(P != P_comm)
            P_pf = iproof->make_symmetry(P_comm,P,P_pf);
        Iproof::node res = iproof->make_mp(comm_equiv,P_pf,pf);
        if(Q != Q_comm)
            res = iproof->make_symmetry(Q,Q_comm,res);
        return res;
    }

    Iproof::node make_commuted_monotonicity(const ast &proof, const std::vector<Iproof::node> &args){
        ast pf = arg(args[0],0);
        ast comm_equiv = arg(args[0],1); // equivalence relation with possible commutations
        ast con = make(Iff,make(Not,arg(comm_equiv,0)),make(Not,arg(comm_equiv,1)));
        std::vector<ast> eqs; eqs.push_back(comm_equiv);
        std::vector<ast> pfs; pfs.push_back(pf);
        ast res = iproof->make_congruence(eqs,con,pfs);
        res = make(commute,res,con);
        return res;
    }

    Iproof::node make_commuted_symmetry(const ast &proof, const std::vector<Iproof::node> &args){
        ast pf = arg(args[0],0);
        ast comm_equiv = arg(args[0],1); // equivalence relation with possible commutations
        ast con = make(Iff,arg(comm_equiv,1),arg(comm_equiv,0));
        ast res = iproof->make_symmetry(con,comm_equiv,pf);
        res = make(commute,res,con);
        return res;
    }

    void unpack_commuted(const ast &proof, const ast &cm, ast &pf, ast &comm_equiv){
        if(sym(cm) == commute){
            pf = arg(cm,0);
            comm_equiv = arg(cm,1);
        }
        else {
            pf = cm;
            comm_equiv = conc(proof);
        }
    }

    Iproof::node make_commuted_transitivity(const ast &proof, const std::vector<Iproof::node> &args){
        ast pf[2], comm_equiv[2];
        for(int i = 0; i < 2; i++)
            unpack_commuted(prem(proof,i),args[i],pf[i],comm_equiv[i]);
        if(!(arg(comm_equiv[0],1) == arg(comm_equiv[1],0))){
            ast tw = twist(prem(proof,1));
            ast np = translate_main(tw,false); 
            unpack_commuted(tw,np,pf[1],comm_equiv[1]);
        }      
        ast con = make(Iff,arg(comm_equiv[0],0),arg(comm_equiv[1],1));
        ast res = iproof->make_transitivity(arg(comm_equiv[0],0),arg(comm_equiv[0],1),arg(comm_equiv[1],1),pf[0],pf[1]);
        res = make(commute,res,con);
        return res;
    }

    ast commute_equality(const ast &eq){
        return make(Equal,arg(eq,1),arg(eq,0));
    }
  
    ast commute_equality_iff(const ast &con){
        if(op(con) != Iff || op(arg(con,0)) != Equal)
            throw unsupported();
        return make(Iff,commute_equality(arg(con,0)),commute_equality(arg(con,1)));
    }
  
    // convert a proof of a=b <-> c=d into a proof of b=a <-> d=c
    // TODO: memoize this?
    ast twist(const ast &proof){
        pfrule dk = pr(proof);
        ast con = commute_equality_iff(conc(proof));
        int n = num_prems(proof);
        std::vector<ast> prs(n);
        if(dk == PR_MONOTONICITY){
            for(int i = 0; i < n; i++)
                prs[i] = prem(proof,i);
        }      
        else
            for(int i = 0; i < n; i++)
                prs[i] = twist(prem(proof,i));
        switch(dk){
        case PR_MONOTONICITY:
        case PR_SYMMETRY:
        case PR_TRANSITIVITY:
        case PR_COMMUTATIVITY:
            prs.push_back(con);
            return clone(proof,prs);
        default:
            throw unsupported();
        }
    }

    struct TermLt {
        iz3mgr &m;
        bool operator()(const ast &x, const ast &y){
            unsigned xid = m.ast_id(x);
            unsigned yid = m.ast_id(y);
            return xid < yid;
        }
        TermLt(iz3mgr &_m) : m(_m) {}
    };

    void SortTerms(std::vector<ast> &terms){
        TermLt foo(*this);
        std::sort(terms.begin(),terms.end(),foo);
    }

    ast SortSum(const ast &t){
        if(!(op(t) == Plus))
            return t;
        int nargs = num_args(t);
        if(nargs < 2) return t;
        std::vector<ast> args(nargs);
        for(int i = 0; i < nargs; i++)
            args[i] = arg(t,i);
        SortTerms(args);
        return make(Plus,args);
    }

    void get_sum_as_vector(const ast &t, std::vector<rational> &coeffs, std::vector<ast> &vars){
        if(!(op(t) == Plus)){
            coeffs.push_back(get_coeff(t));
            vars.push_back(get_linear_var(t));
        }
        else {
            int nargs = num_args(t);
            for(int i = 0; i < nargs; i++)
                get_sum_as_vector(arg(t,i),coeffs,vars);
        }
    }

    ast replace_summands_with_fresh_vars(const ast &t, hash_map<ast,ast> &map){
        if(op(t) == Plus){
            int nargs = num_args(t);
            std::vector<ast> args(nargs);
            for(int i = 0; i < nargs; i++)
                args[i] = replace_summands_with_fresh_vars(arg(t,i),map);
            return make(Plus,args);
        }
        if(op(t) == Times)
            return make(Times,arg(t,0),replace_summands_with_fresh_vars(arg(t,1),map));
        if(map.find(t) == map.end())
            map[t] =  mk_fresh_constant("@s",get_type(t));
        return map[t];
    }

    rational lcd(const std::vector<rational> &rats){
        rational res = rational(1);
        for(unsigned i = 0; i < rats.size(); i++){
            res = lcm(res,denominator(rats[i]));
        }
        return res;
    } 

    Iproof::node reconstruct_farkas_with_dual(const std::vector<ast> &prems, const std::vector<Iproof::node> &pfs, const ast &con){
        int nprems = prems.size();
        std::vector<ast> npcons(nprems);
        hash_map<ast,ast> pain_map; // not needed
        for(int i = 0; i < nprems; i++){
            npcons[i] = painfully_normalize_ineq(conc(prems[i]),pain_map);
            if(op(npcons[i]) == Lt){
                ast constval = z3_simplify(make(Sub,arg(npcons[i],1),make_int(rational(1))));
                npcons[i] = make(Leq,arg(npcons[i],0),constval);
            }
        }
        ast ncon = painfully_normalize_ineq(mk_not(con),pain_map);
        npcons.push_back(ncon);

        hash_map<ast,ast> dual_map;
        std::vector<ast> cvec, vars_seen;
        m().enable_int_real_coercions(true);
        ast rhs = make_real(rational(0));
        for(unsigned i = 0; i < npcons.size(); i++){
            ast c= mk_fresh_constant("@c",real_type());
            cvec.push_back(c);
            ast lhs = arg(npcons[i],0);
            std::vector<rational> coeffs;
            std::vector<ast> vars;
            get_sum_as_vector(lhs,coeffs,vars);
            for(unsigned j = 0; j < coeffs.size(); j++){
                rational coeff = coeffs[j];
                ast var = vars[j];
                if(dual_map.find(var) == dual_map.end()){
                    dual_map[var] = make_real(rational(0));
                    vars_seen.push_back(var);
                }
                ast foo = make(Plus,dual_map[var],make(Times,make_real(coeff),c));
                dual_map[var] = foo;
            }
            rhs = make(Plus,rhs,make(Times,c,arg(npcons[i],1)));
        }
        std::vector<ast> cnstrs;
        for(unsigned i = 0; i < vars_seen.size(); i++)
            cnstrs.push_back(make(Equal,dual_map[vars_seen[i]],make_real(rational(0))));
        cnstrs.push_back(make(Leq,rhs,make_real(rational(0))));
        for(unsigned i = 0; i < cvec.size() - 1; i++)
            cnstrs.push_back(make(Geq,cvec[i],make_real(rational(0))));
        cnstrs.push_back(make(Equal,cvec.back(),make_real(rational(1))));
        ast new_proof;

        // greedily reduce the core
        for(unsigned i = 0; i < cvec.size() - 1; i++){
            std::vector<ast> dummy;
            cnstrs.push_back(make(Equal,cvec[i],make_real(rational(0))));
            if(!is_sat(cnstrs,new_proof,dummy))
                cnstrs.pop_back();
        }

        std::vector<ast> vals = cvec;
        if(!is_sat(cnstrs,new_proof,vals))
            throw iz3_exception("Proof error!");
        std::vector<rational> rat_farkas_coeffs;
        for(unsigned i = 0; i < cvec.size(); i++){
            ast bar = vals[i];
            rational r;
            if(is_numeral(bar,r))
                rat_farkas_coeffs.push_back(r);
            else
                throw iz3_exception("Proof error!");
        }
        rational the_lcd = lcd(rat_farkas_coeffs);
        std::vector<ast> farkas_coeffs;
        std::vector<Iproof::node> my_prems;
        std::vector<ast> my_pcons;
        for(unsigned i = 0; i < prems.size(); i++){
            ast fc = make_int(rat_farkas_coeffs[i] * the_lcd);
            if(!(fc == make_int(rational(0)))){
                farkas_coeffs.push_back(fc);
                my_prems.push_back(pfs[i]);
                my_pcons.push_back(conc(prems[i]));
            }
        }
        farkas_coeffs.push_back(make_int(the_lcd));
        my_prems.push_back(iproof->make_hypothesis(mk_not(con)));
        my_pcons.push_back(mk_not(con));
    
        Iproof::node res = iproof->make_farkas(mk_false(),my_prems,my_pcons,farkas_coeffs);
        return res;
    }

    ast painfully_normalize_ineq(const ast &ineq, hash_map<ast,ast> &map){
        ast res = normalize_inequality(ineq);
        ast lhs = arg(res,0);
        lhs = replace_summands_with_fresh_vars(lhs,map);
        res = make(op(res),SortSum(lhs),arg(res,1));
        return res;
    }

    Iproof::node painfully_reconstruct_farkas(const std::vector<ast> &prems, const std::vector<Iproof::node> &pfs, const ast &con){
        int nprems = prems.size();
        std::vector<ast> pcons(nprems),npcons(nprems);
        hash_map<ast,ast> pcon_to_pf, npcon_to_pcon, pain_map;
        for(int i = 0; i < nprems; i++){
            pcons[i] = conc(prems[i]);
            npcons[i] = painfully_normalize_ineq(pcons[i],pain_map);
            pcon_to_pf[npcons[i]] = pfs[i];
            npcon_to_pcon[npcons[i]] = pcons[i];
        }
        // ast leq = make(Leq,arg(con,0),arg(con,1));
        ast ncon = painfully_normalize_ineq(mk_not(con),pain_map);
        pcons.push_back(mk_not(con));
        npcons.push_back(ncon);
        // ast assumps = make(And,pcons);
        ast new_proof;
        std::vector<ast> dummy;
        if(is_sat(npcons,new_proof,dummy))
            throw iz3_exception("Proof error!");
        pfrule dk = pr(new_proof);
        int nnp = num_prems(new_proof);
        std::vector<Iproof::node> my_prems;
        std::vector<ast> farkas_coeffs, my_pcons;

        if(dk == PR_TH_LEMMA 
           && get_theory_lemma_theory(new_proof) == ArithTheory
           && get_theory_lemma_kind(new_proof) == FarkasKind)
            get_farkas_coeffs(new_proof,farkas_coeffs);
        else if(dk == PR_UNIT_RESOLUTION && nnp == 2){
            for(int i = 0; i < nprems; i++)
                farkas_coeffs.push_back(make_int(rational(1)));
        }
        else
            return reconstruct_farkas_with_dual(prems,pfs,con);

        for(int i = 0; i < nnp; i++){
            ast p = conc(prem(new_proof,i));
            p = really_normalize_ineq(p);
            if(pcon_to_pf.find(p) != pcon_to_pf.end()){
                my_prems.push_back(pcon_to_pf[p]);
                my_pcons.push_back(npcon_to_pcon[p]);
            }
            else if(p == ncon){
                my_prems.push_back(iproof->make_hypothesis(mk_not(con)));
                my_pcons.push_back(mk_not(con));
            }
            else
                return reconstruct_farkas_with_dual(prems,pfs,con);
        }
        Iproof::node res = iproof->make_farkas(mk_false(),my_prems,my_pcons,farkas_coeffs);
        return res;
    }



    ast really_normalize_ineq(const ast &ineq){
        ast res = normalize_inequality(ineq);
        res = make(op(res),SortSum(arg(res,0)),arg(res,1));
        return res;
    }

    Iproof::node reconstruct_farkas(const std::vector<ast> &prems, const std::vector<Iproof::node> &pfs, const ast &con){
        int nprems = prems.size();
        std::vector<ast> pcons(nprems),npcons(nprems);
        hash_map<ast,ast> pcon_to_pf, npcon_to_pcon;
        for(int i = 0; i < nprems; i++){
            pcons[i] = conc(prems[i]);
            npcons[i] = really_normalize_ineq(pcons[i]);
            pcon_to_pf[npcons[i]] = pfs[i];
            npcon_to_pcon[npcons[i]] = pcons[i];
        }
        // ast leq = make(Leq,arg(con,0),arg(con,1));
        ast ncon = really_normalize_ineq(mk_not(con));
        pcons.push_back(mk_not(con));
        npcons.push_back(ncon);
        // ast assumps = make(And,pcons);
        ast new_proof;
        std::vector<ast> dummy;
        if(is_sat(npcons,new_proof,dummy))
            throw iz3_exception("Proof error!");
        pfrule dk = pr(new_proof);
        int nnp = num_prems(new_proof);
        std::vector<Iproof::node> my_prems;
        std::vector<ast> farkas_coeffs, my_pcons;

        if(dk == PR_TH_LEMMA 
           && get_theory_lemma_theory(new_proof) == ArithTheory
           && get_theory_lemma_kind(new_proof) == FarkasKind)
            get_farkas_coeffs(new_proof,farkas_coeffs);
        else if(dk == PR_UNIT_RESOLUTION && nnp == 2){
            for(int i = 0; i < nprems; i++)
                farkas_coeffs.push_back(make_int(rational(1)));
        }
        else
            return painfully_reconstruct_farkas(prems,pfs,con);

        for(int i = 0; i < nnp; i++){
            ast p = conc(prem(new_proof,i));
            p = really_normalize_ineq(p);
            if(pcon_to_pf.find(p) != pcon_to_pf.end()){
                my_prems.push_back(pcon_to_pf[p]);
                my_pcons.push_back(npcon_to_pcon[p]);
            }
            else if(p == ncon){
                my_prems.push_back(iproof->make_hypothesis(mk_not(con)));
                my_pcons.push_back(mk_not(con));
            }
            else
                return painfully_reconstruct_farkas(prems,pfs,con);
        }
        Iproof::node res = iproof->make_farkas(mk_false(),my_prems,my_pcons,farkas_coeffs);
        return res;
    }

    bool is_eq_propagate(const ast &proof){
        return pr(proof) == PR_TH_LEMMA && get_theory_lemma_theory(proof) == ArithTheory && get_theory_lemma_kind(proof) == EqPropagateKind;
    }

    ast EqPropagate(const ast &con, const std::vector<ast> &prems, const std::vector<Iproof::node> &args){
        Iproof::node fps[2];
        ast ineq_con[2];
        for(int i = 0; i < 2; i++){
            opr o = i == 0 ? Leq : Geq;
            ineq_con[i] = make(o, arg(con,0), arg(con,1));
            fps[i] = reconstruct_farkas(prems,args,ineq_con[i]);
        }
        ast res = iproof->make_leq2eq(arg(con,0), arg(con,1), ineq_con[0], ineq_con[1]);
        std::vector<Iproof::node> dummy_clause;
        for(int i = 0; i < 2; i++)
            res = iproof->make_resolution(ineq_con[i],dummy_clause,res,fps[i]);
        return res;
    }

    ast ArithMysteryRule(const ast &con, const std::vector<ast> &prems, const std::vector<Iproof::node> &args){
        // Hope for the best!
        Iproof::node guess = reconstruct_farkas(prems,args,con);
        return guess;
    }

    struct CannotCombineEqPropagate {};

    void CombineEqPropagateRec(const ast &proof, std::vector<ast> &prems, std::vector<Iproof::node> &args, ast &eqprem){
        if(pr(proof) == PR_TRANSITIVITY && is_eq_propagate(prem(proof,1))){
            CombineEqPropagateRec(prem(proof,0), prems, args, eqprem);
            ast dummy;
            CombineEqPropagateRec(prem(proof,1), prems, args, dummy);
            return;
        }
        if(is_eq_propagate(proof)){
            int nprems = num_prems(proof);
            for(int i = 0; i < nprems; i++){
                prems.push_back(prem(proof,i));
                ast ppf = translate_main(prem(proof,i),false);
                args.push_back(ppf);
            }
            return;
        }
        eqprem = proof;
    }

    ast CombineEqPropagate(const ast &proof){
        std::vector<ast> prems, args;
        ast eq1;
        CombineEqPropagateRec(proof, prems, args, eq1);
        ast eq2con = conc(proof);
        if(!eq1.null())
            eq2con = make(Equal,arg(conc(eq1),1),arg(conc(proof),1));
        ast eq2 = EqPropagate(eq2con,prems,args);
        if(!eq1.null()){
            Iproof::node foo = translate_main(eq1,false);
            eq2 = iproof->make_transitivity(arg(conc(eq1),0), arg(conc(eq1),1), arg(conc(proof),1), foo, eq2);
        }
        return eq2;
    }

    bool get_store_array(const ast &t, ast &res){
        if(op(t) == Store){
            res = t;
            return true;
        }
        int nargs = num_args(t);
        for(int i = 0; i < nargs; i++)
            if(get_store_array(arg(t,i),res))
                return true;
        return false;
    }

    // translate a Z3 proof term into interpolating proof system

    Iproof::node translate_main(ast proof, bool expect_clause = true){
        AstToIpf &tr = translation; 
        hash_map<ast,Iproof::node> &trc = expect_clause ? tr.first : tr.second;
        std::pair<ast,Iproof::node> foo(proof,Iproof::node());
        std::pair<hash_map<ast,Iproof::node>::iterator, bool> bar = trc.insert(foo);
        Iproof::node &res = bar.first->second;
        if(!bar.second) return res;

        // Try the locality rule first

        int frame = get_locality(proof);
        if(frame != -1){
            ast e = from_ast(conc(proof));
            if(frame >= frames) frame = frames - 1;
            std::vector<ast> foo;
            if(expect_clause)
                get_Z3_lits(conc(proof),foo);
            else
                foo.push_back(e);
            AstSet &hyps = get_hyps(proof);
            for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
                foo.push_back(mk_not(*it));
            res = iproof->make_assumption(frame,foo);
            return res;
        }

        // If the proof is not local, break it down by proof rule

        pfrule dk = pr(proof);
        unsigned nprems = num_prems(proof);
        if(dk == PR_UNIT_RESOLUTION){
            res = translate_ur(proof);
        }
        else if(dk == PR_LEMMA){
            ast contra = prem(proof,0); // this is a proof of false from some hyps
            res = translate_main(contra);
            if(!expect_clause){
                std::vector<ast> foo;  // the negations of the hyps form a clause
                foo.push_back(from_ast(conc(proof)));
                AstSet &hyps = get_hyps(proof);
                for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
                    foo.push_back(mk_not(*it));
                res = iproof->make_contra(res,foo);
            }
        }
        else {
            std::vector<ast> lits;
            ast con = conc(proof);
            if(expect_clause)
                get_Z3_lits(con, lits);
            else
                lits.push_back(from_ast(con));

            // pattern match some idioms
            if(dk == PR_MODUS_PONENS && pr(prem(proof,0)) == PR_QUANT_INST){
                if(get_locality_rec(prem(proof,1)) == INT_MAX) {
                    res = iproof->make_axiom(lits);
                    return res;
                }
            }
            if(dk == PR_MODUS_PONENS && expect_clause && op(con) == Or && op(conc(prem(proof,0))) == Or){
                Iproof::node clause = translate_main(prem(proof,0),true);
                res = RewriteClause(clause,prem(proof,1));
                return res;
            }

#if 0
            if(dk == PR_MODUS_PONENS && expect_clause && op(con) == Or)
                std::cout << "foo!\n";
#endif

            // no idea why this shows up
            if(dk == PR_MODUS_PONENS_OEQ){
                if(conc(prem(proof,0)) == con){
                    res = translate_main(prem(proof,0),expect_clause);
                    return res;
                }
                if(expect_clause && op(con) == Or){ // skolemization does this
                    Iproof::node clause = translate_main(prem(proof,0),true);
                    res = RewriteClause(clause,prem(proof,1));
                    return res;
                }
            }
      
#if 0
            if(1 && dk == PR_TRANSITIVITY && pr(prem(proof,1)) == PR_COMMUTATIVITY){
                Iproof::node clause = translate_main(prem(proof,0),true);
                res = make(commute,clause,conc(prem(proof,0))); // HACK -- we depend on Iproof::node being same as ast.
                return res;
            }
      
            if(1 && dk == PR_TRANSITIVITY && pr(prem(proof,0)) == PR_COMMUTATIVITY){
                Iproof::node clause = translate_main(prem(proof,1),true);
                res = make(commute,clause,conc(prem(proof,1))); // HACK -- we depend on Iproof::node being same as ast.
                return res;
            }
#endif

            if(dk == PR_TRANSITIVITY && is_eq_propagate(prem(proof,1))){
                try {
                    res = CombineEqPropagate(proof);
                    return res;
                }
                catch(const CannotCombineEqPropagate &){
                }
            }

            /* this is the symmetry rule for ~=, that is, takes x ~= y and yields y ~= x.
               the proof idiom uses commutativity, monotonicity and mp, but we replace it here
               with symmtrey and resolution, that is, we prove y = x |- x = y, then resolve
               with the proof of ~(x=y) to get ~y=x. */
            if(dk == PR_MODUS_PONENS && pr(prem(proof,1)) == PR_MONOTONICITY && pr(prem(prem(proof,1),0)) == PR_COMMUTATIVITY && num_prems(prem(proof,1)) == 1){
                Iproof::node ante = translate_main(prem(proof,0),false);
                ast eq0 = arg(conc(prem(prem(proof,1),0)),0);
                ast eq1 = arg(conc(prem(prem(proof,1),0)),1);
                Iproof::node eq1hy = iproof->make_hypothesis(eq1);
                Iproof::node eq0pf = iproof->make_symmetry(eq0,eq1,eq1hy);
                std::vector<ast> clause; // just a dummy
                res = iproof->make_resolution(eq0,clause,ante,eq0pf);
                return res;
            }

            /* This idiom takes ~P and Q=P, yielding ~Q. It uses a "rewrite"
               (Q=false) = ~Q. We eliminate the rewrite by using symmetry,
               congruence and modus ponens. */

            if(dk == PR_MODUS_PONENS && pr(prem(proof,1)) == PR_REWRITE && pr(prem(proof,0)) == PR_TRANSITIVITY && pr(prem(prem(proof,0),1)) == PR_IFF_FALSE){
                if(op(con) == Not && arg(con,0) == arg(conc(prem(proof,0)),0)){
                    Iproof::node ante1 = translate_main(prem(prem(proof,0),0),false);
                    Iproof::node ante2 = translate_main(prem(prem(prem(proof,0),1),0),false);
                    ast ante1_con = conc(prem(prem(proof,0),0));
                    ast eq0 = arg(ante1_con,0);
                    ast eq1 = arg(ante1_con,1);
                    ast symm_con = make(Iff,eq1,eq0);
                    Iproof::node ante1s = iproof->make_symmetry(symm_con,ante1_con,ante1);
                    ast cong_con = make(Iff,make(Not,eq1),make(Not,eq0));
                    Iproof::node ante1sc = iproof->make_congruence(symm_con,cong_con,ante1s);
                    res = iproof->make_mp(cong_con,ante2,ante1sc);
                    return res;
                }
            }
      

            // translate all the premises
            std::vector<Iproof::node> args(nprems);
            for(unsigned i = 0; i < nprems; i++)
                args[i] = translate_main(prem(proof,i),false);

            for(unsigned i = 0; i < nprems; i++)
                if(sym(args[i]) == commute
                   && !(dk == PR_TRANSITIVITY || dk == PR_MODUS_PONENS || dk == PR_SYMMETRY ||  (dk == PR_MONOTONICITY && op(arg(con,0)) == Not)))
                    throw unsupported();

            switch(dk){
            case PR_TRANSITIVITY: {
                if(sym(args[0]) == commute || sym(args[1]) == commute)
                    res = make_commuted_transitivity(proof,args);
                else {
                    // assume the premises are x = y, y = z
                    ast x = arg(conc(prem(proof,0)),0);
                    ast y = arg(conc(prem(proof,0)),1);
                    ast z = arg(conc(prem(proof,1)),1);
                    res = iproof->make_transitivity(x,y,z,args[0],args[1]);
                }
                break;
            }
            case PR_QUANT_INTRO:
            case PR_MONOTONICITY:
                {
                    std::vector<ast> eqs; eqs.resize(args.size());
                    for(unsigned i = 0; i < args.size(); i++)
                        eqs[i] = conc(prem(proof,i));
                    if(op(arg(con,0)) == Not && sym(args[0]) == commute)
                        res = make_commuted_monotonicity(proof,args);
                    else
                        res = iproof->make_congruence(eqs,con,args);
                    break;
                }
            case PR_REFLEXIVITY: {
                res = iproof->make_reflexivity(con);
                break;
            }
            case PR_SYMMETRY: {
                if(sym(args[0]) == commute)
                    res = make_commuted_symmetry(proof,args);
                else
                    res = iproof->make_symmetry(con,conc(prem(proof,0)),args[0]);
                break;
            }
            case PR_MODUS_PONENS: {
                if(sym(args[1]) == commute)
                    res = make_commuted_modus_ponens(proof,args);
                else 
                    res = iproof->make_mp(conc(prem(proof,1)),args[0],args[1]);
                break;
            }
            case PR_TH_LEMMA: {
                switch(get_theory_lemma_theory(proof)){
                case ArithTheory:
                    switch(get_theory_lemma_kind(proof)){
                    case FarkasKind: {
                        std::vector<ast> farkas_coeffs, prem_cons;
                        get_farkas_coeffs(proof,farkas_coeffs);
                        if(nprems == 0) {// axiom, not rule
                            int nargs = num_args(con);
                            if(farkas_coeffs.size() != (unsigned)nargs){
                                pfgoto(proof);
                                throw unsupported();
                            }
                            for(int i = 0; i < nargs; i++){
                                ast lit = mk_not(arg(con,i));
                                prem_cons.push_back(lit);
                                args.push_back(iproof->make_hypothesis(lit));
                            }
                        }
                        else {  // rule version (proves false)
                            prem_cons.resize(nprems);
                            for(unsigned i = 0; i < nprems; i++)
                                prem_cons[i] = conc(prem(proof,i));
                        }
                        res = iproof->make_farkas(con,args,prem_cons,farkas_coeffs);
                        break;
                    }
                    case Leq2EqKind: {
                        // conc should be (or x = y (not (leq x y)) (not(leq y z)) )
                        ast xeqy = arg(conc(proof),0);
                        ast x = arg(xeqy,0);
                        ast y = arg(xeqy,1);
                        res = iproof->make_leq2eq(x,y,arg(arg(conc(proof),1),0),arg(arg(conc(proof),2),0));
                        break;
                    }
                    case Eq2LeqKind: {
                        // conc should be (or (not (= x y)) (leq x y))
                        ast xeqy = arg(arg(conc(proof),0),0);
                        ast xleqy = arg(conc(proof),1);
                        ast x = arg(xeqy,0);
                        ast y = arg(xeqy,1);
                        res = iproof->make_eq2leq(x,y,xleqy);
                        break;
                    }
                    case GCDTestKind: {
                        std::vector<rational> farkas_coeffs;
                        get_broken_gcd_test_coeffs(proof,farkas_coeffs);
                        if(farkas_coeffs.size() != nprems){
                            pfgoto(proof);
                            throw unsupported();
                        }
                        std::vector<Iproof::node> my_prems; my_prems.resize(2);
                        std::vector<ast> my_prem_cons; my_prem_cons.resize(2);
                        std::vector<ast> my_farkas_coeffs; my_farkas_coeffs.resize(2);
                        my_prems[0] = GCDtoDivRule(proof, true, farkas_coeffs, args, my_prem_cons[0]);
                        my_prems[1] = GCDtoDivRule(proof, false, farkas_coeffs, args, my_prem_cons[1]);
                        ast con = mk_false();
                        my_farkas_coeffs[0] = my_farkas_coeffs[1] = make_int("1");
                        res = iproof->make_farkas(con,my_prems,my_prem_cons,my_farkas_coeffs);
                        break;
                    }
                    case AssignBoundsKind: {
                        if(args.size() > 0)
                            res =  AssignBoundsRule2Farkas(proof, conc(proof), args);
                        else
                            res = AssignBounds2Farkas(proof,conc(proof));
                        break;
                    }
                    case GomoryCutKind: {
                        if(args.size() > 0)
                            res =  GomoryCutRule2Farkas(proof, conc(proof), args);
                        else
                            throw unsupported();
                        break;
                    }
                    case EqPropagateKind: {
                        std::vector<ast> prems(nprems);
                        for(unsigned i = 0; i < nprems; i++)
                            prems[i] = prem(proof,i);
                        res = EqPropagate(con,prems,args);
                        break;
                    }
                    case ArithMysteryKind: {
                        // Z3 hasn't told us what kind of lemma this is -- maybe we can guess
                        std::vector<ast> prems(nprems);
                        for(unsigned i = 0; i < nprems; i++)
                            prems[i] = prem(proof,i);
                        res = ArithMysteryRule(con,prems,args);
                        break;
                    }
                    default:
                        throw unsupported();
                    }
                    break;
                case ArrayTheory: {// nothing fancy for this
                    ast store_array;
                    if(get_store_array(con,store_array))
                        res = iproof->make_axiom(lits,ast_scope(store_array));
                    else
                        res = iproof->make_axiom(lits); // for array extensionality axiom
                    break;
                }
                default:
                    throw unsupported();
                }
                break;
            }
            case PR_HYPOTHESIS: {
                res = iproof->make_hypothesis(conc(proof));
                break;
            }
            case PR_QUANT_INST: {
                res = iproof->make_axiom(lits);
                break;
            }
            case PR_DEF_AXIOM: { // this should only happen for formulas resulting from quantifier instantiation
                res = iproof->make_axiom(lits);
                break;
            }
            case PR_IFF_TRUE: { // turns p into p <-> true, noop for us
                res = args[0];
                break;
            }
            case PR_IFF_FALSE: { // turns ~p into p <-> false, noop for us
                if(is_local(con))
                    res = args[0];
                else
                    throw unsupported();
                break;
            }
            case PR_COMMUTATIVITY: {
                ast comm_equiv = make(op(con),arg(con,0),arg(con,0));
                ast pf = iproof->make_reflexivity(comm_equiv);
                res = make(commute,pf,comm_equiv);
                break;
            }
            case PR_NOT_OR_ELIM:
            case PR_AND_ELIM: {
                std::vector<ast> rule_ax, res_conc;
                ast piv = conc(prem(proof,0));
                rule_ax.push_back(make(Not,piv));
                rule_ax.push_back(con);
                ast pf = iproof->make_axiom(rule_ax);
                res_conc.push_back(con);
                res = iproof->make_resolution(piv,res_conc,pf,args[0]);
                break;
            }
            default:
                pfgoto(proof);
                assert(0 && "translate_main: unsupported proof rule");
                throw unsupported();
            }
        }

        return res;
    }

    void clear_translation(){
        translation.first.clear();
        translation.second.clear();
    }

    // We actually compute the interpolant here and then produce a proof consisting of just a lemma

    iz3proof::node translate(ast proof, iz3proof &dst){
        std::vector<ast> itps;
        scan_skolems(proof);
        for(int i = 0; i < frames -1; i++){
#ifdef NEW_LOCALITY
            rng = range_downward(i);
            locality.clear();
#endif
            iproof = iz3proof_itp::create(this,range_downward(i),weak_mode());
            try {
                Iproof::node ipf = translate_main(proof);
                ast itp = iproof->interpolate(ipf);
                itps.push_back(itp);
                delete iproof;
                clear_translation();
            }
            catch (const iz3proof_itp::proof_error &) {
                delete iproof;
                clear_translation();
                throw iz3proof::proof_error();
            }
            catch (const unsupported &exc) {
                delete iproof;
                clear_translation();
                throw exc;
            }
        }
        // Very simple proof -- lemma of the empty clause with computed interpolation
        iz3proof::node Ipf = dst.make_lemma(std::vector<ast>(),itps);  // builds result in dst
        return Ipf;
    }

    iz3translation_full(iz3mgr &mgr,
            iz3secondary *_secondary,
                        const std::vector<std::vector<ast> > &cnsts,
            const std::vector<int> &parents,
            const std::vector<ast> &theory)
        : iz3translation(mgr, cnsts, parents, theory)
    {
        frames = cnsts.size();
        traced_lit = ast();
        type boolbooldom[2] = {bool_type(),bool_type()};
        commute = function("@commute",2,boolbooldom,bool_type());
        m().inc_ref(commute);
    }

    ~iz3translation_full(){
        m().dec_ref(commute);
    }
};




#ifdef IZ3_TRANSLATE_FULL

iz3translation *iz3translation::create(iz3mgr &mgr,
                       iz3secondary *secondary,
                       const std::vector<std::vector<ast> > &cnsts,
                       const std::vector<int> &parents,
                       const std::vector<ast> &theory){
    return new iz3translation_full(mgr,secondary,cnsts,parents,theory);
}


#if 1

// This is just to make sure certain methods are compiled, so we can call then from the debugger.

void iz3translation_full_trace_lit(iz3translation_full *p, iz3mgr::ast lit, iz3mgr::ast proof){
    p->trace_lit(lit, proof);
}

void iz3translation_full_show_step(iz3translation_full *p,  iz3mgr::ast proof){
    p->show_step(proof);
}

void iz3translation_full_show_marked(iz3translation_full *p,  iz3mgr::ast proof){
    p->show_marked(proof);
}

void iz3translation_full_show_lit(iz3translation_full *p,  iz3mgr::ast lit){
    p->show_lit(lit);
}

void iz3translation_full_show_z3_lit(iz3translation_full *p, iz3mgr::ast a){
    p->show_z3_lit(a);
}

void iz3translation_full_pfgoto(iz3translation_full *p, iz3mgr::ast proof){
    p->pfgoto(proof);
}
  

void iz3translation_full_pfback(iz3translation_full *p ){
    p->pfback();
}

void iz3translation_full_pffwd(iz3translation_full *p ){
    p->pffwd();
}

void iz3translation_full_pfprem(iz3translation_full *p, int i){
    p->pfprem(i);
}

void iz3translation_full_expand(iz3translation_full *p, int i){
    p->expand(i);
}

void iz3translation_full_symbols_out_of_scope(iz3translation_full *p, int i, const iz3mgr::ast &t){
    p->symbols_out_of_scope(i,t);
}

void iz3translation_full_conc_symbols_out_of_scope(iz3translation_full *p, int i, const iz3mgr::ast &t){
    p->conc_symbols_out_of_scope(i,t);
}

struct stdio_fixer {
    stdio_fixer(){
        std::cout.rdbuf()->pubsetbuf(0,0);
    }

} my_stdio_fixer;

#endif

#endif


