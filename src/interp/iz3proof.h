/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3proof.h

  Abstract:

  This class defines a simple interpolating proof system.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifndef IZ3PROOF_H
#define IZ3PROOF_H

#include <set>

#include "iz3base.h"
#include "iz3secondary.h"

// #define CHECK_PROOFS

/** This class defines a simple proof system.

    A proof is a dag consisting of "nodes". The children of each node
    are its "premises". Each node has a "conclusion" that is a clause,
    represented as a vector of literals.

    The literals are represented by abstract syntax trees. Operations
    on these, including computation of scopes are provided by iz3base.

    A proof can be interpolated, provided it is restricted to the
    rules Resolution, Assumption, Contra and Lemma, and that all
    clauses are strict (i.e., each literal in each clause is local).

*/

class iz3proof {
 public:
    /** The type of proof nodes (nodes in the derivation tree). */
    typedef int node;

    /** Enumeration of proof rules. */
    enum rule {Resolution,Assumption,Hypothesis,Theory,Axiom,Contra,Lemma,Reflexivity,Symmetry,Transitivity,Congruence,EqContra};

    /** Interface to prover. */
    typedef iz3base prover;

    /** Ast type. */
    typedef prover::ast ast;

    /** Object thrown in case of a proof error. */
    struct proof_error: public iz3_exception {
        proof_error(): iz3_exception("proof_error") {}
    };

    /* Null proof node */
    static const node null = -1;

    /** Make a resolution node with given pivot liter and premises.
        The conclusion of premise1 should contain the negation of the
        pivot literal, while the conclusion of premise2 should containe the
        pivot literal.
    */
    node make_resolution(ast pivot, node premise1, node premise2);

    /** Make an assumption node. The given clause is assumed in the given frame. */
    node make_assumption(int frame, const std::vector<ast> &assumption);

    /** Make a hypothesis node. If phi is the hypothesis, this is
        effectively phi |- phi. */
    node make_hypothesis(ast hypothesis);

    /** Make a theory node. This can be any inference valid in the theory. */
    node make_theory(const std::vector<ast> &conclusion, std::vector<node> premises);

    /** Make an axiom node. The conclusion must be an instance of an axiom. */
    node make_axiom(const std::vector<ast> &conclusion);

    /** Make a Contra node. This rule takes a derivation of the form
        Gamma |- False and produces |- \/~Gamma. */

    node make_contra(node prem, const std::vector<ast> &conclusion);

    /** Make a lemma node. A lemma node must have an interpolation. */
    node make_lemma(const std::vector<ast> &conclusion, const std::vector<ast> &interpolation);

    /** Make a Reflexivity node. This rule produces |- x = x */
  
    node make_reflexivity(ast con);
  
    /** Make a Symmetry node. This takes a derivation of |- x = y and
        produces | y = x */

    node make_symmetry(ast con, node prem);

    /** Make a transitivity node. This takes derivations of |- x = y
        and |- y = z produces | x = z */

    node make_transitivity(ast con, node prem1, node prem2);
  
    /** Make a congruence node. This takes derivations of |- x_i = y_i
        and produces |- f(x_1,...,x_n) = f(y_1,...,y_n) */
  
    node make_congruence(ast con, const std::vector<node> &prems);

    /** Make an equality contradicition node. This takes |- x = y
        and |- !(x = y) and produces false. */
  
    node make_eqcontra(node prem1, node prem2);
  
    /** Get the rule of a node in a proof. */
    rule get_rule(node n){
        return nodes[n].rl;
    }

    /** Get the pivot of a resolution node. */
    ast get_pivot(node n){
        return nodes[n].aux;
    }

    /** Get the frame of an assumption node. */
    int get_frame(node n){
        return nodes[n].frame;
    }

    /** Get the number of literals of the conclusion of a node. */
    int get_num_conclusion_lits(node n){
        return get_conclusion(n).size();
    }

    /** Get the nth literal of the conclusion of a node. */
    ast get_nth_conclusion_lit(node n, int i){
        return get_conclusion(n)[i];
    }

    /** Get the conclusion of a node. */
    void get_conclusion(node n, std::vector<ast> &result){
        result = get_conclusion(n);
    }

    /** Get the number of premises of a node. */
    int get_num_premises(node n){
        return nodes[n].premises.size();
    }

    /** Get the nth premise of a node. */
    int get_nth_premise(node n, int i){
        return nodes[n].premises[i];
    }

    /** Get all the premises of a node. */
    void get_premises(node n, std::vector<node> &result){
        result = nodes[n].premises;
    }

    /** Create a new proof node, replacing the premises of an old
        one. */

    node clone(node n, std::vector<node> &premises){
        if(premises == nodes[n].premises)
            return n;
        nodes.push_back(nodes[n]);
        nodes.back().premises = premises;
        return nodes.size()-1;
    }

    /** Copy a proof node from src */
    node copy(iz3proof &src, node n);

    /** Resolve two lemmas on a given literal. */

    node resolve_lemmas(ast pivot, node left, node right);

    /** Swap two proofs. */
    void swap(iz3proof &other){
        std::swap(pv,other.pv);
        nodes.swap(other.nodes);
        interps.swap(other.interps);
    }
    
    /** Compute an interpolant for a proof, where the "A" side is defined by
        the given range of frames. Parameter "weak", when true, uses different
        interpolation system that resutls in generally weaker interpolants.
    */
    ast interpolate(const prover::range &_rng, bool weak = false
#ifdef CHECK_PROOFS
                    , Z3_ast assump = (Z3_ast)0, std::vector<int> *parents = 0

#endif
                    );
  
    /** print proof node to a stream */

    void print(std::ostream &s, node n);

    /** show proof node on stdout */
    void show(node n);

    /** Construct a proof, with a given prover. */
    iz3proof(prover *p){
        pv = p;
    }

    /** Default constructor */
    iz3proof(){pv = 0;}


 protected:
    
    struct node_struct {
        rule rl;
        ast aux;
        int frame;
        std::vector<ast> conclusion;
        std::vector<node> premises;
    };

    std::vector<node_struct> nodes;
    std::vector<std::vector<ast> > interps; // interpolations of lemmas
    prover *pv;

    node make_node(){
        nodes.push_back(node_struct());
        return nodes.size()-1;
    }

    void resolve(ast pivot, std::vector<ast> &cls1, const std::vector<ast> &cls2);

    node copy_rec(stl_ext::hash_map<node,node> &memo, iz3proof &src, node n);

    void interpolate_lemma(node_struct &n);

    // lazily compute the result of resolution
    // the node member "frame" indicates result is computed
    const std::vector<ast> &get_conclusion(node x){
        node_struct &n = nodes[x];
        if(n.rl == Resolution && !n.frame){
            n.conclusion = get_conclusion(n.premises[0]);
            resolve(n.aux,n.conclusion,get_conclusion(n.premises[1]));
            n.frame = 1;
        }
        return n.conclusion;
    }

    prover::range rng;  
    bool weak;
    stl_ext::hash_set<ast> b_lits;
    ast my_or(ast x, ast y);
#ifdef CHECK_PROOFS
    std::vector<Z3_ast> child_interps;
#endif
    bool pred_in_A(ast id);
    bool term_in_B(ast id);
    bool frame_in_A(int frame);
    bool lit_in_B(ast lit);
    ast get_A_lits(std::vector<ast> &cls);
    ast get_B_lits(std::vector<ast> &cls);
    void find_B_lits();
    ast disj_of_set(std::set<ast> &s);
    void mk_or_factor(int p1, int p2, int i, std::vector<ast> &itps, std::vector<std::set<ast> > &disjs);
    void mk_and_factor(int p1, int p2, int i, std::vector<ast> &itps, std::vector<std::set<ast> > &disjs);
    void set_of_B_lits(std::vector<ast> &cls, std::set<ast> &res);
    void set_of_A_lits(std::vector<ast> &cls, std::set<ast> &res);
};

#endif
