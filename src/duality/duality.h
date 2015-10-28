/*++
  Copyright (c) 2012 Microsoft Corporation

  Module Name:

  duality.h

  Abstract:

  main header for duality

  Author:

  Ken McMillan (kenmcmil)

  Revision History:


  --*/

#pragma once

#include "duality_wrapper.h"
#include <list>
#include <map>

// make hash_map and hash_set available
using namespace stl_ext;

namespace Duality {

    struct implicant_solver;

    /* Generic operations on Z3 formulas */

    struct Z3User {

        context &ctx;

        typedef func_decl FuncDecl;
        typedef expr Term;

    Z3User(context &_ctx) : ctx(_ctx){}
  
        const char *string_of_int(int n);
      
        Term conjoin(const std::vector<Term> &args);

        Term sum(const std::vector<Term> &args);

        Term CloneQuantifier(const Term &t, const Term &new_body);

        Term SubstRec(hash_map<ast, Term> &memo, const Term &t);

        Term SubstRec(hash_map<ast, Term> &memo, hash_map<func_decl, func_decl> &map, const Term &t);

        void Strengthen(Term &x, const Term &y);

        // return the func_del of an app if it is uninterpreted

        bool get_relation(const Term &t, func_decl &R);

        // return true if term is an individual variable
        // TODO: have to check that it is not a background symbol

        bool is_variable(const Term &t);

        FuncDecl SuffixFuncDecl(Term t, int n);


        Term SubstRecHide(hash_map<ast, Term> &memo, const Term &t, int number);

        void CollectConjuncts(const Term &f, std::vector<Term> &lits, bool pos = true);

        void SortTerms(std::vector<Term> &terms);

        Term SortSum(const Term &t);

        void Summarize(const Term &t);

        int CountOperators(const Term &t);

        Term SubstAtom(hash_map<ast, Term> &memo, const expr &t, const expr &atom, const expr &val);

        Term CloneQuantAndSimp(const expr &t, const expr &body);

        Term RemoveRedundancy(const Term &t);

        Term IneqToEq(const Term &t);

        bool IsLiteral(const expr &lit, expr &atom, expr &val);

        expr Negate(const expr &f);

        expr SimplifyAndOr(const std::vector<expr> &args, bool is_and);

        expr ReallySimplifyAndOr(const std::vector<expr> &args, bool is_and);

        int MaxIndex(hash_map<ast,int> &memo, const Term &t);

        bool IsClosedFormula(const Term &t);

        Term AdjustQuantifiers(const Term &t);

        FuncDecl RenumberPred(const FuncDecl &f, int n);

        FuncDecl NumberPred(const FuncDecl &f, int n);

        Term ExtractStores(hash_map<ast, Term> &memo, const Term &t, std::vector<expr> &cnstrs, hash_map<ast,expr> &renaming);


    protected:

        void SummarizeRec(hash_set<ast> &memo, std::vector<expr> &lits, int &ops, const Term &t);
        int CountOperatorsRec(hash_set<ast> &memo, const Term &t);
        void RemoveRedundancyOp(bool pol, std::vector<expr> &args, hash_map<ast, Term> &smemo);
        Term RemoveRedundancyRec(hash_map<ast, Term> &memo, hash_map<ast, Term> &smemo, const Term &t);
        Term SubstAtomTriv(const expr &foo, const expr &atom, const expr &val);
        expr ReduceAndOr(const std::vector<expr> &args, bool is_and, std::vector<expr> &res);
        expr FinishAndOr(const std::vector<expr> &args, bool is_and);
        expr PullCommonFactors(std::vector<expr> &args, bool is_and);
        Term IneqToEqRec(hash_map<ast, Term> &memo, const Term &t);
        Term CloneQuantAndSimp(const expr &t, const expr &body, bool is_forall);
        Term PushQuantifier(const expr &t, const expr &body, bool is_forall);
        void CollectJuncts(const Term &f, std::vector<Term> &lits, decl_kind op, bool negate);
        Term DeleteBoundRec(hash_map<int,hash_map<ast,Term> > &memo, int level, int num, const Term &t);
        Term DeleteBound(int level, int num, const Term &t);

    };

    /** This class represents a relation post-fixed point (RPFP) problem as
     *  a "problem graph". The graph consists of Nodes and hyper-edges.
     * 
     * A node consists of
     * - Annotation, a symbolic relation
     * - Bound, a symbolic relation giving an upper bound on Annotation
     * 
     *
     * A hyper-edge consists of:
     *  - Children, a sequence of children Nodes,
     *  - F, a symbolic relational transformer,
     *  - Parent, a single parent Node.
     *  
     * The graph is "solved" when:
     * - For every Node n, n.Annotation subseteq n.Bound
     * - For every hyperedge e, e.F(e.Children.Annotation) subseteq e.Parent.Annotation
     * 
     * where, if x is a sequence of Nodes, x.Annotation is the sequences
     * of Annotations of the nodes in the sequence.
     * 
     * A symbolic Transformer consists of
     * - RelParams, a sequence of relational symbols
     * - IndParams, a sequence of individual symbols
     * - Formula, a formula over RelParams and IndParams
     * 
     * A Transformer t represents a function that takes sequence R of relations
     * and yields the relation lambda (t.Indparams). Formula(R/RelParams).
     * 
     * As a special case, a nullary Transformer (where RelParams is the empty sequence)
     * represents a fixed relation.
     * 
     * An RPFP consists of
     * - Nodes, a set of Nodes
     * - Edges, a set of hyper-edges
     * - Context, a prover context that contains formula AST's
     *  
     * Multiple RPFP's can use the same Context, but you should be careful
     * that only one RPFP asserts constraints in the context at any time. 
     * 
     *  */
    class RPFP : public Z3User
    {
    public:
      
        class Edge;
        class Node;
        bool HornClauses;

      
        /** Interface class for interpolating solver. */

        class LogicSolver {
        public:
           
            context *ctx;   /** Z3 context for formulas */
            solver *slvr;   /** Z3 solver */
            bool need_goals; /** Can the solver use the goal tree to optimize interpolants? */
            solver aux_solver; /** For temporary use -- don't leave assertions here. */

            /** Tree interpolation. This method assumes the formulas in TermTree
                "assumptions" are currently asserted in the solver. The return
                value indicates whether the assertions are satisfiable. In the
                UNSAT case, a tree interpolant is returned in "interpolants".
                In the SAT case, a model is returned. 
            */

            virtual
                lbool interpolate_tree(TermTree *assumptions,
                                       TermTree *&interpolants,
                                       model &_model,
                                       TermTree *goals = 0,
                                       bool weak = false
                                       ) = 0;
           
            /** Declare a constant in the background theory. */
            virtual void declare_constant(const func_decl &f) = 0;

            /** Is this a background constant? */
            virtual bool is_constant(const func_decl &f) = 0;

            /** Get the constants in the background vocabulary */
            virtual hash_set<func_decl> &get_constants() = 0;

            /** Assert a background axiom. */
            virtual void assert_axiom(const expr &axiom) = 0;

            /** Get the background axioms. */
            virtual const std::vector<expr> &get_axioms() = 0;

            /** Return a string describing performance. */
            virtual std::string profile() = 0;

            virtual void write_interpolation_problem(const std::string &file_name,
                                                     const std::vector<expr> &assumptions,
                                                     const std::vector<expr> &theory
                                                     ){}

            /** Cancel, throw Canceled object if possible. */
            virtual void cancel(){ }

            /* Note: aux solver uses extensional array theory, since it
               needs to be able to produce counter-models for
               interpolants the have array equalities in them.
            */
        LogicSolver(context &c) : aux_solver(c,true){}

            virtual ~LogicSolver(){}
        };

        /** This solver uses iZ3. */
        class iZ3LogicSolver : public LogicSolver {
        public:
            interpolating_context *ictx;   /** iZ3 context for formulas */
            interpolating_solver *islvr;   /** iZ3 solver */

            lbool interpolate_tree(TermTree *assumptions,
                                   TermTree *&interpolants,
                                   model &_model,
                                   TermTree *goals = 0,
                                   bool weak = false)
            {
                literals _labels;
                islvr->SetWeakInterpolants(weak);
                return islvr->interpolate_tree(assumptions,interpolants,_model,_labels,true);
            }

            void assert_axiom(const expr &axiom){
#if 1
                // HACK: large "distict" predicates can kill the legacy SMT solver.
                // encode them with a UIF
                if(axiom.is_app() && axiom.decl().get_decl_kind() == Distinct)
                    if(axiom.num_args() > 10){
                        sort s = axiom.arg(0).get_sort();
                        std::vector<sort> sv;
                        sv.push_back(s);
                        int nargs = axiom.num_args();
                        std::vector<expr> args(nargs);
                        func_decl f = ctx->fresh_func_decl("@distinct",sv,ctx->int_sort());
                        for(int i = 0; i < nargs; i++){
                            expr a = axiom.arg(i);
                            expr new_cnstr = f(a) == ctx->int_val(i);
                            args[i] = new_cnstr;
                        }
                        expr cnstr = ctx->make(And,args);
                        islvr->AssertInterpolationAxiom(cnstr);
                        return;
                    }
#endif
                islvr->AssertInterpolationAxiom(axiom);
            }

            const std::vector<expr> &get_axioms() {
                return islvr->GetInterpolationAxioms();
            }

            std::string profile(){
                return islvr->profile();
            }

#if 0
            iZ3LogicSolver(config &_config){
                ctx = ictx = new interpolating_context(_config);
                slvr = islvr = new interpolating_solver(*ictx);
                need_goals = false;
                islvr->SetWeakInterpolants(true);
            }
#endif

        iZ3LogicSolver(context &c, bool models = true) : LogicSolver(c) {
                ctx = ictx = &c;
                slvr = islvr = new interpolating_solver(*ictx, models);
                need_goals = false;
                islvr->SetWeakInterpolants(true);
            }

            void write_interpolation_problem(const std::string &file_name,
                                             const std::vector<expr> &assumptions,
                                             const std::vector<expr> &theory
                                             ){
#if 0
                islvr->write_interpolation_problem(file_name,assumptions,theory);
#endif

            }

            void cancel(){islvr->cancel();}

            /** Declare a constant in the background theory. */
            virtual void declare_constant(const func_decl &f){
                bckg.insert(f);
            }
	
            /** Is this a background constant? */
            virtual bool is_constant(const func_decl &f){
                return bckg.find(f) != bckg.end();
            }

            /** Get the constants in the background vocabulary */
            virtual hash_set<func_decl> &get_constants(){
                return bckg;
            }

            ~iZ3LogicSolver(){
                // delete ictx;
                delete islvr;
            }
        private:
            hash_set<func_decl> bckg;

        };

#if 0
        /** Create a logic solver from a Z3 configuration. */
        static iZ3LogicSolver *CreateLogicSolver(config &_config){
            return new iZ3LogicSolver(_config);
        }
#endif      

        /** Create a logic solver from a low-level Z3 context. 
            Only use this if you know what you're doing. */
        static iZ3LogicSolver *CreateLogicSolver(context c){
            return new iZ3LogicSolver(c);
        }

        LogicSolver *ls;

    protected:
        int nodeCount;
        int edgeCount;
      
        class stack_entry
        {
        public:
            std::list<Edge *> edges;
            std::list<Node *> nodes;
            std::list<std::pair<Edge *,Term> > constraints;
        };
      
      
    public:
        model dualModel;
    protected:
        literals dualLabels;
        std::list<stack_entry> stack;
        std::vector<Term> axioms; // only saved here for printing purposes
        solver &aux_solver;
        hash_set<ast> *proof_core;
      
    public:

        /** Construct an RPFP graph with a given interpolating prover context. It is allowed to
            have multiple RPFP's use the same context, but you should never have teo RPFP's
            with the same conext asserting nodes or edges at the same time. Note, if you create
            axioms in one RPFP, them create a second RPFP with the same context, the second will
            inherit the axioms. 
        */

    RPFP(LogicSolver *_ls) : Z3User(*(_ls->ctx)), dualModel(*(_ls->ctx)), aux_solver(_ls->aux_solver)
            {
                ls = _ls;
                nodeCount = 0;
                edgeCount = 0;
                stack.push_back(stack_entry());
                HornClauses = false;
                proof_core = 0;
            }

        virtual ~RPFP();
      
        /** Symbolic representation of a relational transformer */
        class Transformer
        {
        public:
            std::vector<FuncDecl> RelParams;
            std::vector<Term> IndParams;
            Term Formula;
            RPFP *owner;
            hash_map<std::string,Term> labels;
	
            Transformer *Clone()
            {
                return new Transformer(*this);
            }
	
            void SetEmpty(){
                Formula = owner->ctx.bool_val(false);
            }

            void SetFull(){
                Formula = owner->ctx.bool_val(true);
            }

            bool IsEmpty(){
                return eq(Formula,owner->ctx.bool_val(false));
            }

            bool IsFull(){
                return eq(Formula,owner->ctx.bool_val(true));
            }

            void UnionWith(const Transformer &other){
                Term t = owner->SubstParams(other.IndParams,IndParams,other.Formula);
                Formula = Formula || t;
            }

            void IntersectWith(const Transformer &other){
                Term t = owner->SubstParams(other.IndParams,IndParams,other.Formula);
                Formula = Formula && t;
            }

            bool SubsetEq(const Transformer &other){
                Term t = owner->SubstParams(other.IndParams,IndParams,other.Formula);
                expr test = Formula && !t;
                owner->aux_solver.push();
                owner->aux_solver.add(test);
                check_result res = owner->aux_solver.check();
                owner->aux_solver.pop(1);
                return res == unsat;
            }

            void Complement(){
                Formula = !Formula;
            }
	
            void Simplify(){
                Formula = Formula.simplify();
            }

        Transformer(const std::vector<FuncDecl> &_RelParams, const std::vector<Term> &_IndParams, const Term &_Formula, RPFP *_owner)
            : RelParams(_RelParams), IndParams(_IndParams), Formula(_Formula) {owner = _owner;}
        };
      
        /** Create a symbolic transformer. */
        Transformer CreateTransformer(const std::vector<FuncDecl> &_RelParams, const std::vector<Term> &_IndParams, const Term &_Formula)
        {
            // var ops = new Util.ContextOps(ctx);
            // var foo = ops.simplify_lhs(_Formula);
            // t.Formula = foo.Item1;
            // t.labels = foo.Item2;
            return Transformer(_RelParams,_IndParams,_Formula,this);
        }
      
        /** Create a relation (nullary relational transformer) */
        Transformer CreateRelation(const std::vector<Term> &_IndParams, const Term &_Formula)
        {
            return CreateTransformer(std::vector<FuncDecl>(), _IndParams, _Formula);
        }
      
        /** A node in the RPFP graph */
        class Node
        {
        public:
            FuncDecl Name;
            Transformer Annotation;
            Transformer Bound;
            Transformer Underapprox;
            RPFP *owner;
            int number;
            Edge *Outgoing;
            std::vector<Edge *> Incoming;
            Term dual;
            Node *map;
            unsigned recursion_bound;
	
        Node(const FuncDecl &_Name, const Transformer &_Annotation, const Transformer &_Bound, const Transformer &_Underapprox, const Term &_dual, RPFP *_owner, int _number)
            : Name(_Name), Annotation(_Annotation), Bound(_Bound), Underapprox(_Underapprox), dual(_dual) {owner = _owner; number = _number; Outgoing = 0; recursion_bound = UINT_MAX;}
        };
      
        /** Create a node in the graph. The input is a term R(v_1...v_n)
         *  where R is an arbitrary relational symbol and v_1...v_n are
         *  arbitary distinct variables. The names are only of mnemonic value,
         *  however, the number and type of arguments determine the type
         *  of the relation at this node. */
      
        Node *CreateNode(const Term &t)
        {
            std::vector<Term> _IndParams;
            int nargs = t.num_args();
            for(int i = 0; i < nargs; i++)
                _IndParams.push_back(t.arg(i));
            Node *n = new Node(t.decl(),
                               CreateRelation(_IndParams,ctx.bool_val(true)),
                               CreateRelation(_IndParams,ctx.bool_val(true)),
                               CreateRelation(_IndParams,ctx.bool_val(false)),
                               expr(ctx), this, ++nodeCount
                               );
            nodes.push_back(n);
            return n;
        }
      
        /** Clone a node (can be from another graph).  */
      
        Node *CloneNode(Node *old)
        {
            Node *n = new Node(old->Name,
                               old->Annotation,
                               old->Bound,
                               old->Underapprox,
                               expr(ctx),
                               this,
                               ++nodeCount
                               );
            nodes.push_back(n);
            n->map = old;
            return n;
        }
      
        /** Delete a node. You can only do this if not connected to any edges.*/
        void DeleteNode(Node *node){
            if(node->Outgoing || !node->Incoming.empty())
                throw "cannot delete RPFP node";
            for(std::vector<Node *>::iterator it = nodes.end(), en = nodes.begin(); it != en;){
                if(*(--it) == node){
                    nodes.erase(it);
                    break;
                }
            }
            delete node;
        }

        /** This class represents a hyper-edge in the RPFP graph */
      
        class Edge
        {
        public:
            Transformer F;
            Node *Parent;
            std::vector<Node *> Children;
            RPFP *owner;
            int number;
            // these should be internal...
            Term dual;
            hash_map<func_decl,int> relMap;
            hash_map<ast,Term> varMap;
            Edge *map;
            Term labeled;
            std::vector<Term> constraints;
	
        Edge(Node *_Parent, const Transformer &_F, const std::vector<Node *> &_Children, RPFP *_owner, int _number)
            : F(_F), Parent(_Parent), Children(_Children), dual(expr(_owner->ctx)) {
                owner = _owner;
                number = _number;
            }
        };
      
        
        /** Create a hyper-edge. */
        Edge *CreateEdge(Node *_Parent, const Transformer &_F, const std::vector<Node *> &_Children)
        {
            Edge *e = new Edge(_Parent,_F,_Children,this,++edgeCount);
            _Parent->Outgoing = e;
            for(unsigned i = 0; i < _Children.size(); i++)
                _Children[i]->Incoming.push_back(e);
            edges.push_back(e);
            return e;
        }
      
      
        /** Delete a hyper-edge and unlink it from any nodes. */
        void DeleteEdge(Edge *edge){
            if(edge->Parent)
                edge->Parent->Outgoing = 0;
            for(unsigned int i = 0; i < edge->Children.size(); i++){
                std::vector<Edge *> &ic = edge->Children[i]->Incoming;
                for(std::vector<Edge *>::iterator it = ic.begin(), en = ic.end(); it != en; ++it){
                    if(*it == edge){
                        ic.erase(it);
                        break;
                    }
                }
            }
            for(std::vector<Edge *>::iterator it = edges.end(), en = edges.begin(); it != en;){
                if(*(--it) == edge){
                    edges.erase(it);
                    break;
                }
            }
            delete edge;
        }
      
        /** Create an edge that lower-bounds its parent. */
        Edge *CreateLowerBoundEdge(Node *_Parent)
        {
            return CreateEdge(_Parent, _Parent->Annotation, std::vector<Node *>());
        }
      

        /** For incremental solving, asserts the constraint associated
         * with this edge in the SMT context. If this edge is removed,
         * you must pop the context accordingly. The second argument is
         * the number of pushes we are inside. */
      
        virtual void AssertEdge(Edge *e, int persist = 0, bool with_children = false, bool underapprox = false);

        /* Constrain an edge by the annotation of one of its children. */

        void ConstrainParent(Edge *parent, Node *child);

        /** For incremental solving, asserts the negation of the upper bound associated
         * with a node.
         * */
      
        void AssertNode(Node *n);

        /** Assert a constraint on an edge in the SMT context. 
         */
        void ConstrainEdge(Edge *e, const Term &t);
      
        /** Fix the truth values of atomic propositions in the given
            edge to their values in the current assignment. */
        void FixCurrentState(Edge *root);
    
        void FixCurrentStateFull(Edge *edge, const expr &extra);
      
        void FixCurrentStateFull(Edge *edge, const std::vector<expr> &assumps, const hash_map<ast,expr> &renaming);

        /** Declare a constant in the background theory. */

        void DeclareConstant(const FuncDecl &f);

        /** Assert a background axiom. Background axioms can be used to provide the
         *  theory of auxilliary functions or relations. All symbols appearing in
         *  background axioms are considered global, and may appear in both transformer
         *  and relational solutions. Semantically, a solution to the RPFP gives
         *  an interpretation of the unknown relations for each interpretation of the
         *  auxilliary symbols that is consistent with the axioms. Axioms should be
         *  asserted before any calls to Push. They cannot be de-asserted by Pop. */

        void AssertAxiom(const Term &t);

#if 0
        /** Do not call this. */
      
        void RemoveAxiom(const Term &t);
#endif

        /** Solve an RPFP graph. This means either strengthen the annotation
         *  so that the bound at the given root node is satisfied, or
         *  show that this cannot be done by giving a dual solution 
         *  (i.e., a counterexample). 
         *  
         * In the current implementation, this only works for graphs that
         * are:
         * - tree-like
         * 
         * - closed.
         * 
         * In a tree-like graph, every nod has out most one incoming and one out-going edge,
         * and there are no cycles. In a closed graph, every node has exactly one out-going
         * edge. This means that the leaves of the tree are all hyper-edges with no
         * children. Such an edge represents a relation (nullary transformer) and thus
         * a lower bound on its parent. The parameter root must be the root of this tree.
         * 
         * If Solve returns LBool.False, this indicates success. The annotation of the tree
         * has been updated to satisfy the upper bound at the root. 
         * 
         * If Solve returns LBool.True, this indicates a counterexample. For each edge,
         * you can then call Eval to determine the values of symbols in the transformer formula.
         * You can also call Empty on a node to determine if its value in the counterexample
         * is the empty relation.
         * 
         *    \param root The root of the tree
         *    \param persist Number of context pops through which result should persist 
         * 
         * 
         */

        lbool Solve(Node *root, int persist);
      
        /** Same as Solve, but annotates only a single node. */

        lbool SolveSingleNode(Node *root, Node *node);

        /** Get the constraint tree (but don't solve it) */
      
        TermTree *GetConstraintTree(Node *root, Node *skip_descendant = 0);
  
        /** Dispose of the dual model (counterexample) if there is one. */
      
        void DisposeDualModel();

        /** Check satisfiability of asserted edges and nodes. Same functionality as
         * Solve, except no primal solution (interpolant) is generated in the unsat case. */ 
      
        check_result Check(Node *root, std::vector<Node *> underapproxes = std::vector<Node *>(), 
                           std::vector<Node *> *underapprox_core = 0);

        /** Update the model, attempting to make the propositional literals in assumps true. If possible,
            return sat, else return unsat and keep the old model. */
      
        check_result CheckUpdateModel(Node *root, std::vector<expr> assumps);

        /** Determines the value in the counterexample of a symbol occuring in the transformer formula of
         *  a given edge. */
      
        Term Eval(Edge *e, Term t);
	
        /** Return the fact derived at node p in a counterexample. */

        Term EvalNode(Node *p);
    
        /** Returns true if the given node is empty in the primal solution. For proecudure summaries,
            this means that the procedure is not called in the current counter-model. */
      
        bool Empty(Node *p);

        /** Compute an underapproximation of every node in a tree rooted at "root",
            based on a previously computed counterexample. */

        Term ComputeUnderapprox(Node *root, int persist);

        /** Try to strengthen the annotation of a node by removing disjuncts. */
        void Generalize(Node *root, Node *node);


        /** Compute disjunctive interpolant for node by case splitting */
        void InterpolateByCases(Node *root, Node *node);

        /** Push a scope. Assertions made after Push can be undone by Pop. */
      
        void Push();

        /** Exception thrown when bad clause is encountered */
      
        struct bad_clause {
            std::string msg;
            int i;
            bad_clause(const std::string &_msg, int _i){
                msg = _msg;
                i = _i;
            }
        };

        struct parse_error {
            std::string msg;
            parse_error(const std::string &_msg){
                msg = _msg;
            }
        };

        struct file_not_found {
        };

        struct bad_format {
        };

        // thrown on internal error
        struct Bad {
        };
      
        // thrown on more serious internal error
        struct ReallyBad {
        };

        // throw when greedy reduction fails
        struct greedy_reduce_failed {};

        /** Pop a scope (see Push). Note, you cannot pop axioms. */
      
        void Pop(int num_scopes);
      
        /** Erase the proof by performing a Pop, Push and re-assertion of
            all the popped constraints */
        void PopPush();

        /** Return true if the given edge is used in the proof of unsat.
            Can be called only after Solve or Check returns an unsat result. */
      
        bool EdgeUsedInProof(Edge *edge);


        /** Convert a collection of clauses to Nodes and Edges in the RPFP.
	  
            Predicate unknowns are uninterpreted predicates not
            occurring in the background theory.
          
            Clauses are of the form 
          
            B => P(t_1,...,t_k)
	  
            where P is a predicate unknown and predicate unknowns
            occur only positivey in H and only under existential
            quantifiers in prenex form.
	  
            Each predicate unknown maps to a node. Each clause maps to
            an edge. Let C be a clause B => P(t_1,...,t_k) where the
            sequence of predicate unknowns occurring in B (in order
            of occurrence) is P_1..P_n. The clause maps to a transformer
            T where:
	  
            T.Relparams = P_1..P_n
            T.Indparams = x_1...x+k
            T.Formula = B /\ t_1 = x_1 /\ ... /\ t_k = x_k
	  
            Throws exception bad_clause(msg,i) if a clause i is
            in the wrong form.
	  
        */
      
        struct label_struct {
            symbol name;
            expr value;
            bool pos;
	label_struct(const symbol &s, const expr &e, bool b)
	: name(s), value(e), pos(b) {}
        };

      
#ifdef _WINDOWS
        __declspec(dllexport)
#endif
            void FromClauses(const std::vector<Term> &clauses, const std::vector<unsigned> *bounds = 0);

        void FromFixpointContext(fixedpoint fp, std::vector<Term> &queries);

        void WriteSolution(std::ostream &s);

        void WriteCounterexample(std::ostream &s, Node *node);

        enum FileFormat {DualityFormat, SMT2Format, HornFormat}; 

        /** Write the RPFP to a file (currently in SMTLIB 1.2 format) */
        void WriteProblemToFile(std::string filename, FileFormat format = DualityFormat);

        /** Read the RPFP from a file (in specificed format) */
        void ReadProblemFromFile(std::string filename, FileFormat format = DualityFormat);

        /** Translate problem to Horn clause form */
        void ToClauses(std::vector<Term> &cnsts, FileFormat format = DualityFormat);

        /** Translate the RPFP to a fixed point context, with queries */
        fixedpoint ToFixedPointProblem(std::vector<expr> &queries);

        /** Nodes of the graph. */
        std::vector<Node *> nodes;

        /** Edges of the graph. */
        std::vector<Edge *> edges;

        /** Fuse a vector of transformers. If the total number of inputs of the transformers
            is N, then the result is an N-ary transfomer whose output is the union of
            the outputs of the given transformers. The is, suppose we have a vetor of transfoermers
            {T_i(r_i1,...,r_iN(i) : i=1..M}. The the result is a transformer 
	       
            F(r_11,...,r_iN(1),...,r_M1,...,r_MN(M)) = 
            T_1(r_11,...,r_iN(1)) U ... U T_M(r_M1,...,r_MN(M))
        */

        Transformer Fuse(const std::vector<Transformer *> &trs);

        /** Fuse edges so that each node is the output of at most one edge. This
            transformation is solution-preserving, but changes the numbering of edges in
            counterexamples.
        */
        void FuseEdges();

        void RemoveDeadNodes();

        Term SubstParams(const std::vector<Term> &from,
                         const std::vector<Term> &to, const Term &t);

        Term SubstParamsNoCapture(const std::vector<Term> &from,
                                  const std::vector<Term> &to, const Term &t);

        Term Localize(Edge *e, const Term &t);

        void EvalNodeAsConstraint(Node *p, Transformer &res);

        TermTree *GetGoalTree(Node *root);

        int EvalTruth(hash_map<ast,int> &memo, Edge *e, const Term &f);

        void GetLabels(Edge *e, std::vector<symbol> &labels);

        //      int GetLabelsRec(hash_map<ast,int> *memo, const Term &f, std::vector<symbol> &labels, bool labpos);

        /** Compute and save the proof core for future calls to
            EdgeUsedInProof.  You only need to call this if you will pop
            the solver before calling EdgeUsedInProof.
        */
        void ComputeProofCore();

        int CumulativeDecisions();

        void GreedyReduceNodes(std::vector<Node *> &nodes);

        check_result CheckWithConstrainedNodes(std::vector<Node *> &posnodes,std::vector<Node *> &negnodes);

        solver &slvr(){
            return *ls->slvr;
        }

    protected:
      
        void ClearProofCore(){
            if(proof_core)
                delete proof_core;
            proof_core = 0;
        }

        Term SuffixVariable(const Term &t, int n);
      
        Term HideVariable(const Term &t, int n);

        void RedVars(Node *node, Term &b, std::vector<Term> &v);

        Term RedDualRela(Edge *e, std::vector<Term> &args, int idx);

        Term LocalizeRec(Edge *e,  hash_map<ast,Term> &memo, const Term &t);

        void SetEdgeMaps(Edge *e);

        Term ReducedDualEdge(Edge *e);

        TermTree *ToTermTree(Node *root, Node *skip_descendant = 0);

        TermTree *ToGoalTree(Node *root);

        void CollapseTermTreeRec(TermTree *root, TermTree *node);

        TermTree *CollapseTermTree(TermTree *node);

        void DecodeTree(Node *root, TermTree *interp, int persist);

        Term GetUpperBound(Node *n);

        TermTree *AddUpperBound(Node *root, TermTree *t);

#if 0
        void WriteInterps(System.IO.StreamWriter f, TermTree t);
#endif    

        void WriteEdgeVars(Edge *e,  hash_map<ast,int> &memo, const Term &t, std::ostream &s);

        void WriteEdgeAssignment(std::ostream &s, Edge *e);

    
        // Scan the clause body for occurrences of the predicate unknowns
  
        Term ScanBody(hash_map<ast,Term> &memo, 
                      const Term &t,
                      hash_map<func_decl,Node *> &pmap,
                      std::vector<func_decl> &res,
                      std::vector<Node *> &nodes);

        Term RemoveLabelsRec(hash_map<ast,Term> &memo, const Term &t, std::vector<label_struct> &lbls);

        Term RemoveLabels(const Term &t, std::vector<label_struct > &lbls);

        Term GetAnnotation(Node *n);


        Term GetUnderapprox(Node *n);

        Term UnderapproxFlag(Node *n);

        hash_map<ast,Node *> underapprox_flag_rev;

        Node *UnderapproxFlagRev(const Term &flag);

        Term ProjectFormula(std::vector<Term> &keep_vec, const Term &f);

        int SubtermTruth(hash_map<ast,int> &memo, const Term &);

        void ImplicantRed(hash_map<ast,int> &memo, const Term &f, std::vector<Term> &lits,
                          hash_set<ast> *done, bool truth, hash_set<ast> &dont_cares);

        void Implicant(hash_map<ast,int> &memo, const Term &f, std::vector<Term> &lits, hash_set<ast> &dont_cares);

        Term UnderapproxFormula(const Term &f, hash_set<ast> &dont_cares);

        void ImplicantFullRed(hash_map<ast,int> &memo, const Term &f, std::vector<Term> &lits,
                              hash_set<ast> &done, hash_set<ast> &dont_cares, bool extensional = true);

    public:
        Term UnderapproxFullFormula(const Term &f, bool extensional = true);

    protected:
        Term ToRuleRec(Edge *e,  hash_map<ast,Term> &memo, const Term &t, std::vector<expr> &quants);

        hash_map<ast,Term> resolve_ite_memo;

        Term ResolveIte(hash_map<ast,int> &memo, const Term &t, std::vector<Term> &lits,
                        hash_set<ast> *done, hash_set<ast> &dont_cares);

        struct ArrayValue {
            bool defined;
            std::map<ast,ast> entries;
            expr def_val;
        };

        void EvalArrayTerm(const Term &t, ArrayValue &res);

        Term EvalArrayEquality(const Term &f);

        Term ModelValueAsConstraint(const Term &t);

        void GetLabelsRec(hash_map<ast,int> &memo, const Term &f, std::vector<symbol> &labels,
                          hash_set<ast> *done, bool truth);

        Term SubstBoundRec(hash_map<int,hash_map<ast,Term> > &memo, hash_map<int,Term> &subst, int level, const Term &t);

        Term SubstBound(hash_map<int,Term> &subst, const Term &t);

        void ConstrainEdgeLocalized(Edge *e, const Term &t);

        void GreedyReduce(solver &s, std::vector<expr> &conjuncts);
      
        void NegateLits(std::vector<expr> &lits);

        expr SimplifyOr(std::vector<expr> &lits);

        expr SimplifyAnd(std::vector<expr> &lits);

        void SetAnnotation(Node *root, const expr &t);

        void AddEdgeToSolver(Edge *edge);

        void AddEdgeToSolver(implicant_solver &aux_solver, Edge *edge);

        void AddToProofCore(hash_set<ast> &core);

        void GetGroundLitsUnderQuants(hash_set<ast> *memo, const Term &f, std::vector<Term> &res, int under);

        Term StrengthenFormulaByCaseSplitting(const Term &f, std::vector<expr> &case_lits);
    
        expr NegateLit(const expr &f);

        expr GetEdgeFormula(Edge *e, int persist, bool with_children, bool underapprox);

        bool IsVar(const expr &t);

        void GetVarsRec(hash_set<ast> &memo, const expr &cnst, std::vector<expr> &vars);

        expr UnhoistPullRec(hash_map<ast,expr> & memo, const expr &w, hash_map<ast,expr> & init_defs, hash_map<ast,expr> & const_params, hash_map<ast,expr> &const_params_inv, std::vector<expr> &new_params);

        void AddParamsToTransformer(Transformer &trans, const std::vector<expr> &params);
 
        expr AddParamsToApp(const expr &app, const func_decl &new_decl, const std::vector<expr> &params);

        expr GetRelRec(hash_set<ast> &memo, const expr &t, const func_decl &rel);

        expr GetRel(Edge *edge, int child_idx);

        void GetDefs(const expr &cnst, hash_map<ast,expr> &defs);

        void GetDefsRec(const expr &cnst, hash_map<ast,expr> &defs);

        void AddParamsToNode(Node *node, const std::vector<expr> &params);

        void UnhoistLoop(Edge *loop_edge, Edge *init_edge);

        void Unhoist();
      
        Term ElimIteRec(hash_map<ast,expr> &memo, const Term &t, std::vector<expr> &cnsts);

        Term ElimIte(const Term &t);

        void MarkLiveNodes(hash_map<Node *,std::vector<Edge *> > &outgoing, hash_set<Node *> &live_nodes, Node *node);

        virtual void slvr_add(const expr &e);
      
        virtual void slvr_pop(int i);

        virtual void slvr_push();
      
        virtual check_result slvr_check(unsigned n = 0, expr * const assumptions = 0, unsigned *core_size = 0, expr *core = 0);

        virtual lbool ls_interpolate_tree(TermTree *assumptions,
                                          TermTree *&interpolants,
                                          model &_model,
                                          TermTree *goals = 0,
                                          bool weak = false);

        virtual bool proof_core_contains(const expr &e);

    };
    

    /** RPFP solver base class. */

    class Solver {
      
    public:
      
        class Counterexample {
        private:
            RPFP *tree;
            RPFP::Node *root;
        public:
            Counterexample(){
                tree = 0;
                root = 0;
            }
            Counterexample(RPFP *_tree, RPFP::Node *_root){
                tree = _tree;
                root = _root;
            }
            ~Counterexample(){
                if(tree) delete tree;
            }
            void swap(Counterexample &other){
                std::swap(tree,other.tree);
                std::swap(root,other.root);
            }
            void set(RPFP *_tree, RPFP::Node *_root){
                if(tree) delete tree;
                tree = _tree;
                root = _root;
            }
            void clear(){
                if(tree) delete tree;
                tree = 0;
            }
            RPFP *get_tree() const {return tree;}
            RPFP::Node *get_root() const {return root;}
        private:
            Counterexample &operator=(const Counterexample &);
            Counterexample(const Counterexample &);
        };
      
        /** Solve the problem. You can optionally give an old
            counterexample to use as a guide. This is chiefly useful for
            abstraction refinement metholdologies, and is only used as a
            heuristic. */
      
        virtual bool Solve() = 0;
      
        virtual Counterexample &GetCounterexample() = 0;
      
        virtual bool SetOption(const std::string &option, const std::string &value) = 0;
      
        /** Learn heuristic information from another solver. This
            is chiefly useful for abstraction refinement, when we want to
            solve a series of similar problems. */

        virtual void LearnFrom(Solver *old_solver) = 0;

        /** Return true if the solution be incorrect due to recursion bounding.
            That is, the returned "solution" might contain all derivable facts up to the
            given recursion bound, but not be actually a fixed point.
        */

        virtual bool IsResultRecursionBounded() = 0;

        virtual ~Solver(){}

        static Solver *Create(const std::string &solver_class, RPFP *rpfp);

        /** This can be called asynchrnously to cause Solve to throw a
            Canceled exception at some time in the future.
        */
        virtual void Cancel() = 0;

        /** Object thrown on cancellation */
        struct Canceled {};
      
        /** Object thrown on incompleteness */
        struct Incompleteness {};
    };
}


// Allow to hash on nodes and edges in deterministic way

namespace hash_space {
    template <>
        class hash<Duality::RPFP::Node *> {
    public:
        size_t operator()(const Duality::RPFP::Node *p) const {
            return p->number;
        }
    };
}

namespace hash_space {
    template <>
        class hash<Duality::RPFP::Edge *> {
    public:
        size_t operator()(const Duality::RPFP::Edge *p) const {
            return p->number;
        }
    };
}

// allow to walk sets of nodes without address dependency

namespace std {
    template <>
        class less<Duality::RPFP::Node *> {
    public:
        bool operator()(Duality::RPFP::Node * const &s, Duality::RPFP::Node * const &t) const {
            return s->number < t->number; // s.raw()->get_id() < t.raw()->get_id();
        }
    };
}

// #define LIMIT_STACK_WEIGHT 5


namespace Duality {
    /** Caching version of RPFP. Instead of asserting constraints, returns assumption literals */

    class RPFP_caching : public RPFP {
    public:

        /** appends assumption literals for edge to lits. if with_children is true,
            includes that annotation of the edge's children. 
        */ 
        void AssertEdgeCache(Edge *e, std::vector<Term> &lits, bool with_children = false);
      
        /** appends assumption literals for node to lits */
        void AssertNodeCache(Node *, std::vector<Term> lits);

        /** check assumption lits, and return core */
        check_result CheckCore(const std::vector<Term> &assumps, std::vector<Term> &core);
      
        /** Clone another RPFP into this one, keeping a map */
        void Clone(RPFP *other);

        /** Get the clone of a node */
        Node *GetNodeClone(Node *other_node);

        /** Get the clone of an edge */
        Edge *GetEdgeClone(Edge *other_edge);

        /** Try to strengthen the parent of an edge */
        void GeneralizeCache(Edge *edge);

        /** Try to propagate some facts from children to parents of edge.
            Return true if success. */
        bool PropagateCache(Edge *edge);

        /** Construct a caching RPFP using a LogicSolver */
    RPFP_caching(LogicSolver *_ls) : RPFP(_ls) {}

        /** Constraint an edge by its child's annotation. Return
            assumption lits. */
        void ConstrainParentCache(Edge *parent, Node *child, std::vector<Term> &lits);

#ifdef LIMIT_STACK_WEIGHT
        virtual void AssertEdge(Edge *e, int persist = 0, bool with_children = false, bool underapprox = false);
#endif

        virtual ~RPFP_caching(){}

    protected:
        hash_map<ast,expr> AssumptionLits;
        hash_map<Node *, Node *> NodeCloneMap;
        hash_map<Edge *, Edge *> EdgeCloneMap;
        std::vector<expr> alit_stack;
        std::vector<unsigned> alit_stack_sizes;

        // to let us use one solver per edge
        struct edge_solver {
            hash_map<ast,expr> AssumptionLits;
            uptr<solver> slvr;
        };
        hash_map<Edge *, edge_solver > edge_solvers;
      
#ifdef LIMIT_STACK_WEIGHT
        struct weight_counter {
            int val;
            weight_counter(){val = 0;}
            void swap(weight_counter &other){
                std::swap(val,other.val);
            }
        };
      
        struct big_stack_entry {
            weight_counter weight_added;
            std::vector<expr> new_alits;
            std::vector<expr> alit_stack;
            std::vector<unsigned> alit_stack_sizes;
        };

        std::vector<expr> new_alits;
        weight_counter weight_added;
        std::vector<big_stack_entry> big_stack;
#endif



        void GetAssumptionLits(const expr &fmla, std::vector<expr> &lits, hash_map<ast,expr> *opt_map = 0);

        void GreedyReduceCache(std::vector<expr> &assumps, std::vector<expr> &core);

        void FilterCore(std::vector<expr> &core, std::vector<expr> &full_core);
        void ConstrainEdgeLocalizedCache(Edge *e, const Term &tl, std::vector<expr> &lits);

        virtual void slvr_add(const expr &e);
      
        virtual void slvr_pop(int i);

        virtual void slvr_push();
      
        virtual check_result slvr_check(unsigned n = 0, expr * const assumptions = 0, unsigned *core_size = 0, expr *core = 0);

        virtual lbool ls_interpolate_tree(TermTree *assumptions,
                                          TermTree *&interpolants,
                                          model &_model,
                                          TermTree *goals = 0,
                                          bool weak = false);

        virtual bool proof_core_contains(const expr &e);

        void GetTermTreeAssertionLiterals(TermTree *assumptions);

        void GetTermTreeAssertionLiteralsRec(TermTree *assumptions);

        edge_solver &SolverForEdge(Edge *edge, bool models, bool axioms);

    public:
        struct scoped_solver_for_edge {
            solver *orig_slvr;
            RPFP_caching *rpfp;
            edge_solver *es;
            scoped_solver_for_edge(RPFP_caching *_rpfp, Edge *edge, bool models = false, bool axioms = false){
                rpfp = _rpfp;
                orig_slvr = rpfp->ls->slvr;
                es = &(rpfp->SolverForEdge(edge,models,axioms)); 
                rpfp->ls->slvr = es->slvr.get();
                rpfp->AssumptionLits.swap(es->AssumptionLits);
            }
            ~scoped_solver_for_edge(){
                rpfp->ls->slvr = orig_slvr;
                rpfp->AssumptionLits.swap(es->AssumptionLits);
            }
        };

    };

}
