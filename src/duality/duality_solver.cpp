/*++
  Copyright (c) 2012 Microsoft Corporation

  Module Name:

  duality_solver.h

  Abstract:

  implements relational post-fixedpoint problem
  (RPFP) solver

  Author:

  Ken McMillan (kenmcmil)

  Revision History:


  --*/

#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#endif

#include "duality.h"
#include "duality_profiling.h"

#include <stdio.h>
#include <set>
#include <map>
#include <list>
#include <iterator>
#include <sstream>

// TODO: make these official options or get rid of them

#define NEW_CAND_SEL
// #define LOCALIZE_CONJECTURES
// #define CANDS_FROM_UPDATES
#define CANDS_FROM_COVER_FAIL
#define DEPTH_FIRST_EXPAND
#define MINIMIZE_CANDIDATES
// #define MINIMIZE_CANDIDATES_HARDER
#define BOUNDED
// #define CHECK_CANDS_FROM_IND_SET
#define UNDERAPPROX_NODES
#define NEW_EXPAND
#define EARLY_EXPAND
// #define TOP_DOWN
// #define EFFORT_BOUNDED_STRAT
#define SKIP_UNDERAPPROX_NODES
// #define KEEP_EXPANSIONS
// #define USE_CACHING_RPFP
// #define PROPAGATE_BEFORE_CHECK
#define NEW_STRATIFIED_INLINING

#define USE_RPFP_CLONE
#define USE_NEW_GEN_CANDS

//#define NO_PROPAGATE
//#define NO_GENERALIZE
//#define NO_DECISIONS

namespace Duality {

    // TODO: must be a better place for this...
    static char string_of_int_buffer[20];

    static const char *string_of_int(int n){
        sprintf(string_of_int_buffer,"%d",n);
        return string_of_int_buffer;
    }

    /** Generic object for producing diagnostic output. */

    class Reporter {
    protected:
        RPFP *rpfp;
    public:
        Reporter(RPFP *_rpfp){
            rpfp = _rpfp;
        }
        virtual void Extend(RPFP::Node *node){}
        virtual void Update(RPFP::Node *node, const RPFP::Transformer &update, bool eager){}
        virtual void Bound(RPFP::Node *node){}
        virtual void Expand(RPFP::Edge *edge){}
        virtual void AddCover(RPFP::Node *covered, std::vector<RPFP::Node *> &covering){}
        virtual void RemoveCover(RPFP::Node *covered, RPFP::Node *covering){}
        virtual void Conjecture(RPFP::Node *node, const RPFP::Transformer &t){}
        virtual void Forcing(RPFP::Node *covered, RPFP::Node *covering){}
        virtual void Dominates(RPFP::Node *node, RPFP::Node *other){}
        virtual void InductionFailure(RPFP::Edge *edge, const std::vector<RPFP::Node *> &children){}
        virtual void UpdateUnderapprox(RPFP::Node *node, const RPFP::Transformer &update){}
        virtual void Reject(RPFP::Edge *edge, const std::vector<RPFP::Node *> &Children){}
        virtual void Message(const std::string &msg){}
        virtual void Depth(int){}
        virtual ~Reporter(){}
    };

    Reporter *CreateStdoutReporter(RPFP *rpfp);
    Reporter *CreateConjectureFileReporter(RPFP *rpfp, const std::string &fname);
  
    /** Object we throw in case of catastrophe. */

    struct InternalError {
        std::string msg;
        InternalError(const std::string _msg)
            : msg(_msg) {}
    };


    /** This is the main solver. It takes anarbitrary (possibly cyclic)
        RPFP and either annotates it with a solution, or returns a
        counterexample derivation in the form of an embedd RPFP tree. */

    class Duality : public Solver {

    public:
        Duality(RPFP *_rpfp)
            : ctx(_rpfp->ctx),
              slvr(_rpfp->slvr()),
              nodes(_rpfp->nodes),
              edges(_rpfp->edges)
        {
            rpfp = _rpfp;
            reporter = 0;
            conj_reporter = 0;
            heuristic = 0;
            unwinding = 0;
            FullExpand = false;
            NoConj = false;
            FeasibleEdges = true;
            UseUnderapprox = true;
            Report = false;
            StratifiedInlining = false;
            RecursionBound = -1;
            BatchExpand = false;
            {
                scoped_no_proof no_proofs_please(ctx.m());
#ifdef USE_RPFP_CLONE
                clone_rpfp = new RPFP_caching(rpfp->ls);
                clone_rpfp->Clone(rpfp);
#endif      
#ifdef USE_NEW_GEN_CANDS
                gen_cands_rpfp = new RPFP_caching(rpfp->ls);
                gen_cands_rpfp->Clone(rpfp);
#endif      
            }
        }

        ~Duality(){
#ifdef USE_RPFP_CLONE
            delete clone_rpfp;
#endif      
#ifdef USE_NEW_GEN_CANDS
            delete gen_cands_rpfp;
#endif
            if(unwinding) delete unwinding;
        }

#ifdef USE_RPFP_CLONE
        RPFP_caching *clone_rpfp;
#endif      
#ifdef USE_NEW_GEN_CANDS
        RPFP_caching *gen_cands_rpfp;
#endif      


        typedef RPFP::Node Node;
        typedef RPFP::Edge Edge;

        /** This struct represents a candidate for extending the
            unwinding. It consists of an edge to instantiate
            and a vector of children for the new instance. */
    
        struct Candidate {
            Edge *edge; std::vector<Node *>
            Children;
        };
    
        /** Comparison operator, allowing us to sort Nodes
            by their number field. */
    
        struct lnode
        {
            bool operator()(const Node* s1, const Node* s2) const
            {
                return s1->number < s2->number;
            }
        };

        typedef std::set<Node *, lnode> Unexpanded;  // sorted set of Nodes

        /** This class provides a heuristic for expanding a derivation
            tree. */

        class Heuristic {
            RPFP *rpfp;

            /** Heuristic score for unwinding nodes. Currently this
                counts the number of updates. */
            struct score {
                int updates;
                score() : updates(0) {}
            };
            hash_map<RPFP::Node *,score> scores;
      
        public:
            Heuristic(RPFP *_rpfp){
                rpfp = _rpfp;
            }

            virtual ~Heuristic(){}

            virtual void Update(RPFP::Node *node){
                scores[node].updates++;
            }

            /** Heuristic choice of nodes to expand. Takes a set "choices"
                and returns a subset "best". We currently choose the
                nodes with the fewest updates.
            */
#if 0
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best){
                int best_score = INT_MAX;
                for(std::set<Node *>::iterator it = choices.begin(), en = choices.end(); it != en; ++it){
                    Node *node = (*it)->map;
                    int score = scores[node].updates;
                    best_score = std::min(best_score,score);
                }
                for(std::set<Node *>::iterator it = choices.begin(), en = choices.end(); it != en; ++it)
                    if(scores[(*it)->map].updates == best_score)
                        best.insert(*it);
            }
#else
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best, bool high_priority=false, bool best_only=false){
                if(high_priority) return;
                int best_score = INT_MAX;
                int worst_score = 0;
                for(std::set<Node *>::iterator it = choices.begin(), en = choices.end(); it != en; ++it){
                    Node *node = (*it)->map;
                    int score = scores[node].updates;
                    best_score = std::min(best_score,score);
                    worst_score = std::max(worst_score,score);
                }
                int cutoff = best_only ? best_score : (best_score + (worst_score-best_score)/2);
                for(std::set<Node *>::iterator it = choices.begin(), en = choices.end(); it != en; ++it)
                    if(scores[(*it)->map].updates <= cutoff)
                        best.insert(*it);
            }
#endif
      
            /** Called when done expanding a tree */
            virtual void Done() {}

            /** Ask whether a node should be used/unused in the tree. Returns,
                1 if yes, -1 if no, and 0 if don't care. */

            virtual int UseNode(Node *node){
                return 0;
            }
        };
    
        /** The Proposer class proposes conjectures eagerly. These can come
            from any source, including predicate abstraction, templates, or
            previous solver runs. The proposed conjectures are checked
            with low effort when the unwinding is expanded.
        */

        class Proposer {
        public:
            /** Given a node in the unwinding, propose some conjectures */
            virtual std::vector<RPFP::Transformer> &Propose(Node *node) = 0;
            virtual ~Proposer(){};
        };


        class Covering; // see below

        // These members represent the state of the algorithm.

        RPFP *rpfp;                          // the input RPFP 
        Reporter *reporter;                  // object for logging
        Reporter *conj_reporter;             // object for logging conjectures
        Heuristic *heuristic;                // expansion heuristic
        context &ctx;                        // Z3 context
        solver &slvr;                        // Z3 solver
        std::vector<RPFP::Node *> &nodes;    // Nodes of input RPFP
        std::vector<RPFP::Edge *> &edges;    // Edges of input RPFP
        std::vector<RPFP::Node *> leaves;    // leaf nodes of unwinding (unused)
        Unexpanded unexpanded;               // unexpanded nodes
        std::list<Candidate> candidates;     // candidates for expansion
        // maps children to edges in input RPFP
        hash_map<Node *, std::vector<Edge *> > edges_by_child;
        // maps each node in input RPFP to its expanded instances
        hash_map<Node *, std::vector<Node *> > insts_of_node;
        // maps each node in input RPFP to all its instances
        hash_map<Node *, std::vector<Node *> > all_of_node;
        RPFP *unwinding;                     // the unwinding 
        Covering *indset;                    // proposed inductive subset
        Counterexample cex;                  // counterexample
        std::list<Node *> to_expand;
        hash_set<Node *> updated_nodes;
        hash_map<Node *, Node *> underapprox_map; // maps underapprox nodes to the nodes they approximate
        int last_decisions;
        hash_set<Node *> overapproxes;
        std::vector<Proposer *> proposers;
        std::string ConjectureFile;
        bool stratified_inlining_done;

#ifdef BOUNDED
        struct Counter {
            unsigned val;
            Counter(){val = 0;}
        };
        typedef std::map<Node *,Counter> NodeToCounter;
        hash_map<Node *,NodeToCounter> back_edges; // counts of back edges
#endif
    
        /** Solve the problem. */
        virtual bool Solve(){
            PreSolve();
            bool res = SolveMain();  // does the actual work
            PostSolve();
            return res;
        }

        void PreSolve(){
            reporter = Report ? CreateStdoutReporter(rpfp) : new Reporter(rpfp);
            conj_reporter = ConjectureFile.empty() ? 0 : CreateConjectureFileReporter(rpfp,ConjectureFile); 
#ifndef LOCALIZE_CONJECTURES
            heuristic = !cex.get_tree() ? new Heuristic(rpfp) : new ReplayHeuristic(rpfp,cex);
#else
            heuristic = !cex.get_tree() ? (Heuristic *)(new LocalHeuristic(rpfp))
                : (Heuristic *)(new ReplayHeuristic(rpfp,cex));
#endif
            // determine if we are recursion bounded
            for(unsigned i = 0; i < rpfp->nodes.size(); i++)
                if(rpfp->nodes[i]->recursion_bound < UINT_MAX)
                    RecursionBound = 0;
            cex.clear(); // in case we didn't use it for heuristic
            if(unwinding) delete unwinding;
            unwinding = new RPFP(rpfp->ls);
            unwinding->HornClauses = rpfp->HornClauses;
            indset = new Covering(this);
            last_decisions = 0;
            CreateEdgesByChildMap();
#ifndef TOP_DOWN
            CreateInitialUnwinding();
#else
            CreateLeaves();
            for(unsigned i = 0; i < leaves.size(); i++)
                if(!SatisfyUpperBound(leaves[i]))
                    return false;
#endif
            StratifiedLeafCount = -1;
            stratified_inlining_done = false;
        }

        void PostSolve(){
            //  print_profile(std::cout);
            delete indset;
            delete heuristic;
            // delete unwinding; // keep the unwinding for future mining of predicates
            delete reporter;
            if(conj_reporter)
                delete conj_reporter;
            for(unsigned i = 0; i < proposers.size(); i++)
                delete proposers[i];
        }

        bool RecheckBounds(){
            for(unsigned i = 0; i < unwinding->nodes.size(); i++){
                Node *node = unwinding->nodes[i];
                node->Bound = node->map->Bound;
                if(!SatisfyUpperBound(node))
                    return false;
            }
            return true;
        }

        void CreateInitialUnwinding(){
            if(!StratifiedInlining){
                CreateLeaves();
                if(FeasibleEdges)NullaryCandidates();
                else InstantiateAllEdges();
            }
            else {
#ifdef NEW_STRATIFIED_INLINING

#else
                CreateLeaves();
#endif
            }
      
        }

        void Cancel(){
            // TODO
        }

#if 0
        virtual void Restart(RPFP *_rpfp){
            rpfp = _rpfp;
            delete unwinding;
            nodes = _rpfp->nodes;
            edges = _rpfp->edges;
            leaves.clear();
            unexpanded.clear();               // unexpanded nodes
            candidates.clear();     // candidates for expansion
            edges_by_child.clear();
            insts_of_node.clear();
            all_of_node.clear();
            to_expand.clear();
        }
#endif

        virtual void LearnFrom(Solver *other_solver){
            // get the counterexample as a guide
            cex.swap(other_solver->GetCounterexample());

            // propose conjectures based on old unwinding
            Duality *old_duality = dynamic_cast<Duality *>(other_solver);
            if(old_duality)
                proposers.push_back(new HistoryProposer(old_duality,this));
        }

        /** Return a reference to the counterexample */
        virtual Counterexample &GetCounterexample(){
            return cex;
        }

        // options
        bool FullExpand;    // do not use partial expansion of derivation tree
        bool NoConj;        // do not use conjectures (no forced covering)
        bool FeasibleEdges; // use only feasible edges in unwinding
        bool UseUnderapprox; // use underapproximations
        bool Report;         // spew on stdout
        bool StratifiedInlining; // Do stratified inlining as preprocessing step
        int RecursionBound;  // Recursion bound for bounded verification
        bool BatchExpand;
        bool EnableRestarts; 
    
        bool SetBoolOption(bool &opt, const std::string &value){
            if(value == "0") {
                opt = false;
                return true;
            }
            if(value == "1") {
                opt = true;
                return true;
            }
            return false;
        }

        bool SetIntOption(int &opt, const std::string &value){
            opt = atoi(value.c_str());
            return true;
        }

        /** Set options (not currently used) */
        virtual bool SetOption(const std::string &option, const std::string &value){
            if(option == "full_expand"){
                return SetBoolOption(FullExpand,value);
            }
            if(option == "no_conj"){
                return SetBoolOption(NoConj,value);
            }
            if(option == "feasible_edges"){
                return SetBoolOption(FeasibleEdges,value);
            }
            if(option == "use_underapprox"){
                return SetBoolOption(UseUnderapprox,value);
            }
            if(option == "report"){
                return SetBoolOption(Report,value);
            }
            if(option == "stratified_inlining"){
                return SetBoolOption(StratifiedInlining,value);
            }
            if(option == "batch_expand"){
                return SetBoolOption(BatchExpand,value);
            }
            if(option == "recursion_bound"){
                return SetIntOption(RecursionBound,value);
            }
            if(option == "conjecture_file"){
                ConjectureFile = value;
            }
            if(option == "enable_restarts"){
                return SetBoolOption(EnableRestarts,value);
            }
            return false;
        }

        /** Create an instance of a node in the unwinding. Set its
            annotation to true, and mark it unexpanded. */
        Node* CreateNodeInstance(Node *node, int number = 0){
            RPFP::Node *inst = unwinding->CloneNode(node);
            inst->Annotation.SetFull();
            if(number < 0) inst->number = number;
            unexpanded.insert(inst);
            all_of_node[node].push_back(inst);
            return inst;
        }

        /** Create an instance of an edge in the unwinding, with given
            parent and children. */
        void CreateEdgeInstance(Edge *edge, Node *parent, const std::vector<Node *> &children){
            RPFP::Edge *inst = unwinding->CreateEdge(parent,edge->F,children);
            inst->map = edge;
        }

        void MakeLeaf(Node *node, bool do_not_expand = false){
            node->Annotation.SetEmpty();
            Edge *e = unwinding->CreateLowerBoundEdge(node);
#ifdef TOP_DOWN
            node->Annotation.SetFull(); // allow this node to cover others
#endif
            if(StratifiedInlining)
                node->Annotation.SetFull(); // allow this node to cover others
            else
                updated_nodes.insert(node);
            e->map = 0;
            reporter->Extend(node);
#ifdef EARLY_EXPAND
            if(!do_not_expand)
                TryExpandNode(node);
#endif
            // e->F.SetEmpty();
        }

        void MakeOverapprox(Node *node){
            node->Annotation.SetFull();
            Edge *e = unwinding->CreateLowerBoundEdge(node);
            overapproxes.insert(node);
            e->map = 0;
        }

        /** We start the unwinding with leaves that under-approximate
            each relation with false. */
        void CreateLeaves(){
            unexpanded.clear();
            leaves.clear();
            for(unsigned i = 0; i <  nodes.size(); i++){
                RPFP::Node *node = CreateNodeInstance(nodes[i]);
                if(0 && nodes[i]->Outgoing->Children.size() == 0)
                    CreateEdgeInstance(nodes[i]->Outgoing,node,std::vector<Node *>());
                else {
                    if(!StratifiedInlining)
                        MakeLeaf(node);
                    else {
                        MakeOverapprox(node);
                        LeafMap[nodes[i]] = node;
                    }
                }
                leaves.push_back(node);
            }
        }

        /** Create the map from children to edges in the input RPFP.  This
            is used to generate candidates for expansion. */
        void CreateEdgesByChildMap(){
            edges_by_child.clear();
            for(unsigned i = 0; i < edges.size(); i++){
                Edge *e = edges[i];
                std::set<Node *> done;
                for(unsigned j = 0; j < e->Children.size(); j++){
                    Node *c = e->Children[j];
                    if(done.find(c) == done.end())  // avoid duplicates
                        edges_by_child[c].push_back(e);
                    done.insert(c);
                }
            }
        }

        void NullaryCandidates(){
            for(unsigned i = 0; i < edges.size(); i++){
                RPFP::Edge *edge = edges[i];
                if(edge->Children.size() == 0){
                    Candidate cand;
                    cand.edge = edge;
                    candidates.push_back(cand);
                }
            } 
        }

        void InstantiateAllEdges(){
            hash_map<Node *, Node *> leaf_map;
            for(unsigned i = 0; i < leaves.size(); i++){
                leaf_map[leaves[i]->map] = leaves[i];
                insts_of_node[leaves[i]->map].push_back(leaves[i]);
            }
            unexpanded.clear();
            for(unsigned i = 0; i < edges.size(); i++){
                Edge *edge = edges[i];
                Candidate c; c.edge = edge;
                c.Children.resize(edge->Children.size());
                for(unsigned j = 0; j < c.Children.size(); j++)
                    c.Children[j] = leaf_map[edge->Children[j]];
                Node *new_node;
                Extend(c,new_node);
#ifdef EARLY_EXPAND
                TryExpandNode(new_node);
#endif
            }
            for(Unexpanded::iterator it = unexpanded.begin(), en = unexpanded.end(); it != en; ++it)
                indset->Add(*it);
            for(unsigned i = 0; i < leaves.size(); i++){
                std::vector<Node *> &foo = insts_of_node[leaves[i]->map];
                foo.erase(foo.begin());
            }
        }

        bool ProducedBySI(Edge *edge, std::vector<Node *> &children){
            if(LeafMap.find(edge->Parent) == LeafMap.end()) return false;
            Node *other = LeafMap[edge->Parent];
            if(other->Outgoing->map != edge) return false;
            std::vector<Node *> &ochs = other->Outgoing->Children;
            for(unsigned i = 0; i < children.size(); i++)
                if(ochs[i] != children[i]) return false;
            return true;
        }

        /** Add a candidate for expansion, but not if Stratified inlining has already
            produced it */

        void AddCandidate(Edge *edge, std::vector<Node *> &children){
            if(StratifiedInlining && ProducedBySI(edge,children))
                return;
            candidates.push_back(Candidate());
            candidates.back().edge = edge;
            candidates.back().Children = children;
        }

        /** Generate candidates for expansion, given a vector of candidate
            sets for each argument position.  This recursively produces
            the cross product.
        */
        void GenCandidatesRec(int pos, Edge *edge,
                              const std::vector<std::vector<Node *> > &vec,
                              std::vector<Node *> &children){
            if(pos == (int)vec.size()){
                AddCandidate(edge,children);
            }
            else {
                for(unsigned i = 0; i < vec[pos].size(); i++){
                    children[pos] = vec[pos][i];
                    GenCandidatesRec(pos+1,edge,vec,children);
                }
            }
        }

        /** Setup for above recursion. */
        void GenCandidates(int pos, Edge *edge,
                           const std::vector<std::vector<Node *> > &vec){
            std::vector<Node *> children(vec.size());
            GenCandidatesRec(0,edge,vec,children);
        }

        /** Expand a node. We find all the candidates for expansion using
            this node and other already expanded nodes. This is a little
            tricky, since a node may be used for multiple argument
            positions of an edge, and we don't want to produce duplicates.
        */

#ifndef NEW_EXPAND
        void ExpandNode(Node *node){
            std::vector<Edge *> &nedges = edges_by_child[node->map];
            for(unsigned i = 0; i < nedges.size(); i++){
                Edge *edge = nedges[i];
                for(unsigned npos = 0; npos < edge->Children.size(); ++npos){
                    if(edge->Children[npos] == node->map){
                        std::vector<std::vector<Node *> > vec(edge->Children.size());
                        vec[npos].push_back(node);
                        for(unsigned j = 0; j < edge->Children.size(); j++){
                            if(j != npos){
                                std::vector<Node *> &insts = insts_of_node[edge->Children[j]];
                                for(unsigned k = 0; k < insts.size(); k++)
                                    if(indset->Candidate(insts[k]))
                                        vec[j].push_back(insts[k]);
                            }
                            if(j < npos && edge->Children[j] == node->map)
                                vec[j].push_back(node);
                        }
                        GenCandidates(0,edge,vec);
                    }
                }
            }
            unexpanded.erase(node);
            insts_of_node[node->map].push_back(node);
        }
#else
        /** If the current proposed solution is not inductive,
            use the induction failure to generate candidates for extension. */
        void ExpandNode(Node *node){
            unexpanded.erase(node);
            insts_of_node[node->map].push_back(node);
            timer_start("GenCandIndFailUsing");
            std::vector<Edge *> &nedges = edges_by_child[node->map];
            for(unsigned i = 0; i < nedges.size(); i++){
                Edge *edge = nedges[i];
                slvr.push();
                RPFP *checker = new RPFP(rpfp->ls);
                Node *root = CheckerJustForEdge(edge,checker,true);
                if(root){
                    expr using_cond = ctx.bool_val(false);
                    for(unsigned npos = 0; npos < edge->Children.size(); ++npos)
                        if(edge->Children[npos] == node->map)
                            using_cond = using_cond || checker->Localize(root->Outgoing->Children[npos]->Outgoing,NodeMarker(node));
                    slvr.add(using_cond);
                    if(checker->Check(root) != unsat){
                        Candidate candidate;
                        ExtractCandidateFromCex(edge,checker,root,candidate);
                        reporter->InductionFailure(edge,candidate.Children);
                        candidates.push_back(candidate);
                    }
                }
                slvr.pop(1);
                delete checker;
            }
            timer_stop("GenCandIndFailUsing");
        }
#endif
    
        void ExpandNodeFromOther(Node *node, Node *other){
            std::vector<Edge *> &in = other->Incoming;
            for(unsigned i = 0; i < in.size(); i++){
                Edge *edge = in[i];
                Candidate cand;
                cand.edge = edge->map;
                cand.Children = edge->Children;
                for(unsigned j = 0; j < cand.Children.size(); j++)
                    if(cand.Children[j] == other)
                        cand.Children[j] = node;
                candidates.push_front(cand);
            }
            // unexpanded.erase(node);
            // insts_of_node[node->map].push_back(node);
        }

        /** Expand a node based on some uncovered node it dominates.
            This pushes cahdidates onto the *front* of the candidate
            queue, so these expansions are done depth-first. */
        bool ExpandNodeFromCoverFail(Node *node){
            if(!node->Outgoing || node->Outgoing->Children.size() == 0)
                return false;
            Node *other = indset->GetSimilarNode(node);
            if(!other)
                return false;
#ifdef UNDERAPPROX_NODES
            Node *under_node = CreateUnderapproxNode(node);
            underapprox_map[under_node] = node;
            indset->CoverByNode(node,under_node);
            ExpandNodeFromOther(under_node,other);
            ExpandNode(under_node);
#else
            ExpandNodeFromOther(node,other);
            unexpanded.erase(node);
            insts_of_node[node->map].push_back(node);
#endif
            return true;
        }
      
    
        /** Make a boolean variable to act as a "marker" for a node. */
        expr NodeMarker(Node *node){
            std::string name = std::string("@m_") + string_of_int(node->number);
            return ctx.constant(name.c_str(),ctx.bool_sort());
        }

        /** Make a boolean variable to act as a "marker" for a pair of nodes. */
        expr NodeMarker(Node *node1, Node *node2){
            std::string name = std::string("@m_") + string_of_int(node1->number);
            name += std::string("_") + string_of_int(node2->number);
            return ctx.constant(name.c_str(),ctx.bool_sort());
        }

        /** Union the annotation of dst into src. If with_markers is
            true, we conjoin the annotation formula of dst with its
            marker. This allows us to discover which disjunct is
            true in a satisfying assignment. */
        void UnionAnnotations(RPFP::Transformer &dst, Node *src, bool with_markers = false){
            if(!with_markers)
                dst.UnionWith(src->Annotation);
            else {
                RPFP::Transformer t = src->Annotation;
                t.Formula = t.Formula && NodeMarker(src);
                dst.UnionWith(t);
            }
        }

        void GenNodeSolutionFromIndSet(Node *node, RPFP::Transformer &annot, bool with_markers = false){
            annot.SetEmpty();
            std::vector<Node *> &insts = insts_of_node[node];
            for(unsigned j = 0; j < insts.size(); j++)
                if(indset->Contains(insts[j]))
                    UnionAnnotations(annot,insts[j],with_markers);
            annot.Simplify();
        }    

        bool NodeSolutionFromIndSetFull(Node *node){
            std::vector<Node *> &insts = insts_of_node[node];
            for(unsigned j = 0; j < insts.size(); j++)
                if(indset->Contains(insts[j]))
                    if(insts[j]->Annotation.IsFull())
                        return true;
            return false;
        }

        bool recursionBounded;

        /** See if the solution might be bounded. */
        void TestRecursionBounded(){
            recursionBounded = false;
            if(RecursionBound == -1)
                return;
            for(unsigned i = 0; i < nodes.size(); i++){
                Node *node = nodes[i];
                std::vector<Node *> &insts = insts_of_node[node];
                for(unsigned j = 0; j < insts.size(); j++)
                    if(indset->Contains(insts[j]))
                        if(NodePastRecursionBound(insts[j],true))
                            recursionBounded = true;
            }
        }    

        bool IsResultRecursionBounded(){
            return recursionBounded;
        }

        /** Generate a proposed solution of the input RPFP from
            the unwinding, by unioning the instances of each node. */
        void GenSolutionFromIndSet(bool with_markers = false){
            for(unsigned i = 0; i < nodes.size(); i++){
                Node *node = nodes[i];
                GenNodeSolutionFromIndSet(node,node->Annotation,with_markers);
            }
        }

#ifdef BOUNDED
        bool NodePastRecursionBound(Node *node, bool report = false){
            if(RecursionBound < 0) return false;
            NodeToCounter &backs = back_edges[node];
            for(NodeToCounter::iterator it = backs.begin(), en = backs.end(); it != en; ++it){
                if(it->second.val > it->first->recursion_bound){
                    if(report){
                        std::ostringstream os;
                        os << "cut off " << it->first->Name.name() << " at depth " << it->second.val;
                        reporter->Message(os.str());
                    }
                    return true;
                }
            }
            return false;
        }
#endif

        /** Test whether a given extension candidate actually represents
            an induction failure. Right now we approximate this: if
            the resulting node in the unwinding could be labeled false,
            it clearly is not an induction failure. */

        bool CandidateFeasible(const Candidate &cand){
            if(!FeasibleEdges) return true;
            timer_start("CandidateFeasible");
            RPFP *checker = new RPFP(rpfp->ls);
            // std::cout << "Checking feasibility of extension " << cand.edge->Parent->number << std::endl;
            checker->Push();
            std::vector<Node *> chs(cand.Children.size());
            Node *root = checker->CloneNode(cand.edge->Parent);
#ifdef BOUNDED
            for(unsigned i = 0; i < cand.Children.size(); i++)
                if(NodePastRecursionBound(cand.Children[i])){
                    timer_stop("CandidateFeasible");
                    return false;
                }
#endif      
#ifdef NEW_CAND_SEL
            GenNodeSolutionFromIndSet(cand.edge->Parent,root->Bound);
#else
            root->Bound.SetEmpty();
#endif
            checker->AssertNode(root);
            for(unsigned i = 0; i < cand.Children.size(); i++)
                chs[i] = checker->CloneNode(cand.Children[i]);
            Edge *e = checker->CreateEdge(root,cand.edge->F,chs);
            checker->AssertEdge(e,0,true);
            // std::cout << "Checking SAT: " << e->dual << std::endl;
            bool res = checker->Check(root) != unsat;
            // std::cout << "Result: " << res << std::endl;
            if(!res)reporter->Reject(cand.edge,cand.Children);
            checker->Pop(1);
            delete checker;
            timer_stop("CandidateFeasible");
            return res;
        }


        hash_map<Node *, int> TopoSort;
        int TopoSortCounter;
        std::vector<Edge *> SortedEdges;
    
        void DoTopoSortRec(Node *node){
            if(TopoSort.find(node) != TopoSort.end())
                return;
            TopoSort[node] = INT_MAX;  // just to break cycles
            Edge *edge = node->Outgoing; // note, this is just *one* outgoing edge
            if(edge){
                std::vector<Node *> &chs = edge->Children;
                for(unsigned i = 0; i < chs.size(); i++)
                    DoTopoSortRec(chs[i]);
            }
            TopoSort[node] = TopoSortCounter++;
            SortedEdges.push_back(edge);
        }

        void DoTopoSort(){
            TopoSort.clear();
            SortedEdges.clear();
            TopoSortCounter = 0;
            for(unsigned i = 0; i < nodes.size(); i++)
                DoTopoSortRec(nodes[i]);
        }

    
        int StratifiedLeafCount;

#ifdef NEW_STRATIFIED_INLINING

        /** Stratified inlining builds an initial layered unwinding before
            switching to the LAWI strategy. Currently the number of layers
            is one. Only nodes that are the targets of back edges are
            consider to be leaves. This assumes we have already computed a
            topological sort.
        */

        bool DoStratifiedInlining(){
            if(stratified_inlining_done)
                return true;
            stratified_inlining_done = true;
            DoTopoSort();
            int depth = 1; // TODO: make this an option
            std::vector<hash_map<Node *,Node *> > unfolding_levels(depth+1);
            for(int level = 1; level <= depth; level++)
                for(unsigned i = 0; i < SortedEdges.size(); i++){
                    Edge *edge = SortedEdges[i];
                    Node *parent = edge->Parent;
                    std::vector<Node *> &chs = edge->Children;
                    std::vector<Node *> my_chs(chs.size());
                    for(unsigned j = 0; j < chs.size(); j++){
                        Node *child = chs[j];
                        int ch_level = TopoSort[child] >= TopoSort[parent] ? level-1 : level;
                        if(unfolding_levels[ch_level].find(child) == unfolding_levels[ch_level].end()){
                            if(ch_level == 0) 
                                unfolding_levels[0][child] = CreateLeaf(child);
                            else
                                throw InternalError("in levelized unwinding");
                        }
                        my_chs[j] = unfolding_levels[ch_level][child];
                    }
                    Candidate cand; cand.edge = edge; cand.Children = my_chs;
                    Node *new_node;
                    bool ok = Extend(cand,new_node);
                    MarkExpanded(new_node); // we don't expand here -- just mark it done
                    if(!ok) return false; // got a counterexample
                    unfolding_levels[level][parent] = new_node;
                }
            return true;
        }

        Node *CreateLeaf(Node *node){
            RPFP::Node *nchild = CreateNodeInstance(node);
            MakeLeaf(nchild, /* do_not_expand = */ true);
            nchild->Annotation.SetEmpty();
            return nchild;
        }      

        void MarkExpanded(Node *node){
            if(unexpanded.find(node) != unexpanded.end()){
                unexpanded.erase(node);
                insts_of_node[node->map].push_back(node);
            }
        }

#else

        /** In stratified inlining, we build the unwinding from the bottom
            down, trying to satisfy the node bounds. We do this as a pre-pass,
            limiting the expansion. If we get a counterexample, we are done,
            else we continue as usual expanding the unwinding upward.
        */

        bool DoStratifiedInlining(){
            timer_start("StratifiedInlining");
            DoTopoSort();
            for(unsigned i = 0; i < leaves.size(); i++){
                Node *node = leaves[i];
                bool res = SatisfyUpperBound(node);
                if(!res){
                    timer_stop("StratifiedInlining");
                    return false;
                }
            }
            // don't leave any dangling nodes!
#ifndef EFFORT_BOUNDED_STRAT
            for(unsigned i = 0; i < leaves.size(); i++)
                if(!leaves[i]->Outgoing)
                    MakeLeaf(leaves[i],true);    
#endif
            timer_stop("StratifiedInlining");
            return true;
        }
    
#endif

        /** Here, we do the downward expansion for stratified inlining */

        hash_map<Node *, Node *> LeafMap, StratifiedLeafMap;
    
        Edge *GetNodeOutgoing(Node *node, int last_decs = 0){
            if(overapproxes.find(node) == overapproxes.end()) return node->Outgoing; /* already expanded */
            overapproxes.erase(node);
#ifdef EFFORT_BOUNDED_STRAT
            if(last_decs > 5000){
                // RPFP::Transformer save = node->Annotation;
                node->Annotation.SetEmpty();
                Edge *e = unwinding->CreateLowerBoundEdge(node);
                // node->Annotation = save;
                insts_of_node[node->map].push_back(node);
                // std::cout << "made leaf: " << node->number << std::endl;
                return e;
            }
#endif
            Edge *edge = node->map->Outgoing;
            std::vector<Node *> &chs = edge->Children;

            // make sure we don't create a covered node in this process!

            for(unsigned i = 0; i < chs.size(); i++){
                Node *child = chs[i];
                if(TopoSort[child] < TopoSort[node->map]){
                    Node *leaf = LeafMap[child];
                    if(!indset->Contains(leaf)){
                        node->Outgoing->F.Formula = ctx.bool_val(false); // make this a proper leaf, else bogus cex
                        return node->Outgoing;
                    }
                }
            }

            std::vector<Node *> nchs(chs.size());
            for(unsigned i = 0; i < chs.size(); i++){
                Node *child = chs[i];
                if(TopoSort[child] < TopoSort[node->map]){
                    Node *leaf = LeafMap[child];
                    nchs[i] = leaf;
                    if(unexpanded.find(leaf) != unexpanded.end()){
                        unexpanded.erase(leaf);
                        insts_of_node[child].push_back(leaf);
                    }
                }
                else {
                    if(StratifiedLeafMap.find(child) == StratifiedLeafMap.end()){
                        RPFP::Node *nchild = CreateNodeInstance(child,StratifiedLeafCount--);
                        MakeLeaf(nchild);
                        nchild->Annotation.SetEmpty();
                        StratifiedLeafMap[child] = nchild;
                        indset->SetDominated(nchild);
                    }
                    nchs[i] = StratifiedLeafMap[child];
                }
            }
            CreateEdgeInstance(edge,node,nchs);
            reporter->Extend(node);
            return node->Outgoing;
        }

        void SetHeuristicOldNode(Node *node){
            LocalHeuristic *h = dynamic_cast<LocalHeuristic *>(heuristic);
            if(h)
                h->SetOldNode(node);
        }

        bool SolveMain(){
            timer_start("SolveMain");
            bool res = SolveMainInt();  // does the actual work
            timer_stop("SolveMain");
            return res;
        }

        /** This does the actual solving work. We try to generate
            candidates for extension. If we succed, we extend the
            unwinding. If we fail, we have a solution. */
        bool SolveMainInt(){
            if(StratifiedInlining && !DoStratifiedInlining())
                return false;
#ifdef BOUNDED
            DoTopoSort();
#endif
            while(true){
                timer_start("ProduceCandidatesForExtension");
                ProduceCandidatesForExtension();
                timer_stop("ProduceCandidatesForExtension");
                if(candidates.empty()){
                    GenSolutionFromIndSet();
                    TestRecursionBounded();
                    return true;
                }
                Candidate cand = candidates.front();
                candidates.pop_front();
                if(CandidateFeasible(cand)){
                    Node *new_node;
                    if(!Extend(cand,new_node))
                        return false;
#ifdef EARLY_EXPAND
                    TryExpandNode(new_node);
#endif
                }
            }
        }

        // hack: put something local into the underapproximation formula
        // without this, interpolants can be pretty bad
        void AddThing(expr &conj){
            std::string name = "@thing";
            expr thing = ctx.constant(name.c_str(),ctx.bool_sort());
            if(conj.is_app() && conj.decl().get_decl_kind() == And){
                std::vector<expr> conjs(conj.num_args()+1);
                for(unsigned i = 0; i+1 < conjs.size(); i++)
                    conjs[i] = conj.arg(i);
                conjs[conjs.size()-1] = thing;
                conj = rpfp->conjoin(conjs);
            }
        }

        Node *CreateUnderapproxNode(Node *node){
            // cex.get_tree()->ComputeUnderapprox(cex.get_root(),0);
            RPFP::Node *under_node = CreateNodeInstance(node->map /* ,StratifiedLeafCount-- */);
            under_node->Annotation.IntersectWith(cex.get_root()->Underapprox);
            AddThing(under_node->Annotation.Formula);
            Edge *e = unwinding->CreateLowerBoundEdge(under_node);
            under_node->Annotation.SetFull(); // allow this node to cover others
            back_edges[under_node] = back_edges[node];
            e->map = 0;
            reporter->Extend(under_node);
            return under_node;
        }
    
        /** Try to prove a conjecture about a node. If successful
            update the unwinding annotation appropriately. */
        bool ProveConjecture(Node *node, const RPFP::Transformer &t,Node *other = 0, Counterexample *_cex = 0){
            reporter->Conjecture(node,t);
            timer_start("ProveConjecture");
            RPFP::Transformer save = node->Bound;
            node->Bound.IntersectWith(t);

#ifndef LOCALIZE_CONJECTURES
            bool ok = SatisfyUpperBound(node);
#else
            SetHeuristicOldNode(other);
            bool ok = SatisfyUpperBound(node);
            SetHeuristicOldNode(0);
#endif      

            if(ok){
                timer_stop("ProveConjecture");
                return true;
            }
#ifdef UNDERAPPROX_NODES
            if(UseUnderapprox && last_decisions > 500){
                std::cout << "making an underapprox\n";
                ExpandNodeFromCoverFail(node);
            }
#endif
            if(_cex) (*_cex).swap(cex); // return the cex if asked
            cex.clear();                // throw away the useless cex
            node->Bound = save; // put back original bound
            timer_stop("ProveConjecture");
            return false;
        }

        /** If a node is part of the inductive subset, expand it.
            We ask the inductive subset to exclude the node if possible.
        */
        void TryExpandNode(RPFP::Node *node){
            if(indset->Close(node)) return;
            if(!NoConj && indset->Conjecture(node)){
#ifdef UNDERAPPROX_NODES
                /* TODO: temporary fix. this prevents an infinite loop in case
                   the node is covered by multiple others. This should be
                   removed when covering by a set is implemented.
                */ 
                if(indset->Contains(node)){
                    unexpanded.erase(node);
                    insts_of_node[node->map].push_back(node);
                }
#endif
                return; 
            }
#ifdef UNDERAPPROX_NODES
            if(!indset->Contains(node))
                return; // could be covered by an underapprox node
#endif
            indset->Add(node);
#if defined(CANDS_FROM_COVER_FAIL) && !defined(UNDERAPPROX_NODES)
            if(ExpandNodeFromCoverFail(node))
                return;
#endif
            ExpandNode(node);
        }

        /** Make the conjunction of markers for all (expanded) instances of
            a node in the input RPFP. */
        expr AllNodeMarkers(Node *node){
            expr res = ctx.bool_val(true);
            std::vector<Node *> &insts = insts_of_node[node];
            for(int k = insts.size()-1; k >= 0; k--)
                res = res && NodeMarker(insts[k]);
            return res;
        }

        void RuleOutNodesPastBound(Node *node, RPFP::Transformer &t){
#ifdef BOUNDED
            if(RecursionBound < 0)return;
            std::vector<Node *> &insts = insts_of_node[node];
            for(unsigned i = 0; i < insts.size(); i++)
                if(NodePastRecursionBound(insts[i]))
                    t.Formula = t.Formula && !NodeMarker(insts[i]);
#endif
        }
  
    
        void GenNodeSolutionWithMarkersAux(Node *node, RPFP::Transformer &annot, expr &marker_disjunction, Node *other_node){
#ifdef BOUNDED
            if(RecursionBound >= 0 && NodePastRecursionBound(node))
                return;
#endif
            RPFP::Transformer temp = node->Annotation;
            expr marker = (!other_node) ? NodeMarker(node) : NodeMarker(node, other_node);
            temp.Formula = (!marker || temp.Formula);
            annot.IntersectWith(temp);
            marker_disjunction = marker_disjunction || marker;
        }

        bool GenNodeSolutionWithMarkers(Node *node, RPFP::Transformer &annot, bool expanded_only = false, Node *other_node = 0){
            bool res = false;
            annot.SetFull();
            expr marker_disjunction = ctx.bool_val(false);
            std::vector<Node *> &insts = expanded_only ? insts_of_node[node] : all_of_node[node];
            for(unsigned j = 0; j < insts.size(); j++){
                Node *node = insts[j];
                if(indset->Contains(insts[j])){
                    GenNodeSolutionWithMarkersAux(node, annot, marker_disjunction, other_node); res = true;
                }
            }
            annot.Formula = annot.Formula && marker_disjunction;
            annot.Simplify();
            return res;
        }    

        /** Make a checker to determine if an edge in the input RPFP
            is satisfied. */
        Node *CheckerJustForEdge(Edge *edge, RPFP *checker, bool expanded_only = false){
            Node *root = checker->CloneNode(edge->Parent);
            GenNodeSolutionFromIndSet(edge->Parent, root->Bound);
            if(root->Bound.IsFull())
                return 0;
            checker->AssertNode(root);
            std::vector<Node *> cs;
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Node *oc = edge->Children[j];
                Node *nc = checker->CloneNode(oc);
                if(!GenNodeSolutionWithMarkers(oc,nc->Annotation,expanded_only))
                    return 0;
                Edge *e = checker->CreateLowerBoundEdge(nc);
                checker->AssertEdge(e);
                cs.push_back(nc);
            }
            checker->AssertEdge(checker->CreateEdge(root,edge->F,cs));
            return root;
        }

#ifndef MINIMIZE_CANDIDATES_HARDER

#if 0
        /** Make a checker to detheermine if an edge in the input RPFP
            is satisfied. */
        Node *CheckerForEdge(Edge *edge, RPFP *checker){
            Node *root = checker->CloneNode(edge->Parent);
            root->Bound = edge->Parent->Annotation;
            root->Bound.Formula = (!AllNodeMarkers(edge->Parent)) || root->Bound.Formula;
            checker->AssertNode(root);
            std::vector<Node *> cs;
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Node *oc = edge->Children[j];
                Node *nc = checker->CloneNode(oc);
                nc->Annotation = oc->Annotation;
                RuleOutNodesPastBound(oc,nc->Annotation);
                Edge *e = checker->CreateLowerBoundEdge(nc);
                checker->AssertEdge(e);
                cs.push_back(nc);
            }
            checker->AssertEdge(checker->CreateEdge(root,edge->F,cs));
            return root;
        }
  
#else
        /** Make a checker to determine if an edge in the input RPFP
            is satisfied. */
        Node *CheckerForEdge(Edge *edge, RPFP *checker){
            Node *root = checker->CloneNode(edge->Parent);
            GenNodeSolutionFromIndSet(edge->Parent, root->Bound);
#if 0
            if(root->Bound.IsFull())
                return = 0;
#endif
            checker->AssertNode(root);
            std::vector<Node *> cs;
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Node *oc = edge->Children[j];
                Node *nc = checker->CloneNode(oc);
                GenNodeSolutionWithMarkers(oc,nc->Annotation,true);
                Edge *e = checker->CreateLowerBoundEdge(nc);
                checker->AssertEdge(e);
                cs.push_back(nc);
            }
            checker->AssertEdge(checker->CreateEdge(root,edge->F,cs));
            return root;
        }
#endif

        /** If an edge is not satisfied, produce an extension candidate
            using instances of its children that violate the parent annotation.
            We find these using the marker predicates. */
        void ExtractCandidateFromCex(Edge *edge, RPFP *checker, Node *root, Candidate &candidate){
            candidate.edge = edge;
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Node *node = root->Outgoing->Children[j];
                Edge *lb = node->Outgoing;
                std::vector<Node *> &insts = insts_of_node[edge->Children[j]];
#ifndef MINIMIZE_CANDIDATES
                for(int k = insts.size()-1; k >= 0; k--)
#else
                    for(unsigned k = 0; k < insts.size(); k++)
#endif
                        {
                            Node *inst = insts[k];
                            if(indset->Contains(inst)){
                                if(checker->Empty(node) || 
                                   eq(lb ? checker->Eval(lb,NodeMarker(inst)) : checker->dualModel.eval(NodeMarker(inst,node)),ctx.bool_val(true))){
                                    candidate.Children.push_back(inst);
                                    goto next_child;
                                }
                            }
                        }
                throw InternalError("No candidate from induction failure");
            next_child:;
            }
        }
#else


        /** Make a checker to determine if an edge in the input RPFP
            is satisfied. */
        Node *CheckerForEdge(Edge *edge, RPFP *checker){
            Node *root = checker->CloneNode(edge->Parent);
            GenNodeSolutionFromIndSet(edge->Parent, root->Bound);
            if(root->Bound.IsFull())
                return = 0;
            checker->AssertNode(root);
            std::vector<Node *> cs;
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Node *oc = edge->Children[j];
                Node *nc = checker->CloneNode(oc);
                GenNodeSolutionWithMarkers(oc,nc->Annotation,true);
                Edge *e = checker->CreateLowerBoundEdge(nc);
                checker->AssertEdge(e);
                cs.push_back(nc);
            }
            checker->AssertEdge(checker->CreateEdge(root,edge->F,cs));
            return root;
        }

        /** If an edge is not satisfied, produce an extension candidate
            using instances of its children that violate the parent annotation.
            We find these using the marker predicates. */
        void ExtractCandidateFromCex(Edge *edge, RPFP *checker, Node *root, Candidate &candidate){
            candidate.edge = edge;
            std::vector<expr> assumps;
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Edge *lb = root->Outgoing->Children[j]->Outgoing;
                std::vector<Node *> &insts = insts_of_node[edge->Children[j]];
                for(unsigned k = 0; k < insts.size(); k++)
                    {
                        Node *inst = insts[k];
                        expr marker = NodeMarker(inst);
                        if(indset->Contains(inst)){
                            if(checker->Empty(lb->Parent) || 
                               eq(checker->Eval(lb,marker),ctx.bool_val(true))){
                                candidate.Children.push_back(inst);
                                assumps.push_back(checker->Localize(lb,marker));
                                goto next_child;
                            }
                            assumps.push_back(checker->Localize(lb,marker));
                            if(checker->CheckUpdateModel(root,assumps) != unsat){
                                candidate.Children.push_back(inst);
                                goto next_child;
                            }
                            assumps.pop_back();
                        }
                    }
                throw InternalError("No candidate from induction failure");
            next_child:;
            }
        }

#endif


        Node *CheckerForEdgeClone(Edge *edge, RPFP_caching *checker){
            Edge *gen_cands_edge = checker->GetEdgeClone(edge);
            Node *root = gen_cands_edge->Parent;
            root->Outgoing = gen_cands_edge;
            GenNodeSolutionFromIndSet(edge->Parent, root->Bound);
#if 0
            if(root->Bound.IsFull())
                return = 0;
#endif
            checker->AssertNode(root);
            for(unsigned j = 0; j < edge->Children.size(); j++){
                Node *oc = edge->Children[j];
                Node *nc = gen_cands_edge->Children[j];
                GenNodeSolutionWithMarkers(oc,nc->Annotation,true,nc);
            }
            checker->AssertEdge(gen_cands_edge,1,true);
            return root;
        }

        /** If the current proposed solution is not inductive,
            use the induction failure to generate candidates for extension. */
        void GenCandidatesFromInductionFailure(bool full_scan = false){
            timer_start("GenCandIndFail");
            GenSolutionFromIndSet(true /* add markers */);
            for(unsigned i = 0; i < edges.size(); i++){
                Edge *edge = edges[i];
                if(!full_scan && updated_nodes.find(edge->Parent) == updated_nodes.end())
                    continue;
#ifndef USE_NEW_GEN_CANDS
                slvr.push();
                RPFP *checker = new RPFP(rpfp->ls);
                Node *root = CheckerForEdge(edge,checker);
                if(checker->Check(root) != unsat){
                    Candidate candidate;
                    ExtractCandidateFromCex(edge,checker,root,candidate);
                    reporter->InductionFailure(edge,candidate.Children);
                    candidates.push_back(candidate);
                }
                slvr.pop(1);
                delete checker;
#else
                if(!NodeSolutionFromIndSetFull(edge->Parent)){
                    RPFP_caching::scoped_solver_for_edge ssfe(gen_cands_rpfp,edge,true /* models */, true /*axioms*/);
                    gen_cands_rpfp->Push();
                    Node *root = CheckerForEdgeClone(edge,gen_cands_rpfp);
                    if(gen_cands_rpfp->Check(root) != unsat){
                        Candidate candidate;
                        ExtractCandidateFromCex(edge,gen_cands_rpfp,root,candidate);
                        reporter->InductionFailure(edge,candidate.Children);
                        candidates.push_back(candidate);
                    }
                    gen_cands_rpfp->Pop(1);
                }
#endif
            }
            updated_nodes.clear();
            timer_stop("GenCandIndFail");
#ifdef CHECK_CANDS_FROM_IND_SET
            for(std::list<Candidate>::iterator it = candidates.begin(), en = candidates.end(); it != en; ++it){
                if(!CandidateFeasible(*it))
                    throw "produced infeasible candidate";
            }
#endif
            if(!full_scan && candidates.empty()){
                reporter->Message("No candidates from updates. Trying full scan.");
                GenCandidatesFromInductionFailure(true);
            }
        }

#ifdef CANDS_FROM_UPDATES
        /** If the given edge is not inductive in the current proposed solution,
            use the induction failure to generate candidates for extension. */
        void GenCandidatesFromEdgeInductionFailure(RPFP::Edge *edge){
            GenSolutionFromIndSet(true /* add markers */);
            for(unsigned i = 0; i < edges.size(); i++){
                slvr.push();
                Edge *edge = edges[i];
                RPFP *checker = new RPFP(rpfp->ls);
                Node *root = CheckerForEdge(edge,checker);
                if(checker->Check(root) != unsat){
                    Candidate candidate;
                    ExtractCandidateFromCex(edge,checker,root,candidate);
                    reporter->InductionFailure(edge,candidate.Children);
                    candidates.push_back(candidate);
                }
                slvr.pop(1);
                delete checker;
            }
        }
#endif

        /** Find the unexpanded nodes in the inductive subset. */
        void FindNodesToExpand(){
            for(Unexpanded::iterator it = unexpanded.begin(), en = unexpanded.end(); it != en; ++it){
                Node *node = *it;
                if(indset->Candidate(node))
                    to_expand.push_back(node);
            }
        }

        /** Try to create some extension candidates from the unexpanded
            nodes. */
        void ProduceSomeCandidates(){
            while(candidates.empty() && !to_expand.empty()){
                Node *node = to_expand.front();
                to_expand.pop_front();
                TryExpandNode(node);
            }
        }
  
        std::list<Candidate> postponed_candidates;

        /** Try to produce some extension candidates, first from unexpanded
            nides, and if this fails, from induction failure. */
        void ProduceCandidatesForExtension(){
            if(candidates.empty())
                ProduceSomeCandidates();
            while(candidates.empty()){
                FindNodesToExpand();
                if(to_expand.empty()) break;
                ProduceSomeCandidates();
            }
            if(candidates.empty()){
#ifdef DEPTH_FIRST_EXPAND
                if(postponed_candidates.empty()){
                    GenCandidatesFromInductionFailure();
                    postponed_candidates.swap(candidates);
                }
                if(!postponed_candidates.empty()){
                    candidates.push_back(postponed_candidates.front());
                    postponed_candidates.pop_front();
                }
#else
                GenCandidatesFromInductionFailure();
#endif
            }
        }

        bool Update(Node *node, const RPFP::Transformer &fact, bool eager=false){
            if(!node->Annotation.SubsetEq(fact)){
                reporter->Update(node,fact,eager);
                if(conj_reporter)
                    conj_reporter->Update(node,fact,eager);
                indset->Update(node,fact);
                updated_nodes.insert(node->map);
                node->Annotation.IntersectWith(fact);
                return true;
            }
            return false;
        }
    
        bool UpdateNodeToNode(Node *node, Node *top){
            return Update(node,top->Annotation);
        }

        /** Update the unwinding solution, using an interpolant for the
            derivation tree. */
        void UpdateWithInterpolant(Node *node, RPFP *tree, Node *top){
            if(top->Outgoing)
                for(unsigned i = 0; i < top->Outgoing->Children.size(); i++)
                    UpdateWithInterpolant(node->Outgoing->Children[i],tree,top->Outgoing->Children[i]);
            UpdateNodeToNode(node, top);
            heuristic->Update(node);
        }

        /** Update unwinding lower bounds, using a counterexample. */

        void UpdateWithCounterexample(Node *node, RPFP *tree, Node *top){
            if(top->Outgoing)
                for(unsigned i = 0; i < top->Outgoing->Children.size(); i++)
                    UpdateWithCounterexample(node->Outgoing->Children[i],tree,top->Outgoing->Children[i]);
            if(!top->Underapprox.SubsetEq(node->Underapprox)){
                reporter->UpdateUnderapprox(node,top->Underapprox);
                // indset->Update(node,top->Annotation);
                node->Underapprox.UnionWith(top->Underapprox);
                heuristic->Update(node);
            }
        }

        /** Try to update the unwinding to satisfy the upper bound of a
            node. */
        bool SatisfyUpperBound(Node *node){
            if(node->Bound.IsFull()) return true;
#ifdef PROPAGATE_BEFORE_CHECK
            Propagate();
#endif
            reporter->Bound(node);
            int start_decs = rpfp->CumulativeDecisions();
            DerivationTree *dtp = new DerivationTreeSlow(this,unwinding,reporter,heuristic,FullExpand);
            DerivationTree &dt = *dtp;
            bool res = dt.Derive(unwinding,node,UseUnderapprox);
            int end_decs = rpfp->CumulativeDecisions();
            // std::cout << "decisions: " << (end_decs - start_decs)  << std::endl;
            last_decisions = end_decs - start_decs;
            if(res){
                cex.set(dt.tree,dt.top); // note tree is now owned by cex
                if(UseUnderapprox){
                    UpdateWithCounterexample(node,dt.tree,dt.top);
                }
            }
            else {
                UpdateWithInterpolant(node,dt.tree,dt.top);
                delete dt.tree;
            }
            delete dtp;
            return !res;
        }
    
        /* For a given nod in the unwinding, get conjectures from the
           proposers and check them locally. Update the node with any true
           conjectures.
        */

        void DoEagerDeduction(Node *node){
            for(unsigned i = 0; i < proposers.size(); i++){
                const std::vector<RPFP::Transformer> &conjectures = proposers[i]->Propose(node);
                for(unsigned j = 0; j < conjectures.size(); j++){ 
                    const RPFP::Transformer &conjecture = conjectures[j];
                    RPFP::Transformer bound(conjecture);
                    std::vector<expr> conj_vec;
                    unwinding->CollectConjuncts(bound.Formula,conj_vec);
                    for(unsigned k = 0; k < conj_vec.size(); k++){
                        bound.Formula = conj_vec[k];
                        if(CheckEdgeCaching(node->Outgoing,bound) == unsat)
                            Update(node,bound, /* eager = */ true);
                        //else
                        //std::cout << "conjecture failed\n";
                    }
                }
            }
        }

      
        check_result CheckEdge(RPFP *checker, Edge *edge){
            Node *root = edge->Parent;
            checker->Push();
            checker->AssertNode(root);
            checker->AssertEdge(edge,1,true);
            check_result res = checker->Check(root);
            checker->Pop(1);
            return res;
        }

        check_result CheckEdgeCaching(Edge *unwinding_edge, const RPFP::Transformer &bound){

            // use a dedicated solver for this edge
            // TODO: can this mess be hidden somehow?

            RPFP_caching *checker = gen_cands_rpfp; // TODO: a good choice?
            Edge *edge = unwinding_edge->map; // get the edge in the original RPFP
            RPFP_caching::scoped_solver_for_edge ssfe(checker,edge,true /* models */, true /*axioms*/);
            Edge *checker_edge = checker->GetEdgeClone(edge);
      
            // copy the annotations and bound to the clone
            Node *root = checker_edge->Parent;
            root->Bound = bound;
            for(unsigned j = 0; j < checker_edge->Children.size(); j++){
                Node *oc = unwinding_edge->Children[j];
                Node *nc = checker_edge->Children[j];
                nc->Annotation = oc->Annotation;
            }
      
            return CheckEdge(checker,checker_edge);
        }


        /* If the counterexample derivation is partial due to
           use of underapproximations, complete it. */

        void BuildFullCex(Node *node){
            DerivationTree dt(this,unwinding,reporter,heuristic,FullExpand); 
            bool res = dt.Derive(unwinding,node,UseUnderapprox,true); // build full tree
            if(!res) throw "Duality internal error in BuildFullCex";
            cex.set(dt.tree,dt.top);
        }
    
        void UpdateBackEdges(Node *node){
#ifdef BOUNDED
            std::vector<Node *> &chs = node->Outgoing->Children;
            for(unsigned i = 0; i < chs.size(); i++){
                Node *child = chs[i];
                bool is_back = TopoSort[child->map] >= TopoSort[node->map];
                NodeToCounter &nov = back_edges[node];
                NodeToCounter chv = back_edges[child];
                if(is_back)
                    chv[child->map].val++;
                for(NodeToCounter::iterator it = chv.begin(), en = chv.end(); it != en; ++it){
                    Node *back = it->first;
                    Counter &c = nov[back];
                    c.val = std::max(c.val,it->second.val);
                }
            }
#endif
        }

        /** Extend the unwinding, keeping it solved. */
        bool Extend(Candidate &cand, Node *&node){
            timer_start("Extend");
            node = CreateNodeInstance(cand.edge->Parent);
            CreateEdgeInstance(cand.edge,node,cand.Children);
            UpdateBackEdges(node);
            reporter->Extend(node);
            DoEagerDeduction(node); // first be eager...
            bool res = SatisfyUpperBound(node); // then be lazy
            if(res) indset->CloseDescendants(node);
            else {
#ifdef UNDERAPPROX_NODES
                ExpandUnderapproxNodes(cex.get_tree(), cex.get_root());
#endif
                if(UseUnderapprox) BuildFullCex(node);
                timer_stop("Extend");
                return res;
            }
            timer_stop("Extend");
            return res;
        }

        void ExpandUnderapproxNodes(RPFP *tree, Node *root){
            Node *node = root->map;
            if(underapprox_map.find(node) != underapprox_map.end()){
                RPFP::Transformer cnst = root->Annotation;
                tree->EvalNodeAsConstraint(root, cnst);
                cnst.Complement();
                Node *orig = underapprox_map[node];
                RPFP::Transformer save = orig->Bound;
                orig->Bound = cnst;
                DerivationTree dt(this,unwinding,reporter,heuristic,FullExpand);
                bool res = dt.Derive(unwinding,orig,UseUnderapprox,true,tree);
                if(!res){
                    UpdateWithInterpolant(orig,dt.tree,dt.top);
                    throw "bogus underapprox!";
                }
                ExpandUnderapproxNodes(tree,dt.top);
            }
            else if(root->Outgoing){
                std::vector<Node *> &chs = root->Outgoing->Children;
                for(unsigned i = 0; i < chs.size(); i++)
                    ExpandUnderapproxNodes(tree,chs[i]);
            }
        }

        // Propagate conjuncts up the unwinding
        void Propagate(){
            reporter->Message("beginning propagation");
            timer_start("Propagate");
            std::vector<Node *> sorted_nodes = unwinding->nodes;
            std::sort(sorted_nodes.begin(),sorted_nodes.end(),std::less<Node *>()); // sorts by sequence number
            hash_map<Node *,std::set<expr> > facts;
            for(unsigned i = 0; i < sorted_nodes.size(); i++){
                Node *node = sorted_nodes[i];
                std::set<expr> &node_facts = facts[node->map];
                if(!(node->Outgoing && indset->Contains(node)))
                    continue;
                std::vector<expr> conj_vec;
                unwinding->CollectConjuncts(node->Annotation.Formula,conj_vec);
                std::set<expr> conjs;
                std::copy(conj_vec.begin(),conj_vec.end(),std::inserter(conjs,conjs.begin()));
                if(!node_facts.empty()){
                    RPFP *checker = new RPFP(rpfp->ls);
                    slvr.push();
                    Node *root = checker->CloneNode(node);
                    Edge *edge = node->Outgoing;
                    // checker->AssertNode(root);
                    std::vector<Node *> cs;
                    for(unsigned j = 0; j < edge->Children.size(); j++){
                        Node *oc = edge->Children[j];
                        Node *nc = checker->CloneNode(oc);
                        nc->Annotation = oc->Annotation; // is this needed?
                        cs.push_back(nc);
                    }
                    Edge *checker_edge = checker->CreateEdge(root,edge->F,cs); 
                    checker->AssertEdge(checker_edge, 0, true, false);
                    std::vector<expr> propagated;
                    for(std::set<expr> ::iterator it = node_facts.begin(), en = node_facts.end(); it != en;){
                        const expr &fact = *it;
                        if(conjs.find(fact) == conjs.end()){
                            root->Bound.Formula = fact;
                            slvr.push();
                            checker->AssertNode(root);
                            check_result res = checker->Check(root);
                            slvr.pop();
                            if(res != unsat){
                                std::set<expr> ::iterator victim = it;
                                ++it;
                                node_facts.erase(victim); // if it ain't true, nix it
                                continue;
                            }
                            propagated.push_back(fact);
                        }
                        ++it;
                    }
                    slvr.pop();
                    for(unsigned i = 0; i < propagated.size(); i++){
                        root->Annotation.Formula = propagated[i];
                        UpdateNodeToNode(node,root);
                    }
                    delete checker;
                }
                for(std::set<expr> ::iterator it = conjs.begin(), en = conjs.end(); it != en; ++it){
                    expr foo = *it;
                    node_facts.insert(foo);
                }
            }
            timer_stop("Propagate");
        }
    

        /** This class represents a derivation tree. */
        class DerivationTree {
        public:

            virtual ~DerivationTree(){}

            DerivationTree(Duality *_duality, RPFP *rpfp, Reporter *_reporter, Heuristic *_heuristic, bool _full_expand) 
                : slvr(rpfp->slvr()),
                  ctx(rpfp->ctx)
            {
                duality = _duality;
                reporter = _reporter;
                heuristic = _heuristic; 
                full_expand = _full_expand;
            }

            Duality *duality;
            Reporter *reporter;
            Heuristic *heuristic;
            solver &slvr;
            context &ctx;
            RPFP *tree; 
            RPFP::Node *top;
            std::list<RPFP::Node *> leaves;
            bool full_expand;
            bool underapprox; 
            bool constrained;
            bool false_approx; 
            std::vector<Node *> underapprox_core;
            int start_decs, last_decs;

            /* We build derivation trees in one of three modes:

               1) In normal mode, we build the full tree without considering
               underapproximations.

               2) In underapprox mode, we use underapproximations to cut off
               the tree construction. THis means the resulting tree may not
               be complete.

               3) In constrained mode, we build the full tree but use
               underapproximations as upper bounds. This mode is used to
               complete the partial derivation constructed in underapprox
               mode.
            */

            bool Derive(RPFP *rpfp, RPFP::Node *root, bool _underapprox, bool _constrained = false, RPFP *_tree = 0){
                underapprox = _underapprox;
                constrained = _constrained;
                false_approx = true;
                timer_start("Derive");
#ifndef USE_CACHING_RPFP
                tree = _tree ? _tree : new RPFP(rpfp->ls);
#else
                RPFP::LogicSolver *cache_ls = new RPFP::iZ3LogicSolver(ctx);
                cache_ls->slvr->push();
                tree = _tree ? _tree : new RPFP_caching(cache_ls);
#endif
                tree->HornClauses = rpfp->HornClauses;
                tree->Push(); // so we can clear out the solver later when finished
                top = CreateApproximatedInstance(root);
                tree->AssertNode(top); // assert the negation of the top-level spec
                timer_start("Build");
                bool res = Build();
                heuristic->Done();
                timer_stop("Build");
                timer_start("Pop");
                tree->Pop(1);
                timer_stop("Pop");
#ifdef USE_CACHING_RPFP
                cache_ls->slvr->pop(1);
                delete cache_ls;
                tree->ls = rpfp->ls;
#endif
                timer_stop("Derive");
                return res;
            }

#define WITH_CHILDREN

            void InitializeApproximatedInstance(RPFP::Node *to){
                to->Annotation = to->map->Annotation;
#ifndef WITH_CHILDREN
                tree->CreateLowerBoundEdge(to);
#endif
                leaves.push_back(to);
            }

            Node *CreateApproximatedInstance(RPFP::Node *from){
                Node *to = tree->CloneNode(from);
                InitializeApproximatedInstance(to);
                return to;
            }

            bool CheckWithUnderapprox(){
                timer_start("CheckWithUnderapprox");
                std::vector<Node *> leaves_vector(leaves.size());
                std::copy(leaves.begin(),leaves.end(),leaves_vector.begin());
                check_result res = tree->Check(top,leaves_vector);
                timer_stop("CheckWithUnderapprox");
                return res != unsat;
            }

            virtual bool Build(){
#ifdef EFFORT_BOUNDED_STRAT
                start_decs = tree->CumulativeDecisions();
#endif
                while(ExpandSomeNodes(true)); // do high-priority expansions
                while (true)
                    {
#ifndef WITH_CHILDREN
                        timer_start("asserting leaves");
                        timer_start("pushing");
                        tree->Push();
                        timer_stop("pushing");
                        for(std::list<RPFP::Node *>::iterator it = leaves.begin(), en = leaves.end(); it != en; ++it)
                            tree->AssertEdge((*it)->Outgoing,1);    // assert the overapproximation, and keep it past pop
                        timer_stop("asserting leaves");
                        lbool res = tree->Solve(top, 2);            // incremental solve, keep interpolants for two pops
                        timer_start("popping leaves");
                        tree->Pop(1);
                        timer_stop("popping leaves");
#else
                        lbool res;
                        if((underapprox || false_approx) && top->Outgoing && CheckWithUnderapprox()){
                            if(constrained) goto expand_some_nodes;   // in constrained mode, keep expanding
                            goto we_are_sat;                          // else if underapprox is sat, we stop
                        }
                        // tree->Check(top);
                        res = tree->Solve(top, 1);            // incremental solve, keep interpolants for one pop
#endif
                        if (res == l_false)
                            return false;

                    expand_some_nodes:
                        if(ExpandSomeNodes())
                            continue;

                    we_are_sat:
                        if(underapprox && !constrained){
                            timer_start("ComputeUnderapprox");
                            tree->ComputeUnderapprox(top,1);
                            timer_stop("ComputeUnderapprox");
                        }
                        else {
#ifdef UNDERAPPROX_NODES
#ifndef SKIP_UNDERAPPROX_NODES
                            timer_start("ComputeUnderapprox");
                            tree->ComputeUnderapprox(top,1);
                            timer_stop("ComputeUnderapprox");
#endif
#endif
                        }
                        return true;
                    }
            }

            virtual void ExpandNode(RPFP::Node *p){
                // tree->RemoveEdge(p->Outgoing);
                Edge *ne = p->Outgoing;
                if(ne) {
                    // reporter->Message("Recycling edge...");
                    std::vector<RPFP::Node *> &cs = ne->Children;
                    for(unsigned i = 0; i < cs.size(); i++)
                        InitializeApproximatedInstance(cs[i]);
                    // ne->dual = expr();
                }
                else {
                    Edge *edge = duality->GetNodeOutgoing(p->map,last_decs);
                    std::vector<RPFP::Node *> &cs = edge->Children;
                    std::vector<RPFP::Node *> children(cs.size());
                    for(unsigned i = 0; i < cs.size(); i++)
                        children[i] = CreateApproximatedInstance(cs[i]);
                    ne = tree->CreateEdge(p, p->map->Outgoing->F, children);
                    ne->map = p->map->Outgoing->map;
                }
#ifndef WITH_CHILDREN
                tree->AssertEdge(ne);  // assert the edge in the solver
#else
                tree->AssertEdge(ne,0,!full_expand,(underapprox || false_approx));  // assert the edge in the solver
#endif
                reporter->Expand(ne);
            }

#define      UNDERAPPROXCORE
#ifndef UNDERAPPROXCORE
            void ExpansionChoices(std::set<Node *> &best){
                std::set<Node *> choices;
                for(std::list<RPFP::Node *>::iterator it = leaves.begin(), en = leaves.end(); it != en; ++it)
                    if (!tree->Empty(*it)) // if used in the counter-model
                        choices.insert(*it);
                heuristic->ChooseExpand(choices, best);
            }
#else
#if 0

            void ExpansionChoices(std::set<Node *> &best){
                std::vector <Node *> unused_set, used_set;
                std::set<Node *> choices;
                for(std::list<RPFP::Node *>::iterator it = leaves.begin(), en = leaves.end(); it != en; ++it){
                    Node *n = *it;
                    if (!tree->Empty(n))
                        used_set.push_back(n);
                    else
                        unused_set.push_back(n);
                }
                if(tree->Check(top,unused_set) == unsat)
                    throw "error in ExpansionChoices";
                for(unsigned i = 0; i < used_set.size(); i++){
                    Node *n = used_set[i];
                    unused_set.push_back(n);
                    if(!top->Outgoing || tree->Check(top,unused_set) == unsat){
                        unused_set.pop_back();
                        choices.insert(n);
                    }
                    else
                        std::cout << "Using underapprox of " << n->number << std::endl;
                }
                heuristic->ChooseExpand(choices, best);
            }
#else
            void ExpansionChoicesFull(std::set<Node *> &best, bool high_priority, bool best_only = false){
                std::set<Node *> choices;
                for(std::list<RPFP::Node *>::iterator it = leaves.begin(), en = leaves.end(); it != en; ++it)
                    if (high_priority || !tree->Empty(*it)) // if used in the counter-model
                        choices.insert(*it);
                heuristic->ChooseExpand(choices, best, high_priority, best_only);
            }

            void ExpansionChoicesRec(std::vector <Node *> &unused_set, std::vector <Node *> &used_set, 
                                     std::set<Node *> &choices, int from, int to){
                if(from == to) return;
                int orig_unused = unused_set.size();
                unused_set.resize(orig_unused + (to - from));
                std::copy(used_set.begin()+from,used_set.begin()+to,unused_set.begin()+orig_unused);
                if(!top->Outgoing || tree->Check(top,unused_set) == unsat){
                    unused_set.resize(orig_unused);
                    if(to - from == 1){
#if 1
                        std::cout << "Not using underapprox of " << used_set[from] ->number << std::endl;
#endif
                        choices.insert(used_set[from]);
                    }
                    else {
                        int mid = from + (to - from)/2;
                        ExpansionChoicesRec(unused_set, used_set, choices, from, mid);
                        ExpansionChoicesRec(unused_set, used_set, choices, mid, to);
                    }
                }
                else {
#if 1
                    std::cout << "Using underapprox of ";
                    for(int i = from; i < to; i++){
                        std::cout << used_set[i]->number << " ";
                        if(used_set[i]->map->Underapprox.IsEmpty())
                            std::cout << "(false!) ";
                    }
                    std::cout  << std::endl;
#endif
                }
            }
      
            std::set<Node *> old_choices;

            void ExpansionChoices(std::set<Node *> &best, bool high_priority, bool best_only = false){
                if(!underapprox || constrained || high_priority){
                    ExpansionChoicesFull(best, high_priority,best_only);
                    return;
                }
                std::vector <Node *> unused_set, used_set;
                std::set<Node *> choices;
                for(std::list<RPFP::Node *>::iterator it = leaves.begin(), en = leaves.end(); it != en; ++it){
                    Node *n = *it;
                    if (!tree->Empty(n)){
                        if(old_choices.find(n) != old_choices.end() || n->map->Underapprox.IsEmpty())
                            choices.insert(n);
                        else
                            used_set.push_back(n);
                    }
                    else
                        unused_set.push_back(n);
                }
                if(tree->Check(top,unused_set) == unsat)
                    throw "error in ExpansionChoices";
                ExpansionChoicesRec(unused_set, used_set, choices, 0, used_set.size());
                old_choices = choices;
                heuristic->ChooseExpand(choices, best, high_priority);
            }
#endif
#endif
      
            bool ExpandSomeNodes(bool high_priority = false, int max = INT_MAX){
#ifdef EFFORT_BOUNDED_STRAT
                last_decs = tree->CumulativeDecisions() - start_decs;
#endif
                timer_start("ExpandSomeNodes");
                timer_start("ExpansionChoices");
                std::set<Node *> choices;
                ExpansionChoices(choices,high_priority,max != INT_MAX);
                timer_stop("ExpansionChoices");
                std::list<RPFP::Node *> leaves_copy = leaves; // copy so can modify orig
                leaves.clear();
                int count = 0;
                for(std::list<RPFP::Node *>::iterator it = leaves_copy.begin(), en = leaves_copy.end(); it != en; ++it){
                    if(choices.find(*it) != choices.end() && count < max){
                        count++;
                        ExpandNode(*it);
                    }
                    else leaves.push_back(*it);
                }
                timer_stop("ExpandSomeNodes");
                return !choices.empty();
            }

            void RemoveExpansion(RPFP::Node *p){
                Edge *edge = p->Outgoing;
                Node *parent = edge->Parent; 
#ifndef KEEP_EXPANSIONS
                std::vector<RPFP::Node *> cs = edge->Children;
                tree->DeleteEdge(edge);
                for(unsigned i = 0; i < cs.size(); i++)
                    tree->DeleteNode(cs[i]);
#endif
                leaves.push_back(parent);
            }
      
            // remove all the descendants of tree root (but not root itself)
            void RemoveTree(RPFP *tree, RPFP::Node *root){
                Edge *edge = root->Outgoing;
                std::vector<RPFP::Node *> cs = edge->Children;
                tree->DeleteEdge(edge);
                for(unsigned i = 0; i < cs.size(); i++){
                    RemoveTree(tree,cs[i]);
                    tree->DeleteNode(cs[i]);
                }
            }
        };

        class DerivationTreeSlow : public DerivationTree {
        public:
      
            struct stack_entry {
                unsigned level; // SMT solver stack level
                std::vector<Node *> expansions;
            };

            std::vector<stack_entry> stack;

            hash_map<Node *, expr> updates;

            int restart_interval;

            DerivationTreeSlow(Duality *_duality, RPFP *rpfp, Reporter *_reporter, Heuristic *_heuristic, bool _full_expand) 
                : DerivationTree(_duality, rpfp, _reporter, _heuristic, _full_expand) {
                stack.push_back(stack_entry());
            }

            struct DoRestart {};

            virtual bool Build(){
                restart_interval = 3;
                while (true) {
                    try {
                        return BuildMain();
                    }
                    catch (const DoRestart &) {
                        // clear the statck and try again
                        updated_nodes.clear();
                        while(stack.size() > 1)
                            PopLevel();
                        reporter->Message("restarted");
                        restart_interval += 1;
                    }
                }
            }


            // When we check, try to use the same children that were used in the
            // previous counterexample.
            check_result Check(){
#if 0
                std::vector<Node *> posnodes, negnodes;
                std::vector<Node *> &expansions = stack.back().expansions;
                for(unsigned i = 0; i < expansions.size(); i++){
                    Node *node = expansions[i];
                    std::vector<Node*> &chs = node->Outgoing->Children;
                    for(unsigned j = 0; j < chs.size(); j++){
                        Node *ch = chs[j];
                        int use = heuristic->UseNode(ch); 
                        if(use == 1)
                            posnodes.push_back(ch);
                        else if (use == -1)
                            negnodes.push_back(ch);
                    }
                }
                if(!(posnodes.empty() && negnodes.empty())){
                    check_result res = tree->CheckWithConstrainedNodes(posnodes,negnodes);
                    if(res != unsat){
                        reporter->Message("matched previous counterexample");
                        return res;
                    }
                }
#endif
                return tree->Check(top);
            }

            bool BuildMain(){

                stack.back().level = tree->slvr().get_scope_level();
                bool was_sat = true;
                int update_failures = 0;
                int total_updates = 0;

                while (true)
                    {
                        lbool res;

                        unsigned slvr_level = tree->slvr().get_scope_level();
                        if(slvr_level != stack.back().level)
                            throw "stacks out of sync!";
                        reporter->Depth(stack.size());

                        //   res = tree->Solve(top, 1);            // incremental solve, keep interpolants for one pop
                        check_result foo = Check();
                        res = foo == unsat ? l_false : l_true;

                        if (res == l_false) {
                            if (stack.empty()) // should never happen
                                return false;

                            {
                                std::vector<Node *> &expansions = stack.back().expansions;
                                int update_count = 0;
                                for(unsigned i = 0; i < expansions.size(); i++){
                                    Node *node = expansions[i];
                                    try {
                                        tree->SolveSingleNode(top,node);
#ifdef NO_GENERALIZE
                                        node->Annotation.Formula = tree->RemoveRedundancy(node->Annotation.Formula).simplify();
#else
                                        if(expansions.size() == 1 && NodeTooComplicated(node))
                                            SimplifyNode(node);
                                        else
                                            node->Annotation.Formula = tree->RemoveRedundancy(node->Annotation.Formula).simplify();
                                        Generalize(node);
#endif
                                    }
                                    catch(const RPFP::Bad &){
                                        // bad interpolants can get us here
                                        throw DoRestart();
                                    }
                                    catch(const RPFP::ReallyBad &){
                                        // this could be caused by incompleteness
                                        for(unsigned i = 0; i < expansions.size(); i++){
                                            Node *node = expansions[i];
                                            node->map->Annotation.SetFull();
                                            std::vector<Node *> &chs = node->map->Outgoing->Children;
                                            for(unsigned j = 0; j < chs.size(); j++)
                                                chs[j]->Annotation.SetFull();
                                            reporter->Message("incompleteness: cleared annotation and child annotations");
                                        }
                                        throw DoRestart();
                                    }
                                    catch(char const *msg){
                                        // bad interpolants can get us here
                                        reporter->Message(std::string("interpolation failure:") + msg);
                                        throw DoRestart();
                                    }
                                    catch(const RPFP::greedy_reduce_failed &){
                                        // if we couldn't reduce, just continue (maybe should restart?)
                                        reporter->Message("interpolant verification failed");
                                    }
                                    if(RecordUpdate(node)){
                                        update_count++;
                                        total_updates++;
                                    }
                                    else
                                        heuristic->Update(node->map); // make it less likely to expand this node in future
                                }
#if 1
                                if(duality->EnableRestarts)
                                    if(total_updates >= restart_interval)
                                        throw DoRestart();
#endif
                                if(update_count == 0){
                                    if(was_sat){
                                        update_failures++;
                                        if(update_failures > 10){
                                            for(unsigned i = 0; i < expansions.size(); i++){
                                                Node *node = expansions[i];
                                                node->map->Annotation.SetFull();
                                                reporter->Message("incompleteness: cleared annotation");
                                            }
                                            throw DoRestart();
                                        }
                                    }
                                    reporter->Message("backtracked without learning");
                                }
                                else update_failures = 0;
                            }
                            tree->ComputeProofCore(); // need to compute the proof core before popping solver
                            bool propagated = false;
                            while(1) {
                                bool prev_level_used = LevelUsedInProof(stack.size()-2); // need to compute this before pop
                                PopLevel();
                                if(stack.size() == 1)break;
                                if(prev_level_used){
                                    Node *node = stack.back().expansions[0];
#ifndef NO_PROPAGATE
                                    if(!Propagate(node)) break;
#endif
                                    if(!RecordUpdate(node)) break; // shouldn't happen!
                                    RemoveUpdateNodesAtCurrentLevel(); // this level is about to be deleted -- remove its children from update list
                                    propagated = true;
                                    continue;
                                }
                                if(propagated) break;  // propagation invalidates the proof core, so disable non-chron backtrack
                                RemoveUpdateNodesAtCurrentLevel(); // this level is about to be deleted -- remove its children from update list
                                std::vector<Node *> &unused_ex = stack.back().expansions;
                                for(unsigned i = 0; i < unused_ex.size(); i++)
                                    heuristic->Update(unused_ex[i]->map); // make it less likely to expand this node in future
                            } 
                            HandleUpdatedNodes();
                            if(stack.size() == 1){
                                if(top->Outgoing)
                                    tree->DeleteEdge(top->Outgoing); // in case we kept the tree
                                return false;
                            }
                            was_sat = false;
                        }
                        else {
                            was_sat = true;
                            tree->Push();
                            std::vector<Node *> &expansions = stack.back().expansions;
#ifndef NO_DECISIONS
#if 0
                            if(expansions.size() > 0)
                                tree->GreedyReduceNodes(expansions[0]->Outgoing->Children); // try to reduce number of children
#endif
                            for(unsigned i = 0; i < expansions.size(); i++){
                                tree->FixCurrentState(expansions[i]->Outgoing);
                            }
#endif
#if 0
                            if(tree->slvr().check() == unsat)
                                throw "help!";
#endif
                            int expand_max = 1;
                            if(0&&duality->BatchExpand){
                                int thing = stack.size() / 10; // * 0.1;
                                expand_max = std::max(1,thing);
                                if(expand_max > 1)
                                    std::cout << "foo!\n";
                            }

                            if(ExpandSomeNodes(false,expand_max))
                                continue;
                            tree->Pop(1);
                            node_order.clear();
                            while(stack.size() > 1){
                                tree->Pop(1);
                                std::vector<Node *> &expansions = stack.back().expansions;
                                for(unsigned i = 0; i < expansions.size(); i++)
                                    node_order.push_back(expansions[i]);
                                stack.pop_back();
                            }
#if 0
                            Reduce();
#endif
                            return true;
                        }
                    }
            }
      
            std::vector<Node *> node_order;

            void Reduce(){
                tree->Push();
                // tree->AssertNode(top); // assert the negation of the top-level spec
                for(int i = node_order.size()-1; i >= 0; --i){
                    Edge *edge = node_order[i]->Outgoing;
                    if(edge){
                        for(unsigned j = 0; j < edge->Children.size(); j++){
                            Node *ch = edge->Children[j];
                            if(!ch->Outgoing)
                                ch->Annotation.SetEmpty();
                        }
                        tree->AssertEdge(edge,0,true);
                    }
                }
                tree->GreedyReduceNodes(node_order); // try to reduce the counterexample size
                tree->Pop(1);
            }

            void PopLevel(){
                std::vector<Node *> &expansions = stack.back().expansions;
                tree->Pop(1);
                hash_set<Node *> leaves_to_remove;
                for(unsigned i = 0; i < expansions.size(); i++){
                    Node *node = expansions[i];
                    //      if(node != top)
                    //tree->ConstrainParent(node->Incoming[0],node);
                    std::vector<Node *> &cs = node->Outgoing->Children;
                    for(unsigned i = 0; i < cs.size(); i++){
                        leaves_to_remove.insert(cs[i]);
                        UnmapNode(cs[i]);
                        if(std::find(updated_nodes.begin(),updated_nodes.end(),cs[i]) != updated_nodes.end())
                            throw "help!";
                    }
                }
                RemoveLeaves(leaves_to_remove); // have to do this before actually deleting the children
                for(unsigned i = 0; i < expansions.size(); i++){
                    Node *node = expansions[i];
                    RemoveExpansion(node);
                }
                stack.pop_back();
            }

            bool NodeTooComplicated(Node *node){
                int ops = tree->CountOperators(node->Annotation.Formula);
                if(ops > 10) return true;
                node->Annotation.Formula = tree->RemoveRedundancy(node->Annotation.Formula).simplify();
                return tree->CountOperators(node->Annotation.Formula) > 3;
            }

            void SimplifyNode(Node *node){
                // have to destroy the old proof to get a new interpolant
                timer_start("SimplifyNode");
                tree->PopPush();
                try {
                    tree->InterpolateByCases(top,node);
                }
                catch(const RPFP::Bad&){
                    timer_stop("SimplifyNode");
                    throw RPFP::Bad();
                }
                timer_stop("SimplifyNode");
            }

            bool LevelUsedInProof(unsigned level){
                std::vector<Node *> &expansions = stack[level].expansions;
                for(unsigned i = 0; i < expansions.size(); i++)
                    if(tree->EdgeUsedInProof(expansions[i]->Outgoing))
                        return true;
                return false;
            }

            void RemoveUpdateNodesAtCurrentLevel() {
                for(std::list<Node *>::iterator it = updated_nodes.begin(), en = updated_nodes.end(); it != en;){
                    Node *node = *it;
                    if(AtCurrentStackLevel(node->Incoming[0]->Parent)){
                        std::list<Node *>::iterator victim = it;
                        ++it;
                        updated_nodes.erase(victim);
                    }
                    else
                        ++it;
                }
            }

            void RemoveLeaves(hash_set<Node *> &leaves_to_remove){
                std::list<RPFP::Node *> leaves_copy;
                leaves_copy.swap(leaves);
                for(std::list<RPFP::Node *>::iterator it = leaves_copy.begin(), en = leaves_copy.end(); it != en; ++it){
                    if(leaves_to_remove.find(*it) == leaves_to_remove.end())
                        leaves.push_back(*it);
                }
            }

            hash_map<Node *, std::vector<Node *> > node_map;
            std::list<Node *> updated_nodes;

            virtual void ExpandNode(RPFP::Node *p){
                stack.push_back(stack_entry());
                stack.back().level = tree->slvr().get_scope_level();
                stack.back().expansions.push_back(p);
                DerivationTree::ExpandNode(p);
                std::vector<Node *> &new_nodes = p->Outgoing->Children;
                for(unsigned i = 0; i < new_nodes.size(); i++){
                    Node *n = new_nodes[i];
                    node_map[n->map].push_back(n);
                }
            }

            bool RecordUpdate(Node *node){
                bool res = duality->UpdateNodeToNode(node->map,node);
                if(res){
                    std::vector<Node *> to_update = node_map[node->map];
                    for(unsigned i = 0; i < to_update.size(); i++){
                        Node *node2 = to_update[i];
                        // maintain invariant that no nodes on updated list are created at current stack level
                        if(node2 == node || !(node->Incoming.size() > 0 && AtCurrentStackLevel(node2->Incoming[0]->Parent))){
                            updated_nodes.push_back(node2);
                            if(node2 != node)
                                node2->Annotation = node->Annotation;
                        }
                    }
                }
                return res;
            }
      
            void HandleUpdatedNodes(){
                for(std::list<Node *>::iterator it = updated_nodes.begin(), en = updated_nodes.end(); it != en;){
                    Node *node = *it;
                    node->Annotation = node->map->Annotation;
                    if(node->Incoming.size() > 0)
                        tree->ConstrainParent(node->Incoming[0],node);
                    if(AtCurrentStackLevel(node->Incoming[0]->Parent)){
                        std::list<Node *>::iterator victim = it;
                        ++it;
                        updated_nodes.erase(victim);
                    }
                    else
                        ++it;
                }
            }
      
            bool AtCurrentStackLevel(Node *node){
                std::vector<Node *> vec = stack.back().expansions;
                for(unsigned i = 0; i < vec.size(); i++)
                    if(vec[i] == node)
                        return true;
                return false;
            }

            void UnmapNode(Node *node){
                std::vector<Node *> &vec = node_map[node->map];
                for(unsigned i = 0; i < vec.size(); i++){
                    if(vec[i] == node){
                        std::swap(vec[i],vec.back());
                        vec.pop_back();
                        return;
                    }
                }
                throw "can't unmap node";
            }

            void Generalize(Node *node){
#ifndef USE_RPFP_CLONE
                tree->Generalize(top,node);
#else
                RPFP_caching *clone_rpfp = duality->clone_rpfp;
                if(!node->Outgoing->map) return;
                Edge *clone_edge = clone_rpfp->GetEdgeClone(node->Outgoing->map);
                Node *clone_node = clone_edge->Parent;
                clone_node->Annotation = node->Annotation;
                for(unsigned i = 0; i < clone_edge->Children.size(); i++)
                    clone_edge->Children[i]->Annotation = node->map->Outgoing->Children[i]->Annotation;
                clone_rpfp->GeneralizeCache(clone_edge);
                node->Annotation = clone_node->Annotation;
#endif
            }

            bool Propagate(Node *node){
#ifdef USE_RPFP_CLONE
                RPFP_caching *clone_rpfp = duality->clone_rpfp;
                Edge *clone_edge = clone_rpfp->GetEdgeClone(node->Outgoing->map);
                Node *clone_node = clone_edge->Parent;
                clone_node->Annotation = node->map->Annotation;
                for(unsigned i = 0; i < clone_edge->Children.size(); i++)
                    clone_edge->Children[i]->Annotation = node->map->Outgoing->Children[i]->Annotation;
                bool res = clone_rpfp->PropagateCache(clone_edge);
                if(res)
                    node->Annotation = clone_node->Annotation;
                return res;
#else
                return false;
#endif
            }

        };


        class Covering {

            struct cover_info {
                Node *covered_by;
                std::list<Node *> covers;
                bool dominated;
                std::set<Node *> dominates;
                cover_info(){
                    covered_by = 0;
                    dominated = false;
                }
            };

            typedef hash_map<Node *,cover_info> cover_map;
            cover_map cm;
            Duality *parent;
            bool some_updates;

#define NO_CONJ_ON_SIMPLE_LOOPS
#ifdef NO_CONJ_ON_SIMPLE_LOOPS
            hash_set<Node *> simple_loops;
#endif

            Node *&covered_by(Node *node){
                return cm[node].covered_by;
            }

            std::list<Node *> &covers(Node *node){
                return cm[node].covers;
            }

            std::vector<Node *> &insts_of_node(Node *node){
                return parent->insts_of_node[node];
            }

            Reporter *reporter(){
                return parent->reporter;
            }

            std::set<Node *> &dominates(Node *x){
                return cm[x].dominates;
            }
      
            bool dominates(Node *x, Node *y){
                std::set<Node *> &d = cm[x].dominates;
                return d.find(y) != d.end();
            }

            bool &dominated(Node *x){
                return cm[x].dominated;
            }

        public:

            Covering(Duality *_parent){
                parent = _parent;
                some_updates = false;

#ifdef NO_CONJ_ON_SIMPLE_LOOPS
                hash_map<Node *,std::vector<Edge *> > outgoing;
                for(unsigned i = 0; i < parent->rpfp->edges.size(); i++)
                    outgoing[parent->rpfp->edges[i]->Parent].push_back(parent->rpfp->edges[i]);
                for(unsigned i = 0; i < parent->rpfp->nodes.size(); i++){
                    Node * node = parent->rpfp->nodes[i];
                    std::vector<Edge *> &outs = outgoing[node];
                    if(outs.size() == 2){
                        for(int j = 0; j < 2; j++){
                            Edge *loop_edge = outs[j];
                            if(loop_edge->Children.size() == 1 && loop_edge->Children[0] == loop_edge->Parent)
                                simple_loops.insert(node);
                        }
                    }
                }
#endif

            }
      
            bool IsCoveredRec(hash_set<Node *> &memo, Node *node){
                if(memo.find(node) != memo.end())
                    return false;
                memo.insert(node);
                if(covered_by(node)) return true;
                for(unsigned i = 0; i < node->Outgoing->Children.size(); i++)
                    if(IsCoveredRec(memo,node->Outgoing->Children[i]))
                        return true;
                return false;
            }
      
            bool IsCovered(Node *node){
                hash_set<Node *> memo;
                return IsCoveredRec(memo,node);
            }

#ifndef UNDERAPPROX_NODES
            void RemoveCoveringsBy(Node *node){
                std::list<Node *> &cs = covers(node);
                for(std::list<Node *>::iterator it = cs.begin(), en = cs.end(); it != en; it++){
                    covered_by(*it) = 0;
                    reporter()->RemoveCover(*it,node);
                }
                cs.clear();
            }
#else
            void RemoveCoveringsBy(Node *node){
                std::vector<Node *> &cs = parent->all_of_node[node->map];
                for(std::vector<Node *>::iterator it = cs.begin(), en = cs.end(); it != en; it++){
                    Node *other = *it;
                    if(covered_by(other) && CoverOrder(node,other)){
                        covered_by(other) = 0;
                        reporter()->RemoveCover(*it,node);
                    }
                }
            }
#endif

            void RemoveAscendantCoveringsRec(hash_set<Node *> &memo, Node *node){
                if(memo.find(node) != memo.end())
                    return;
                memo.insert(node);
                RemoveCoveringsBy(node);
                for(std::vector<Edge *>::iterator it = node->Incoming.begin(), en = node->Incoming.end(); it != en; ++it)
                    RemoveAscendantCoveringsRec(memo,(*it)->Parent);
            }

            void RemoveAscendantCoverings(Node *node){
                hash_set<Node *> memo;
                RemoveAscendantCoveringsRec(memo,node);
            }

            bool CoverOrder(Node *covering, Node *covered){
#ifdef UNDERAPPROX_NODES
                if(parent->underapprox_map.find(covered) != parent->underapprox_map.end())
                    return false;
                if(parent->underapprox_map.find(covering) != parent->underapprox_map.end())
                    return covering->number < covered->number || parent->underapprox_map[covering] == covered;
#endif
                return covering->number < covered->number;
            }

            bool CheckCover(Node *covered, Node *covering){
                return
                    CoverOrder(covering,covered) 
                    && covered->Annotation.SubsetEq(covering->Annotation)
                    && !IsCovered(covering);
            }
      
            bool CoverByNode(Node *covered, Node *covering){
                if(CheckCover(covered,covering)){
                    covered_by(covered) = covering;
                    covers(covering).push_back(covered);
                    std::vector<Node *> others; others.push_back(covering);
                    reporter()->AddCover(covered,others);
                    RemoveAscendantCoverings(covered);
                    return true;
                }
                else
                    return false;
            }

#ifdef UNDERAPPROX_NODES
            bool CoverByAll(Node *covered){
                RPFP::Transformer all = covered->Annotation;
                all.SetEmpty();
                std::vector<Node *> &insts = parent->insts_of_node[covered->map];
                std::vector<Node *> others;
                for(unsigned i = 0; i < insts.size(); i++){
                    Node *covering = insts[i];
                    if(CoverOrder(covering,covered) && !IsCovered(covering)){
                        others.push_back(covering);
                        all.UnionWith(covering->Annotation);
                    }
                }
                if(others.size() && covered->Annotation.SubsetEq(all)){
                    covered_by(covered) = covered; // anything non-null will do
                    reporter()->AddCover(covered,others);
                    RemoveAscendantCoverings(covered);
                    return true;
                }
                else
                    return false;
            }
#endif

            bool Close(Node *node){
                if(covered_by(node))
                    return true;
#ifndef UNDERAPPROX_NODES
                std::vector<Node *> &insts = insts_of_node(node->map);
                for(unsigned i = 0; i < insts.size(); i++)
                    if(CoverByNode(node,insts[i]))
                        return true;
#else
                if(CoverByAll(node))
                    return true;
#endif
                return false;
            }

            bool CloseDescendantsRec(hash_set<Node *> &memo, Node *node){
                if(memo.find(node) != memo.end())
                    return false;
                for(unsigned i = 0; i < node->Outgoing->Children.size(); i++)
                    if(CloseDescendantsRec(memo,node->Outgoing->Children[i]))
                        return true;
                if(Close(node))
                    return true;
                memo.insert(node);
                return false;
            }
      
            bool CloseDescendants(Node *node){
                timer_start("CloseDescendants");
                hash_set<Node *> memo;
                bool res = CloseDescendantsRec(memo,node);
                timer_stop("CloseDescendants");
                return res;
            }

            bool Contains(Node *node){
                timer_start("Contains");
                bool res = !IsCovered(node);
                timer_stop("Contains");
                return res;
            }

            bool Candidate(Node *node){
                timer_start("Candidate");
                bool res = !IsCovered(node) && !dominated(node);
                timer_stop("Candidate");
                return res;
            }

            void SetDominated(Node *node){
                dominated(node) = true;
            }

            bool CouldCover(Node *covered, Node *covering){
#ifdef NO_CONJ_ON_SIMPLE_LOOPS
                // Forsimple loops, we rely on propagation, not covering
                if(simple_loops.find(covered->map) != simple_loops.end())
                    return false;
#endif
#ifdef UNDERAPPROX_NODES
                // if(parent->underapprox_map.find(covering) != parent->underapprox_map.end())
                // return parent->underapprox_map[covering] == covered;
#endif
                if(CoverOrder(covering,covered) 
                   && !IsCovered(covering)){
                    RPFP::Transformer f(covering->Annotation); f.SetEmpty();
#if defined(TOP_DOWN) || defined(EFFORT_BOUNDED_STRAT)
                    if(parent->StratifiedInlining)
                        return true;
#endif
                    return !covering->Annotation.SubsetEq(f);
                }
                return false;
            }      

            bool ContainsCex(Node *node, Counterexample &cex){
                expr val = cex.get_tree()->Eval(cex.get_root()->Outgoing,node->Annotation.Formula);
                return eq(val,parent->ctx.bool_val(true));
            }

            /** We conjecture that the annotations of similar nodes may be
                true of this one. We start with later nodes, on the
                principle that their annotations are likely weaker. We save
                a counterexample -- if annotations of other nodes are true
                in this counterexample, we don't need to check them.
            */

#ifndef UNDERAPPROX_NODES
            bool Conjecture(Node *node){
                std::vector<Node *> &insts = insts_of_node(node->map);
                Counterexample cex; 
                for(int i = insts.size() - 1; i >= 0; i--){
                    Node *other = insts[i];
                    if(CouldCover(node,other)){
                        reporter()->Forcing(node,other);
                        if(cex.get_tree() && !ContainsCex(other,cex))
                            continue;
                        cex.clear();
                        if(parent->ProveConjecture(node,other->Annotation,other,&cex))
                            if(CloseDescendants(node))
                                return true;
                    }
                }
                cex.clear();
                return false;
            }
#else
            bool Conjecture(Node *node){
                std::vector<Node *> &insts = insts_of_node(node->map);
                Counterexample cex; 
                RPFP::Transformer Bound = node->Annotation;
                Bound.SetEmpty();
                bool some_other = false;
                for(int i = insts.size() - 1; i >= 0; i--){
                    Node *other = insts[i];
                    if(CouldCover(node,other)){
                        reporter()->Forcing(node,other);
                        Bound.UnionWith(other->Annotation);
                        some_other = true;
                    }
                }
                if(some_other && parent->ProveConjecture(node,Bound)){
                    CloseDescendants(node);
                    return true;
                }
                return false;
            }
#endif

            void Update(Node *node, const RPFP::Transformer &update){
                RemoveCoveringsBy(node);
                some_updates = true;
            }

#ifndef UNDERAPPROX_NODES
            Node *GetSimilarNode(Node *node){
                if(!some_updates)
                    return 0;
                std::vector<Node *> &insts = insts_of_node(node->map);
                for(int i = insts.size()-1; i >= 0;  i--){
                    Node *other = insts[i];
                    if(dominates(node,other))
                        if(CoverOrder(other,node) 
                           && !IsCovered(other))
                            return other;
                }
                return 0;
            }
#else
            Node *GetSimilarNode(Node *node){
                if(!some_updates)
                    return 0;
                std::vector<Node *> &insts = insts_of_node(node->map);
                for(int i = insts.size() - 1; i >= 0; i--){
                    Node *other = insts[i];
                    if(CoverOrder(other,node) 
                       && !IsCovered(other))
                        return other;
                }
                return 0;
            }
#endif

            bool Dominates(Node * node, Node *other){
                if(node == other) return false;
                if(other->Outgoing->map == 0) return true;
                if(node->Outgoing->map == other->Outgoing->map){
                    assert(node->Outgoing->Children.size() == other->Outgoing->Children.size());
                    for(unsigned i = 0; i < node->Outgoing->Children.size(); i++){
                        Node *nc = node->Outgoing->Children[i];
                        Node *oc = other->Outgoing->Children[i];
                        if(!(nc == oc || oc->Outgoing->map ==0 || dominates(nc,oc)))
                            return false;
                    }
                    return true;
                }  
                return false; 
            }

            void Add(Node *node){
                std::vector<Node *> &insts = insts_of_node(node->map);
                for(unsigned i = 0; i < insts.size(); i++){
                    Node *other = insts[i];
                    if(Dominates(node,other)){
                        cm[node].dominates.insert(other);
                        cm[other].dominated = true;
                        reporter()->Dominates(node, other);
                    }
                }
            }

        };

        /* This expansion heuristic makes use of a previuosly obtained
           counterexample as a guide. This is for use in abstraction
           refinement schemes.*/

        class ReplayHeuristic : public Heuristic {

            Counterexample old_cex;
        public:
            ReplayHeuristic(RPFP *_rpfp, Counterexample &_old_cex)
                : Heuristic(_rpfp)
            {
                old_cex.swap(_old_cex); // take ownership from caller
            }

            ~ReplayHeuristic(){
            }

            // Maps nodes of derivation tree into old cex
            hash_map<Node *, Node*> cex_map;
      
            void Done() {
                cex_map.clear();
                old_cex.clear();
            }

            void ShowNodeAndChildren(Node *n){
                std::cout << n->Name.name() << ": ";
                std::vector<Node *> &chs = n->Outgoing->Children;
                for(unsigned i = 0; i < chs.size(); i++)
                    std::cout << chs[i]->Name.name() << " " ;
                std::cout << std::endl;
            }

            // HACK: When matching relation names, we drop suffixes used to
            // make the names unique between runs. For compatibility
            // with boggie, we drop suffixes beginning with @@
            std::string BaseName(const std::string &name){
                int pos = name.find("@@");
                if(pos >= 1)
                    return name.substr(0,pos);
                return name;
            }

            Node *MatchNode(Node *node){
                if(cex_map.find(node) == cex_map.end()){ // try to match an unmatched node
                    Node *parent = node->Incoming[0]->Parent; // assumes we are a tree!
                    if(cex_map.find(parent) == cex_map.end())
                        throw "catastrophe in ReplayHeuristic::ChooseExpand";
                    Node *old_parent = cex_map[parent];
                    std::vector<Node *> &chs = parent->Outgoing->Children;
                    if(old_parent && old_parent->Outgoing){
                        std::vector<Node *> &old_chs = old_parent->Outgoing->Children;
                        for(unsigned i = 0, j=0; i < chs.size(); i++){
                            if(j < old_chs.size() && BaseName(chs[i]->Name.name().str()) == BaseName(old_chs[j]->Name.name().str()))
                                cex_map[chs[i]] = old_chs[j++];
                            else {
                                std::cerr << "WARNING: duality: unmatched child: " << chs[i]->Name.name() << std::endl;
                                cex_map[chs[i]] = 0;
                            }
                        }
                        goto matching_done;
                    }
                    for(unsigned i = 0; i < chs.size(); i++)
                        cex_map[chs[i]] = 0;
                }
            matching_done:
                return cex_map[node];
            }

            int UseNode(Node *node){
                if (!old_cex.get_tree())
                    return 0;
                Node *old_node = MatchNode(node);
                if(!old_node)
                    return 0;
                return old_cex.get_tree()->Empty(old_node) ? -1 : 1;
            }

            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best, bool high_priority, bool best_only){
                if(cex_map.empty())
                    cex_map[*(choices.begin())] = old_cex.get_root();  // match the root nodes
                if(!high_priority || !old_cex.get_tree()){
                    Heuristic::ChooseExpand(choices,best,false);
                    return;
                }
                // first, try to match the derivatino tree nodes to the old cex
                std::set<Node *> matched, unmatched;
                for(std::set<Node *>::iterator it = choices.begin(), en = choices.end(); it != en; ++it){
                    Node *node = (*it);
                    Node *old_node = MatchNode(node);
                    if(!old_node)
                        unmatched.insert(node);
                    else if(old_cex.get_tree()->Empty(old_node))
                        unmatched.insert(node);
                    else
                        matched.insert(node);
                }
                if (matched.empty() && !high_priority)
                    Heuristic::ChooseExpand(unmatched,best,false);
                else
                    Heuristic::ChooseExpand(matched,best,false);
            }
        };


        class LocalHeuristic : public Heuristic {

            RPFP::Node *old_node;
        public:
            LocalHeuristic(RPFP *_rpfp)
                : Heuristic(_rpfp)
            {
                old_node = 0;
            }

            void SetOldNode(RPFP::Node *_old_node){
                old_node = _old_node;
                cex_map.clear();
            }

            // Maps nodes of derivation tree into old subtree
            hash_map<Node *, Node*> cex_map;
      
            virtual void ChooseExpand(const std::set<RPFP::Node *> &choices, std::set<RPFP::Node *> &best){
                if(old_node == 0){
                    Heuristic::ChooseExpand(choices,best);
                    return;
                }
                // first, try to match the derivatino tree nodes to the old cex
                std::set<Node *> matched, unmatched;
                for(std::set<Node *>::iterator it = choices.begin(), en = choices.end(); it != en; ++it){
                    Node *node = (*it);
                    if(cex_map.empty())
                        cex_map[node] = old_node;  // match the root nodes
                    if(cex_map.find(node) == cex_map.end()){ // try to match an unmatched node
                        Node *parent = node->Incoming[0]->Parent; // assumes we are a tree!
                        if(cex_map.find(parent) == cex_map.end())
                            throw "catastrophe in ReplayHeuristic::ChooseExpand";
                        Node *old_parent = cex_map[parent];
                        std::vector<Node *> &chs = parent->Outgoing->Children;
                        if(old_parent && old_parent->Outgoing){
                            std::vector<Node *> &old_chs = old_parent->Outgoing->Children;
                            if(chs.size() == old_chs.size()){
                                for(unsigned i = 0; i < chs.size(); i++)
                                    cex_map[chs[i]] = old_chs[i];
                                goto matching_done;
                            }
                            else
                                std::cout << "derivation tree does not match old cex" << std::endl;
                        }
                        for(unsigned i = 0; i < chs.size(); i++)
                            cex_map[chs[i]] = 0;
                    }
                matching_done:
                    Node *old_node = cex_map[node];
                    if(!old_node)
                        unmatched.insert(node);
                    else if(old_node != node->map)
                        unmatched.insert(node);
                    else
                        matched.insert(node);
                }
                Heuristic::ChooseExpand(unmatched,best);
            }
        };

        /** This proposer class generates conjectures based on the
            unwinding generated by a previous solver. The assumption is
            that the provious solver was working on a different
            abstraction of the same system. The trick is to adapt the
            annotations in the old unwinding to the new predicates.  We
            start by generating a map from predicates and parameters in
            the old problem to the new. 

            HACK: mapping is done by cheesy name comparison.
        */
    
        class HistoryProposer : public Proposer
        {
            Duality *old_solver;
            Duality *new_solver;
            hash_map<Node *, std::vector<RPFP::Transformer> > conjectures;

        public:
            /** Construct a history solver. */
            HistoryProposer(Duality *_old_solver, Duality *_new_solver)
                : old_solver(_old_solver), new_solver(_new_solver) {

                // tricky: names in the axioms may have changed -- map them
                hash_set<func_decl> &old_constants = old_solver->unwinding->ls->get_constants();
                hash_set<func_decl> &new_constants = new_solver->rpfp->ls->get_constants();
                hash_map<std::string,func_decl> cmap;
                for(hash_set<func_decl>::iterator it = new_constants.begin(), en = new_constants.end(); it != en; ++it)
                    cmap[GetKey(*it)] = *it;
                hash_map<func_decl,func_decl> bckg_map;
                for(hash_set<func_decl>::iterator it = old_constants.begin(), en = old_constants.end(); it != en; ++it){
                    func_decl f = new_solver->ctx.translate(*it); // move to new context
                    if(cmap.find(GetKey(f)) != cmap.end())
                        bckg_map[f] = cmap[GetKey(f)];
                    // else
                    //  std::cout << "constant not matched\n";
                }

                RPFP *old_unwinding = old_solver->unwinding;
                hash_map<std::string, std::vector<Node *> > pred_match;

                // index all the predicates in the old unwinding
                for(unsigned i = 0; i < old_unwinding->nodes.size(); i++){
                    Node *node = old_unwinding->nodes[i];
                    std::string key = GetKey(node);
                    pred_match[key].push_back(node);
                }

                // match with predicates in the new RPFP
                RPFP *rpfp = new_solver->rpfp;
                for(unsigned i = 0; i < rpfp->nodes.size(); i++){
                    Node *node = rpfp->nodes[i];
                    std::string key = GetKey(node);
                    std::vector<Node *> &matches = pred_match[key];
                    for(unsigned j = 0; j < matches.size(); j++)
                        MatchNodes(node,matches[j],bckg_map);
                }
            }
      
            virtual std::vector<RPFP::Transformer> &Propose(Node *node){
                return conjectures[node->map];
            }

            virtual ~HistoryProposer(){
            };

        private:
            void MatchNodes(Node *new_node, Node *old_node, hash_map<func_decl,func_decl> &bckg_map){
                if(old_node->Annotation.IsFull())
                    return; // don't conjecture true!
                hash_map<std::string, expr> var_match;
                std::vector<expr> &new_params = new_node->Annotation.IndParams;
                // Index the new parameters by their keys
                for(unsigned i = 0; i < new_params.size(); i++)
                    var_match[GetKey(new_params[i])] = new_params[i];
                RPFP::Transformer &old = old_node->Annotation;
                std::vector<expr> from_params = old.IndParams;
                for(unsigned j = 0; j < from_params.size(); j++)
                    from_params[j] = new_solver->ctx.translate(from_params[j]); // get in new context
                std::vector<expr> to_params = from_params;
                for(unsigned j = 0; j < to_params.size(); j++){
                    std::string key = GetKey(to_params[j]);
                    if(var_match.find(key) == var_match.end()){
                        // std::cout << "unmatched parameter!\n";
                        return;
                    }
                    to_params[j] = var_match[key];
                }
                expr fmla = new_solver->ctx.translate(old.Formula); // get in new context
                fmla = new_solver->rpfp->SubstParams(old.IndParams,to_params,fmla); // substitute parameters
                hash_map<ast,expr> memo;
                fmla = new_solver->rpfp->SubstRec(memo,bckg_map,fmla); // substitute background constants
                RPFP::Transformer new_annot = new_node->Annotation;
                new_annot.Formula = fmla;
                conjectures[new_node].push_back(new_annot);
            }
      
            // We match names by removing suffixes beginning with double at sign

            std::string GetKey(Node *node){
                return GetKey(node->Name);
            }

            std::string GetKey(const expr &var){
                return GetKey(var.decl());
            }

            std::string GetKey(const func_decl &f){
                std::string name = f.name().str();
                int idx = name.find("@@");
                if(idx >= 0)
                    name.erase(idx);
                return name;
            }
        };
    };

    static int stop_event = -1;

    class StreamReporter : public Reporter {
        std::ostream &s;
    public:
        StreamReporter(RPFP *_rpfp, std::ostream &_s)
            : Reporter(_rpfp), s(_s) {event = 0; depth = -1;}
        int event;
        int depth;
        void ev(){
            if(stop_event == event){
                std::cout << "stop!\n";
            }
            s << "[" << event++ << "]" ;
        }
        virtual void Extend(RPFP::Node *node){
            ev(); s << "node " << node->number << ": " << node->Name.name();
            std::vector<RPFP::Node *> &rps = node->Outgoing->Children;
            for(unsigned i = 0; i < rps.size(); i++)
                s << " " << rps[i]->number;
            s << std::endl;
        }
        virtual void Update(RPFP::Node *node, const RPFP::Transformer &update, bool eager){
            ev(); s << "update " << node->number << " " << node->Name.name()  << ": ";
            rpfp->Summarize(update.Formula);
            if(depth > 0) s << " (depth=" << depth << ")";
            if(eager) s << " (eager)";
            s << std::endl;
        }
        virtual void Bound(RPFP::Node *node){
            ev(); s << "check " << node->number << std::endl;
        }
        virtual void Expand(RPFP::Edge *edge){
            RPFP::Node *node = edge->Parent;
            ev(); s << "expand " << node->map->number << " " << node->Name.name();
            if(depth > 0) s << " (depth=" << depth << ")";
            s << std::endl;
        }
        virtual void Depth(int d){
            depth = d;
        }
        virtual void AddCover(RPFP::Node *covered, std::vector<RPFP::Node *> &covering){
            ev(); s << "cover " << covered->Name.name() << ": " << covered->number << " by ";
            for(unsigned i = 0; i < covering.size(); i++)
                s << covering[i]->number << " ";
            s << std::endl;
        }
        virtual void RemoveCover(RPFP::Node *covered, RPFP::Node *covering){
            ev(); s << "uncover " << covered->Name.name() << ": " << covered->number << " by " << covering->number << std::endl;
        }
        virtual void Forcing(RPFP::Node *covered, RPFP::Node *covering){
            ev(); s << "forcing " << covered->Name.name() << ": " << covered->number << " by " << covering->number << std::endl;
        }
        virtual void Conjecture(RPFP::Node *node, const RPFP::Transformer &t){
            ev(); s << "conjecture " << node->number << " " << node->Name.name() << ": ";
            rpfp->Summarize(t.Formula);
            s << std::endl;
        }
        virtual void Dominates(RPFP::Node *node, RPFP::Node *other){
            ev(); s << "dominates " << node->Name.name() << ": " << node->number << " > " << other->number << std::endl;
        }
        virtual void InductionFailure(RPFP::Edge *edge, const std::vector<RPFP::Node *> &children){
            ev(); s << "induction failure: " << edge->Parent->Name.name() << ", children =";
            for(unsigned i = 0; i < children.size(); i++)
                s << " " << children[i]->number;
            s << std::endl;
        }
        virtual void UpdateUnderapprox(RPFP::Node *node, const RPFP::Transformer &update){
            ev(); s << "underapprox " << node->number << " " << node->Name.name()  << ": " << update.Formula << std::endl;
        }
        virtual void Reject(RPFP::Edge *edge, const std::vector<RPFP::Node *> &children){
            ev(); s << "reject " << edge->Parent->number << " " << edge->Parent->Name.name() << ": ";
            for(unsigned i = 0; i < children.size(); i++)
                s << " " << children[i]->number;
            s << std::endl;
        }
        virtual void Message(const std::string &msg){
            ev(); s << "msg " << msg << std::endl;
        }
    
    };


    class DualityDepthBounded : public Solver {

        Duality *duality;
        context &ctx;                        // Z3 context
        solver &slvr;                        // Z3 solver

    public:
        DualityDepthBounded(RPFP *_rpfp) :
            ctx(_rpfp->ctx),
            slvr(_rpfp->slvr()){
            rpfp = _rpfp;
            DepthBoundRPFP();
            duality = alloc(Duality,drpfp);
        }

        ~DualityDepthBounded(){
            dealloc(duality);
            delete drpfp;
        }

        bool Solve(){
            int depth_bound = 10;
            bool res;
            SetMaxDepthRPFP(depth_bound);
            duality->PreSolve();
            while(true){
                res = duality->SolveMain();
                if(!res || GetSolution())
                    break;
                depth_bound++;
                SetMaxDepthRPFP(depth_bound);
                res = duality->RecheckBounds();
                if(!res)
                    break;
            }
            duality->PostSolve();
            if(!res)
                ConvertCex();
            return res;
        }

        Counterexample &GetCounterexample(){
            return cex;
        }

        bool SetOption(const std::string &option, const std::string &value){
            return duality->SetOption(option,value);
        }

        virtual void LearnFrom(Solver *old_solver){
            DualityDepthBounded *old = dynamic_cast<DualityDepthBounded *>(old_solver);
            if(old){
                duality->LearnFrom(old->duality);
            }
        }

        bool IsResultRecursionBounded(){
            return duality->IsResultRecursionBounded();
        }

        void Cancel(){
            duality->Cancel();
        }

        typedef RPFP::Node Node;
        typedef RPFP::Edge Edge;
        RPFP *rpfp, *drpfp;
        hash_map<Node *, Node *> db_map, db_rev_map;
        hash_map<Edge *, Edge *> db_edge_rev_map;
        std::vector<expr> db_saved_bounds;
        Counterexample cex;

        expr AddParamToRels(hash_map<ast,expr> &memo, hash_map<func_decl,func_decl> &rmap, const expr &p, const expr &t) {
            std::pair<ast,expr> foo(t,expr(ctx));
            std::pair<hash_map<ast,expr>::iterator, bool> bar = memo.insert(foo);
            expr &res = bar.first->second;
            if(!bar.second) return res;

            if (t.is_app())
                {
                    func_decl f = t.decl();
                    std::vector<expr> args;
                    int nargs = t.num_args();
                    for(int i = 0; i < nargs; i++)
                        args.push_back(AddParamToRels(memo, rmap, p, t.arg(i)));
                    hash_map<func_decl,func_decl>::iterator rit = rmap.find(f);
                    if(rit != rmap.end()){
                        args.push_back(p);
                        res = (rit->second)(args);
                        res = ctx.make(And,res,ctx.make(Geq,p,ctx.int_val(0)));
                    }
                    else
                        res = f(args);
                }
            else if (t.is_quantifier())
                {
                    expr body = AddParamToRels(memo, rmap, p, t.body());
                    res = clone_quantifier(t, body);
                }
            else res = t;
            return res;
        }


        void DepthBoundRPFP(){
            drpfp = new RPFP(rpfp->ls);
            expr dvar = ctx.int_const("@depth");
            expr dmax = ctx.int_const("@depth_max");
            for(unsigned i = 0; i < rpfp->nodes.size(); i++){
                Node *node = rpfp->nodes[i];
                std::vector<sort> arg_sorts;
                const std::vector<expr> &params = node->Annotation.IndParams;
                for(unsigned j = 0; j < params.size(); j++)
                    arg_sorts.push_back(params[j].get_sort());
                arg_sorts.push_back(ctx.int_sort());
                std::string new_name = std::string("@db@") + node->Name.name().str();
                func_decl f = ctx.function(new_name.c_str(),arg_sorts.size(), &arg_sorts[0],ctx.bool_sort());
                std::vector<expr> args = params;
                args.push_back(dvar);
                expr pat = f(args);
                Node *dnode = drpfp->CreateNode(pat);
                db_map[node] = dnode;
                db_rev_map[dnode] = node;
                expr bound_fmla = node->Bound.Formula;
                if(!eq(bound_fmla,ctx.bool_val(true))){
                    bound_fmla = implies(dvar == dmax,bound_fmla);
                    dnode->Bound.Formula = bound_fmla;
                }
                db_saved_bounds.push_back(bound_fmla);
                // dnode->Annotation.Formula = ctx.make(And,node->Annotation.Formula,ctx.make(Geq,dvar,ctx.int_val(0)));
            }
            for(unsigned i = 0; i < rpfp->edges.size(); i++){
                Edge *edge = rpfp->edges[i];
                std::vector<Node *> new_children;
                std::vector<func_decl> new_relparams;
                hash_map<func_decl,func_decl> rmap;
                for(unsigned j = 0; j < edge->Children.size(); j++){
                    Node *ch = edge->Children[j];
                    Node *nch = db_map[ch];
                    func_decl f = nch->Name;
                    func_decl sf = drpfp->NumberPred(f,j);
                    new_children.push_back(nch);
                    new_relparams.push_back(sf);
                    rmap[edge->F.RelParams[j]] = sf;
                }
                std::vector<expr> new_indparams = edge->F.IndParams;
                new_indparams.push_back(dvar);
                hash_map<ast,expr> memo;
                expr new_fmla = AddParamToRels(memo,rmap,ctx.make(Sub,dvar,ctx.int_val(1)),edge->F.Formula);
                RPFP::Transformer new_t = drpfp->CreateTransformer(new_relparams,new_indparams,new_fmla);
                Node *new_parent = db_map[edge->Parent];
                db_edge_rev_map[drpfp->CreateEdge(new_parent,new_t,new_children)] = edge;
            }
        }

        void SetMaxDepthRPFP(int depth){
            hash_map<ast,expr> subst;
            expr dmax = ctx.int_const("@depth_max");
            subst[dmax] = ctx.int_val(depth);
            for(unsigned i = 0; i < drpfp->nodes.size(); i++){
                Node *node = drpfp->nodes[i];
                expr fmla = db_saved_bounds[i];
                fmla = drpfp->SubstRec(subst,fmla);
                node->Bound.Formula = fmla;
            }
        }

        void ConvertCex(){
            cex.clear();
            RPFP *tree = new RPFP(rpfp->ls);
            Node *root;
            Counterexample &dctx = duality->GetCounterexample();
            hash_map<Node *, Node *> ctx_node_map;
            for(unsigned i = 0; i < dctx.get_tree()->nodes.size(); i++){
                Node *dnode = dctx.get_tree()->nodes[i];
                Node *onode = db_rev_map[dnode->map->map];
                Node *node = tree->CloneNode(onode);
                node->number = dnode->number; // numbers have to match for model to make sense
                ctx_node_map[dnode] = node;
                if(dnode == dctx.get_root())
                    root = node;
            }
            for(unsigned i = 0; i < dctx.get_tree()->edges.size(); i++){
                Edge *dedge = dctx.get_tree()->edges[i];
                Edge *oedge = db_edge_rev_map[dedge->map];
                Node *parent = ctx_node_map[dedge->Parent];
                std::vector<Node *> chs;
                for(unsigned j = 0; j < dedge->Children.size(); j++)
                    chs.push_back(ctx_node_map[dedge->Children[j]]);
                Edge *edge = tree->CreateEdge(parent,oedge->F,chs);
                edge->number = dedge->number; // numbers have to match for model to make sense
                edge->map = oedge;
            }
            tree->dualModel = dctx.get_tree()->dualModel;
            cex.set(tree,root);
        }

        bool GetSolution(){
            for(unsigned i = 0; i < rpfp->nodes.size(); i++)
                if(!drpfp->nodes[i]->Annotation.SubsetEq(rpfp->nodes[i]->Bound))
                    return false;
            expr dvar = ctx.int_const("@depth");
            hash_map<ast,expr> subst;
            subst[dvar] = ctx.int_val(INT_MAX);
            for(unsigned i = 0; i < rpfp->nodes.size(); i++){
                expr fmla = drpfp->nodes[i]->Annotation.Formula;
                fmla = drpfp->SubstRec(subst,fmla);
                fmla = fmla.simplify();
                rpfp->nodes[i]->Annotation.Formula = fmla;
            }
            return true;
        }

        void UndoDepthBoundRPFP(){
#if 0
            if(cex.get_tree()){
                // here, need to map the cex back...
            }
            // also need to map the proof back, but we don't...
#endif
        }
    };

    Solver *Solver::Create(const std::string &solver_class, RPFP *rpfp){
        //    Solver *s = alloc(DualityDepthBounded,rpfp);
        Solver *s = alloc(Duality,rpfp);
        return s;
    }

    Reporter *CreateStdoutReporter(RPFP *rpfp){
        return new StreamReporter(rpfp, std::cout);
    }

    class ConjectureFileReporter : public Reporter {
        std::ofstream s;
    public:
        ConjectureFileReporter(RPFP *_rpfp, const std::string &fname)
            : Reporter(_rpfp), s(fname.c_str()) {}
        virtual void Update(RPFP::Node *node, const RPFP::Transformer &update, bool eager){
            s << "(define-fun " << node->Name.name() << " (";
            for(unsigned i = 0; i < update.IndParams.size(); i++){
                if(i != 0)
                    s << " ";
                s << "(" << update.IndParams[i] << " " << update.IndParams[i].get_sort() << ")";
            }
            s << ") Bool \n";
            s << update.Formula << ")\n";
            s << std::endl;
        }
    };

    Reporter *CreateConjectureFileReporter(RPFP *rpfp, const std::string &fname){
        return new ConjectureFileReporter(rpfp, fname);
    }

}

