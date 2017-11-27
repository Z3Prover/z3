/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_proof_utils.cpp

Abstract:
    Utilities to traverse and manipulate proofs

Author:
    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#include "muz/spacer/spacer_proof_utils.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"

#include "ast/proof_checker/proof_checker.h"
#include <unordered_map>
#include "params.h"
#include "muz/spacer/spacer_iuc_proof.h"

namespace spacer {
    
    /*
     * ====================================
     * methods for proof traversal
     * ====================================
     */
ProofIteratorPostOrder::ProofIteratorPostOrder(proof* root, ast_manager& manager) : m(manager)
{m_todo.push_back(root);}

bool ProofIteratorPostOrder::hasNext()
{return !m_todo.empty();}

/*
 * iterative post-order depth-first search (DFS) through the proof DAG
 */
proof* ProofIteratorPostOrder::next()
{
    while (!m_todo.empty()) {
        proof* currentNode = m_todo.back();

        // if we haven't already visited the current unit
        if (!m_visited.is_marked(currentNode)) {
            bool existsUnvisitedParent = false;

            // add unprocessed premises to stack for DFS. If there is at least one unprocessed premise, don't compute the result
            // for currentProof now, but wait until those unprocessed premises are processed.
            for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i) {
                SASSERT(m.is_proof(currentNode->get_arg(i)));
                proof* premise = to_app(currentNode->get_arg(i));

                // if we haven't visited the current premise yet
                if (!m_visited.is_marked(premise)) {
                    // add it to the stack
                    m_todo.push_back(premise);
                    existsUnvisitedParent = true;
                }
            }

            // if we already visited all parent-inferences, we can visit the inference too
            if (!existsUnvisitedParent) {
                m_visited.mark(currentNode, true);
                m_todo.pop_back();
                return currentNode;
            }
        } else {
            m_todo.pop_back();
        }
    }
    // we have already iterated through all inferences
    return NULL;
}

    /*
     * ====================================
     * methods for dot printing
     * ====================================
     */
    void pp_proof_dot_to_stream(ast_manager& m, std::ofstream& dotstream, proof* pr, iuc_proof* iuc_pr = nullptr);
    std::string escape_dot(const std::string &s);
    void pp_proof_post_process_dot(std::string dot_filepath, std::ofstream &dotstream);

    void pp_proof_dot(ast_manager& m, proof* pr, iuc_proof* iuc_pr)
    {
        // open temporary dot-file
        std::string dotfile_path = "proof.dot";
        std::ofstream dotstream(dotfile_path);
        
        // dump dot representation to stream
        pp_proof_dot_to_stream(m, dotstream, pr, iuc_pr);
        
        // post process dot-file, TODO: factor this out to a different place
        pp_proof_post_process_dot(dotfile_path,dotstream);
    }
    
    void pp_proof_dot_to_stream(ast_manager& m, std::ofstream& dotstream, proof* pr, iuc_proof* iuc_pr)
    {
        dotstream << "digraph proof { \n";
        std::unordered_map<unsigned, unsigned> id_to_small_id;
        unsigned counter = 0;
        
        ProofIteratorPostOrder it2(pr, m);
        while (it2.hasNext())
        {
            proof* currentNode = it2.next();
            
            SASSERT(id_to_small_id.find(currentNode->get_id()) == id_to_small_id.end());
            id_to_small_id.insert(std::make_pair(currentNode->get_id(), counter));
            
            std::string color = "white";
            if (iuc_pr != nullptr)
            {
                if (iuc_pr->is_a_marked(currentNode) && !iuc_pr->is_b_marked(currentNode))
                {
                    color = "red";
                }
                else if(iuc_pr->is_b_marked(currentNode) && !iuc_pr->is_a_marked(currentNode))
                {
                    color = "blue";
                }
                else if(iuc_pr->is_b_marked(currentNode) && iuc_pr->is_a_marked(currentNode))
                {
                    color = "purple";
                }
            }

            // compute label
            params_ref p;
            p.set_uint("max_depth", 4294967295u);
            p.set_uint("min_alias_size", 4294967295u);
            
            std::ostringstream label_ostream;
            label_ostream << mk_pp(m.get_fact(currentNode),m,p) << "\n";
            std::string label = escape_dot(label_ostream.str());
            
            // compute edge-label
            std::string edge_label = "";
            if (m.get_num_parents(currentNode) == 0)
            {
                switch (currentNode->get_decl_kind())
                {
                    case PR_ASSERTED:
                        edge_label = "asserted:";
                        break;
                    case PR_HYPOTHESIS:
                        edge_label = "hyp:";
                        color = "grey";
                        break;
                    default:
                        if (currentNode->get_decl_kind() == PR_TH_LEMMA)
                        {
                            edge_label = "th_axiom:";
                            func_decl* d = currentNode->get_decl();
                            symbol sym;
                            if (d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
                                d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
                                d->get_parameter(1).is_symbol(sym) && sym == "farkas")
                            {
                                edge_label = "th_axiom(farkas):";
                            }
                        }
                        else
                        {
                            edge_label = "unknown axiom-type:";
                            break;
                        }
                }
            }
            else
            {
                if (currentNode->get_decl_kind() == PR_LEMMA)
                {
                    edge_label = "lemma:";
                }
                else if (currentNode->get_decl_kind() == PR_TH_LEMMA)
                {
                    func_decl* d = currentNode->get_decl();
                    symbol sym;
                    if (d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
                        d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
                        d->get_parameter(1).is_symbol(sym) && sym == "farkas")
                    {
                        edge_label = "th_lemma(farkas):";
                    }
                    else
                    {
                        edge_label = "th_lemma(other):";
                    }
                }
            }
            
            // generate entry for node in dot-file
            dotstream   << "node_" << counter << " "
            << "["
            << "shape=box,style=\"filled\","
            << "label=\"" << edge_label << " " << label << "\", "
            << "fillcolor=\"" << color << "\""
            << "]\n";
            
            // add entry for each edge to that node
            for (unsigned i = m.get_num_parents(currentNode); i > 0  ; --i)
            {
                proof* premise = to_app(currentNode->get_arg(i-1));
                unsigned premise_small_id = id_to_small_id[premise->get_id()];
                dotstream   << "node_" << premise_small_id
                << " -> "
                << "node_" << counter
                << ";\n";
            }
            
            ++counter;
        }
        dotstream << "\n}" << std::endl;
    }
    
    std::string escape_dot(const std::string &s)
    {
        std::string res;
        res.reserve(s.size()); // preallocate
        for (auto c : s) {
            if (c == '\n')
                res.append("\\l");
            else
                res.push_back(c);
        }
        return res;
    }
    
    void pp_proof_post_process_dot(std::string dot_filepath, std::ofstream &dotstream)
    {
        // replace variables in the dotfiles with nicer descriptions (hack: hard coded replacement for now)
        std::vector<std::vector<std::string> > predicates;
        std::vector<std::string> l1 = {"L1","i","n","A"};
        predicates.push_back(l1);
        std::vector<std::string> l2 = {"L2","j","m","B"};
        predicates.push_back(l2);
        
        for(auto& predicate : predicates)
        {
            std::string predicate_name = predicate[0];
            for (unsigned i=0; i+1 < predicate.size(); ++i)
            {
                std::string new_name = predicate[i+1];
                std::string substring0 = predicate_name + "_" + std::to_string(i) + "_0";
                std::string substringN = predicate_name + "_" + std::to_string(i) + "_n";
                
                std::string command0 = "sed -i '.bak' 's/" + substring0 + "/" + new_name + "/g' " + dot_filepath;
                verbose_stream() << command0 << std::endl;
                system(command0.c_str());
                
                std::string commandN = "sed -i '.bak' s/" + substringN + "/" + new_name + "\\'" + "/g " + dot_filepath;
                verbose_stream() << commandN << std::endl;
                system(commandN.c_str());
            }
        }
        
        verbose_stream() << "end of postprocessing";
    }

    /*
     * ====================================
     * methods for reducing hypothesis
     * ====================================
     */
    
class reduce_hypotheses {
    ast_manager &m;
    // tracking all created expressions
    expr_ref_vector m_pinned;

    // cache for the transformation
    obj_map<proof, proof*> m_cache;

    // map from unit literals to their hypotheses-free derivations
    obj_map<expr, proof*> m_units;

    // -- all hypotheses in the the proof
    obj_hashtable<expr> m_hyps;

    // marks hypothetical proofs
    ast_mark m_hypmark;


    // stack
    ptr_vector<proof> m_todo;

    void reset()
    {
        m_cache.reset();
        m_units.reset();
        m_hyps.reset();
        m_hypmark.reset();
        m_pinned.reset();
    }

    bool compute_mark1(proof *pr)
    {
        bool hyp_mark = false;
        // lemmas clear all hypotheses
        if (!m.is_lemma(pr)) {
            for (unsigned i = 0, sz = m.get_num_parents(pr); i < sz; ++i) {
                if (m_hypmark.is_marked(m.get_parent(pr, i))) {
                    hyp_mark = true;
                    break;
                }
            }
        }
        m_hypmark.mark(pr, hyp_mark);
        return hyp_mark;
    }

    void compute_marks(proof* pr)
    {
        proof *p;
        ProofIteratorPostOrder pit(pr, m);
        while (pit.hasNext()) {
            p = pit.next();
            if (m.is_hypothesis(p)) {
                m_hypmark.mark(p, true);
                m_hyps.insert(m.get_fact(p));
            } else {
                compute_mark1(p);
            }
        }
        ProofIteratorPostOrder pit2(pr, m);
        while (pit2.hasNext()) {
            p = pit2.next();
            if (!m.is_hypothesis(p))
            {
                // collect units that are hyp-free and are used as hypotheses somewhere
                if (!m_hypmark.is_marked(p) && m.has_fact(p) && m_hyps.contains(m.get_fact(p)))
                {
                    m_units.insert(m.get_fact(p), p);
                }
            }
        }
    }
    void find_units(proof *pr)
    {
        // optional. not implemented yet.
    }

    void reduce(proof* pf, proof_ref &out)
    {
        proof *res = NULL;

        m_todo.reset();
        m_todo.push_back(pf);
        ptr_buffer<proof> args;
        bool dirty = false;

        while (!m_todo.empty()) {
            proof *p, *tmp, *tmp2, *pp;
            unsigned todo_sz;

            p = m_todo.back();
            if (m_cache.find(p, tmp)) {
                res = tmp;
                m_todo.pop_back();
                continue;
            }

            dirty = false;
            args.reset();
            todo_sz = m_todo.size();
            for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i) {
                pp = m.get_parent(p, i);
                if (m_cache.find(pp, tmp)) {
                    args.push_back(tmp);
                    dirty = dirty || pp != tmp;
                } else {
                    m_todo.push_back(pp);
                }
            }

            if (todo_sz < m_todo.size()) { continue; }
            else { m_todo.pop_back(); }

            if (m.is_hypothesis(p)) {
                // hyp: replace by a corresponding unit
                if (m_units.find(m.get_fact(p), tmp)) {
                    // if the transformed subproof ending in the unit has already been computed, use it
                    if (m_cache.find(tmp,tmp2))
                    {
                        res = tmp2;
                    }
                    // otherwise first compute the transformed subproof ending in the unit
                    else
                    {
                        m_todo.push_back(tmp);
                        continue;
                    }
                } else { res = p; }
            }

            else if (!dirty) { res = p; }

            else if (m.is_lemma(p)) {
                //lemma: reduce the premise; remove reduced consequences from conclusion
                SASSERT(args.size() == 1);
                res = mk_lemma_core(args.get(0), m.get_fact(p));
                compute_mark1(res);
            } else if (m.is_unit_resolution(p)) {
                // unit: reduce untis; reduce the first premise; rebuild unit resolution
                res = mk_unit_resolution_core(args.size(), args.c_ptr());
                compute_mark1(res);
            } else  {
                // if any literal is false, we don't need a step
                bool has_empty_clause_premise = false;
                for (unsigned i = 0; i < args.size(); ++i)
                {
                    if (m.is_false(m.get_fact(args[i])))
                    {
                        has_empty_clause_premise = true;
                        res = args[i];
                    }
                }
                
                // otherwise:
                if (!has_empty_clause_premise)
                {
                    // other: reduce all premises; reapply
                    if (m.has_fact(p)) { args.push_back(to_app(m.get_fact(p))); }
                    SASSERT(p->get_decl()->get_arity() == args.size());
                    res = m.mk_app(p->get_decl(), args.size(), (expr * const*)args.c_ptr());
                    m_pinned.push_back(res);
                    compute_mark1(res);
                }
            }

            SASSERT(res);
            m_cache.insert(p, res);

            if (!m_hypmark.is_marked(res) && m.has_fact(res) && m.is_false(m.get_fact(res))) { break; }
        }

        out = res;
    }

    // returns true if (hypothesis (not a)) would be reduced
    bool is_reduced(expr *a)
    {
        expr_ref e(m);
        if (m.is_not(a)) { e = to_app(a)->get_arg(0); }
        else { e = m.mk_not(a); }

        return m_units.contains(e);
    }
    proof *mk_lemma_core(proof *pf, expr *fact)
    {
        ptr_buffer<expr> args;
        expr_ref lemma(m);

        if (m.is_or(fact)) {
            for (unsigned i = 0, sz = to_app(fact)->get_num_args(); i < sz; ++i) {
                expr *a = to_app(fact)->get_arg(i);
                if (!is_reduced(a))
                { args.push_back(a); }
            }
        } else if (!is_reduced(fact))
        { args.push_back(fact); }


        if (args.size() == 0) { return pf; }
        else if (args.size() == 1) {
            lemma = args.get(0);
        } else {
            lemma = m.mk_or(args.size(), args.c_ptr());
        }
        proof* res = m.mk_lemma(pf, lemma);
        m_pinned.push_back(res);

        // XXX this is wrong because lemma is a proof and m_hyps only
        // XXX contains expressions.
        // XXX Not sure this is ever needed.
        if (m_hyps.contains(lemma)) {
            m_units.insert(lemma, res);
        }
        return res;
    }

    proof *mk_unit_resolution_core(unsigned num_args, proof* const *args)
    {

        ptr_buffer<proof> pf_args;
        pf_args.push_back(args [0]);

        // if any literal is false, we don't need a unit resolution step
        for (unsigned i = 1; i < num_args; ++i)
        {
            if (m.is_false(m.get_fact(args[i])))
            {
                return args[i];
            }
        }

        app *cls_fact = to_app(m.get_fact(args[0]));
        ptr_buffer<expr> cls;
        if (m.is_or(cls_fact)) {
            for (unsigned i = 0, sz = cls_fact->get_num_args(); i < sz; ++i)
            { cls.push_back(cls_fact->get_arg(i)); }
        } else { cls.push_back(cls_fact); }

        // construct new resolvent
        ptr_buffer<expr> new_fact_cls;
        bool found;
        // XXX quadratic
        for (unsigned i = 0, sz = cls.size(); i < sz; ++i) {
            found = false;
            for (unsigned j = 1; j < num_args; ++j) {
                if (m.is_complement(cls.get(i), m.get_fact(args [j]))) {
                    found = true;
                    pf_args.push_back(args [j]);
                    break;
                }
            }
            if (!found) {
                new_fact_cls.push_back(cls.get(i));
            }
        }

        SASSERT(new_fact_cls.size() + pf_args.size() - 1 == cls.size());
        expr_ref new_fact(m);
        new_fact = mk_or(m, new_fact_cls.size(), new_fact_cls.c_ptr());

        // create new proof step
        if (pf_args.size() == 1) // the only premise is the clause itself
        {
            return args[0];
        }
        else
        {
            proof *res = m.mk_unit_resolution(pf_args.size(), pf_args.c_ptr(), new_fact);
            m_pinned.push_back(res);
            return res;
        }
    }

    // reduce all units, if any unit reduces to false return true and put its proof into out
    bool reduce_units(proof_ref &out)
    {
        proof_ref res(m);
        for (auto entry : m_units) {
            reduce(entry.get_value(), res);
            if (m.is_false(m.get_fact(res))) {
                out = res;
                return true;
            }
            res.reset();
        }
        return false;
    }


public:
    reduce_hypotheses(ast_manager &m) : m(m), m_pinned(m) {}


    void operator()(proof_ref &pr)
    {
        compute_marks(pr);
        reduce(pr.get(), pr);
        reset();
    }
};
void reduce_hypotheses(proof_ref &pr)
{
    ast_manager &m = pr.get_manager();
    class reduce_hypotheses hypred(m);
    hypred(pr);
    DEBUG_CODE(proof_checker pc(m);
               expr_ref_vector side(m);
               SASSERT(pc.check(pr, side));
              );
}
}
