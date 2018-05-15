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
#include "muz/base/dl_util.h"

namespace spacer {

    // arith lemmas: second parameter specifies exact type of lemma, could be "farkas", "triangle-eq", "eq-propagate", "assign-bounds", maybe also something else
    bool is_arith_lemma(ast_manager& m, proof* pr)
    {
        if (pr->get_decl_kind() == PR_TH_LEMMA)
        {
            func_decl* d = pr->get_decl();
            symbol sym;
            if (d->get_num_parameters() >= 1 &&
                d->get_parameter(0).is_symbol(sym) && sym == "arith")
            {
                return true;
            }
        }
        return false;
    }

    bool is_farkas_lemma(ast_manager& m, proof* pr)
    {
        if (pr->get_decl_kind() == PR_TH_LEMMA)
        {
            func_decl* d = pr->get_decl();
            symbol sym;
            if (d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
                d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
                d->get_parameter(1).is_symbol(sym) && sym == "farkas")
            {
                return true;
            }
        }
        return false;
    }

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
                    case PR_TH_LEMMA:
                        if (is_farkas_lemma(m, currentNode))
                        {
                            edge_label = "th_axiom(farkas):";
                        }
                        else
                        {
                            edge_label = "th_axiom:";
                        }
                        break;
                    default:
                            edge_label = "unknown axiom-type:";
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
     * methods for transforming proofs
     * ====================================
     */

    void theory_axiom_reducer::reset()
    {
        m_cache.reset();
        m_pinned.reset();
    }

    proof_ref theory_axiom_reducer::reduce(proof* pr)
    {
        ProofIteratorPostOrder pit(pr, m);
        while (pit.hasNext())
        {
            proof* p = pit.next();

            if (m.get_num_parents(p) == 0 && is_arith_lemma(m, p))
            {
                // we have an arith-theory-axiom and want to get rid of it
                // we need to replace the axiom with 1a) corresponding hypothesis', 1b) a theory lemma and a 1c) a lemma. Furthermore update datastructures
                app *cls_fact = to_app(m.get_fact(p));
                ptr_buffer<expr> cls;
                if (m.is_or(cls_fact)) {
                    for (unsigned i = 0, sz = cls_fact->get_num_args(); i < sz; ++i)
                    { cls.push_back(cls_fact->get_arg(i)); }
                } else { cls.push_back(cls_fact); }

                // 1a) create hypothesis'
                ptr_buffer<proof> hyps;
                for (unsigned i=0; i < cls.size(); ++i)
                {
                    expr* hyp_fact = m.is_not(cls[i]) ? to_app(cls[i])->get_arg(0) : m.mk_not(cls[i]);
                    proof* hyp = m.mk_hypothesis(hyp_fact);
                    m_pinned.push_back(hyp);
                    hyps.push_back(hyp);
                }

                // 1b) create farkas lemma: need to rebuild parameters since mk_th_lemma adds tid as first parameter
                unsigned num_params = p->get_decl()->get_num_parameters();
                parameter const* params = p->get_decl()->get_parameters();
                vector<parameter> parameters;
                for (unsigned i = 1; i < num_params; ++i) {
                    parameters.push_back(params[i]);
                }

                SASSERT(params[0].is_symbol());
                family_id tid = m.mk_family_id(params[0].get_symbol());
                SASSERT(tid != null_family_id);

                proof* th_lemma = m.mk_th_lemma(tid, m.mk_false(),hyps.size(), hyps.c_ptr(), num_params-1, parameters.c_ptr());
                SASSERT(is_arith_lemma(m, th_lemma));

                // 1c) create lemma
                proof* res = m.mk_lemma(th_lemma, cls_fact);
                SASSERT(m.get_fact(res) == m.get_fact(p));
                m_pinned.push_back(res);
                m_cache.insert(p, res);
            }
            else
            {
                bool dirty = false; // proof is dirty, if a subproof of one of its premises has been transformed

                ptr_buffer<expr> args;
                for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i)
                {
                    proof* pp = m.get_parent(p, i);
                    proof* tmp;
                    if (m_cache.find(pp, tmp))
                    {
                        args.push_back(tmp);
                        dirty = dirty || pp != tmp;
                    }
                    else
                    {
                        SASSERT(false);
                    }
                }
                if (!dirty) // if not dirty just use the old step
                {
                    m_cache.insert(p, p);
                }
                else // otherwise create new step with the corresponding proofs of the premises
                {
                    if (m.has_fact(p)) { args.push_back(m.get_fact(p)); }
                    SASSERT(p->get_decl()->get_arity() == args.size());
                    proof* res = m.mk_app(p->get_decl(), args.size(), (expr * const*)args.c_ptr());
                    m_pinned.push_back(res);
                    m_cache.insert(p, res);
                }
            }
        }

        proof* res;
        VERIFY(m_cache.find(pr,res));
        DEBUG_CODE(proof_checker pc(m);
                   expr_ref_vector side(m);
                   SASSERT(pc.check(res, side));
                   );

        return proof_ref(res,m);
    }

    void hypothesis_reducer::reset()
    {
        m_cache.reset();
        m_units.reset();
        m_active_hyps.reset();
        m_parent_hyps.reset();
        m_pinned_active_hyps.reset();
        m_pinned_parent_hyps.reset();
        m_pinned.reset();
    }

    void hypothesis_reducer::compute_hypsets(proof* pr)
    {
        ptr_vector<proof> todo;
        todo.push_back(pr);

        while (!todo.empty())
        {
            proof* p = todo.back();

            if (m_active_hyps.contains(p))
            {
                SASSERT(m_parent_hyps.contains(p));
                todo.pop_back();
            }
            // if we haven't already visited the current unit
            else
            {
                bool existsUnvisitedParent = false;

                // add unprocessed premises to stack for DFS. If there is at least one unprocessed premise, don't compute the result
                // for p now, but wait until those unprocessed premises are processed.
                for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                    SASSERT(m.is_proof(p->get_arg(i)));
                    proof* premise = to_app(p->get_arg(i));

                    // if we haven't visited the premise yet
                    if (!m_active_hyps.contains(premise))
                    {
                        SASSERT(!m_parent_hyps.contains(premise));
                        // add it to the stack
                        todo.push_back(premise);
                        existsUnvisitedParent = true;
                    }
                }

                // if we already visited all premises, we can visit p too
                if (!existsUnvisitedParent)
                {
                    todo.pop_back();

                    // create active_hyps-set and parent_hyps-set for step p
                    proof_set* active_hyps = alloc(proof_set);
                    m_pinned_active_hyps.insert(active_hyps);
                    m_active_hyps.insert(p, active_hyps);

                    expr_set* parent_hyps = alloc(expr_set);
                    m_pinned_parent_hyps.insert(parent_hyps);
                    m_parent_hyps.insert(p, parent_hyps);

                    // fill both sets
                    if (m.is_hypothesis(p))
                    {
                        active_hyps->insert(p);
                        parent_hyps->insert(m.get_fact(p));
                    }
                    else
                    {
                        for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i)
                        {
                            proof* pp = m.get_parent(p, i);
                            datalog::set_union(*parent_hyps, *m_parent_hyps.find(pp));

                            if (!m.is_lemma(p)) // lemmas clear all hypotheses
                            {
                                datalog::set_union(*active_hyps, *m_active_hyps.find(pp));
                            }
                        }
                    }
                }
            }
        }
    }

    // collect all units that are hyp-free and are used as hypotheses somewhere
    // requires that m_active_hyps and m_parent_hyps have been computed
    void hypothesis_reducer::collect_units(proof* pr)
    {
        expr_set* all_hyps = m_parent_hyps.find(pr);
        SASSERT(all_hyps != nullptr);

        ProofIteratorPostOrder pit(pr, m);
        while (pit.hasNext()) {
            proof* p = pit.next();
            if (!m.is_hypothesis(p))
            {
                proof_set* active_hyps = m_active_hyps.find(p);
                SASSERT(active_hyps != nullptr);

                // collect units that are hyp-free and are used as hypotheses in the proof pr
                if (active_hyps->empty() && m.has_fact(p) && all_hyps->contains(m.get_fact(p)))
                {
                    m_units.insert(m.get_fact(p), p);
                }
            }
        }
    }

    proof_ref hypothesis_reducer::reduce(proof* pr)
    {
        compute_hypsets(pr);
        collect_units(pr);

        proof* res = compute_transformed_proof(pr);
        SASSERT(res != nullptr);

        proof_ref res_ref(res,m);

        reset();
        DEBUG_CODE(proof_checker pc(m);
                   expr_ref_vector side(m);
                   SASSERT(pc.check(res, side));
                   );
        return res_ref;
    }

    proof* hypothesis_reducer::compute_transformed_proof(proof* pf)
    {
        proof *res = NULL;

        ptr_vector<proof> todo;
        todo.push_back(pf);
        ptr_buffer<proof> args;
        bool dirty = false;

        while (!todo.empty()) {
            proof *p, *tmp, *pp;
            unsigned todo_sz;

            p = todo.back();
            if (m_cache.find(p, tmp)) {
                todo.pop_back();
                continue;
            }

            dirty = false;
            args.reset();
            todo_sz = todo.size();
            for (unsigned i = 0, sz = m.get_num_parents(p); i < sz; ++i) {
                pp = m.get_parent(p, i);
                if (m_cache.find(pp, tmp)) {
                    args.push_back(tmp);
                    dirty = dirty || pp != tmp;
                } else {
                    todo.push_back(pp);
                }
            }

            if (todo_sz < todo.size()) { continue; }
            else { todo.pop_back(); }


            // here the proof transformation begins
            // INV: whenever we visit p, active_hyps and parent_hyps have been computed for the args.
            if (m.is_hypothesis(p))
            {
                // hyp: replace by a corresponding unit
                if (m_units.find(m.get_fact(p), tmp))
                {
                    // look up the proof of the unit:
                    // if there is a transformed proof use that one
                    // otherwise use the original proof
                    proof* proof_of_unit;
                    if (!m_cache.find(tmp,proof_of_unit))
                    {
                        proof_of_unit = tmp;
                    }

                    // compute hypsets (have not been computed in general, since the unit can be anywhere in the proof)
                    compute_hypsets(proof_of_unit);

                    // if the transformation doesn't create a cycle, perform it
                    SASSERT(m_parent_hyps.contains(proof_of_unit));
                    expr_set* parent_hyps = m_parent_hyps.find(proof_of_unit);
                    if (!parent_hyps->contains(p))
                    {
                        res = proof_of_unit;
                        // hypsets have already been computed for proof_of_unit
                    }
                    // otherwise don't transform the proof and just use the hypothesis
                    else
                    {
                        res = p;
                        // hypsets have already been computed for p
                    }
                }
                else
                {
                    res = p;
                    // hypsets have already been computed for p
                }
            }
            else if (!dirty) { res = p; }

            else if (m.is_lemma(p))
            {
                //lemma: reduce the premise; remove reduced consequences from conclusion
                SASSERT(args.size() == 1);
                res = mk_lemma_core(args[0], m.get_fact(p));
                compute_hypsets(res);
            }
            else if (m.is_unit_resolution(p))
            {
                // unit: reduce untis; reduce the first premise; rebuild unit resolution
                res = mk_unit_resolution_core(args);
                compute_hypsets(res);
            }
            else
            {
                res = mk_step_core(p, args);
                compute_hypsets(res);
            }

            SASSERT(res);
            m_cache.insert(p, res);

            SASSERT(m_active_hyps.contains(res));
            proof_set* active_hyps = m_active_hyps.find(res);
            if (active_hyps->empty() && m.has_fact(res) && m.is_false(m.get_fact(res)))
            {
                return res;
            }
        }
        UNREACHABLE();
        return nullptr;
    }

    proof* hypothesis_reducer::mk_lemma_core(proof* premise, expr *fact)
    {
        SASSERT(m.is_false(m.get_fact(premise)));

        SASSERT(m_active_hyps.contains(premise));
        proof_set* active_hyps = m_active_hyps.find(premise);

        // if there is no active hypothesis return the premise
        if (active_hyps->empty())
        {
            return premise;
        }
        // otherwise build disjunction of the negated active hypothesis' and add lemma step.
        else
        {
            expr_ref_buffer args(m);
            for (auto hyp : *active_hyps)
            {
                expr* hyp_fact = m.get_fact(hyp);
                expr_ref negated_hyp_fact(m);
                negated_hyp_fact = m.is_not(hyp_fact) ? to_app(hyp_fact)->get_arg(0) : m.mk_not(hyp_fact);
                args.push_back(negated_hyp_fact);
            }

            expr_ref lemma(m);
            if (args.size() == 1)
            {
                lemma = args[0];
            }
            else
            {
                lemma = m.mk_or(args.size(), args.c_ptr());
            }
            proof_ref res(m);
            res = m.mk_lemma(premise, lemma);
            m_pinned.push_back(res);
            return res;
        }
    }

    proof* hypothesis_reducer::mk_unit_resolution_core(ptr_buffer<proof>& args)
    {
        ptr_buffer<proof> pf_args; // the arguments of the transformed unit resolution step
        pf_args.push_back(args [0]); // the first element of args is the clause to resolve with

        // if any literal is false, we don't need a unit resolution step
        // could be the case due to transformations which already have been done
        for (unsigned i = 1; i < args.size(); ++i)
        {
            if (m.is_false(m.get_fact(args[i])))
            {
                return args[i];
            }
        }

        app *cls_fact = to_app(m.get_fact(args[0])); // BUG: I guess this shouldn't work with quantifiers (since they are no apps)
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
            for (unsigned j = 1; j < args.size(); ++j) {
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
            proof* res = m.mk_unit_resolution(pf_args.size(), pf_args.c_ptr(), new_fact);
            m_pinned.push_back(res);
            return res;
        }
    }

    proof* hypothesis_reducer::mk_step_core(proof* old_step, ptr_buffer<proof>& args)
    {
        // if any of the literals is false, we don't need a step
        for (unsigned i = 0; i < args.size(); ++i)
        {
            if (m.is_false(m.get_fact(args[i])))
            {
                return args[i];
            }
        }

        // otherwise build step
        args.push_back(to_app(m.get_fact(old_step))); // BUG: I guess this doesn't work with quantifiers (since they are no apps)

        SASSERT(old_step->get_decl()->get_arity() == args.size());
        proof* res = m.mk_app(old_step->get_decl(), args.size(), (expr * const*)args.c_ptr());
        m_pinned.push_back(res);
        return res;
    }

};
