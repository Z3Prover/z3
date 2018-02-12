/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    proof_utils.cpp

Abstract:
    Utilities to traverse and manipulate proofs

Author:
    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/proofs/proof_utils.h"
#include "ast/proofs/proof_checker.h"
#include "ast/rewriter/var_subst.h"
#include "util/container_util.h"


proof_post_order::proof_post_order(proof* root, ast_manager& manager) : m(manager)
{m_todo.push_back(root);}

bool proof_post_order::hasNext()
{return !m_todo.empty();}

/*
 * iterative post-order depth-first search (DFS) through the proof DAG
 */
proof* proof_post_order::next()
{
    while (!m_todo.empty()) {
        proof* currentNode = m_todo.back();

        // if we haven't already visited the current unit
        if (!m_visited.is_marked(currentNode)) {
            bool existsUnvisitedParent = false;

            // add unprocessed premises to stack for DFS. 
            // If there is at least one unprocessed premise, don't compute the result
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
    return nullptr;
}


class reduce_hypotheses {
    ast_manager &m;
    // tracking all created expressions
    expr_ref_vector m_pinned;

    // cache for the transformation
    obj_map<proof, proof*> m_cache;

    // map from unit literals to their hypotheses-free derivations
    obj_map<expr, proof*> m_units;

    // -- all hypotheses in the proof
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

    void compute_marks(proof* pr)  {
        proof *p;
        proof_post_order pit(pr, m);
        while (pit.hasNext()) {
            p = pit.next();
            if (m.is_hypothesis(p)) {
                m_hypmark.mark(p, true);
                m_hyps.insert(m.get_fact(p));
            } 
            else {
                bool hyp_mark = compute_mark1(p);
                // collect units that are hyp-free and are used as hypotheses somewhere
                if (!hyp_mark && m.has_fact(p) && m_hyps.contains(m.get_fact(p))) { 
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
        proof *res = nullptr;

        m_todo.reset();
        m_todo.push_back(pf);
        ptr_buffer<proof> args;
        bool dirty = false;

        while (!m_todo.empty()) {
            proof *p, *tmp, *pp;
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
                    res = tmp;
                } else { res = p; }
            }

            else if (!dirty) { res = p; }

            else if (m.is_lemma(p)) {
                //lemma: reduce the premise; remove reduced consequences from conclusion
                SASSERT(args.size() == 1);
                res = mk_lemma_core(args.get(0), m.get_fact(p));
                compute_mark1(res);
            } else if (m.is_unit_resolution(p)) {
                // unit: reduce units; reduce the first premise; rebuild unit resolution
                res = mk_unit_resolution_core(args.size(), args.c_ptr());
                compute_mark1(res);
            } else  {
                // other: reduce all premises; reapply
                if (m.has_fact(p)) { args.push_back(to_app(m.get_fact(p))); }
                SASSERT(p->get_decl()->get_arity() == args.size());
                res = m.mk_app(p->get_decl(), args.size(), (expr * const*)args.c_ptr());
                m_pinned.push_back(res);
                compute_mark1(res);
            }

            SASSERT(res);
            m_cache.insert(p, res);

            if (m.has_fact(res) && m.is_false(m.get_fact(res))) { break; }
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

        if (m_hyps.contains(lemma))
        { m_units.insert(lemma, res); }
        return res;
    }

    proof *mk_unit_resolution_core(unsigned num_args, proof* const *args)
    {

        ptr_buffer<proof> pf_args;
        pf_args.push_back(args [0]);

        app *cls_fact = to_app(m.get_fact(args[0]));
        ptr_buffer<expr> cls;
        if (m.is_or(cls_fact)) {
            for (unsigned i = 0, sz = cls_fact->get_num_args(); i < sz; ++i)
            { cls.push_back(cls_fact->get_arg(i)); }
        } else { cls.push_back(cls_fact); }

        // construct new resovent
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
        proof *res = m.mk_unit_resolution(pf_args.size(), pf_args.c_ptr(), new_fact);
        m_pinned.push_back(res);
        return res;
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
        if (!reduce_units(pr)) {
            reduce(pr.get(), pr);
        }
        reset();
    }
};

void reduce_hypotheses(proof_ref &pr) {
    ast_manager &m = pr.get_manager();
    class reduce_hypotheses hypred(m);
    hypred(pr);
    DEBUG_CODE(proof_checker pc(m);
               expr_ref_vector side(m);
               SASSERT(pc.check(pr, side));
              );
}



#include "ast/ast_smt2_pp.h"

class reduce_hypotheses0 {
    typedef obj_hashtable<expr> expr_set;
    ast_manager&          m;
    // reference for any expression created by the transformation
    expr_ref_vector       m_refs;
    // currently computed result
    obj_map<proof,proof*> m_cache;
    // map conclusions to closed proofs that derive them
    obj_map<expr, proof*> m_units;
    // currently active units
    ptr_vector<expr>      m_units_trail;
    // size of m_units_trail at the last push
    unsigned_vector       m_limits;
    // map from proofs to active hypotheses
    obj_map<proof, expr_set*> m_hypmap;
    // reference train for hypotheses sets
    ptr_vector<expr_set>  m_hyprefs;
    ptr_vector<expr>      m_literals;
    
    void reset() {
        m_refs.reset();
        m_cache.reset();
        m_units.reset();
        m_units_trail.reset();
        m_limits.reset();
        std::for_each(m_hyprefs.begin(), m_hyprefs.end(), delete_proc<expr_set>());
        m_hypmap.reset();
        m_hyprefs.reset();
        m_literals.reset();
    }
    
    void push() {
        m_limits.push_back(m_units_trail.size());
    }
    
    void pop() {
        unsigned sz = m_limits.back();
        while (m_units_trail.size() > sz) {
            m_units.remove(m_units_trail.back());
            m_units_trail.pop_back();
        }
        m_limits.pop_back();
    }
    
    void get_literals(expr* clause) {
        m_literals.reset();
        if (m.is_or(clause)) {
            m_literals.append(to_app(clause)->get_num_args(), to_app(clause)->get_args());                
        }
        else {
            m_literals.push_back(clause);
        }
    }
    
    void add_hypotheses(proof* p) {
        expr_set* hyps = nullptr;
        bool inherited = false;
        if (p->get_decl_kind() == PR_HYPOTHESIS) {
            hyps = alloc(expr_set);
            hyps->insert(m.get_fact(p));
            m_hyprefs.push_back(hyps);
        }
        else {
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                expr_set* hyps1 = m_hypmap.find(m.get_parent(p, i));
                if (hyps1) {
                    if (!hyps) {
                        hyps = hyps1;
                        inherited = true;
                        continue;
                    }
                    if (inherited) {
                        hyps = alloc(expr_set,*hyps);
                        m_hyprefs.push_back(hyps);
                        inherited = false;
                    }
                    set_union(*hyps, *hyps1);
                }
            }
        }
        m_hypmap.insert(p, hyps);
    }

    expr_ref complement_lit(expr* e) {
        expr* e1;
        if (m.is_not(e, e1)) {
            return expr_ref(e1, m);
        }
        else {
            return expr_ref(m.mk_not(e), m);
        }
    }
    
    bool in_hypotheses(expr* e, expr_set* hyps) {
        if (!hyps) {
            return false;
        }
        expr_ref not_e = complement_lit(e);
        return hyps->contains(not_e);
    }

    bool contains_hypothesis(proof* p) {
        ptr_vector<proof> todo;
        ast_mark visit;
        todo.push_back(p);
        while (!todo.empty()) {
            p = todo.back();
            todo.pop_back();
            if (visit.is_marked(p)) {
                continue;
            }
            visit.mark(p, true);
            if (PR_HYPOTHESIS == p->get_decl_kind()) {
                return true;
            }
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                todo.push_back(m.get_parent(p, i));
            }
        }
        return false;
    }

    bool is_closed(proof* p) {
        expr_set* hyps = m_hypmap.find(p);
        return !hyps || hyps->empty();
    }    
    
public:
    reduce_hypotheses0(ast_manager& m): m(m), m_refs(m) {}
    
    void operator()(proof_ref& pr) {
        proof_ref tmp(m);
        tmp = pr;
        elim(pr);
        reset();
        CTRACE("proof_utils", contains_hypothesis(pr),
            tout << "Contains hypothesis:\n";
            tout << mk_ismt2_pp(tmp, m) << "\n====>\n";
            tout << mk_ismt2_pp(pr, m) << "\n";);
        
    }
    
    void elim(proof_ref& p) {
        proof_ref tmp(m);
        proof* result = p.get();
        if (m_cache.find(p, result)) {
            p = result;
            return;
        }
        //SASSERT (p.get () == result);
        switch(p->get_decl_kind()) {
        case PR_HYPOTHESIS:
            // replace result by m_units[m.get_fact (p)] if defined
            // AG: This is the main step. Replace a hypothesis by a derivation of its consequence
            if (!m_units.find(m.get_fact(p), result)) {
                // restore the result back to p
                result = p.get();
            }
            // compute hypothesis of the result
            // not clear what 'result' is at this point.
            // probably the proof at the top of the call
            // XXX not clear why this is re-computed each time
            // XXX moreover, m_units are guaranteed to be closed!
            // XXX so no hypotheses are needed for them
            add_hypotheses(result);
            break;
        case PR_LEMMA: {
            SASSERT(m.get_num_parents(p) == 1);
            tmp = m.get_parent(p, 0);
            // eliminate hypothesis recursively in the proof of the lemma
            elim(tmp);
            expr_set* hyps = m_hypmap.find(tmp);
            expr_set* new_hyps = nullptr;
            // XXX if the proof is correct, the hypotheses of the tmp
            // XXX should be exactly those of the consequence of the lemma
            // XXX but if this code actually eliminates hypotheses, the set might be a subset
            if (hyps) {
                new_hyps = alloc(expr_set, *hyps);
            }
            expr* fact = m.get_fact(p);
            // when hypothesis is a single literal of the form 
            // (or A B), and the fact of p is (or A B).            
            if (hyps && hyps->size() == 1 && in_hypotheses(fact, hyps)) {
                m_literals.reset();
                m_literals.push_back(fact);
            }
            else {
                get_literals(fact);
            }

            // go over all the literals in the consequence of the lemma
            for (unsigned i = 0; i < m_literals.size(); ++i) {
                expr* e = m_literals[i];
                // if the literal is not in hypothesis, skip it
                if (!in_hypotheses(e, hyps)) {
                    m_literals[i] = m_literals.back();
                    m_literals.pop_back();
                    --i;
                }
                // if the literal is in hypothesis remove it because
                // it is not in hypothesis set of the lemma
                // XXX but we assume that lemmas have empty hypothesis set.
                // XXX eventually every element of new_hyps must be removed!
                else {
                    SASSERT(new_hyps);
                    expr_ref not_e = complement_lit(e);
                    SASSERT(new_hyps->contains(not_e));
                    new_hyps->remove(not_e);
                }
            }
            // killed all hypotheses, so can stop at the lemma since
            // we have a closed pf of false
            if (m_literals.empty()) {
                result = tmp;
            }
            else {
                // create a new lemma, but might be re-creating existing one
                expr_ref clause(m);
                if (m_literals.size() == 1) {
                    clause = m_literals[0];
                }
                else {
                    clause = m.mk_or(m_literals.size(), m_literals.c_ptr());
                }
                tmp = m.mk_lemma(tmp, clause);
                m_refs.push_back(tmp);
                result = tmp;
            }
            if (new_hyps && new_hyps->empty()) {
                dealloc(new_hyps);
                new_hyps = nullptr;
            }
            m_hypmap.insert(result, new_hyps);
            // might push 0 into m_hyprefs. No reason for that
            m_hyprefs.push_back(new_hyps);
            TRACE("proof_utils",            
                    tout << "New lemma: " << mk_pp(m.get_fact(p), m) 
                      << "\n==>\n" 
                      << mk_pp(m.get_fact(result), m) << "\n";
                if (hyps) {
                    expr_set::iterator it = hyps->begin();
                    expr_set::iterator end = hyps->end();
                    for (; it != end; ++it) {
                        tout << "Hypothesis: " << mk_pp(*it, m) << "\n";
                    }
                });                               
            
            break;
        }
        case PR_UNIT_RESOLUTION: {
            proof_ref_vector parents(m);
            // get the clause being resolved with
            parents.push_back(m.get_parent(p, 0));
            // save state
            push();
            bool found_false = false;
            // for every derivation of a unit literal
            for (unsigned i = 1; i < m.get_num_parents(p); ++i) {
                // see if it derives false
                tmp = m.get_parent(p, i);
                elim(tmp);
                if (m.is_false(m.get_fact(tmp))) {
                    // if derived false, the whole pf is false and we can bail out
                    result = tmp;
                    found_false = true;
                    break;
                }
                // -- otherwise, the fact has not changed. nothing to simplify
                SASSERT(m.get_fact(tmp) == m.get_fact(m.get_parent(p, i)));
                parents.push_back(tmp);          
                // remember that we have this derivation while we have not poped the trail
                // but only if the proof is closed (i.e., a real unit)
                if (is_closed(tmp) && !m_units.contains(m.get_fact(tmp))) {
                    m_units.insert(m.get_fact(tmp), tmp);
                    m_units_trail.push_back(m.get_fact(tmp));
                }
            }
            if (found_false) {
                pop();
                break;
            }
            // look at the clause being resolved with
            tmp = m.get_parent(p, 0);
            // remember its fact
            expr* old_clause = m.get_fact(tmp);
            // attempt to reduce its fact
            elim(tmp);
            // update parents
            parents[0] = tmp;
            // if the new fact is false, bail out
            expr* clause = m.get_fact(tmp);
            if (m.is_false(clause)) {
                m_refs.push_back(tmp);
                result = tmp;
                pop();
                break;
            }
            //
            // case where clause is a literal in the old clause.
            // i.e., reduce multi-literal clause to a unit
            //
            if (is_literal_in_clause(clause, old_clause)) {
                // if the resulting literal was resolved, get a pf of false and bail out
                bool found = false;
                for (unsigned i = 1; !found && i < parents.size(); ++i) {
                    if (m.is_complement(clause, m.get_fact(parents[i].get()))) {
                        parents[1] = parents[i].get();
                        parents.resize(2);
                        result = m.mk_unit_resolution(parents.size(), parents.c_ptr());
                        m_refs.push_back(result);               
                        add_hypotheses(result);
                        found = true;
                    }                    
                }
                // else if the resulting literal is not resolved, it is the new consequence  
                if (!found) {
                    result = parents[0].get();
                }
                pop(); 
                break;
            }
            //
            // case where new clause is a subset of old clause.
            // the literals in clause should be a subset of literals in old_clause.
            // 
            get_literals(clause);
            for (unsigned i = 1; i < parents.size(); ++i) {
                bool found = false;
                for (unsigned j = 0; j < m_literals.size(); ++j) {
                    if (m.is_complement(m_literals[j], m.get_fact(parents[i].get()))) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    // literal was removed as hypothesis.
                    parents[i] = parents.back();
                    parents.pop_back();
                    --i;
                }
            }
            if (parents.size() == 1) {
                result = parents[0].get();
            }
            else {
                result = m.mk_unit_resolution(parents.size(), parents.c_ptr());
                m_refs.push_back(result);               
                add_hypotheses(result);
            }
            pop();
            break;
        }                
        default: {
            ptr_buffer<expr> args;
            bool change = false;
            bool found_false = false;
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                tmp = m.get_parent(p, i);
                elim(tmp);
                if (m.is_false(m.get_fact(tmp))) {
                    result = tmp;
                    found_false = true;
                    break;
                }
                // SASSERT(m.get_fact(tmp) == m.get_fact(m.get_parent(p, i)));
                change = change || (tmp != m.get_parent(p, i));
                args.push_back(tmp);
            }
            if (found_false) {
                break;
            }
            if (m.has_fact(p)) {
                args.push_back(m.get_fact(p));
            }
            if (change) {
                tmp = m.mk_app(p->get_decl(), args.size(), args.c_ptr());
                m_refs.push_back(tmp);
            }
            else {
                tmp = p;
            }
            result = tmp;                
            add_hypotheses(result);
            break;
        }
        }          
        SASSERT(m_hypmap.contains(result));
        m_cache.insert(p, result);
        p = result;
    }        

    bool is_literal_in_clause(expr* fml, expr* clause) {
        if (!m.is_or(clause)) {
            return false;
        }
        app* cl = to_app(clause);
        for (unsigned i = 0; i < cl->get_num_args(); ++i) {
            if (cl->get_arg(i) == fml) {
                return true;
            }
        }
        return false;
    }
};

void proof_utils::reduce_hypotheses(proof_ref& pr) {
    ast_manager& m = pr.get_manager();
    class reduce_hypotheses0 reduce(m);
    reduce(pr);
    CTRACE("proof_utils", !is_closed(m, pr), tout << mk_pp(pr, m) << "\n";);
}

class proof_is_closed {
    ast_manager&     m;
    ptr_vector<expr> m_literals;
    ast_mark         m_visit;

    void reset() {
        m_literals.reset();
        m_visit.reset();
    }

    bool check(proof* p) {
        // really just a partial check because nodes may be visited 
        // already under a different lemma scope.
        if (m_visit.is_marked(p)) {
            return true;
        }
        bool result = false;
        m_visit.mark(p, true);
        switch(p->get_decl_kind()) {
        case PR_LEMMA: {
            unsigned sz = m_literals.size();
            expr* cls = m.get_fact(p);
            m_literals.push_back(cls);
            if (m.is_or(cls)) {
                m_literals.append(to_app(cls)->get_num_args(), to_app(cls)->get_args());
            }
            SASSERT(m.get_num_parents(p) == 1);
            result = check(m.get_parent(p, 0));
            m_literals.resize(sz);
            break;            
        }
        case PR_HYPOTHESIS: {
            expr* fact = m.get_fact(p);
            for (unsigned i = 0; i < m_literals.size(); ++i) {
                if (m.is_complement(m_literals[i], fact)) {
                    result = true;
                    break;
                }
            }
            break;
        }
        default: 
            result = true;
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                if (!check(m.get_parent(p, i))) {
                    result = false;
                    break;
                }
            }
            break;
        }
        
        return result;
    }
    
public:
    proof_is_closed(ast_manager& m): m(m) {}

    bool operator()(proof *p) {
        bool ok = check(p);
        reset();
        return ok;
    }
};

bool proof_utils::is_closed(ast_manager& m, proof* p) {
    proof_is_closed checker(m);
    return checker(p);
}


static void permute_unit_resolution(expr_ref_vector& refs, obj_map<proof,proof*>& cache, proof_ref& pr) {
    ast_manager& m = pr.get_manager();
    proof* pr2 = nullptr;
    proof_ref_vector parents(m);
    proof_ref prNew(pr); 
    if (cache.find(pr, pr2)) {
        pr = pr2;
        return;
    }
    
    for (unsigned i = 0; i < m.get_num_parents(pr); ++i) {
        prNew = m.get_parent(pr, i);
        permute_unit_resolution(refs, cache, prNew);
        parents.push_back(prNew);
    }
    
    prNew = pr;
    if (pr->get_decl_kind() == PR_UNIT_RESOLUTION &&
        parents[0]->get_decl_kind() == PR_TH_LEMMA) { 
        /*
          Unit resolution:
          T1:      (or l_1 ... l_n l_1' ... l_m')
          T2:      (not l_1)
          ...
          T(n+1):  (not l_n)
                   [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
          Th lemma:
          T1:      (not l_1)
          ...
          Tn:      (not l_n)
          [th-lemma T1 ... Tn]: (or l_{n+1} ... l_m)
                    
          Such that (or l_1 .. l_n l_{n+1} .. l_m) is a theory axiom.
                    
          Implement conversion:
                    
                 T1 |- not l_1 ... Tn |- not l_n  
                 -------------------------------  TH_LEMMA
                          (or k_1 .. k_m j_1 ... j_m)    S1 |- not k_1 ... Sm |- not k_m
                          -------------------------------------------------------------- UNIT_RESOLUTION
                                        (or j_1 .. j_m)


            |-> 

                    T1 |- not l_1 ... Tn |- not l_n S1 |- not k_1 ... Sm |- not k_m
                    ---------------------------------------------------------------- TH_LEMMA
                                        (or j_1 .. j_m)

        */
        proof_ref_vector premises(m);
        proof* thLemma = parents[0].get();
        for (unsigned i = 0; i < m.get_num_parents(thLemma); ++i) {
            premises.push_back(m.get_parent(thLemma, i));
        }
        for (unsigned i = 1; i < parents.size(); ++i) {
            premises.push_back(parents[i].get());
        }
        parameter const* params = thLemma->get_decl()->get_parameters();
        unsigned num_params = thLemma->get_decl()->get_num_parameters();
        SASSERT(params[0].is_symbol());
        family_id tid = m.mk_family_id(params[0].get_symbol());
        SASSERT(tid != null_family_id);
        // AG: This can break a theory lemma. In particular, for Farkas lemmas the coefficients
        // AG: for the literals propagated from the unit resolution are missing.
        // AG: Why is this a good thing to do?
        // AG: This can lead to merging of the units with other terms in interpolation,
        // AG: but without farkas coefficients this does not make sense
        prNew = m.mk_th_lemma(tid, m.get_fact(pr), 
                              premises.size(), premises.c_ptr(), num_params-1, params+1);
    }
    else {
        ptr_vector<expr> args;
        for (unsigned i = 0; i < parents.size(); ++i) {
            args.push_back(parents[i].get());
        }
        if (m.has_fact(pr)) {
            args.push_back(m.get_fact(pr));
        }
        prNew = m.mk_app(pr->get_decl(), args.size(), args.c_ptr());
    }    
    
    cache.insert(pr, prNew);
    refs.push_back(prNew);
    pr = prNew;
}


// permute unit resolution over Theory lemmas to track premises.
void proof_utils::permute_unit_resolution(proof_ref& pr) {
    expr_ref_vector refs(pr.get_manager());
    obj_map<proof,proof*> cache;
    ::permute_unit_resolution(refs, cache, pr);
}

class push_instantiations_up_cl {
    ast_manager& m;
public:
    push_instantiations_up_cl(ast_manager& m): m(m) {}

    void operator()(proof_ref& p) {
        expr_ref_vector s0(m);
        p = push(p, s0);
    }

private:

    proof* push(proof* p, expr_ref_vector const& sub) {
        proof_ref_vector premises(m);
        expr_ref conclusion(m);
        svector<std::pair<unsigned, unsigned> >  positions;
        vector<expr_ref_vector> substs;

        if (m.is_hyper_resolve(p, premises, conclusion, positions, substs)) {
            for (unsigned i = 0; i < premises.size(); ++i) {
                compose(substs[i], sub);
                premises[i] = push(premises[i].get(), substs[i]);
                substs[i].reset();
            }
            instantiate(sub, conclusion);
            return 
                m.mk_hyper_resolve(premises.size(), premises.c_ptr(), conclusion, 
                                   positions, 
                                   substs);
        }        
        if (sub.empty()) {
            return p;
        }
        if (m.is_modus_ponens(p)) {
            SASSERT(m.get_num_parents(p) == 2);
            proof* p0 = m.get_parent(p, 0);
            proof* p1 = m.get_parent(p, 1);
            if (m.get_fact(p0) == m.get_fact(p)) {
                return push(p0, sub);
            }
            expr* e1, *e2;
            if (m.is_rewrite(p1, e1, e2) && 
                is_quantifier(e1) && is_quantifier(e2) &&
                to_quantifier(e1)->get_num_decls() == to_quantifier(e2)->get_num_decls()) {
                expr_ref r1(e1,m), r2(e2,m);
                instantiate(sub, r1);
                instantiate(sub, r2);
                p1 = m.mk_rewrite(r1, r2);
                return m.mk_modus_ponens(push(p0, sub), p1);
            }
        }
        premises.push_back(p);
        substs.push_back(sub);
        conclusion = m.get_fact(p);
        instantiate(sub, conclusion);
        return m.mk_hyper_resolve(premises.size(), premises.c_ptr(), conclusion, positions, substs);
    }

    void compose(expr_ref_vector& sub, expr_ref_vector const& s0) {
        for (unsigned i = 0; i < sub.size(); ++i) {
            expr_ref e(m);
            var_subst(m, false)(sub[i].get(), s0.size(), s0.c_ptr(), e);
            sub[i] = e;            
        }
    }

    void instantiate(expr_ref_vector const& sub, expr_ref& fml) {
        if (sub.empty()) {
            return;
        }
        if (!is_forall(fml)) {
            return;
        }
        quantifier* q = to_quantifier(fml);
        if (q->get_num_decls() != sub.size()) {
            TRACE("proof_utils", tout << "quantifier has different number of variables than substitution";
                  tout << mk_pp(q, m) << "\n";
                  tout << sub.size() << "\n";);
            return;
        }
        var_subst(m, false)(q->get_expr(), sub.size(), sub.c_ptr(), fml);
    }

};

void proof_utils::push_instantiations_up(proof_ref& pr) {
    push_instantiations_up_cl push(pr.get_manager());
    push(pr);
}


