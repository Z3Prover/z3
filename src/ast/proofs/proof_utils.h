/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    proof_utils.h

Abstract:
    Utilities to traverse and manipulate proofs

Author:
    Bernhard Gleiss
    Arie Gurfinkel
    Nikolaj Bjorner

Revision History:

--*/

#ifndef PROOF_UTILS_H_
#define PROOF_UTILS_H_
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/proofs/proof_checker.h"

/*
 * iterator, which traverses the proof in depth-first post-order.
 */

class proof_post_order {
public:
    proof_post_order(proof* refutation, ast_manager& manager);
    bool hasNext();
    proof* next();

private:
    ptr_vector<proof> m_todo;
    ast_mark          m_visited; // the proof nodes we have already visited
    ast_manager&      m;
};

void reduce_hypotheses(proof_ref &pr);


class proof_utils {
public:
    /**
       \brief reduce the set of hypotheses used in the proof.
     */
    static void reduce_hypotheses(proof_ref& pr);

    /**
       \brief Check that a proof does not contain open hypotheses.
    */
    static bool is_closed(ast_manager& m, proof* p);

    /**
       \brief Permute unit resolution rule with th-lemma
    */
    static void permute_unit_resolution(proof_ref& pr);

    /**
       \brief Push instantiations created in hyper-resolutions up to leaves.
       This produces a "ground" proof where leaves are annotated by instantiations.
    */
    static void push_instantiations_up(proof_ref& pr);


};

class elim_aux_assertions {

    static bool matches_fact(expr_ref_vector &args, expr* &match) {
        ast_manager &m = args.get_manager();
        expr *fact = args.back();
        for (unsigned i = 0, sz = args.size() - 1; i < sz; ++i) {
            expr *arg = args.get(i);
            if (m.is_proof(arg) &&
                m.has_fact(to_app(arg)) &&
                m.get_fact(to_app(arg)) == fact) {
                match = arg;
                return true;
            }
        }
        return false;
    }

    app_ref m_aux;
public:
    elim_aux_assertions(app_ref const& aux) : m_aux(aux) {}

    void mk_or_core(expr_ref_vector &args, expr_ref &res)
    {
        ast_manager &m = args.get_manager();
        unsigned j = 0;
        for (unsigned i = 0, sz = args.size(); i < sz; ++i) {
            if (m.is_false(args.get(i))) { continue; }
            if (i != j) { args [j] = args.get(i); }
            ++j;
        }
        SASSERT(j >= 1);
        res = j > 1 ? m.mk_or(j, args.c_ptr()) : args.get(0);
    }

    void mk_app(func_decl *decl, expr_ref_vector &args, expr_ref &res)
    {
        ast_manager &m = args.get_manager();
        bool_rewriter brwr(m);

        if (m.is_or(decl))
        { mk_or_core(args, res); }
        else if (m.is_iff(decl) && args.size() == 2)
            // avoiding simplifying equalities. In particular,
            // we don't want (= (not a) (not b)) to be reduced to (= a b)
        { res = m.mk_iff(args.get(0), args.get(1)); }
        else
        { brwr.mk_app(decl, args.size(), args.c_ptr(), res); }
    }

    void operator()(ast_manager &m, proof *pr, proof_ref &res)
    {
        DEBUG_CODE(proof_checker pc(m);
                   expr_ref_vector side(m);
                   SASSERT(pc.check(pr, side));
                  );
        obj_map<app, app*> cache;
        bool_rewriter brwr(m);

        // for reference counting of new proofs
        app_ref_vector pinned(m);

        ptr_vector<app> todo;
        todo.push_back(pr);

        expr_ref not_aux(m);
        not_aux = m.mk_not(m_aux);

        expr_ref_vector args(m);

        while (!todo.empty()) {
            app *p, *r;
            expr *a;

            p = todo.back();
            if (cache.find(pr, r)) {
                todo.pop_back();
                continue;
            }

            SASSERT(!todo.empty() || pr == p);
            bool dirty = false;
            unsigned todo_sz = todo.size();
            args.reset();
            for (unsigned i = 0, sz = p->get_num_args(); i < sz; ++i) {
                expr* arg = p->get_arg(i);
                if (arg == m_aux.get()) {
                    dirty = true;
                    args.push_back(m.mk_true());
                } else if (arg == not_aux.get()) {
                    dirty = true;
                    args.push_back(m.mk_false());
                }
                // skip (asserted m_aux)
                else if (m.is_asserted(arg, a) && a == m_aux.get()) {
                    dirty = true;
                }
                // skip (hypothesis m_aux)
                else if (m.is_hypothesis(arg, a) && a == m_aux.get()) {
                    dirty = true;
                } else if (is_app(arg) && cache.find(to_app(arg), r)) {
                    dirty |= (arg != r);
                    args.push_back(r);
                } else if (is_app(arg))
                { todo.push_back(to_app(arg)); }
                else
                    // -- not an app
                { args.push_back(arg); }

            }
            if (todo_sz < todo.size()) {
                // -- process parents
                args.reset();
                continue;
            }

            // ready to re-create
            app_ref newp(m);
            if (!dirty) { newp = p; }
            else if (m.is_unit_resolution(p)) {
                if (args.size() == 2)
                    // unit resolution with m_aux that got collapsed to nothing
                { newp = to_app(args.get(0)); }
                else {
                    ptr_vector<proof> parents;
                    for (unsigned i = 0, sz = args.size() - 1; i < sz; ++i)
                    { parents.push_back(to_app(args.get(i))); }
                    SASSERT(parents.size() == args.size() - 1);
                    newp = m.mk_unit_resolution(parents.size(), parents.c_ptr());
                    // XXX the old and new facts should be
                    // equivalent. The test here is much
                    // stronger. It might need to be relaxed.
                    SASSERT(m.get_fact(newp) == args.back());
                    pinned.push_back(newp);
                }
            } else if (matches_fact(args, a)) {
                newp = to_app(a);
            } else {
                expr_ref papp(m);
                mk_app(p->get_decl(), args, papp);
                newp = to_app(papp.get());
                pinned.push_back(newp);
            }
            cache.insert(p, newp);
            todo.pop_back();
            CTRACE("virtual",
                   p->get_decl_kind() == PR_TH_LEMMA &&
                   p->get_decl()->get_parameter(0).get_symbol() == "arith" &&
                   p->get_decl()->get_num_parameters() > 1 &&
                   p->get_decl()->get_parameter(1).get_symbol() == "farkas",
                   tout << "Old pf: " << mk_pp(p, m) << "\n"
                   << "New pf: " << mk_pp(newp, m) << "\n";);
        }

        proof *r;
        VERIFY(cache.find(pr, r));

        DEBUG_CODE(
            proof_checker pc(m);
            expr_ref_vector side(m);
            SASSERT(pc.check(r, side));
        );

        res = r ;
    }
};

#endif
