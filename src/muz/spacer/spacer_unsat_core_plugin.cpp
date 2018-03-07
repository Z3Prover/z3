/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_unsat_core_plugin.cpp

Abstract:
   plugin for itp cores

Author:
    Bernhard Gleiss

Revision History:


--*/
#include <set>
#include <limits>

#include "ast/rewriter/bool_rewriter.h"
#include "ast/arith_decl_plugin.h"
#include "ast/proofs/proof_utils.h"

#include "solver/solver.h"

#include "smt/smt_farkas_util.h"
#include "smt/smt_solver.h"

#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_unsat_core_plugin.h"
#include "muz/spacer/spacer_unsat_core_learner.h"

namespace spacer
{


void unsat_core_plugin_lemma::compute_partial_core(proof* step)
{
    SASSERT(m_learner.is_a_marked(step));
    SASSERT(m_learner.is_b_marked(step));

    for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
    {
        SASSERT(m_learner.m.is_proof(step->get_arg(i)));
        proof* premise = to_app(step->get_arg(i));

        if (m_learner.is_b_open (premise))
        {
            // by IH, premises that are AB marked are already closed
            SASSERT(!m_learner.is_a_marked(premise));
            add_lowest_split_to_core(premise);
        }
    }
    m_learner.set_closed(step, true);
}

void unsat_core_plugin_lemma::add_lowest_split_to_core(proof* step) const
{
    SASSERT(m_learner.is_b_open(step));
    ast_manager &m = m_learner.m;

    ptr_vector<proof> todo;
    todo.push_back(step);

    while (!todo.empty())
    {
        proof* pf = todo.back();
        todo.pop_back();

        // if current step hasn't been processed,
        if (!m_learner.is_closed(pf))
        {
            m_learner.set_closed(pf, true);
            // the step is b-marked and not closed.
            // by I.H. the step must be already visited
            // so if it is also a-marked, it must be closed
            SASSERT(m_learner.is_b_marked(pf));
            SASSERT(!m_learner.is_a_marked(pf));

            // the current step needs to be interpolated:
            expr* fact = m_learner.m.get_fact(pf);
            // if we trust the current step and we are able to use it
            if (m_learner.is_b_pure (pf) &&
                (m.is_asserted(pf) || is_literal(m, fact)))
            {
                // just add it to the core
                m_learner.add_lemma_to_core(fact);
            }
            // otherwise recurse on premises
            else
            {
                for (unsigned i = 0, sz =  m_learner.m.get_num_parents(pf);
                     i < sz; ++i)
                {
                    SASSERT(m_learner.m.is_proof(pf->get_arg(i)));
                    proof* premise = m.get_parent (pf, i);
                    if (m_learner.is_b_open(premise)) {
                        todo.push_back(premise);
                    }
                }
            }

        }
    }
}


void unsat_core_plugin_farkas_lemma::compute_partial_core(proof* step)
{
    ast_manager &m = m_learner.m;
    SASSERT(m_learner.is_a_marked(step));
    SASSERT(m_learner.is_b_marked(step));
    // XXX this assertion should be true so there is no need to check for it
    SASSERT (!m_learner.is_closed (step));
    func_decl* d = step->get_decl();
    symbol sym;
    if(!m_learner.is_closed(step) && // if step is not already interpolated
       step->get_decl_kind() == PR_TH_LEMMA && // and step is a Farkas lemma
       d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
       d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
       d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
       d->get_num_parameters() >= m_learner.m.get_num_parents(step) + 2) // the following parameters are the Farkas coefficients
    {
        SASSERT(m_learner.m.has_fact(step));

        ptr_vector<app> literals;
        vector<rational> coefficients;

        /* The farkas lemma represents a subproof starting from premise(-set)s A, BNP and BP(ure) and
         * ending in a disjunction D. We need to compute the contribution of BP, i.e. a formula, which
         * is entailed by BP and together with A and BNP entails D.
         *
         * Let Fark(F) be the farkas coefficient for F. We can use the fact that
         * (A*Fark(A) + BNP*Fark(BNP) + BP*Fark(BP) + (neg D)*Fark(D)) => false. (E1)
         * We further have that A+B => C implies (A \land B) => C. (E2)
         *
         * Alternative 1:
         * From (E1) immediately get that BP*Fark(BP) is a solution.
         *
         * Alternative 2:
         * We can rewrite (E2) to rewrite (E1) to
         * (BP*Fark(BP)) => (neg(A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D))) (E3)
         * and since we can derive (A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D)) from
         * A, BNP and D, we also know that it is inconsisent. Therefore
         * neg(A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D)) is a solution.
         *
         * Finally we also need the following workaround:
         * 1) Although we know from theory, that the Farkas coefficients are always nonnegative,
         * the Farkas coefficients provided by arith_core are sometimes negative (must be a bug)
         * as workaround we take the absolute value of the provided coefficients.
         */
        parameter const* params = d->get_parameters() + 2; // point to the first Farkas coefficient

        STRACE("spacer.farkas",
            verbose_stream() << "Farkas input: "<< "\n";
            for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
            {
                SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                proof *prem = m.get_parent (step, i);

                rational coef;
                VERIFY(params[i].is_rational(coef));

                bool b_pure = m_learner.is_b_pure (prem);
                verbose_stream() << (b_pure?"B":"A") << " " << coef << " " << mk_pp(m_learner.m.get_fact(prem), m_learner.m) << "\n";
            }
        );

        bool can_be_closed = true;

        for(unsigned i = 0; i < m.get_num_parents(step); ++i)
        {
            SASSERT(m_learner.m.is_proof(step->get_arg(i)));
            proof * premise = m.get_parent (step, i);

            if (m_learner.is_b_open (premise))
            {
                SASSERT(!m_learner.is_a_marked(premise));

                if (m_learner.is_b_pure (step))
                {
                    if (!m_use_constant_from_a)
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                }
                else
                {
                    can_be_closed = false;

                    if (m_use_constant_from_a)
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                }
            }
            else
            {
                if (m_use_constant_from_a)
                {
                    rational coefficient;
                    VERIFY(params[i].is_rational(coefficient));
                    literals.push_back(to_app(m_learner.m.get_fact(premise)));
                    coefficients.push_back(abs(coefficient));
                }
            }
        }

        if (m_use_constant_from_a)
        {
            params += m_learner.m.get_num_parents(step); // point to the first Farkas coefficient, which corresponds to a formula in the conclusion

            // the conclusion can either be a single formula or a disjunction of several formulas, we have to deal with both situations
            if (m_learner.m.get_num_parents(step) + 2 < d->get_num_parameters())
            {
                unsigned num_args = 1;
                expr* conclusion = m_learner.m.get_fact(step);
                expr* const* args = &conclusion;
                if (m_learner.m.is_or(conclusion))
                {
                    app* _or = to_app(conclusion);
                    num_args = _or->get_num_args();
                    args = _or->get_args();
                }
                SASSERT(m_learner.m.get_num_parents(step) + 2 + num_args == d->get_num_parameters());

                bool_rewriter brw(m_learner.m);
                for (unsigned i = 0; i < num_args; ++i)
                {
                    expr* premise = args[i];

                    expr_ref negatedPremise(m_learner.m);
                    brw.mk_not(premise, negatedPremise);
                    literals.push_back(to_app(negatedPremise));

                    rational coefficient;
                    VERIFY(params[i].is_rational(coefficient));
                    coefficients.push_back(abs(coefficient));
                }
            }
        }

        // only if all b-premises can be used directly, add the farkas core and close the step
        if (can_be_closed)
        {
            m_learner.set_closed(step, true);

            expr_ref res(m_learner.m);
            compute_linear_combination(coefficients, literals, res);

            m_learner.add_lemma_to_core(res);
        }
    }
}

void unsat_core_plugin_farkas_lemma::compute_linear_combination(const vector<rational>& coefficients, const ptr_vector<app>& literals, expr_ref& res)
{
    SASSERT(literals.size() == coefficients.size());

    ast_manager& m = res.get_manager();
    smt::farkas_util util(m);
    if (m_use_constant_from_a)
    {
        util.set_split_literals (m_split_literals); // small optimization: if flag m_split_literals is set, then preserve diff constraints
    }
    for(unsigned i = 0; i < literals.size(); ++i)
    {
        util.add(coefficients[i], literals[i]);
    }
    if (m_use_constant_from_a)
    {
        res = util.get();
    }
    else
    {
        expr_ref negated_linear_combination = util.get();
        res = mk_not(m, negated_linear_combination);
    }
}

    void unsat_core_plugin_farkas_lemma_optimized::compute_partial_core(proof* step)
    {
        SASSERT(m_learner.is_a_marked(step));
        SASSERT(m_learner.is_b_marked(step));

        func_decl* d = step->get_decl();
        symbol sym;
        if(!m_learner.is_closed(step) && // if step is not already interpolated
           step->get_decl_kind() == PR_TH_LEMMA && // and step is a Farkas lemma
           d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
           d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
           d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
           d->get_num_parameters() >= m_learner.m.get_num_parents(step) + 2) // the following parameters are the Farkas coefficients
        {
            SASSERT(m_learner.m.has_fact(step));

            vector<std::pair<app*,rational> > linear_combination; // collects all summands of the linear combination

            parameter const* params = d->get_parameters() + 2; // point to the first Farkas coefficient

            STRACE("spacer.farkas",
               verbose_stream() << "Farkas input: "<< "\n";
               for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
               {
                   SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                   proof *prem = m.get_parent (step, i);

                   rational coef;
                   VERIFY(params[i].is_rational(coef));

                   bool b_pure = m_learner.is_b_pure (prem);
                   verbose_stream() << (b_pure?"B":"A") << " " << coef << " " << mk_pp(m_learner.m.get_fact(prem), m_learner.m) << "\n";
               }
            );

            bool can_be_closed = true;
            for(unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
            {
                SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                proof * premise = m.get_parent (step, i);

                if (m_learner.is_b_marked(premise) && !m_learner.is_closed(premise))
                {
                    SASSERT(!m_learner.is_a_marked(premise));

                    if (m_learner.only_contains_symbols_b(m_learner.m.get_fact(premise)) && !m_learner.is_h_marked(premise))
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        linear_combination.push_back(std::make_pair(to_app(m_learner.m.get_fact(premise)), abs(coefficient)));
                    }
                    else
                    {
                        can_be_closed = false;
                    }
                }
            }

            // only if all b-premises can be used directly, close the step and add linear combinations for later processing
            if (can_be_closed)
            {
                m_learner.set_closed(step, true);
                if (!linear_combination.empty())
                {
                    m_linear_combinations.push_back(linear_combination);
                }
            }
        }
    }

    struct farkas_optimized_less_than_pairs
    {
        inline bool operator() (const std::pair<app*,rational>& pair1, const std::pair<app*,rational>& pair2) const
        {
            return (pair1.first->get_id() < pair2.first->get_id());
        }
    };

    void unsat_core_plugin_farkas_lemma_optimized::finalize()
    {
        if(m_linear_combinations.empty())
        {
            return;
        }
        DEBUG_CODE(
            for (auto& linear_combination : m_linear_combinations) {
            SASSERT(linear_combination.size() > 0);
            });

        // 1. construct ordered basis
        ptr_vector<app> ordered_basis;
        obj_map<app, unsigned> map;
        unsigned counter = 0;
        for (const auto& linear_combination : m_linear_combinations)
        {
            for (const auto& pair : linear_combination)
            {
                if (!map.contains(pair.first))
                {
                    ordered_basis.push_back(pair.first);
                    map.insert(pair.first, counter++);
                }
            }
        }

        // 2. populate matrix
        spacer_matrix matrix(m_linear_combinations.size(), ordered_basis.size());

        for (unsigned i=0; i < m_linear_combinations.size(); ++i)
        {
            auto linear_combination = m_linear_combinations[i];
            for (const auto& pair : linear_combination)
            {
                matrix.set(i, map[pair.first], pair.second);
            }
        }

        // 3. perform gaussian elimination
        unsigned i = matrix.perform_gaussian_elimination();

        // 4. extract linear combinations from matrix and add result to core
        for (unsigned k=0; k < i; k++)// i points to the row after the last row which is non-zero
        {
            ptr_vector<app> literals;
            vector<rational> coefficients;
            for (unsigned l=0; l < matrix.num_cols(); ++l)
            {
                if (!matrix.get(k,l).is_zero())
                {
                    literals.push_back(ordered_basis[l]);
                    coefficients.push_back(matrix.get(k,l));
            }
        }
            SASSERT(literals.size() > 0);
            expr_ref linear_combination(m);
            compute_linear_combination(coefficients, literals, linear_combination);

            m_learner.add_lemma_to_core(linear_combination);
        }

    }

    void unsat_core_plugin_farkas_lemma_optimized::compute_linear_combination(const vector<rational>& coefficients, const ptr_vector<app>& literals, expr_ref& res)
            {
        SASSERT(literals.size() == coefficients.size());

        ast_manager& m = res.get_manager();
        smt::farkas_util util(m);
        for(unsigned i = 0; i < literals.size(); ++i)
                    {
            util.add(coefficients[i], literals[i]);
        }
        expr_ref negated_linear_combination = util.get();
        SASSERT(m.is_not(negated_linear_combination));
        res = mk_not(m, negated_linear_combination); //TODO: rewrite the get-method to return nonnegated stuff?
                    }


    void unsat_core_plugin_farkas_lemma_bounded::finalize()  {
        if (m_linear_combinations.empty()) {
            return;
        }
        DEBUG_CODE(
            for (auto& linear_combination : m_linear_combinations) {
                SASSERT(linear_combination.size() > 0);
            });

        // 1. construct ordered basis
        ptr_vector<app> ordered_basis;
        obj_map<app, unsigned> map;
        unsigned counter = 0;
        for (const auto& linear_combination : m_linear_combinations) {
            for (const auto& pair : linear_combination) {
                if (!map.contains(pair.first)) {
                    ordered_basis.push_back(pair.first);
                    map.insert(pair.first, counter++);
                }
            }
        }

        // 2. populate matrix
        spacer_matrix matrix(m_linear_combinations.size(), ordered_basis.size());

        for (unsigned i=0; i < m_linear_combinations.size(); ++i) {
            auto linear_combination = m_linear_combinations[i];
            for (const auto& pair : linear_combination) {
                matrix.set(i, map[pair.first], pair.second);
            }
        }
        matrix.print_matrix();

        // 3. normalize matrix to integer values
        matrix.normalize();


        arith_util util(m);

        vector<expr_ref_vector> coeffs;
        for (unsigned i=0; i < matrix.num_rows(); ++i) {
            coeffs.push_back(expr_ref_vector(m));
        }

        vector<expr_ref_vector> bounded_vectors;
        for (unsigned j=0; j < matrix.num_cols(); ++j)
        {
            bounded_vectors.push_back(expr_ref_vector(m));
        }

        // 4. find smallest n using guess and check algorithm
        for(unsigned n = 1; true; ++n)
        {
            params_ref p;
            p.set_bool("model", true);
            scoped_ptr<solver> s = mk_smt_solver(m, p, symbol::null); // TODO: incremental version?

            // add new variables w_in,
            for (unsigned i=0; i < matrix.num_rows(); ++i)
            {
                std::string name = "w_" + std::to_string(i) + std::to_string(n);

                func_decl_ref decl(m);
                decl = m.mk_func_decl(symbol(name.c_str()), 0, (sort*const*)nullptr, util.mk_int());
                coeffs[i].push_back(m.mk_const(decl));
            }

            // we need s_jn
            for (unsigned j=0; j < matrix.num_cols(); ++j)
            {
                std::string name = "s_" + std::to_string(j) + std::to_string(n);

                func_decl_ref decl(m);
                decl = m.mk_func_decl(symbol(name.c_str()), 0, (sort*const*)nullptr, util.mk_int());

                expr_ref s_jn(m);
                s_jn = m.mk_const(decl);

                bounded_vectors[j].push_back(s_jn);
            }

            // assert bounds for all s_jn
            for (unsigned l=0; l < n; ++l) {
                for (unsigned j=0; j < matrix.num_cols(); ++j) {
                    expr* s_jn = bounded_vectors[j][l].get();
                    
                    expr_ref lb(util.mk_le(util.mk_int(0), s_jn), m);
                    expr_ref ub(util.mk_le(s_jn, util.mk_int(1)), m);
                    s->assert_expr(lb);
                    s->assert_expr(ub);
                }
            }
            
            // assert: forall i,j: a_ij = sum_k w_ik * s_jk
            for (unsigned i=0; i < matrix.num_rows(); ++i)
                {
                for (unsigned j=0; j < matrix.num_cols(); ++j)
                    {
                    SASSERT(matrix.get(i, j).is_int());
                    app_ref a_ij(util.mk_numeral(matrix.get(i,j), true),m);

                    app_ref sum(m);
                    sum = util.mk_int(0);
                    for (unsigned k=0; k < n; ++k)
                        {
                        sum = util.mk_add(sum, util.mk_mul(coeffs[i][k].get(), bounded_vectors[j][k].get()));
                        }
                    expr_ref eq(m.mk_eq(a_ij, sum),m);
                    s->assert_expr(eq);
                    }
                }

            // check result
            lbool res = s->check_sat(0,nullptr);

            // if sat extract model and add corresponding linear combinations to core
            if (res == lbool::l_true) {
                model_ref model;
                s->get_model(model);
                
                for (unsigned k=0; k < n; ++k) {
                    ptr_vector<app> literals;
                    vector<rational> coefficients;
                    for (unsigned j=0; j < matrix.num_cols(); ++j) {
                        expr_ref evaluation(m);
                        
                        model.get()->eval(bounded_vectors[j][k].get(), evaluation, false);
                        if (!util.is_zero(evaluation)) {
                            literals.push_back(ordered_basis[j]);
                            coefficients.push_back(rational(1));
                        }
                    }
                    SASSERT(!literals.empty()); // since then previous outer loop would have found solution already
                    expr_ref linear_combination(m);
                    compute_linear_combination(coefficients, literals, linear_combination);
                    
                    m_learner.add_lemma_to_core(linear_combination);
                }
                return;
            }
        }
    }

    unsat_core_plugin_min_cut::unsat_core_plugin_min_cut(unsat_core_learner& learner, ast_manager& m) : unsat_core_plugin(learner), m(m){}

    /*
     * traverses proof rooted in step and constructs graph, which corresponds to the proof-DAG, with the following differences:
     *
     * 1) we want to skip vertices, which have a conclusion, which we don't like (call those steps bad and the other ones good). In other words, we start at a good step r and compute the smallest subproof with root r, which has only good leaves. Then we add an edge from the root to each of the leaves and remember that we already dealt with s. Then we recurse on all leaves.
     * 2) we want to introduce two vertices for all (unskipped) edges in order to run the min-cut algorithm
     * 3) we want to introduce a single super-source vertex, which is connected to all source-vertices of the proof-DAG and a
     * single super-sink vertex, to which all sink-vertices of the proof-DAG are connected
     *
     * 1) is dealt with using advance_to_lowest_partial_cut
     * 2) and 3) are dealt with using add_edge
     */
    void unsat_core_plugin_min_cut::compute_partial_core(proof* step)
    {
        ptr_vector<proof> todo;

        SASSERT(m_learner.is_a_marked(step));
        SASSERT(m_learner.is_b_marked(step));
        SASSERT(m.get_num_parents(step) > 0);
        SASSERT(!m_learner.is_closed(step));
        todo.push_back(step);

        while (!todo.empty())
        {
            proof* current = todo.back();
            todo.pop_back();

            // if we need to deal with the node and if we haven't added the corresponding edges so far
            if (!m_learner.is_closed(current) && !m_visited.is_marked(current))
            {
                // compute smallest subproof rooted in current, which has only good edges
                // add an edge from current to each leaf of that subproof
                // add the leaves to todo
                advance_to_lowest_partial_cut(current, todo);
                
                m_visited.mark(current, true);

            }
        }
        m_learner.set_closed(step, true);
    }

    
    void unsat_core_plugin_min_cut::advance_to_lowest_partial_cut(proof* step, ptr_vector<proof>& todo)
    {
        bool is_sink = true;

        ast_manager &m = m_learner.m;
        ptr_vector<proof> todo_subproof;

        for (unsigned i = 0, sz = m.get_num_parents(step); i < sz; ++i)
        {
            proof* premise = m.get_parent (step, i);
            {
                if (m_learner.is_b_marked(premise))
                {
                    todo_subproof.push_back(premise);
                }
            }
        }
        while (!todo_subproof.empty())
        {
            proof* current = todo_subproof.back();
            todo_subproof.pop_back();

            // if we need to deal with the node
            if (!m_learner.is_closed(current))
            {
                SASSERT(!m_learner.is_a_marked(current)); // by I.H. the step must be already visited

                // and the current step needs to be interpolated:
                if (m_learner.is_b_marked(current))
                {
                    // if we trust the current step and we are able to use it
                    if (m_learner.is_b_pure (current) &&
                        (m.is_asserted(current) ||
                         is_literal(m, m.get_fact(current))))
                    {
                        // we found a leaf of the subproof, so
                        // 1) we add corresponding edges
                        if (m_learner.is_a_marked(step))
                        {
                            add_edge(nullptr, current); // current is sink
                        }
                        else
                        {
                            add_edge(step, current); // standard edge
                        }
                        // 2) add the leaf to todo
                        todo.push_back(current);
                        is_sink = false;
                    }
                    // otherwise continue search for leaves of subproof
                    else
                    {
                        for (unsigned i = 0; i < m_learner.m.get_num_parents(current); ++i)
                        {
                            SASSERT(m_learner.m.is_proof(current->get_arg(i)));
                            proof* premise = m.get_parent (current, i);
                            todo_subproof.push_back(premise);
                        }
                    }
                }
            }
        }

        if (is_sink)
        {
            add_edge(step, nullptr);
        }
    }

    /*
     * adds an edge from the out-vertex of i to the in-vertex of j to the graph
     * if i or j isn't already present, it adds the corresponding in- and out-vertices to the graph
     * if i is a nullptr, it is treated as source vertex
     * if j is a nullptr, it is treated as sink vertex
     */
    void unsat_core_plugin_min_cut::add_edge(proof* i, proof* j)
    {
        unsigned node_i;
        unsigned node_j;
        if (i == nullptr)
        {
            node_i = 0;
        }
        else
        {
            unsigned tmp;
            if (m_proof_to_node_plus.find(i, tmp))
            {
                node_i = tmp;
            }
            else
            {
                unsigned node_other = m_min_cut.new_node();
                node_i = m_min_cut.new_node();

                m_proof_to_node_minus.insert(i, node_other);
                m_proof_to_node_plus.insert(i, node_i);

                if (node_i >= m_node_to_formula.size())
                {
                    m_node_to_formula.resize(node_i + 1);
                }
                m_node_to_formula[node_other] = m.get_fact(i);
                m_node_to_formula[node_i] = m.get_fact(i);

                m_min_cut.add_edge(node_other, node_i);
            }
        }

        if (j == nullptr)
        {
            node_j = 1;
        }
        else
        {
            unsigned tmp;
            if (m_proof_to_node_minus.find(j, tmp))
            {
                node_j = tmp;
            }
            else
            {
                node_j = m_min_cut.new_node();
                unsigned node_other = m_min_cut.new_node();

                m_proof_to_node_minus.insert(j, node_j);
                m_proof_to_node_plus.insert(j, node_other);

                if (node_other >= m_node_to_formula.size())
                {
                    m_node_to_formula.resize(node_other + 1);
                }
                m_node_to_formula[node_j] = m.get_fact(j);
                m_node_to_formula[node_other] = m.get_fact(j);

                m_min_cut.add_edge(node_j, node_other);
            }
        }

        // finally connect nodes
        m_min_cut.add_edge(node_i, node_j);
    }

    /*
     * computes min-cut on the graph constructed by compute_partial_core-method
     * and adds the corresponding lemmas to the core
     */
    void unsat_core_plugin_min_cut::finalize()
    {
        unsigned_vector cut_nodes;
        m_min_cut.compute_min_cut(cut_nodes);

        for (unsigned cut_node : cut_nodes)
        {
            m_learner.add_lemma_to_core(m_node_to_formula[cut_node]);
                }
            }
}
