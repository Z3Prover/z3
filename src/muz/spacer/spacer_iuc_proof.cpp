#include "muz/spacer/spacer_iuc_proof.h"
#include "ast/for_each_expr.h"
#include "ast/array_decl_plugin.h"
#include "ast/proofs/proof_utils.h"
#include "muz/spacer/spacer_proof_utils.h"

namespace spacer {

    /*
     * ====================================
     * init
     * ====================================
     */
    iuc_proof::iuc_proof(ast_manager& m, proof* pr, expr_set& b_conjuncts) : m(m), m_pr(pr,m)
    {
        // init A-marks and B-marks
        collect_symbols_b(b_conjuncts);
        compute_marks(b_conjuncts);
    }

    proof* iuc_proof::get()
    {
        return m_pr.get();
    }

    /*
     * ====================================
     * methods for computing symbol colors
     * ====================================
     */
    class collect_pure_proc {
        func_decl_set& m_symbs;
    public:
        collect_pure_proc(func_decl_set& s):m_symbs(s) {}

        void operator()(app* a) {
            if (a->get_family_id() == null_family_id) {
                m_symbs.insert(a->get_decl());
            }
        }
        void operator()(var*) {}
        void operator()(quantifier*) {}
    };

    void iuc_proof::collect_symbols_b(expr_set& b_conjuncts)
    {
        expr_mark visited;
        collect_pure_proc proc(m_symbols_b);
        for (expr_set::iterator it = b_conjuncts.begin(); it != b_conjuncts.end(); ++it)
        {
            for_each_expr(proc, visited, *it);
        }
    }

    class is_pure_expr_proc {
        func_decl_set const& m_symbs;
        array_util           m_au;
    public:
        struct non_pure {};

        is_pure_expr_proc(func_decl_set const& s, ast_manager& m):
        m_symbs(s),
        m_au (m)
        {}

        void operator()(app* a) {
            if (a->get_family_id() == null_family_id) {
                if (!m_symbs.contains(a->get_decl())) {
                    throw non_pure();
                }
            }
            else if (a->get_family_id () == m_au.get_family_id () &&
                     a->is_app_of (a->get_family_id (), OP_ARRAY_EXT)) {
                throw non_pure();
            }
        }
        void operator()(var*) {}
        void operator()(quantifier*) {}
    };

    // requires that m_symbols_b has already been computed, which is done during initialization.
    bool iuc_proof::only_contains_symbols_b(expr* expr) const
    {
        is_pure_expr_proc proc(m_symbols_b, m);
        try {
            for_each_expr(proc, expr);
        }
        catch (is_pure_expr_proc::non_pure)
        {
            return false;
        }
        return true;
    }

    /*
     * ====================================
     * methods for computing which premises
     * have been used to derive the conclusions
     * ====================================
     */

    void iuc_proof::compute_marks(expr_set& b_conjuncts)
    {
        proof_post_order it(m_pr, m);
        while (it.hasNext())
        {
            proof* currentNode = it.next();

            if (m.get_num_parents(currentNode) == 0)
            {
                switch(currentNode->get_decl_kind())
                {

                    case PR_ASSERTED: // currentNode is an axiom
                    {
                        if (b_conjuncts.contains(m.get_fact(currentNode)))
                        {
                            m_b_mark.mark(currentNode, true);
                        }
                        else
                        {
                            m_a_mark.mark(currentNode, true);
                        }
                        break;
                    }
                        // currentNode is a hypothesis:
                    case PR_HYPOTHESIS:
                    {
                        m_h_mark.mark(currentNode, true);
                        break;
                    }
                    default:
                    {
                        break;
                    }
                }
            }
            else
            {
                // collect from parents whether derivation of current node contains A-axioms, B-axioms and hypothesis
                bool need_to_mark_a = false;
                bool need_to_mark_b = false;
                bool need_to_mark_h = false;

                for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i)
                {
                    SASSERT(m.is_proof(currentNode->get_arg(i)));
                    proof* premise = to_app(currentNode->get_arg(i));

                    need_to_mark_a = need_to_mark_a || m_a_mark.is_marked(premise);
                    need_to_mark_b = need_to_mark_b || m_b_mark.is_marked(premise);
                    need_to_mark_h = need_to_mark_h || m_h_mark.is_marked(premise);
                }

                // if current node is application of lemma, we know that all hypothesis are removed
                if(currentNode->get_decl_kind() == PR_LEMMA)
                {
                    need_to_mark_h = false;
                }

                // save results
                m_a_mark.mark(currentNode, need_to_mark_a);
                m_b_mark.mark(currentNode, need_to_mark_b);
                m_h_mark.mark(currentNode, need_to_mark_h);
            }
        }
    }

    bool iuc_proof::is_a_marked(proof* p)
    {
        return m_a_mark.is_marked(p);
    }
    bool iuc_proof::is_b_marked(proof* p)
    {
        return m_b_mark.is_marked(p);
    }
    bool iuc_proof::is_h_marked(proof* p)
    {
        return m_h_mark.is_marked(p);
    }

    /*
     * ====================================
     * methods for dot printing
     * ====================================
     */
    void iuc_proof::pp_dot()
    {
        pp_proof_dot(m, m_pr, this);
    }

    /*
     * ====================================
     * statistics
     * ====================================
     */

    void iuc_proof::print_farkas_stats()
    {
        unsigned farkas_counter = 0;
        unsigned farkas_counter2 = 0;

        proof_post_order it3(m_pr, m);
        while (it3.hasNext())
        {
            proof* currentNode = it3.next();

            // if node is theory lemma
            if (is_farkas_lemma(m, currentNode))
            {
                farkas_counter++;

                // check whether farkas lemma is to be interpolated (could potentially miss farkas lemmas, which are interpolated, because we potentially don't want to use the lowest cut)
                bool has_blue_nonred_parent = false;
                for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i)
                {
                    proof* premise = to_app(currentNode->get_arg(i));
                    if (!is_a_marked(premise) && is_b_marked(premise))
                    {
                        has_blue_nonred_parent = true;
                        break;
                    }
                }
                if (has_blue_nonred_parent && is_a_marked(currentNode))
                {
                    SASSERT(is_b_marked(currentNode));
                    farkas_counter2++;
                }
            }
        }

        verbose_stream() << "\nThis proof contains " << farkas_counter << " Farkas lemmas. " << farkas_counter2 << " Farkas lemmas participate in the lowest cut\n";
    }
}
