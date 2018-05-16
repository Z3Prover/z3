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
iuc_proof::iuc_proof(ast_manager& m, proof* pr, expr_set& core_lits) :
    m(m), m_pr(pr,m) {
    // init A-marks and B-marks
    collect_core_symbols(core_lits);
    compute_marks(core_lits);
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

void iuc_proof::collect_core_symbols(expr_set& core_lits)
{
    expr_mark visited;
    collect_pure_proc proc(m_core_symbols);
    for (expr_set::iterator it = core_lits.begin(); it != core_lits.end(); ++it) {
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

bool iuc_proof::is_core_pure(expr* e) const
{
    is_pure_expr_proc proc(m_core_symbols, m);
    try {
        for_each_expr(proc, e);
    }
    catch (is_pure_expr_proc::non_pure)
    {return false;}

    return true;
}

void iuc_proof::compute_marks(expr_set& core_lits)
{
    proof_post_order it(m_pr, m);
    while (it.hasNext())
    {
        proof* cur = it.next();
        if (m.get_num_parents(cur) == 0)
        {
            switch(cur->get_decl_kind())
            {
            case PR_ASSERTED:
                if (core_lits.contains(m.get_fact(cur)))
                    m_b_mark.mark(cur, true);
                else
                    m_a_mark.mark(cur, true);
                break;
            case PR_HYPOTHESIS:
                m_h_mark.mark(cur, true);
                break;
            default:
                break;
            }
        }
        else
        {
            // collect from parents whether derivation of current node
            // contains A-axioms, B-axioms and hypothesis
            bool need_to_mark_a = false;
            bool need_to_mark_b = false;
            bool need_to_mark_h = false;

            for (unsigned i = 0; i < m.get_num_parents(cur); ++i)
            {
                SASSERT(m.is_proof(cur->get_arg(i)));
                proof* premise = to_app(cur->get_arg(i));

                need_to_mark_a |= m_a_mark.is_marked(premise);
                need_to_mark_b |= m_b_mark.is_marked(premise);
                need_to_mark_h |= m_h_mark.is_marked(premise);
            }

            // if current node is application of a lemma, then all
            // active hypotheses are removed
            if(cur->get_decl_kind() == PR_LEMMA) need_to_mark_h = false;

            // save results
            m_a_mark.mark(cur, need_to_mark_a);
            m_b_mark.mark(cur, need_to_mark_b);
            m_h_mark.mark(cur, need_to_mark_h);
        }
    }
}

/*
 * ====================================
 * statistics
 * ====================================
 */

// debug method
void iuc_proof::dump_farkas_stats()
{
    unsigned fl_total = 0;
    unsigned fl_lowcut = 0;

    proof_post_order it(m_pr, m);
    while (it.hasNext())
    {
        proof* cur = it.next();

        // if node is theory lemma
        if (is_farkas_lemma(m, cur))
        {
            fl_total++;

            // check whether farkas lemma is to be interpolated (could
            // potentially miss farkas lemmas, which are interpolated,
            // because we potentially don't want to use the lowest
            // cut)
            bool has_blue_nonred_parent = false;
            for (unsigned i = 0; i < m.get_num_parents(cur); ++i) {
                proof* premise = to_app(cur->get_arg(i));
                if (!is_a_marked(premise) && is_b_marked(premise)) {
                    has_blue_nonred_parent = true;
                    break;
                }
            }

            if (has_blue_nonred_parent && is_a_marked(cur))
            {
                SASSERT(is_b_marked(cur));
                fl_lowcut++;
            }
        }
    }

    IF_VERBOSE(1, verbose_stream()
               << "\n total farkas lemmas " << fl_total
               << " farkas lemmas in lowest cut " << fl_lowcut << "\n";);
}
}
