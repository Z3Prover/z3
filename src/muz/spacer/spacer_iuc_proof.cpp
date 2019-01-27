#include <unordered_map>
#include "ast/ast_pp_dot.h"

#include "muz/spacer/spacer_iuc_proof.h"
#include "ast/for_each_expr.h"
#include "ast/array_decl_plugin.h"
#include "ast/proofs/proof_utils.h"
#include "muz/spacer/spacer_proof_utils.h"
#include "muz/spacer/spacer_util.h"
namespace spacer {

/*
 * ====================================
 * init
 * ====================================
 */
iuc_proof::iuc_proof(ast_manager& m, proof* pr, const expr_set& core_lits) :
    m(m), m_pr(pr,m) {
    for (auto lit : core_lits) m_core_lits.insert(lit);
    // init A-marks and B-marks
    collect_core_symbols();
    compute_marks();
}

iuc_proof::iuc_proof(ast_manager& m, proof* pr, const expr_ref_vector& core_lits) :
    m(m), m_pr(pr,m) {
    for (auto lit : core_lits) m_core_lits.insert(lit);
    // init A-marks and B-marks
    collect_core_symbols();
    compute_marks();
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

void iuc_proof::collect_core_symbols()
{
    expr_mark visited;
    collect_pure_proc proc(m_core_symbols);
    for (auto lit : m_core_lits)
        for_each_expr(proc, visited, lit);
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
    catch (const is_pure_expr_proc::non_pure &)
    {return false;}

    return true;
}

void iuc_proof::compute_marks()
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
                if (m_core_lits.contains(m.get_fact(cur)))
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
            if (cur->get_decl_kind() == PR_LEMMA) need_to_mark_h = false;

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

void iuc_proof::display_dot(std::ostream& out) {
    out << "digraph proof { \n";

    std::unordered_map<unsigned, unsigned> ids;
    unsigned last_id = 0;

    proof_post_order it(m_pr, m);
    while (it.hasNext())
    {
        proof* curr = it.next();

        SASSERT(ids.count(curr->get_id()) == 0);
        ids.insert(std::make_pair(curr->get_id(), last_id));

        std::string color = "white";
        if (this->is_a_marked(curr) && !this->is_b_marked(curr))
            color = "red";
        else if (!this->is_a_marked(curr) && this->is_b_marked(curr))
            color = "blue";
        else if (this->is_a_marked(curr) && this->is_b_marked(curr) )
            color = "purple";

        // compute node label
        std::ostringstream label_ostream;
        label_ostream << mk_epp(m.get_fact(curr), m) << "\n";
        std::string label = escape_dot(label_ostream.str());

        // compute edge-label
        std::string edge_label = "";
        if (m.get_num_parents(curr) == 0) {
            switch (curr->get_decl_kind())
            {
            case PR_ASSERTED:
                edge_label = "asserted:";
                break;
            case PR_HYPOTHESIS:
                edge_label = "hyp:";
                color = "grey";
                break;
            case PR_TH_LEMMA:
                if (is_farkas_lemma(m, curr))
                    edge_label = "th_axiom(farkas):";
                else if (is_arith_lemma(m, curr))
                    edge_label = "th_axiom(arith):";
                else
                    edge_label = "th_axiom:";
                break;
            default:
                edge_label = "unknown axiom:";
            }
        }
        else {
            if (curr->get_decl_kind() == PR_LEMMA)
                edge_label = "lemma:";
            else if (curr->get_decl_kind() == PR_TH_LEMMA) {
                if (is_farkas_lemma(m, curr))
                    edge_label = "th_lemma(farkas):";
                else if (is_arith_lemma(m, curr))
                    edge_label = "th_lemma(arith):";
                else
                    edge_label = "th_lemma(other):";
            }
        }

        // generate entry for node in dot-file
        out   << "node_" << last_id << " " << "["
              << "shape=box,style=\"filled\","
              << "label=\"" << edge_label << " " << label << "\", "
              << "fillcolor=\"" << color << "\"" << "]\n";

        // add entry for each edge to that node
        for (unsigned i = m.get_num_parents(curr); i > 0  ; --i)
        {
            proof* premise = to_app(curr->get_arg(i-1));
            unsigned pid = ids.at(premise->get_id());
            out   << "node_" << pid << " -> " << "node_" << last_id << ";\n";
        }

        ++last_id;
    }
    out << "\n}" << std::endl;
}
}
