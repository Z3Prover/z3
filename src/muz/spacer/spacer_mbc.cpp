#include <climits>

#include "muz/spacer/spacer_mbc.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/scoped_proof.h"
#include "model/model_evaluator.h"


namespace spacer {

mbc::mbc(ast_manager &m) : m(m) {}

namespace {
class mbc_rewriter_cfg : public default_rewriter_cfg {

    ast_manager &m;
    const mbc::partition_map &m_pmap;
    model &m_mdl;
    model_evaluator m_mev;
    vector<expr_ref_vector> &m_parts;
    unsigned m_current_part;

    obj_map<expr,expr*> m_subs;
public:
    mbc_rewriter_cfg(ast_manager &m, const mbc::partition_map &pmap,
                     model &mdl, vector<expr_ref_vector> &parts) :
        m(m), m_pmap(pmap), m_mdl(mdl), m_mev(m_mdl),
        m_parts(parts), m_current_part(UINT_MAX)
        {m_mev.set_model_completion(true);}

    bool get_subst(expr *s, expr * & t, proof * & t_pr) {
        if (!is_app(s)) return false;
        unsigned part = UINT_MAX;

        // not in partition map
        if (!m_pmap.find (to_app(s)->get_decl(), part)) return false;

        // first part element, remember it
        if (!found_partition()) {
            set_partition(part);
            return false;
        }

        // already in our substitution map
        expr *tmp = nullptr;
        if (m_subs.find(s, tmp)) {
            t = tmp;
            return true;
        }

        // decide value based on model
        expr_ref val(m);

        // eval in the model
        m_mev.eval(s, val, true);

        // store decided equality (also keeps ref to s and val
        m_parts[part].push_back(m.mk_eq(s, val));
        // store substitution
        m_subs.insert(s, val);
        t = val;
        return true;
    }

    void reset_partition() {m_current_part = UINT_MAX;}
    unsigned partition() {return m_current_part;}
    bool found_partition() {return m_current_part < UINT_MAX;}
    void set_partition(unsigned v) {m_current_part = v;}
};
}

void mbc::operator()(const partition_map &pmap, expr_ref_vector &lits,
                     model &mdl, vector<expr_ref_vector> &res) {
    scoped_no_proof _sp (m);

    mbc_rewriter_cfg cfg(m, pmap, mdl, res);
    rewriter_tpl<mbc_rewriter_cfg> rw(m, false, cfg);
    th_rewriter thrw(m);

    for (auto *lit : lits) {
        expr_ref new_lit(m);
        cfg.reset_partition();
        rw(lit, new_lit);
        thrw(new_lit);
        if (cfg.found_partition()) {
            SASSERT(cfg.partition() < res.size());
            res[cfg.partition()].push_back(new_lit);
        }
    }
}

}
