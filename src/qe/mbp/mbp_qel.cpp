/*++

  Module Name:

    mbp_qel.cpp

Abstract:

    Model Based Projection based on term graph

Author:

    Hari Govind V K (hgvk94) 2022-07-12

Revision History:


--*/
#include "qe/mbp/mbp_qel.h"
#include "ast/array_decl_plugin.h"
#include "ast/array_peq.h"
#include "ast/datatype_decl_plugin.h"
#include "model/model.h"
#include "qe/mbp/mbp_arrays.h"
#include "qe/mbp/mbp_arrays_tg.h"
#include "qe/mbp/mbp_basic_tg.h"
#include "qe/mbp/mbp_dt_tg.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_tg_plugins.h"
#include "util/obj_hashtable.h"

namespace mbp {

class mbp_qel::impl {
private:
    ast_manager &m;
    array_util m_array_util;
    datatype_util m_dt_util;
    params_ref m_params;
    mbp::term_graph m_tg;

    ptr_vector<mbp_tg_plugin> m_plugins;

    // set of non_basic variables to be projected. MBP rules are applied to
    // terms containing these variables
    obj_hashtable<app> m_non_basic_vars;

    // Utilities to keep track of which terms have been processed
    expr_sparse_mark m_seen;
    void mark_seen(expr *t) { m_seen.mark(t); }
    bool is_seen(expr *t) { return m_seen.is_marked(t); }

    bool is_non_basic(app *v) {
        return m_dt_util.is_datatype(v->get_sort()) || m_array_util.is_array(v);
    }

    void add_vars(mbp_tg_plugin *p, app_ref_vector &vars) {
        app_ref_vector *new_vars;
        p->get_new_vars(new_vars);
        for (auto v : *new_vars) {
            if (is_non_basic(v)) m_non_basic_vars.insert(v);
            vars.push_back(v);
        }
    }

    // apply all plugins till saturation
    void saturate(app_ref_vector &vars) {
        bool progress;
        do {
            progress = false;
            for (auto *p : m_plugins) {
                if (p->apply()) {
                    progress = true;
                    add_vars(p, vars);
                }
            }
        }
        while (progress);
    }

    void init(app_ref_vector &vars, expr_ref &fml, model &mdl) {
        // variables to apply projection rules on
        for (auto v : vars)
            if (is_non_basic(v)) m_non_basic_vars.insert(v);

        // mark vars as non-ground.
        m_tg.add_vars(vars);
        // treat eq literals as term in the egraph
        m_tg.set_explicit_eq();

        expr_ref_vector fmls(m);
        flatten_and(fml, fmls);
        m_tg.add_lits(fmls);

        add_plugin(alloc(mbp_array_tg, m, m_tg, mdl, m_non_basic_vars, m_seen));
        add_plugin(alloc(mbp_dt_tg, m, m_tg, mdl, m_non_basic_vars, m_seen));
        add_plugin(alloc(mbp_basic_tg, m, m_tg, mdl, m_non_basic_vars, m_seen));
    }

    void add_plugin(mbp_tg_plugin *p) { m_plugins.push_back(p); }

    void enable_model_splitting() {
        for (auto p : m_plugins) p->use_model();
    }

    mbp_tg_plugin *get_plugin(family_id fid) {
        for (auto p : m_plugins)
            if (p->get_family_id() == fid)
                return p;
        return nullptr;
    }

public:
    impl(ast_manager &m, params_ref const &p)
        : m(m), m_array_util(m), m_dt_util(m), m_params(p), m_tg(m) {}

    ~impl() {
        std::for_each(m_plugins.begin(), m_plugins.end(),
                      delete_proc<mbp_tg_plugin>());
    }

    void operator()(app_ref_vector &vars, expr_ref &fml, model &mdl) {
        if (vars.empty())
            return;

        init(vars, fml, mdl);
        // Apply MBP rules till saturation

        TRACE("mbp_tg",
            tout << "mbp tg " << m_tg.get_lits() << "\nand vars " << vars << "\n";);

        // First, apply rules without splitting on model
        saturate(vars);

        enable_model_splitting();

        // Do complete mbp
        saturate(vars);

        TRACE("mbp_tg",
              tout << "mbp tg " << m_tg.get_lits() << " and vars " << vars << "\n";);
        TRACE("mbp_tg_verbose", obj_hashtable<app> vars_tmp;
              collect_uninterp_consts(mk_and(m_tg.get_lits()), vars_tmp);
              for (auto a : vars_tmp) 
                  tout << mk_pp(a->get_decl(), m) << "\n";
              for (auto b : m_tg.get_lits()) 
                  tout << expr_ref(b, m) << "\n";
              for (auto a : vars) tout << expr_ref(a, m) << " ";
              tout << "\n");

        // 1. Apply qe_lite to remove all c-ground variables
        // 2. Collect all core variables in the output (variables used as array
        // indices/values)
        // 3. Re-apply qe_lite to remove non-core variables

        // Step 1.
        m_tg.qel(vars, fml);

        // Step 2.
        //  Variables that appear as array indices or values cannot be
        //  eliminated if they are not c-ground. They are core variables All
        //  other Array/ADT variables can be eliminated, they are redundant.
        obj_hashtable<app> core_vars;
        collect_selstore_vars(fml, core_vars, m);

        std::function<bool(app *)> is_red = [&](app *v) {
            if (!m_dt_util.is_datatype(v->get_sort()) &&
                !m_array_util.is_array(v))
                return false;
            return !core_vars.contains(v);
        };
        expr_sparse_mark red_vars;
        for (auto v : vars)
            if (is_red(v)) 
                red_vars.mark(v);
        CTRACE("mbp_tg", !core_vars.empty(), tout << "vars not redundant ";
               for (auto v : core_vars) tout << " " << app_ref(v, m);
               tout << "\n";);

        std::function<bool(expr *)> non_core = [&](expr *e) {
            if (is_partial_eq(e))
                return true;
            if (m.is_ite(e) || m.is_or(e) || m.is_implies(e) || m.is_distinct(e))
                return true;
            return red_vars.is_marked(e);
        };

        // Step 3.
        m_tg.qel(vars, fml, &non_core);

        CTRACE("mbp_tg", !vars.empty(),
               tout << "before substitution " << fml << "\n";);
        // for all remaining non-cgr bool, dt, array variables, add v = mdl(v)
        expr_sparse_mark s_vars;
        for (auto v : vars) {
            if (m_dt_util.is_datatype(v->get_sort()) ||
                m_array_util.is_array(v) || m.is_bool(v)) {
                CTRACE("mbp_tg",
                       m_array_util.is_array(v) ||
                           m_dt_util.is_datatype(v->get_sort()),
                       tout << "Could not eliminate  " << v->get_name()
                            << "\n";);
                s_vars.mark(v);
                m_tg.add_eq(v, mdl(v));
            }
        }

        std::function<bool(expr *)> substituted = [&](expr *e) {
            return
                is_partial_eq(e) ||
                m.is_ite(e) ||
                red_vars.is_marked(e) ||
                s_vars.is_marked(e);
        };

        // remove all substituted variables
        m_tg.qel(vars, fml, &substituted);
    }
};

mbp_qel::mbp_qel(ast_manager &m, params_ref const &p) {
    m_impl = alloc(impl, m, p);
}

mbp_qel::~mbp_qel() { dealloc(m_impl); }

void mbp_qel::operator()(app_ref_vector &vars, expr_ref &fml, model &mdl) {
    (*m_impl)(vars, fml, mdl);
}

} // namespace mbp
