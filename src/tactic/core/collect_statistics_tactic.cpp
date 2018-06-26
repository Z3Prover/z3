/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    collect_statistics_tactic.cpp

Abstract:

    A tactic for collection of various statistics.

Author:

    Mikolas Janota (mikjan) 2016-06-03
    Christoph (cwinter) 2016-06-03

Notes:

--*/
#include<string>
#include<map>

#include "ast/ast.h"
#include "util/params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/fpa_decl_plugin.h"
#include "tactic/tactical.h"
#include "util/stats.h"

#include "tactic/core/collect_statistics_tactic.h"

class collect_statistics_tactic : public tactic {
    ast_manager &        m;
    params_ref           m_params;
    basic_decl_plugin    m_basic_pi;
    arith_decl_plugin    m_arith_pi;
    array_decl_plugin    m_array_pi;
    bv_decl_plugin       m_bv_pi;
    datatype_decl_plugin m_datatype_pi;
    fpa_decl_plugin      m_fpa_pi;

    typedef std::map<std::string, unsigned long> stats_type;
    stats_type m_stats;

public:
    collect_statistics_tactic(ast_manager & m, params_ref const & p) :
        m(m),
        m_params(p) {
    }

    ~collect_statistics_tactic() override {}

    tactic * translate(ast_manager & m_) override {
        return alloc(collect_statistics_tactic, m_, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
    }

    void collect_param_descrs(param_descrs & r) override {}

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        tactic_report report("collect-statistics", *g);

        collect_proc cp(m, m_stats);
        expr_mark visited;
        const unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++)
            for_each_expr(cp, visited, g->form(i));

        std::cout << "(" << std::endl;
        for (auto const& kv : m_stats) 
            std::cout << " :" << kv.first << "    " << kv.second << std::endl;
        std::cout << ")" << std::endl;

        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {}

    void collect_statistics(statistics & st) const override {
    }

    void reset_statistics() override { reset();  }
    void reset() override { cleanup(); }

protected:
    class collect_proc {
    public:
        ast_manager &            m;
        stats_type &             m_stats;
        obj_hashtable<sort>      m_seen_sorts;
        obj_hashtable<func_decl> m_seen_func_decls;
        unsigned                 m_qdepth;

        collect_proc(ast_manager & m, stats_type & s) : m(m), m_stats(s), m_qdepth(0) {}

        void operator()(var * v) {
            m_stats["bound-variables"]++;
            this->operator()(v->get_sort());
        }

        void operator()(quantifier * q) {
            m_stats["quantifiers"]++;
            SASSERT(is_app(q->get_expr()));
            app * body = to_app(q->get_expr());
            switch (q->get_kind()) {
            case forall_k:
                m_stats["forall-variables"] += q->get_num_decls();
                break;
            case exists_k:
                m_stats["exists-variables"] += q->get_num_decls();
                break;
            case lambda_k:
                m_stats["lambda-variables"] += q->get_num_decls();
                break;
            }
            m_stats["patterns"] += q->get_num_patterns();
            m_stats["no-patterns"] += q->get_num_no_patterns();
            m_qdepth++;
            if (m_stats.find("max-quantification-depth") == m_stats.end() ||
                m_stats["max-quantification-depth"] < m_qdepth)
                m_stats["max-quantification-depth"] = m_qdepth;
            this->operator()(body);
            m_qdepth--;
        }

        void operator()(app * n) {
            m_stats["function-applications"]++;
            this->operator()(n->get_decl());
        }

        void operator()(sort * s) {
            if (m.is_uninterp(s)) {
                if (!m_seen_sorts.contains(s)) {
                    m_stats["uninterpreted-sorts"]++;
                    m_seen_sorts.insert(s);
                }
                m_stats["uninterpreted-sort-occurrences"]++;
            }
            else {
                params_ref prms;
                prms.set_bool("pp.single_line", true);
                std::stringstream ss;
                ss << "(declare-sort " << mk_ismt2_pp(s, m, prms) << ")";
                m_stats[ss.str()]++;

                if (s->get_info()->get_num_parameters() > 0) {
                    std::stringstream ssname;
                    ssname << "(declare-sort (_ " << s->get_name() << " *))";
                    m_stats[ssname.str()]++;
                }
            }
        }

        void operator()(func_decl * f) {
            for (unsigned i = 0; i < f->get_arity(); i++)
                this->operator()(f->get_domain()[i]);
            this->operator()(f->get_range());

            if (f->get_family_id() == null_family_id) {
                if (!m_seen_func_decls.contains(f)) {
                    if (f->get_arity() == 0)
                        m_stats["uninterpreted-constants"]++;
                    else
                        m_stats["uninterpreted-functions"]++;
                    m_seen_func_decls.insert(f);
                }

                if (f->get_arity() > 0)
                    m_stats["uninterpreted-function-occurrences"]++;
            }
            else {
                params_ref prms;
                prms.set_bool("pp.single_line", true);
                std::stringstream ss;
                ss << mk_ismt2_pp(f, m, prms);
                m_stats[ss.str()]++;

                std::stringstream ssfname;
                if (f->get_num_parameters() > 0)
                    ssfname << "(declare-fun (_ " << f->get_name() << " *) *)";
                else
                    ssfname << "(declare-fun " << f->get_name() << " *)";
                m_stats[ssfname.str()]++;
            }

            m_stats["function-applications"]++;
        }
    };
};


tactic * mk_collect_statistics_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(collect_statistics_tactic, m, p));
}
