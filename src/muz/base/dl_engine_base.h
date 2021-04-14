/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_engine_base.h

Abstract:

    Base class for Datalog engines.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#pragma once

#include "model/model.h"
#include "muz/base/dl_util.h"

namespace datalog {
    enum DL_ENGINE {
        DATALOG_ENGINE,
        SPACER_ENGINE,
        BMC_ENGINE,
        QBMC_ENGINE,
        TAB_ENGINE,
        CLP_ENGINE,
        DDNF_ENGINE,
        LAST_ENGINE
    };

    typedef void (*t_new_lemma_eh)(void *state, expr *lemma, unsigned level);
    typedef void (*t_predecessor_eh)(void *state);
    typedef void (*t_unfold_eh)(void *state);

    class engine_base {
        ast_manager& m;
        std::string m_name;
    public:
        engine_base(ast_manager& m, char const* name): m(m), m_name(name) {}
        virtual ~engine_base() {}

        virtual expr_ref get_answer() = 0;
        virtual expr_ref get_ground_sat_answer () {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual lbool query(expr* q) = 0;
        virtual lbool query(unsigned num_rels, func_decl*const* rels) { 
            if (num_rels != 1) return l_undef;
            expr_ref q(m);
            expr_ref_vector args(m);
            sort_ref_vector sorts(m);
            svector<symbol> names;
            func_decl* r = rels[0];
            for (unsigned i = 0; i < r->get_arity(); ++i) {
                args.push_back(m.mk_var(i, r->get_domain(i)));
                sorts.push_back(r->get_domain(i));
                names.push_back(symbol(i));
            }
            sorts.reverse();
            names.reverse();
            q = m.mk_app(r, args.size(), args.data());
            if (!args.empty()) {
                q = m.mk_exists(sorts.size(), sorts.data(), names.data(), q);
            }
            return query(q);
        }
        virtual lbool query_from_lvl (expr* q, unsigned lvl) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }

        virtual void reset_statistics() {}
        virtual void display_profile(std::ostream& out) {}
        virtual void collect_statistics(statistics& st) const {}
        virtual unsigned get_num_levels(func_decl* pred) {
            throw default_exception(std::string("get_num_levels is not supported for ") + m_name);
        }
        virtual expr_ref get_reachable(func_decl* pred) {
              throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual expr_ref get_cover_delta(int level, func_decl* pred) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual void add_cover(int level, func_decl* pred, expr* property) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual void add_invariant (func_decl *pred, expr *property) {
            throw default_exception(std::string("operation is not supported for ") + m_name);
        }
        virtual void display_certificate(std::ostream& out) const {
            throw default_exception(std::string("certificates are not supported for ") + m_name);
        }
        virtual model_ref get_model() {
            return model_ref();
        }

        virtual void get_rules_along_trace (rule_ref_vector& rules) {
            throw default_exception(std::string("get_rules_along_trace is not supported for ") + m_name);
        }
        virtual proof_ref get_proof() {
            return proof_ref(m.mk_asserted(m.mk_false()), m);
        }
        virtual void add_callback(void *state,
                                  const t_new_lemma_eh new_lemma_eh,
                                  const t_predecessor_eh predecessor_eh,
                                  const t_unfold_eh unfold_eh) {
            throw default_exception(std::string("add_lemma_exchange_callbacks is not supported for ") + m_name);
        }
        virtual void add_constraint (expr *c, unsigned lvl){
            throw default_exception(std::string("add_constraint is not supported for ") + m_name);
        }
        virtual void updt_params() {}
        virtual void cancel() {}
        virtual void cleanup() {}
    };

    class context;

    class register_engine_base {
    public:
        virtual engine_base* mk_engine(DL_ENGINE engine_type) = 0;
        virtual void set_context(context* ctx) = 0;
    };
}

