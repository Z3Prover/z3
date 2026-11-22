/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_proof_manager.h

Abstract:

    Dependency cores and owning, fact-level sequence derivations.

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "util/dependency.h"
#include <initializer_list>

namespace seq {

    class proof_manager : public scoped_dependency_manager<unsigned> {
        ast_manager* m = nullptr;
        scoped_ptr<proof_ref_vector> m_sources;
        scoped_ptr<proof_ref_vector> m_generated;
        bool m_active = false;
        bool m_branch = false;
        proof* m_substitution = nullptr;
        symbol m_rule;

    public:
        void set_manager(ast_manager& manager) {
            SASSERT(!m || m == &manager);
            if (m)
                return;
            m = &manager;
            m_sources = alloc(proof_ref_vector, manager);
            m_generated = alloc(proof_ref_vector, manager);
        }
        bool proofs_enabled() const { return m && m->proofs_enabled(); }
        void begin_rule(symbol const& rule, bool branch, proof_ref_vector const& sources) {
            SASSERT(m);
            m_rule = rule;
            m_active = true;
            m_branch = branch;
            m_sources->reset();
            m_sources->append(sources);
            m_generated->reset();
        }
        void end_rule() {
            m_active = m_branch = false;
            m_substitution = nullptr;
            if (m_sources) m_sources->reset();
            if (m_generated) m_generated->reset();
        }
        proof_ref_vector const& generated() const { SASSERT(m_generated); return *m_generated; }
        proof* substitution_proof() const { return m_substitution; }
        void set_substitution_proof(proof* pr) { m_substitution = pr; }
        proof*& substitution_proof_ref() { return m_substitution; }
        void add_premise(proof* pr) {
            if (m_active && pr && !m_sources->contains(pr))
                m_sources->push_back(pr);
        }

        proof* mk_proof(symbol const& rule, expr* fact, std::initializer_list<proof*> parents = {}) {
            if (!proofs_enabled())
                return nullptr;
            SASSERT(m->is_bool(fact));
            proof_ref_vector premises(*m);
            for (proof* p : parents)
                if (p && !premises.contains(p))
                    premises.push_back(p);
            if (!m_active && premises.empty())
                return m->mk_hypothesis(fact);
            if (m_active) {
                for (proof* p : *m_sources)
                    if (!premises.contains(p)) premises.push_back(p);
                // A split chooses local facts; their hypotheses are discharged
                // by its named branch closure, not treated as consequences.
                if (m_branch && parents.size() == 0)
                    premises.push_back(m->mk_hypothesis(fact));
            }
            seq_util u(*m);
            proof* result = u.mk_proof(rule == symbol::null ? m_rule : rule, premises, fact);
            if (m_active) {
                m_generated->push_back(result);
                m_sources->push_back(result);
            }
            return result;
        }
    };

    inline expr_ref equation_fact(seq_util& u, expr_ref_vector const& lhs,
                                  expr_ref_vector const& rhs, bool equality = true) {
        ast_manager& m = u.get_manager();
        sort* s = !lhs.empty() ? lhs[0]->get_sort() : !rhs.empty() ? rhs[0]->get_sort() : u.mk_string_sort();
        expr_ref l(u.str.mk_concat(lhs, s), m);
        expr_ref r(u.str.mk_concat(rhs, s), m);
        expr_ref fact(m.mk_eq(l, r), m);
        if (!equality)
            fact = m.mk_not(fact);
        return fact;
    }

    inline expr_ref substitution_fact(seq_util& u, expr* var, expr_ref_vector const& repl) {
        ast_manager& m = u.get_manager();
        expr_ref rhs(u.str.mk_concat(repl, var->get_sort()), m);
        return expr_ref(m.mk_eq(var, rhs), m);
    }
}
