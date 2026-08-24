/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt_ho_qsolver.cpp

Abstract:

    Higher-order matching and term-enumeration quantifier solver.

--*/

#include "ast/ast_util.h"
#include "ast/euf/ho_matcher.h"
#include "ast/has_free_vars.h"
#include "ast/rewriter/term_enumeration.h"
#include "smt/smt_context.h"
#include "smt/smt_ho_qsolver.h"
#include "smt/smt_quantifier.h"
#include "util/obj_hashtable.h"

namespace smt {

    struct ho_qsolver::imp {
        context&                         ctx;
        quantifier_manager&              qm;
        ast_manager&                     m;
        euf::ho_matcher                  matcher;
        quantifier*                      current_q = nullptr;
        term_enumeration*                terms = nullptr;
        vector<expr_ref_vector>          matches;
        unsigned                         num_candidates = 0;
        unsigned                         num_instances = 0;

        imp(context& ctx, quantifier_manager& qm) :
            ctx(ctx),
            qm(qm),
            m(ctx.get_manager()),
            matcher(m, ctx.get_trail_stack()) {
            matcher.set_max_iterations(ctx.get_fparams().m_ho_matching_bound);

            std::function<void(euf::ho_subst&)> on_match = [this](euf::ho_subst& subst) {
                save_matches(subst);
            };
            matcher.set_on_match(on_match);

            std::function<bool(expr*, expr*)> are_equal = [&ctx](expr* a, expr* b) {
                if (a == b)
                    return true;
                enode* na = ctx.find_enode(a);
                enode* nb = ctx.find_enode(b);
                return na && nb && na->get_root() == nb->get_root();
            };
            std::function<bool(expr*, expr*)> are_distinct = [this, &ctx](expr* a, expr* b) {
                if (m.are_distinct(a, b))
                    return true;
                enode* na = ctx.find_enode(a);
                enode* nb = ctx.find_enode(b);
                if (na && nb && ctx.is_diseq(na, nb))
                    return true;
                expr_ref eq(m.mk_eq(a, b), m);
                return ctx.find_assignment(eq) == l_false;
            };
            std::function<expr*(expr*)> root = [&ctx](expr* e) {
                enode* n = ctx.find_enode(e);
                return n ? n->get_root()->get_expr() : e;
            };
            std::function<expr*(expr*)> next = [&ctx](expr* e) {
                enode* n = ctx.find_enode(e);
                return n ? n->get_next()->get_expr() : e;
            };
            std::function<bool(expr*)> is_cgr_root = [&ctx](expr* e) {
                enode* n = ctx.find_enode(e);
                return !n || !n->uses_cg_table() || ctx.get_cg_root(n) == n;
            };
            std::function<void(expr*, ptr_vector<expr>&)> enum_terms = [this, &ctx](expr* pat, ptr_vector<expr>& result) {
                if (!terms)
                    return;
                func_decl* head = is_app(pat) ? to_app(pat)->get_decl() : nullptr;
                unsigned bound = ctx.get_fparams().m_ho_matching_bound;
                for (expr* term : terms->enum_terms(pat->get_sort())) {
                    if (!head || (is_app(term) && to_app(term)->get_decl() == head))
                        result.push_back(term);
                    if (result.size() >= bound)
                        break;
                }
            };
            matcher.set_are_equal(are_equal);
            matcher.set_are_distinct(are_distinct);
            matcher.set_root(root);
            matcher.set_next(next);
            matcher.set_is_cgr_root(is_cgr_root);
            matcher.set_enum_terms(enum_terms);
        }

        void init_terms(term_enumeration& te) {
            obj_hashtable<func_decl> seen;
            te.add_production(m.mk_true());
            te.add_production(m.mk_false());
            for (enode* n : ctx.enodes()) {
                if (!ctx.is_relevant(n))
                    continue;
                expr* e = n->get_expr();
                te.add_production(e);
                if (!is_app(e))
                    continue;
                func_decl* f = to_app(e)->get_decl();
                if (f->is_skolem() || seen.contains(f))
                    continue;
                seen.insert(f);
                te.add_production(f);
            }
        }

        void save_matches(euf::ho_subst& subst) {
            unsigned n = current_q->get_num_decls();
            unsigned_vector missing;
            ptr_vector<sort> sorts;
            for (unsigned i = 0; i < n; ++i) {
                if (subst.get(i))
                    continue;
                missing.push_back(i);
                sorts.push_back(current_q->get_decl_sort(n - i - 1));
            }

            if (missing.empty()) {
                matches.push_back(subst.get_binding(current_q));
                ++num_candidates;
                return;
            }
            if (!terms)
                return;

            unsigned bound = ctx.get_fparams().m_ho_matching_bound;
            for (expr_ref_vector const& tuple : terms->enum_tuples(sorts.size(), sorts.data())) {
                for (unsigned i = 0; i < missing.size(); ++i)
                    subst.set(missing[i], tuple.get(i));
                matches.push_back(subst.get_binding(current_q));
                for (unsigned i : missing)
                    subst.unset(i);
                ++num_candidates;
                if (matches.size() >= bound)
                    break;
            }
        }

        bool is_clause(quantifier* q, expr_ref_vector& literals) {
            if (!is_forall(q))
                return false;
            literals.reset();
            flatten_or(q->get_expr(), literals);
            auto& m = this->m;
            return all_of(literals, [&m](expr* lit) { return ::is_literal(m, lit); });
        }

        bool instantiate_matches() {
            bool found = false;
            for (expr_ref_vector const& binding : matches) {
                ptr_buffer<enode> nodes;
                unsigned generation = 0;
                bool valid = true;
                for (expr* e : binding) {
                    if (!e || has_free_vars(e)) {
                        valid = false;
                        break;
                    }
                    if (!ctx.e_internalized(e))
                        ctx.internalize(e, false);
                    enode* n = ctx.get_enode(e);
                    nodes.push_back(n);
                    generation = std::max(generation, ctx.get_generation(n));
                }
                if (valid && qm.add_instance(current_q, nodes.size(), nodes.data(), generation)) {
                    found = true;
                    ++num_instances;
                }
            }
            matches.reset();
            return found;
        }

        bool final_check() {
            if (!ctx.get_fparams().m_ho_matching)
                return false;

            scoped_ptr<term_enumeration> term_store;
            if (ctx.get_fparams().m_term_enumeration) {
                term_store = alloc(term_enumeration, m);
                init_terms(*term_store);
                terms = term_store.get();
            }

            bool found = false;
            expr_ref_vector literals(m);
            expr_ref_vector targets(m);
            for (quantifier* q : qm) {
                if (!ctx.is_relevant(q) || ctx.get_assignment(q) != l_true || !is_clause(q, literals))
                    continue;
                current_q = q;
                matches.reset();
                targets.reset();
                for (unsigned i = 0; i < literals.size(); ++i)
                    targets.push_back(m.mk_false());
                matcher(literals.size(), literals.data(), targets.data(), q->get_num_decls());
                found |= instantiate_matches();
            }
            current_q = nullptr;
            terms = nullptr;
            return found;
        }
    };

    ho_qsolver::ho_qsolver(context& ctx, quantifier_manager& qm) {
        m_imp = alloc(imp, ctx, qm);
    }

    ho_qsolver::~ho_qsolver() {
        dealloc(m_imp);
    }

    bool ho_qsolver::final_check() {
        return m_imp->final_check();
    }

    void ho_qsolver::collect_statistics(::statistics& st) const {
        st.update("ho qsolver candidates", m_imp->num_candidates);
        st.update("ho qsolver instances", m_imp->num_instances);
    }
}
