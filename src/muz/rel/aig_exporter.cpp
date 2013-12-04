/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    aig_exporter.cpp

Abstract:

    Export AIG files from horn clauses

--*/

#include "aig_exporter.h"
#include "dl_context.h"
#include <set>

namespace datalog {

    aig_exporter::aig_exporter(const rule_set& rules, context& ctx, const fact_vector *facts) :
        m_rules(rules), m_facts(facts), m(ctx.get_manager()), m_rm(ctx.get_rule_manager()),
        m_aigm(m), m_next_decl_id(1), m_next_aig_expr_id(2), m_num_and_gates(0),
        m_latch_vars(m), m_latch_varsp(m), m_ruleid_var_set(m), m_ruleid_varp_set(m)
    {
        std::set<func_decl*> predicates;
        for (rule_set::decl2rules::iterator I = m_rules.begin_grouped_rules(),
            E = m_rules.end_grouped_rules(); I != E; ++I) {
            predicates.insert(I->m_key);
        }

        for (fact_vector::const_iterator I = facts->begin(), E = facts->end(); I != E; ++I) {
            predicates.insert(I->first);
        }

        // reserve pred id = 0 for initalization purposes
        unsigned num_preds = (unsigned)predicates.size() + 1;

        // poor's man round-up log2
        unsigned preds_bitsize = log2(num_preds);
        if ((1U << preds_bitsize) < num_preds)
            ++preds_bitsize;
        SASSERT((1U << preds_bitsize) >= num_preds);

        for (unsigned i = 0; i < preds_bitsize; ++i) {
            m_ruleid_var_set.push_back(m.mk_fresh_const("rule_id", m.mk_bool_sort()));
            m_ruleid_varp_set.push_back(m.mk_fresh_const("rule_id_p", m.mk_bool_sort()));
        }
    }

    void aig_exporter::mk_latch_vars(unsigned n) {
        for (unsigned i = m_latch_vars.size(); i <= n; ++i) {
            m_latch_vars.push_back(m.mk_fresh_const("latch_var", m.mk_bool_sort()));
            m_latch_varsp.push_back(m.mk_fresh_const("latch_varp", m.mk_bool_sort()));
        }
        SASSERT(m_latch_vars.size() > n);
    }

    expr* aig_exporter::get_latch_var(unsigned i, const expr_ref_vector& vars) {
        mk_latch_vars(i);
        return vars.get(i);
    }

    void aig_exporter::assert_pred_id(func_decl *decl, const expr_ref_vector& vars, expr_ref_vector& exprs) {
        unsigned id = 0;
        if (decl && !m_decl_id_map.find(decl, id)) {
            id = m_next_decl_id++;
            SASSERT(id < (1U << vars.size()));
            m_decl_id_map.insert(decl, id);
        }

        for (unsigned i = 0; i < vars.size(); ++i) {
            exprs.push_back((id & (1U << i)) ? vars[i] : m.mk_not(vars[i]));
        }
    }

    void aig_exporter::collect_var_substs(substitution& subst, const app *h,
        const expr_ref_vector& vars, expr_ref_vector& eqs) {
        for (unsigned i = 0; i < h->get_num_args(); ++i) {
            expr *arg = h->get_arg(i);
            expr *latchvar = get_latch_var(i, vars);

            if (is_var(arg)) {
                var *v = to_var(arg);
                expr_offset othervar;
                if (subst.find(v, 0, othervar)) {
                    eqs.push_back(m.mk_eq(latchvar, othervar.get_expr()));
                } else {
                    subst.insert(v, 0, expr_offset(latchvar, 0));
                }
            } else {
                eqs.push_back(m.mk_eq(latchvar, arg));
            }
        }
    }

    void aig_exporter::operator()(std::ostream& out) {
        expr_ref_vector transition_function(m), output_preds(m);
        var_ref_vector input_vars(m);

        rule_counter& vc = m_rm.get_counter();
        expr_ref_vector exprs(m);
        substitution subst(m);

        for (rule_set::decl2rules::iterator I = m_rules.begin_grouped_rules(),
            E = m_rules.end_grouped_rules(); I != E; ++I) {
            for (rule_vector::iterator II = I->get_value()->begin(),
                EE = I->get_value()->end(); II != EE; ++II) {
                rule *r = *II;
                unsigned numqs = r->get_positive_tail_size();
                if (numqs > 1) {
                    std::cerr << "non-linear clauses not supported\n";
                    exit(-1);
                }

                if (numqs != r->get_uninterpreted_tail_size()) {
                    std::cerr << "negation of queries not supported\n";
                    exit(-1);
                }

                exprs.reset();
                assert_pred_id(numqs ? r->get_tail(0)->get_decl() : 0, m_ruleid_var_set, exprs);
                assert_pred_id(r->get_head()->get_decl(), m_ruleid_varp_set, exprs);

                subst.reset();
                subst.reserve(1, vc.get_max_rule_var(*r)+1);
                if (numqs)
                    collect_var_substs(subst, r->get_tail(0), m_latch_vars, exprs);
                collect_var_substs(subst, r->get_head(), m_latch_varsp, exprs);

                for (unsigned i = numqs; i < r->get_tail_size(); ++i) {
                    expr_ref e(m);
                    subst.apply(r->get_tail(i), e);
                    exprs.push_back(e);
                }

                transition_function.push_back(m.mk_and(exprs.size(), exprs.c_ptr()));
            }
        }

        // collect table facts
        if (m_facts) {
            for (fact_vector::const_iterator I = m_facts->begin(), E = m_facts->end(); I != E; ++I) {
                exprs.reset();
                assert_pred_id(0, m_ruleid_var_set, exprs);
                assert_pred_id(I->first, m_ruleid_varp_set, exprs);

                for (unsigned i = 0; i < I->second.size(); ++i) {
                    exprs.push_back(m.mk_eq(get_latch_var(i, m_latch_varsp), I->second[i]));
                }

                transition_function.push_back(m.mk_and(exprs.size(), exprs.c_ptr()));
            }
        }

        expr *tr = m.mk_or(transition_function.size(), transition_function.c_ptr());
        aig_ref aig = m_aigm.mk_aig(tr);
        expr_ref aig_expr(m);
        m_aigm.to_formula(aig, aig_expr);

#if 0
        std::cout << mk_pp(tr, m) << "\n\n";
        std::cout << mk_pp(aig_expr, m) << "\n\n";
#endif

        // make rule_id vars latches
        for (unsigned i = 0; i < m_ruleid_var_set.size(); ++i) {
            m_latch_vars.push_back(m_ruleid_var_set.get(i));
            m_latch_varsp.push_back(m_ruleid_varp_set.get(i));
        }

        // create vars for latches
        for (unsigned i = 0; i < m_latch_vars.size(); ++i) {
            mk_var(m_latch_vars.get(i));
            mk_input_var(m_latch_varsp.get(i));
        }

        unsigned tr_id = expr_to_aig(aig_expr);

        // create latch next state variables: (ite tr varp var)
        unsigned_vector latch_varp_ids;
        for (unsigned i = 0; i < m_latch_vars.size(); ++i) {
            unsigned in_val = mk_and(tr_id, get_var(m_latch_varsp.get(i)));
            unsigned latch_val = mk_and(neg(tr_id), get_var(m_latch_vars.get(i)));
            latch_varp_ids.push_back(mk_or(in_val, latch_val));
        }
        m_latch_varsp.reset();

        // create output variable (true iff an output predicate is derivable)
        unsigned output_id = 0;
        {
            expr_ref_vector output(m);
            const func_decl_set& preds = m_rules.get_output_predicates();

            for (func_decl_set::iterator I = preds.begin(), E = preds.end(); I != E; ++I) {
                exprs.reset();
                assert_pred_id(*I, m_ruleid_var_set, exprs);
                output.push_back(m.mk_and(exprs.size(), exprs.c_ptr()));
            }

            expr *out = m.mk_or(output.size(), output.c_ptr());
            aig = m_aigm.mk_aig(out);
            m_aigm.to_formula(aig, aig_expr);
            output_id = expr_to_aig(aig_expr);

#if 0
            std::cout << "output formula\n";
            std::cout << mk_pp(out, m) << "\n\n";
            std::cout << mk_pp(aig_expr, m) << "\n\n";
#endif
        }

        // 1) print header
        // aag var_index inputs latches outputs andgates
        out << "aag " << (m_next_aig_expr_id-1)/2 << ' ' << m_input_vars.size()
            << ' ' << m_latch_vars.size() << " 1 " << m_num_and_gates << '\n';

        // 2) print inputs
        for (unsigned i = 0; i < m_input_vars.size(); ++i) {
            out << m_input_vars[i] << '\n';
        }
        
        // 3) print latches
        for (unsigned i = 0; i < m_latch_vars.size(); ++i) {
            out << get_var(m_latch_vars.get(i)) << ' ' << latch_varp_ids[i] << '\n';
        }

        // 4) print outputs  (just one for now)
        out << output_id << '\n';

        // 5) print formula
        out << m_buffer.str();
    }

    unsigned aig_exporter::expr_to_aig(const expr *e) {
        unsigned id;
        if (m_aig_expr_id_map.find(e, id))
            return id;

        if (is_uninterp_const(e))
            return get_var(e);

        switch (e->get_kind()) {
        case AST_APP: {
            const app *a = to_app(e);
            switch (a->get_decl_kind()) {
            case OP_OR:
                SASSERT(a->get_num_args() > 0);
                id = expr_to_aig(a->get_arg(0));
                for (unsigned i = 1; i < a->get_num_args(); ++i) {
                    id = mk_or(id, expr_to_aig(a->get_arg(i)));
                }
                m_aig_expr_id_map.insert(e, id);
                return id;

            case OP_NOT:
                return neg(expr_to_aig(a->get_arg(0)));

            case OP_FALSE:
                return 0;

            case OP_TRUE:
                return 1;
            }
            break;}

        case AST_VAR:
            return get_var(e);
        default:
            UNREACHABLE();
        }
        
        UNREACHABLE();
        return 0;
    }

    unsigned aig_exporter::neg(unsigned id) const {
        return (id % 2) ? (id-1) : (id+1);
    }

    unsigned aig_exporter::mk_and(unsigned id1, unsigned id2) {
        if (id1 > id2)
            std::swap(id1, id2);

        std::pair<unsigned,unsigned> key(id1, id2);
        and_gates_map::const_iterator I = m_and_gates_map.find(key);
        if (I != m_and_gates_map.end())
            return I->second;

        unsigned id = mk_expr_id();
        m_buffer << id << ' ' << id1 << ' ' << id2 << '\n';
        m_and_gates_map[key] = id;
        ++m_num_and_gates;
        return id;
    }

    unsigned aig_exporter::mk_or(unsigned id1, unsigned id2) {
        return neg(mk_and(neg(id1), neg(id2)));
    }

    unsigned aig_exporter::get_var(const expr *e) {
        unsigned id;
        if (m_aig_expr_id_map.find(e, id))
            return id;
        return mk_input_var(e);
    }

    unsigned aig_exporter::mk_var(const expr *e) {
        SASSERT(!m_aig_expr_id_map.contains(e));
        unsigned id = mk_expr_id();
        m_aig_expr_id_map.insert(e, id);
        return id;
    }
    
    unsigned aig_exporter::mk_input_var(const expr *e) {
        SASSERT(!m_aig_expr_id_map.contains(e));
        unsigned id = mk_expr_id();
        m_input_vars.push_back(id);
        if (e)
            m_aig_expr_id_map.insert(e, id);
        return id;
    }

    unsigned aig_exporter::mk_expr_id() {
        unsigned id = m_next_aig_expr_id;
        m_next_aig_expr_id += 2;
        return id;
    }
}
