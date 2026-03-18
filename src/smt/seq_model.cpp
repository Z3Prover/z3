/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_model.cpp

Abstract:

    Implementation of seq_model: model construction for the
    Nielsen-based string solver.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/seq_model.h"
#include "smt/seq/seq_state.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/proto_model/proto_model.h"
#include "ast/ast_pp.h"

namespace smt {

    seq_model::seq_model(ast_manager& m, seq_util& seq,
                           seq_rewriter& rw, euf::sgraph& sg)
        : m(m), m_seq(seq), m_rewriter(rw), m_sg(sg), m_trail(m)
    {}

    void seq_model::init(model_generator& mg, seq::nielsen_graph& nielsen) {
        m_var_values.reset();
        m_var_regex.reset();
        m_trail.reset();
        m_int_model = nullptr;
        m_mg = &mg;

        m_factory = alloc(seq_factory, m, m_seq.get_family_id(), mg.get_model());
        mg.register_factory(m_factory);

        register_existing_values(nielsen);
        seq::nielsen_node* sat_node = nielsen.sat_node();
        SASSERT(sat_node); // in case we report sat, this has to point to a satisfied Nielsen node!
        collect_var_regex_constraints(sat_node);

        // solve integer constraints from the sat_path FIRST so that
        // m_int_model is available when snode_to_value evaluates power exponents
        nielsen.solve_sat_path_ints(m_int_model);

        // extract variable assignments from the satisfying leaf's substitution path
        extract_assignments(nielsen.sat_path());
    }

    model_value_proc* seq_model::mk_value(enode* n, model_generator& mg) {
        app* e = n->get_expr();
        if (!m_seq.is_seq(e) && !m_seq.is_re(e) && !m_seq.str.is_nth_u(e))
            return nullptr;

        // For regex-sorted enodes, return the expression itself as a model value.
        // Regexes are interpreted as themselves in the model.
        if (m_seq.is_re(e)) {
            m_trail.push_back(e);
            return alloc(expr_wrapper_proc, e);
        }

        // For nth_u (underspecified nth), return a fresh value of the element sort.
        if (m_seq.str.is_nth_u(e)) {
            sort* srt = e->get_sort();
            expr* val = m_factory->get_fresh_value(srt);
            if (val) {
                m_trail.push_back(val);
                return alloc(expr_wrapper_proc, to_app(val));
            }
            return nullptr;
        }

        // look up snode for this expression
        euf::snode* sn = m_sg.find(e);
        IF_VERBOSE(2, {
            verbose_stream() << "nseq mk_value: expr=" << mk_bounded_pp(e, m, 2);
            if (sn) verbose_stream() << " snode[" << sn->id() << "] kind=" << (int)sn->kind();
            else verbose_stream() << " snode=null";
            verbose_stream() << "\n";
        });
        expr_ref val(m);
        if (sn)
            val = snode_to_value(sn);

        if (!val) {
            // no assignment found — default to empty string
            val = m_seq.str.mk_empty(e->get_sort());
        }

        if (val) {
            m_trail.push_back(val);
            m_factory->add_trail(val);
            return alloc(expr_wrapper_proc, to_app(val));
        }

        return alloc(expr_wrapper_proc, to_app(m_seq.str.mk_empty(e->get_sort())));
    }

    void seq_model::finalize(model_generator& mg) {
        m_var_values.reset();
        m_var_regex.reset();
        m_trail.reset();
        m_int_model = nullptr;
        m_mg = nullptr;
        m_factory = nullptr;
    }

    void seq_model::extract_assignments(svector<seq::nielsen_edge*> const& sat_path) {
        IF_VERBOSE(1, verbose_stream() << "nseq extract_assignments: path length=" << sat_path.size() << "\n";);

        // compose substitutions root-to-leaf.
        // bindings[i] = (var_snode, current_value_snode).
        // When a new substitution (s.m_var -> s.m_replacement) is applied,
        // substitute s.m_var in all existing values, then record the new binding.
        vector<std::pair<euf::snode*, euf::snode*>> bindings;
        for (seq::nielsen_edge* e : sat_path) {
            for (seq::nielsen_subst const& s : e->subst()) {
                if (!s.m_var) continue;
                IF_VERBOSE(1, {
                    verbose_stream() << "  subst: snode[" << s.m_var->id() << "]";
                    if (s.m_var->get_expr()) verbose_stream() << "=" << mk_bounded_pp(s.m_var->get_expr(), m, 2);
                    verbose_stream() << " -> snode[" << (s.m_replacement ? (int)s.m_replacement->id() : -1) << "]";
                    if (s.m_replacement && s.m_replacement->get_expr()) verbose_stream() << "=" << mk_bounded_pp(s.m_replacement->get_expr(), m, 2);
                    verbose_stream() << "\n";
                });
                for (auto& b : bindings)
                    b.second = m_sg.subst(b.second, s.m_var, s.m_replacement);
                bindings.push_back({s.m_var, s.m_replacement});
            }
        }

        IF_VERBOSE(1, verbose_stream() << "nseq extract_assignments: " << bindings.size() << " bindings\n";);
        for (auto const& b : bindings) {
            unsigned id = b.first->id();
            if (m_var_values.contains(id))
                continue;
            expr_ref val = snode_to_value(b.second);
            IF_VERBOSE(1, {
                verbose_stream() << "  var snode[" << id << "]";
                if (b.first->get_expr()) verbose_stream() << "=" << mk_bounded_pp(b.first->get_expr(), m, 2);
                verbose_stream() << " -> ";
                if (val) verbose_stream() << mk_bounded_pp(val, m, 3); else verbose_stream() << "(null)";
                verbose_stream() << "\n";
            });
            if (val) {
                m_trail.push_back(val);
                m_var_values.insert(id, val);
            }
        }
    }

    expr_ref seq_model::snode_to_value(euf::snode* n) {
        if (!n)
            return expr_ref(m);

        if (n->is_empty()) {
            sort* srt = n->get_sort();
            if (!srt)
                srt = m_seq.str.mk_string_sort();
            return expr_ref(m_seq.str.mk_empty(srt), m);
        }

        if (n->is_char() || n->is_unit()) {
            expr* e = n->get_expr();
            return e ? expr_ref(e, m) : expr_ref(m);
        }

        if (n->is_var())
            return expr_ref(get_var_value(n), m);

        if (n->is_concat()) {
            SASSERT(n->get_sort() && m_seq.is_seq(n->get_sort()));
            expr_ref lhs = snode_to_value(n->arg(0));
            expr_ref rhs = snode_to_value(n->arg(1));
            if (lhs && rhs)
                return expr_ref(m_seq.str.mk_concat(lhs, rhs), m);
            if (lhs)
                return lhs;
            if (rhs)
                return rhs;
            return expr_ref(m);
        }

        if (n->is_power()) {
            SASSERT(n->num_args() == 2);
            // Evaluate the base and exponent to produce a concrete string.
            // The base is a string snode; the exponent is an integer expression
            // whose value comes from the sat_path integer model.
            expr_ref base_val = snode_to_value(n->arg(0));
            if (!base_val)
                return expr_ref(m);

            euf::snode* exp_snode = n->arg(1);
            expr* exp_expr = exp_snode ? exp_snode->get_expr() : nullptr;
            rational exp_val;
            arith_util arith(m);

            // Try to evaluate exponent: first check if it's a numeral,
            // then try the int model from sat_path constraints,
            // finally fall back to the proto_model from model_generator.
            if (exp_expr && arith.is_numeral(exp_expr, exp_val)) {
                // already concrete
            }
            else if (exp_expr && m_int_model.get()) {
                expr_ref result(m);
                if (m_int_model->eval_expr(exp_expr, result, true) && arith.is_numeral(result, exp_val)) {
                    // evaluated from int model
                }
                else if (m_mg) {
                    proto_model& pm = m_mg->get_model();
                    if (pm.eval(exp_expr, result, true) && arith.is_numeral(result, exp_val)) {
                        // evaluated from proto_model
                    }
                    else
                        exp_val = rational(0);
                }
                else
                    exp_val = rational(0);
            }
            else if (exp_expr && m_mg) {
                expr_ref result(m);
                proto_model& pm = m_mg->get_model();
                if (pm.eval(exp_expr, result, true) && arith.is_numeral(result, exp_val)) {
                    // evaluated from proto_model
                }
                else
                    exp_val = rational(0);
            }
            else
                exp_val = rational(0);

            if (exp_val.is_neg())
                exp_val = rational(0);

            // Build the repeated string: base^exp_val
            if (exp_val.is_zero()) {
                sort* srt = n->get_sort();
                SASSERT(srt);
                if (!srt) srt = m_seq.str.mk_string_sort();
                return expr_ref(m_seq.str.mk_empty(srt), m);
            }
            if (exp_val.is_one())
                return base_val;

            // For small exponents, concatenate directly; for large ones,
            // return mk_power to avoid enormous AST chains.
            unsigned n_val = exp_val.get_unsigned();
            constexpr unsigned POWER_EXPAND_LIMIT = 1000;
            if (n_val > POWER_EXPAND_LIMIT)
                return expr_ref(m_seq.str.mk_power(base_val, arith.mk_int(n_val)), m);
            expr_ref acc(base_val);
            for (unsigned i = 1; i < n_val; ++i)
                acc = m_seq.str.mk_concat(acc, base_val);
            return acc;
        }

        // fallback: use the underlying expression
        expr* e = n->get_expr();
        return e ? expr_ref(e, m) : expr_ref(m);
    }

    void seq_model::register_existing_values(seq::nielsen_graph& nielsen) {
        seq::nielsen_node const* root = nielsen.root();
        if (!root)
            return;
        for (auto const& eq : root->str_eqs()) {
            if (eq.m_lhs && eq.m_lhs->get_expr())
                m_factory->register_value(eq.m_lhs->get_expr());
            if (eq.m_rhs && eq.m_rhs->get_expr())
                m_factory->register_value(eq.m_rhs->get_expr());
        }
    }

    expr* seq_model::get_var_value(euf::snode* var) {
        expr* val = nullptr;
        if (m_var_values.find(var->id(), val))
            return val;

        // unconstrained or regex-constrained: delegate to mk_fresh_value
        val = mk_fresh_value(var);
        if (val) {
            m_trail.push_back(val);
            m_var_values.insert(var->id(), val);
        }
        return val;
    }

    expr* seq_model::mk_fresh_value(euf::snode* var) {
        // check if this variable has regex constraints
        euf::snode* re = nullptr;
        if (m_var_regex.find(var->id(), re) && re) {
            expr* re_expr = re->get_expr();
            SASSERT(re_expr);
            expr_ref witness(m);
            // We checked non-emptiness during Nielsen already
            VERIFY(m_rewriter.some_seq_in_re(re_expr, witness) == l_true && witness);
            // std::cout << "Witness for " << mk_pp(var->get_expr(), m) << " in " <<
            //     mk_pp(re_expr, m) << ": " << mk_pp(witness, m) << std::endl;
            m_trail.push_back(witness);
            m_factory->register_value(witness);
            return witness;
        }

        // no regex constraint or witness generation failed: use empty string
        sort* srt = m_seq.str.mk_string_sort();
        if (var->get_expr())
            srt = var->get_expr()->get_sort();
        return m_seq.str.mk_empty(srt);
    }

    void seq_model::collect_var_regex_constraints(seq::nielsen_node const* sat_node) {
        SASSERT(sat_node);
        for (auto const& mem : sat_node->str_mems()) {
            SASSERT(mem.m_str && mem.m_regex);
            VERIFY(mem.is_primitive()); // everything else should have been eliminated already
            euf::snode* first = mem.m_str->first();
            unsigned id = first->id();
            euf::snode* existing = nullptr;
            if (m_var_regex.find(id, existing) && existing) {
                // intersect with existing constraint:
                // build re.inter(existing, new_regex)
                expr* e1 = existing->get_expr();
                expr* e2 = mem.m_regex->get_expr();
                if (e1 && e2) {
                    expr_ref inter(m_seq.re.mk_inter(e1, e2), m);
                    euf::snode* inter_sn = m_sg.mk(inter);
                    SASSERT(inter_sn);
                    m_var_regex.insert(id, inter_sn);
                }
            }
            else
                m_var_regex.insert(id, mem.m_regex);
        }
    }

    bool seq_model::validate_regex(seq_state const& state, ::proto_model& mdl) {
        bool ok = true;

        // validate positive memberships: str ∈ regex
        for (auto const& mem : state.str_mems()) {
            if (!mem.m_str || !mem.m_regex)
                continue;
            expr* s_expr = mem.m_str->get_expr();
            expr* r_expr = mem.m_regex->get_expr();
            if (!s_expr || !r_expr)
                continue;

            expr_ref in_re(m_seq.re.mk_in_re(s_expr, r_expr), m);
            if (mdl.is_false(in_re)) {
                IF_VERBOSE(0, verbose_stream() << "nseq model: positive membership violated: "
                           << mk_bounded_pp(s_expr, m, 3)
                           << " in " << mk_bounded_pp(r_expr, m, 3) << "\n";);
                ok = false;
            }
        }

        return ok;
    }

}
