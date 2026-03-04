/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_model.cpp

Abstract:

    Implementation of nseq_model: model construction for the
    Nielsen-based string solver.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/nseq_model.h"
#include "smt/theory_nseq.h"
#include "smt/nseq_regex.h"
#include "smt/nseq_state.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/proto_model/proto_model.h"
#include "ast/ast_pp.h"

namespace smt {

    nseq_model::nseq_model(theory_nseq& th, ast_manager& m, seq_util& seq,
                           seq_rewriter& rw, euf::sgraph& sg, nseq_regex& regex)
        : m_th(th), m(m), m_seq(seq), m_rewriter(rw), m_sg(sg), m_regex(regex), m_trail(m)
    {}

    void nseq_model::init(model_generator& mg, seq::nielsen_graph& nielsen, nseq_state const& state) {
        m_var_values.reset();
        m_var_regex.reset();
        m_trail.reset();

        m_factory = alloc(seq_factory, m, m_th.get_family_id(), mg.get_model());
        mg.register_factory(m_factory);

        register_existing_values(nielsen);
        collect_var_regex_constraints(state);

        // extract variable assignments from the satisfying leaf's substitution path
        seq::nielsen_node const* sat = nielsen.sat_node();
        IF_VERBOSE(1, verbose_stream() << "nseq model init: sat_node=" << (sat ? "set" : "null")
            << " path_len=" << nielsen.sat_path().size() << "\n";);
        extract_assignments(nielsen.sat_path());
        IF_VERBOSE(1, verbose_stream() << "nseq model: m_var_values has " << m_var_values.size() << " entries\n";);
    }

    model_value_proc* nseq_model::mk_value(enode* n, model_generator& mg) {
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

    void nseq_model::finalize(model_generator& mg) {
        m_var_values.reset();
        m_var_regex.reset();
        m_trail.reset();
        m_factory = nullptr;
    }

    void nseq_model::extract_assignments(svector<seq::nielsen_edge*> const& sat_path) {
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

    expr_ref nseq_model::snode_to_value(euf::snode* n) {
        if (!n)
            return expr_ref(m);

        if (n->is_empty())
            return expr_ref(m_seq.str.mk_empty(m_seq.str.mk_string_sort()), m);

        if (n->is_char() || n->is_unit()) {
            expr* e = n->get_expr();
            return e ? expr_ref(e, m) : expr_ref(m);
        }

        if (n->is_var())
            return expr_ref(get_var_value(n), m);

        if (n->is_concat()) {
            expr_ref lhs = snode_to_value(n->arg(0));
            expr_ref rhs = snode_to_value(n->arg(1));
            if (lhs && rhs)
                return expr_ref(m_seq.str.mk_concat(lhs, rhs), m);
            if (lhs) return lhs;
            if (rhs) return rhs;
            return expr_ref(m);
        }

        // fallback: use the underlying expression
        expr* e = n->get_expr();
        return e ? expr_ref(e, m) : expr_ref(m);
    }

    expr_ref nseq_model::generate_regex_witness(euf::snode* regex, unsigned depth) {
        if (!regex)
            return expr_ref(m_seq.str.mk_empty(m_seq.str.mk_string_sort()), m);

        // depth bound to prevent stack overflow on deep regexes
        if (depth > 1000) {
            sort* srt = m_seq.str.mk_string_sort();
            expr* fresh = m_factory->get_fresh_value(srt);
            return fresh ? expr_ref(fresh, m) : expr_ref(m_seq.str.mk_empty(srt), m);
        }

        // nullable regex: empty string is a valid witness
        if (m_regex.is_nullable(regex))
            return expr_ref(m_seq.str.mk_empty(m_seq.str.mk_string_sort()), m);

        // collect first-position characters
        euf::snode_vector chars;
        m_regex.collect_first_chars(regex, chars);

        if (!chars.empty()) {
            // pick first concrete character, derive, and recurse
            euf::snode* c = chars[0];
            euf::snode* deriv = m_regex.derivative(regex, c);
            expr_ref tail = generate_regex_witness(deriv, depth + 1);
            if (tail && c->get_expr())
                return expr_ref(m_seq.str.mk_concat(c->get_expr(), tail), m);
        }

        // fallback: return fresh value from factory (may not satisfy the regex,
        // but avoids returning empty string which definitely doesn't satisfy non-nullable regex)
        sort* srt = m_seq.str.mk_string_sort();
        expr* fresh = m_factory->get_fresh_value(srt);
        return fresh ? expr_ref(fresh, m) : expr_ref(m_seq.str.mk_empty(srt), m);
    }

    void nseq_model::register_existing_values(seq::nielsen_graph& nielsen) {
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

    expr* nseq_model::get_var_value(euf::snode* var) {
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

    expr* nseq_model::mk_fresh_value(euf::snode* var) {
        // check if this variable has regex constraints
        euf::snode* re = nullptr;
        if (m_var_regex.find(var->id(), re) && re) {
            // generate a witness string satisfying the regex
            expr_ref witness = generate_regex_witness(re);
            if (witness) {
                m_trail.push_back(witness);
                m_factory->register_value(witness);
                return witness;
            }
        }

        // no regex constraint or witness generation failed: use empty string
        sort* srt = m_seq.str.mk_string_sort();
        if (var->get_expr())
            srt = var->get_expr()->get_sort();
        return m_seq.str.mk_empty(srt);
    }

    void nseq_model::collect_var_regex_constraints(nseq_state const& state) {
        for (auto const& mem : state.str_mems()) {
            if (!mem.m_str || !mem.m_regex)
                continue;
            // only collect for variable snodes (leaf variables needing assignment)
            if (!mem.m_str->is_var())
                continue;
            unsigned id = mem.m_str->id();
            euf::snode* existing = nullptr;
            if (m_var_regex.find(id, existing) && existing) {
                // intersect with existing constraint:
                // build re.inter(existing, new_regex)
                expr* e1 = existing->get_expr();
                expr* e2 = mem.m_regex->get_expr();
                if (e1 && e2) {
                    expr_ref inter(m_seq.re.mk_inter(e1, e2), m);
                    euf::snode* inter_sn = m_sg.mk(inter);
                    if (inter_sn)
                        m_var_regex.insert(id, inter_sn);
                }
            }
            else {
                m_var_regex.insert(id, mem.m_regex);
            }
        }
    }

    bool nseq_model::validate_regex(nseq_state const& state, ::proto_model& mdl) {
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
