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
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/proto_model/proto_model.h"
#include "ast/ast_pp.h"

namespace smt {

    static enode* find_root_enode(context& ctx, expr* e) {
        if (!e)
            return nullptr;
        enode* n = ctx.find_enode(e);
        return n ? n->get_root() : nullptr;
    }

    static bool is_model_dependency(context& ctx, enode* n) {
        if (!n)
            return false;
        seq_util seq(ctx.get_manager());
        if (seq.is_seq(n->get_sort()) || seq.is_re(n->get_sort()))
            return false;
        return ctx.is_relevant(n) || ctx.get_manager().is_value(n->get_expr());
    }

    static void collect_expr_dependencies(context& ctx, expr* e, obj_hashtable<enode>& seen, ptr_vector<enode>& deps) {
        if (!e)
            return;
        ptr_vector<expr> todo;
        obj_hashtable<expr> seen_expr;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* cur = todo.back();
            todo.pop_back();
            if (seen_expr.contains(cur))
                continue;
            seen_expr.insert(cur);

            enode* dep = find_root_enode(ctx, cur);
            if (is_model_dependency(ctx, dep) && !seen.contains(dep)) {
                    seen.insert(dep);
                    deps.push_back(dep);
            }

            if (!is_app(cur))
                continue;
            for (expr* arg : *to_app(cur))
                todo.push_back(arg);
        }
    }

    static expr_ref substitute_dependency_values(ast_manager& m, context& ctx, expr* e, obj_map<enode, expr*> const& dep_values) {
        if (!e)
            return expr_ref(m);

        expr* cur = e;
        {
            expr* dval = nullptr;
            enode* dep = find_root_enode(ctx, e);
            if (dep && dep_values.find(dep, dval) && dval) {
                if (m.is_value(dval))
                    return expr_ref(dval, m);
                cur = dval;
            }
        }

        if (!is_app(cur))
            return expr_ref(cur, m);

        app* a = to_app(cur);
        expr_ref_vector args(m);
        bool changed = false;
        for (expr* arg : *a) {
            expr_ref new_arg = substitute_dependency_values(m, ctx, arg, dep_values);
            changed = changed || (new_arg != arg);
            args.push_back(new_arg);
        }
        if (!changed)
            return expr_ref(cur, m);
        return expr_ref(m.mk_app(a->get_decl(), args.size(), args.data()), m);
    }

    class seq_snode_value_proc : public model_value_proc {
        seq_model& m_owner;
        enode* m_node;
        euf::snode* m_snode;
        ptr_vector<enode> m_dependencies;

    public:
        seq_snode_value_proc(seq_model& owner, enode* node, euf::snode* snode)
            : m_owner(owner), m_node(node), m_snode(snode) {
            obj_hashtable<enode> seen;
            if (m_node)
                seen.insert(m_node->get_root());
            m_owner.collect_dependencies(m_snode, seen, m_dependencies);
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            for (enode* d : m_dependencies)
                result.push_back(model_value_dependency(d));
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            SASSERT(values.size() == m_dependencies.size());
            obj_map<enode, expr*> dep_values;
            for (unsigned i = 0; i < m_dependencies.size(); ++i)
                dep_values.insert(m_dependencies[i]->get_root(), values[i]);

            expr_ref val = m_owner.snode_to_value(m_snode, mg, &dep_values);
            if (!val)
                val = m_owner.snode_to_value(m_snode, mg);
            if (!val)
                val = m_owner.m_seq.str.mk_empty(m_node->get_expr()->get_sort());

            m_owner.m_trail.push_back(val);
            m_owner.m_factory->add_trail(val);
            TRACE(seq, tout << "nseq seq_snode_value_proc: " << mk_pp(m_node->get_expr(), m_owner.m) << " -> " << mk_pp(val, m_owner.m) << "\n";);
            return to_app(val);
        }
    };

    seq_model::seq_model(ast_manager& m, context& ctx, seq_util& seq,
                           seq_rewriter& rw, euf::sgraph& sg)
        : m(m), m_ctx(ctx), m_seq(seq), m_rewriter(rw), m_sg(sg), m_trail(m)
    {}

    void seq_model::init(model_generator& mg, seq::nielsen_graph& nielsen) {

        TRACE(seq, nielsen.display(tout << nielsen.to_dot() << "\n"));
        m_var_values.reset();
        m_var_regex.reset();
        m_trail.reset();
        m_mg = &mg;

        m_factory = alloc(seq_factory, m, m_seq.get_family_id(), mg.get_model());
        mg.register_factory(m_factory);

        register_existing_values(nielsen);
        seq::nielsen_node* sat_node = nielsen.sat_node();
        SASSERT(sat_node); // in case we report sat, this has to point to a satisfied Nielsen node!
        collect_var_regex_constraints(sat_node);

        // solve integer constraints from the sat_path FIRST so that
        // m_int_model is available when snode_to_value evaluates power exponents
        // VERIFY(nielsen.solve_sat_path_raw(m_int_model));

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
            return alloc(seq_snode_value_proc, *this, n, sn);

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
        m_mg = nullptr;
        m_factory = nullptr;
    }

    void seq_model::extract_assignments(ptr_vector<seq::nielsen_edge> const& sat_path) {
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
            SASSERT(b.first);
            unsigned id = b.first->first()->id();
            if (m_var_values.contains(id))
                continue;
            expr_ref val = snode_to_value(b.second, *m_mg);
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

    expr_ref seq_model::snode_to_value(euf::snode* n, model_generator& mg) {
        return snode_to_value(n, mg, nullptr);
    }

    expr_ref seq_model::snode_to_value(euf::snode* n, model_generator& mg, obj_map<enode, expr*> const* dep_values) {
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
            SASSERT(m_seq.str.is_unit(e));
            e = to_app(e)->get_arg(0);

            unsigned c;
            if (dep_values && e) {
                expr* dval = nullptr;
                enode* dep = find_root_enode(m_ctx, e);
                if (dep && dep_values->find(dep, dval) && dval && m_seq.is_const_char(dval, c))
                    return expr_ref(m_seq.str.mk_string(zstring(c)), m);
            }

            if (dep_values && e && m_mg) {
                expr_ref e_sub = substitute_dependency_values(m, m_ctx, e, *dep_values);
                expr_ref val_sub(m);
                if (m_mg->get_model().eval(e_sub, val_sub, true) && val_sub && m_seq.is_const_char(val_sub, c))
                    return expr_ref(m_seq.str.mk_string(zstring(c)), m);
            }

            expr_ref val(m);
            if (e && m_mg && m_mg->get_model().eval(e, val, true)) {
                if (val && m_seq.is_const_char(val, c))
                    return expr_ref(m_seq.str.mk_string(zstring(c)), m);
            }

            if (e && m_seq.is_char(e)) {
                return expr_ref(m_seq.str.mk_string("0"), m);
            }

            if (m_mg && e) {
                expr* some = m_mg->get_model().get_some_value(e->get_sort());
                if (some)
                    return expr_ref(m_seq.str.mk_unit(some), m);
            }
            return expr_ref(m_seq.str.mk_unit(e), m);
        }

        if (n->is_var())
            return expr_ref(get_var_value(n, dep_values), m);

        if (n->is_concat()) {
            SASSERT(n->get_sort() && m_seq.is_seq(n->get_sort()));
            expr_ref lhs = snode_to_value(n->arg(0), mg, dep_values);
            expr_ref rhs = snode_to_value(n->arg(1), mg, dep_values);
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
            expr_ref base_val = snode_to_value(n->arg(0), mg, dep_values);
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
            else if (dep_values && exp_expr) {
                expr* dval = nullptr;
                enode* dep = find_root_enode(m_ctx, exp_expr);
                if (dep && dep_values->find(dep, dval) && dval && arith.is_numeral(dval, exp_val)) {
                    // evaluated from dependency values
                }
                else if (m_mg) {
                    expr_ref sub_exp = substitute_dependency_values(m, m_ctx, exp_expr, *dep_values);
                    expr_ref result(m);
                    if (!(m_mg->get_model().eval(sub_exp, result, true) && arith.is_numeral(result, exp_val)))
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

    void seq_model::collect_dependencies(euf::snode* n, obj_hashtable<enode>& seen, ptr_vector<enode>& deps) const {
        if (!n)
            return;

        if (n->is_var()) {
            expr* e = n->get_expr();
            if (e && m_seq.is_seq(e)) {
                expr_ref len_expr(m_seq.str.mk_length(e), m);
                collect_expr_dependencies(m_ctx, len_expr, seen, deps);
            }
            return;
        }

        if (n->is_char() || n->is_unit()) {
            expr* e = n->get_expr();
            if (e && m_seq.str.is_unit(e)) {
                expr* ch = to_app(e)->get_arg(0);
                collect_expr_dependencies(m_ctx, ch, seen, deps);
            }
            return;
        }

        if (n->is_concat()) {
            collect_dependencies(n->arg(0), seen, deps);
            collect_dependencies(n->arg(1), seen, deps);
            return;
        }

        if (n->is_power()) {
            collect_dependencies(n->arg(0), seen, deps);
            if (n->num_args() == 2) {
                euf::snode* exp_snode = n->arg(1);
                expr* exp_expr = exp_snode ? exp_snode->get_expr() : nullptr;
                rational exp_val;
                arith_util arith(m);
                if (exp_expr && !arith.is_numeral(exp_expr, exp_val))
                    collect_expr_dependencies(m_ctx, exp_expr, seen, deps);
            }
        }
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

    expr* seq_model::get_var_value(euf::snode* var, obj_map<enode, expr*> const* dep_values) {
        SASSERT(var);
        unsigned key = var->first()->id();
        expr* val = nullptr;
        if (m_var_values.find(key, val))
            return val;

        // unconstrained or regex-constrained: delegate to mk_fresh_value
        val = mk_fresh_value(var, dep_values);
        if (val) {
            m_trail.push_back(val);
            m_var_values.insert(key, val);
        }
        return val;
    }

    expr* seq_model::mk_fresh_value(euf::snode* var, obj_map<enode, expr*> const* dep_values) {
        SASSERT(var->get_expr());
        if (!m_seq.is_seq(var->get_expr()))
            return nullptr;
        auto  srt = var->get_expr()->get_sort();

        // check if this variable has regex constraints
        euf::snode* re = nullptr;
        unsigned key = var->first()->id();
        if (m_var_regex.find(key, re) && re) {
            expr* re_expr = re->get_expr();
            SASSERT(re_expr);
            expr_ref witness(m);
            // We checked non-emptiness during Nielsen already
            lbool wr = m_rewriter.some_seq_in_re(re_expr, witness);
            if (wr == l_true && witness) {
                m_trail.push_back(witness);
                m_factory->register_value(witness);
                return witness;
            }
            IF_VERBOSE(1, verbose_stream() << "witness extraction failed: " << wr << "\n" << mk_pp(re_expr, m) << "\n");
            UNREACHABLE();
        }

        // No regex constraint: try to respect the assigned length for the variable.
        // This prevents invalid models such as len(x)=1 with x="".
        arith_util arith(m);
        expr_ref len_expr(m_seq.str.mk_length(var->get_expr()), m);
        rational len_val;
        bool has_len = false;

        if (dep_values) {
            expr* dval = nullptr;
            enode* dep = find_root_enode(m_ctx, len_expr);
            if (dep && dep_values->find(dep, dval) && dval && arith.is_numeral(dval, len_val))
                has_len = true;
        }

        if (!has_len && m_mg) {
            expr_ref eval_len(m);
            if (m_mg->get_model().eval(len_expr, eval_len, true) && arith.is_numeral(eval_len, len_val))
                has_len = true;
        }

        if (has_len) {
            if (!len_val.is_int() || len_val.is_neg())
                len_val = rational(0);
            if (len_val.is_zero())
                return m_seq.str.mk_empty(srt);

            constexpr unsigned MAX_CONCRETE_WITNESS = 1024;
            if (len_val.is_unsigned() && len_val.get_unsigned() <= MAX_CONCRETE_WITNESS) {
                unsigned n = len_val.get_unsigned();
                zstring w;
                for (unsigned i = 0; i < n; ++i)
                    w += zstring('0');
                expr* witness = m_seq.str.mk_string(w);
                m_factory->register_value(witness);
                return witness;
            }

            expr* base = m_seq.str.mk_string("0");
            expr* witness = m_seq.str.mk_power(base, arith.mk_int(len_val));
            m_factory->register_value(witness);
            return witness;
        }

        // no regex constraint or witness generation failed: use empty string
        return m_seq.str.mk_empty(srt);
    }

    void seq_model::collect_var_regex_constraints(seq::nielsen_node const* sat_node) {
        SASSERT(sat_node);
        for (auto const& mem : sat_node->str_mems()) {
            SASSERT(mem.m_str && mem.m_regex);
            if (mem.is_trivial())
                continue; // empty string in nullable regex: already satisfied, no variable to constrain
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

    bool seq_model::validate_regex(tracked_str_mem const& mem, ::proto_model& mdl) {
        if (!mem.m_str || !mem.m_regex)
            return true;
        expr* s_expr = mem.m_str->get_expr();
        expr* r_expr = mem.m_regex->get_expr();
        if (!s_expr || !r_expr)
            return true;

        expr_ref in_re(m_seq.re.mk_in_re(s_expr, r_expr), m);
        if (mdl.is_false(in_re)) {
            IF_VERBOSE(0, verbose_stream() << "nseq model: positive membership violated: "
                       << mk_bounded_pp(s_expr, m, 3)
                       << " in " << mk_bounded_pp(r_expr, m, 3) << "\n";);
            return false;
        }
        return true;
    }

}
