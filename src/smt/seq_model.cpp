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

Notes:

We end up with a set of substitutions and membership constraints
x -> rx
y -> ry
z in R_z
u in R_u

Plan:
Compute solutions for variables in rx, ry store them in m_var_values
We can compute these solutions on demand.
When evaluating x, use dependencies from rx. 
This can include character variables that are assigned values by other theories.
Reconstruct value for x using value for rx.


Model construction in z3 is designed to be hierarchical.
During model initialization solvers register depenendencies between enodes for model construction.
The dependencies should be acyclic to enable bottom-up model construction.
Values for dependencies are accessed in the model_value_proc class.
For strings/sequences we have a natural way to record dependencies.
unit/character nodes depend on the elements they contain.

--*/
#include "smt/seq_model.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_arith_value.h"
#include "smt/proto_model/proto_model.h"
#include "ast/ast_pp.h"

namespace smt {

    class seq_snode_value_proc : public model_value_proc {
        seq_model& m_owner;
        enode* m_node;
        euf::snode const* m_snode;
        enode_vector m_dependencies;

    public:
        seq_snode_value_proc(seq_model& owner, enode* node, euf::snode const* snode)
            : m_owner(owner), m_node(node), m_snode(snode) {
            m_owner.collect_dependencies(m_snode, m_dependencies);
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            for (enode* d : m_dependencies)
                result.push_back(model_value_dependency(d));
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            SASSERT(values.size() == m_dependencies.size());

            expr_ref val = m_owner.snode_to_value(m_snode, m_dependencies, values);
            if (!val)
                val = m_owner.m_seq.str.mk_empty(m_node->get_expr()->get_sort());

            m_owner.m_trail.push_back(val);
            m_owner.m_factory->add_trail(val);
            TRACE(seq, tout << "nseq seq_snode_value_proc: " << mk_pp(m_node->get_expr(), m_owner.m) << " -> " << mk_pp(val, m_owner.m) << "\n";);
            return to_app(val);
        }
    };

    // Stable key for a variable snode. The sgraph may hold several distinct
    // snode objects for the same hash-consed expression (e.g. one created at
    // internalization and one re-created during the Nielsen search), so snode
    // ids are NOT a reliable key. Expressions are perfectly shared, so their
    // id is stable across all snodes that denote the same term.
    static unsigned var_key(euf::snode const* n) {
        return n->first()->get_expr()->get_id();
    }

    seq_model::seq_model(ast_manager& m, context& ctx, seq_util& seq,
                           seq_rewriter& rw, euf::sgraph& sg)
        : m(m), m_ctx(ctx), m_seq(seq), m_rewriter(rw), m_sg(sg), m_trail(m)
    {}

    void seq_model::init(model_generator& mg, seq::nielsen_graph& nielsen) {

        TRACE(seq, nielsen.display(tout << nielsen.to_dot() << "\n"));
        m_var_values.reset();
        m_var_replacement.reset();
        m_var_regex.reset();
        m_view_vars.reset();
        m_trail.reset();

        m_factory = alloc(seq_factory, m, m_seq.get_family_id(), mg.get_model());
        mg.register_factory(m_factory);

        seq::nielsen_node* sat_node = nielsen.sat_node();
        SASSERT(sat_node); // in case we report sat, this has to point to a satisfied Nielsen node!
        m_nielsen = &nielsen;
        m_sat_node = sat_node;
        collect_var_regex_constraints(sat_node);


        // solve integer constraints from the sat_path FIRST so that
        // m_int_model is available when snode_to_value evaluates power exponents
        // VERIFY(nielsen.solve_sat_path_raw(m_int_model));

        // extract variable assignments from the satisfying leaf's substitution path
        extract_assignments(nielsen.sat_path());
        
    }

    model_value_proc* seq_model::mk_value(enode* n, model_generator& mg) {
        expr* e = n->get_expr();

        if (!m_seq.is_seq(e) && !m_seq.is_re(e) && !m_seq.str.is_nth_u(e))
            return nullptr;

        // For regex-sorted enodes, return the expression itself as a model value.
        // Regexes are interpreted as themselves in the model.
        if (m_seq.is_re(e)) {
            m_trail.push_back(e);
            return alloc(expr_wrapper_proc, to_app(e));
        }

        // For nth_u (underspecified nth): the Nielsen character-peel /
        // regex-if-split records the chosen character as a relevant
        // equality literal (e.g. (= (seq.nth_u x 0) (_ Char 65))), so the
        // enode's equivalence class contains the required character
        // constant. Use it; only fall back to a fresh value when the
        // peeled character is genuinely unconstrained.
        if (m_seq.str.is_nth_u(e)) {
            sort *srt = e->get_sort();
            expr* val = nullptr;
            enode* it = n;
            do {
                if (m.is_value(it->get_expr())) {
                    val = it->get_expr();
                    break;
                }
                it = it->get_next();
            }
            while (it != n);
            if (!val)
                val = m_factory->get_fresh_value(srt);
            if (val) {
                m_trail.push_back(val);
                return alloc(expr_wrapper_proc, to_app(val));
            }
            return nullptr;
        }

        // look up snode for this expression
        euf::snode const* sn = m_sg.find(e);
        IF_VERBOSE(2, {
            verbose_stream() << "nseq mk_value: expr=" << mk_bounded_pp(e, m, 2);
            if (sn) verbose_stream() << " snode[" << sn->id() << "] kind=" << (int)sn->kind();
            else verbose_stream() << " snode=null";
            verbose_stream() << "\n";
        });
        if (sn)
            return alloc(seq_snode_value_proc, *this, n, sn);

        expr_ref val(m);
        if (m_seq.is_seq(e))
            // no assignment found — default to empty string
            val = m_seq.str.mk_empty(e->get_sort());
        else
            val = e;

        m_trail.push_back(val);
        m_factory->add_trail(val);
        return alloc(expr_wrapper_proc, to_app(val));
    }

    void seq_model::finalize(model_generator& mg) {
        m_var_values.reset();
        m_var_regex.reset();
        m_var_replacement.reset();
        m_trail.reset();
        m_factory = nullptr;
    }

    void seq_model::extract_assignments(ptr_vector<seq::nielsen_edge> const& sat_path) {
        IF_VERBOSE(1, verbose_stream() << "nseq extract_assignments: path length=" << sat_path.size() << "\n";);

        // compose substitutions root-to-leaf.
        // bindings[i] = (var_snode, current_value_snode).
        // When a new substitution (s.m_var -> s.m_replacement) is applied,
        // substitute s.m_var in all existing values, then record the new binding.

        vector<std::pair<euf::snode const*, euf::snode const*>> bindings;
        for (seq::nielsen_edge* e : sat_path) {
            for (seq::nielsen_subst const& s : e->subst()) {
                SASSERT(s.m_var);
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
        for (auto const &[var, replacement] : bindings) {
            SASSERT(var);
            // Key by expression id, not snode id: the sgraph may hold two distinct
            // snode objects for the same (hash-consed) expression, so snode ids are
            // not a stable key across the substitution trees we traverse here.
            unsigned id = var_key(var);
            SASSERT(!m_var_replacement.contains(id));
            m_var_replacement.insert(id, replacement);
        }
    }
    
    void seq_model::collect_dependencies(euf::snode const* n, enode_vector &deps) const {
        uint_set seen;
        buffer<euf::snode const*> todo;
        todo.push_back(n);
        while (!todo.empty()) {
            auto curr = todo.back();
            todo.pop_back();
            if (seen.contains(curr->id()))
                continue;
            seen.insert(curr->id());
            if (m.is_value(curr->get_expr()))
                ;
            else if (curr->is_empty())
                ;
            else if (curr->is_char_or_unit()) {
                expr *e = curr->arg(0)->get_expr();
                if (m_ctx.e_internalized(e))
                    deps.push_back(m_ctx.get_enode(e));
            }
            else if (curr->is_concat()) {
                for (unsigned i = 0; i < curr->num_args(); ++i)
                    todo.push_back(curr->arg(i));
            }
            else if (curr->is_power()) {
                // pretend there are no dependencies
                // TODO - may not be sufficient if the exponent is a variable with a binding that contains dependencies
            }
            else if (curr->is_var()) {
                // we could have a binding n |-> replacement
                // we want to collect all elements in replacement as dependencies
                // when using the dependencies to build a value for n we should
                // map the values that are passed in to the sub-terms that are listed as dependencies.
                // sub-terms are under concat, power and unit
                euf::snode const* replacement = nullptr;
                if (m_var_replacement.find(var_key(curr), replacement))
                    todo.push_back(replacement);
            }
            else {
                IF_VERBOSE(0, {
                    verbose_stream() << "nseq collect_dependencies_rec: unhandled snode kind " << (int)curr->kind()
                                     << "\n";
                    verbose_stream() << "  curr: snode[" << curr->id() << "]";
                    if (curr->get_expr())
                        verbose_stream() << " expr=" << mk_bounded_pp(curr->get_expr(), m, 2);
                    verbose_stream() << "\n";
                });
                UNREACHABLE();
            }
        }
        // verbose_stream() << "collect " << mk_pp(n->get_expr(), m) << " " << deps.size() << "\n";
    }
   
    expr_ref seq_model::snode_to_value(euf::snode const* n, enode_vector const &deps, expr_ref_vector const &values) {
        // var2value: leaf deps keyed by expression ID (populated from `deps`/`values`).
        // node2value: computed nodes keyed by (snode_id * 2 + is_recursive).
        // The recursion flag is part of the key because the SAME variable snode
        // appears in two distinct roles in a Nielsen substitution such as D -> "cc" D:
        // the outer variable (is_recursive == false, value == value of its replacement)
        // and the inner "leftover" remainder (is_recursive == true, value == "").
        u_map<expr *> var2value;
        u_map<expr *> node2value;
        // resolve: check leaf deps by expression ID, computed nodes by (snode,recursive) key.
        auto resolve = [&](euf::snode const* s, expr*& out) -> bool {
            if (var2value.find(s->get_expr()->get_id(), out))
                return true;
            return node2value.find(s->id(), out);
        };
        buffer<euf::snode const* > todo;
        for (unsigned i = 0; i < deps.size(); ++i) {
            var2value.insert(deps[i]->get_expr_id(), values[i]);
        }
        todo.push_back(n);
        expr_ref_vector args(m), pinned(m);
        arith_util a(m);

        expr *val = nullptr;
        while (!todo.empty()) {
            auto curr = todo.back();
            // Early exit: already computed (as leaf dep or computed node).
            expr* cached = nullptr;
            if (resolve(curr, cached)) {
                todo.pop_back();
                continue;
            }

            if (curr->is_empty())
                val = curr->get_expr();
            else if (m.is_value(curr->get_expr()))
                val = curr->get_expr();
            else if (curr->is_power()) {
                auto ival = int_value(curr->arg(1)->get_expr());
                val = m_seq.str.mk_power(curr->arg(0)->get_expr(), a.mk_int(ival));
            }
            else if (curr->is_char_or_unit()) {
                auto arg = curr->arg(0);
                expr *e = arg->get_expr();
                expr *charval = nullptr;
                if (m_ctx.e_internalized(e)) {
                    charval = var2value[e->get_id()];
                }
                else if (m_seq.str.is_nth_u(e)) {
                    expr *var_value = get_var_value(arg->arg(0));
                    auto index = int_value(arg->arg(1)->get_expr());
                    charval = m_seq.str.mk_nth(var_value, a.mk_int(index));
                }
                else {
                    NOT_IMPLEMENTED_YET();
                }
                val = m_seq.str.mk_unit(charval);
            }
            else if (curr->is_concat()) {
                args.reset();
                bool all_ready = true;
                for (unsigned i = 0; i < curr->num_args(); ++i) {
                    auto arg = curr->arg(i);
                    expr* av = nullptr;
                    if (resolve(arg, av))
                        args.push_back(av);
                    else {
                        todo.push_back(arg);
                        all_ready = false;
                    }
                }
                if (all_ready)
                    val = m_seq.str.mk_concat(args, curr->get_sort());
                else
                    continue; // not all arguments processed yet, will retry after children
            }
            else if (curr->is_var()) {
                euf::snode const* replacement = nullptr;
                if (m_var_replacement.find(var_key(curr), replacement)) {
                    // outer variable: its value is the value of its replacement.
                    expr* rv = nullptr;
                    if (!resolve(replacement, rv)) {
                        todo.push_back(replacement);
                        continue;
                    }
                    val = rv;
                }
                else {
                    // genuinely free variable (no replacement): respect its
                    // length / regex constraints.
                    val = get_var_value(curr);
                }
            }
            else {
                IF_VERBOSE(0, verbose_stream() << "not handled " << mk_pp(curr->get_expr(), m) << "\n");
                UNREACHABLE();
            }
            node2value.insert(curr->id(), val);
            pinned.push_back(val);
            todo.pop_back();
        }
        expr* result = nullptr;
        node2value.find(n->id(), result);
        if (!result)
            var2value.find(n->get_expr()->get_id(), result);
        return expr_ref(result, m);
    }

    expr* seq_model::get_var_value(euf::snode const* var) {
        SASSERT(var);
        const unsigned key = var_key(var);
        expr* val = nullptr;
        if (m_var_values.find(key, val))
            return val;

        // unconstrained or regex-constrained: delegate to mk_fresh_value
        val = mk_fresh_value(var);
        SASSERT(val);
        m_trail.push_back(val);
        m_var_values.insert(key, val);
        return val;
    }

    // Gets the arithmetic value of e. In QF_SLIA mode theory_lra does not register
    // numeral constants as LP variables, so get_value_equiv misses cases like
    // (str.len w) being equivalent to numeral 5 via EUF. Walking the EUF class
    // and checking for numerals directly handles this.
    bool seq_model::get_arith_value(expr* e, rational& val) const {
        if (!m_ctx.e_internalized(e))
            return false;
        const arith_util a(m);
        enode* root = m_ctx.get_enode(e);
        enode* it = root;
        do {
            if (a.is_numeral(it->get_expr(), val))
                return true;
            it = it->get_next();
        } while (it != root);
        arith_value avalue(m);
        avalue.init(&m_ctx);
        return avalue.get_value_equiv(e, val);
    }

    rational seq_model::int_value(expr *_e) {
        rational val;
        const arith_util a(m);

        // Try the original expression first. Composite exponent terms (e.g.
        // (- (* 2 (gpn! G)) (+ 3 (gpn! G)))) are built and internalized by the
        // Nielsen solver, so the arithmetic solver knows their value directly.
        // Rewriting them (below) can yield a structurally different term that is
        // NOT internalized, in which case get_arith_value bails out and we would
        // silently return 0 -- collapsing the power to the empty string.
        if (a.is_numeral(_e, val))
            return val;
        if (get_arith_value(_e, val))
            return val;

        // Fall back to the rewritten form (folds nested numerals, etc.).
        expr_ref e(_e, m);
        m_ctx.get_rewriter()(e);
        if (a.is_numeral(e, val))
            return val;

        bool has_val = get_arith_value(e, val);
        CTRACE(seq, !has_val, tout << "no value associated with " << mk_pp(e, m) << "\n";);
        return val;
    }

    expr* seq_model::mk_fresh_value(euf::snode const* var) {
        SASSERT(var->get_expr());
        SASSERT(m_seq.is_seq(var->get_expr()));
        auto  srt = var->get_expr()->get_sort();
        unsigned key = var_key(var);

        // Land-state view (paper §5.3): the variable is pinned to L_{Q,{s}}(head),
        // which is not a plain regex.  Build a witness by the product search over
        // ALL of the variable's primitive constraints (view AND any plain regex).
        // This is authoritative for a view variable — we must NOT fall through to
        // the plain m_var_regex path below, which sees only the plain constraints
        // and would emit a word that violates the view (unsound witness).
        if (m_nielsen && m_sat_node && m_view_vars.contains(key)) {
            expr_ref len_e(m_seq.str.mk_length(var->get_expr()), m);
            rational len_val;
            unsigned len = UINT_MAX;
            if (get_arith_value(len_e, len_val) && len_val.is_unsigned())
                len = len_val.get_unsigned();
            zstring w;
            // Try the arith-assigned length first (keeps the model length-consistent);
            // if the view∩plain intersection has no word of that length (the arith
            // length and the regex are only loosely coupled), retry unconstrained so
            // the emitted word still satisfies every regex/view constraint.
            bool ok = m_nielsen->product_witness(var, *m_sat_node, len, w);
            if (!ok && len != UINT_MAX)
                ok = m_nielsen->product_witness(var, *m_sat_node, UINT_MAX, w);
            if (ok) {
                expr* witness = m_seq.str.mk_string(w);
                m_trail.push_back(witness);
                m_factory->register_value(witness);
                return witness;
            }
            IF_VERBOSE(1, verbose_stream() << "nseq view witness failed for "
                << mk_pp(var->get_expr(), m) << "\n");
            // product search exhausted: fall through only to the length fallback,
            // never to the view-ignoring plain path (guarded by !m_view_vars below).
        }

        // check if this variable has regex constraints (non-view vars only; a view
        // var is fully handled above — its plain constraints are already folded
        // into the product search).
        euf::snode const* re = nullptr;
        if (!m_view_vars.contains(key) && m_var_regex.find(key, re) && re) {
            expr* re_expr = re->get_expr();
            SASSERT(re_expr);

            expr_ref len_expr(m_seq.str.mk_length(var->get_expr()), m);
            rational len_val;
            bool has_len = get_arith_value(len_expr, len_val);
            CTRACE(seq, !has_len, tout << "no value associated with " << mk_pp(len_expr, m) << "\n";);
            
            if (has_len && len_val.is_unsigned()) {
                unsigned n = len_val.get_unsigned();
                expr_ref loop(m_seq.re.mk_loop(m_seq.re.mk_full_char(re_expr->get_sort()), n, n), m);
                re_expr = m_seq.re.mk_inter(re_expr, loop);
            }

            zstring str;
            expr_ref witness(m);
            // We checked non-emptiness during Nielsen already
            lbool wr = m_rewriter.some_string_in_re(re_expr, str);
            if (wr != l_true) {
                // some_seq_in_re can fail (l_undef / l_false) on regexes it does
                // not fully support — notably projection operators (re.proj),
                // but also some plain Boolean-closure / large length-intersected
                // shapes.  Fall back to a derivative-automaton BFS that builds an
                // accepting word of the requested length directly.
                wr = derivative_witness(m_sg.mk(re_expr), witness);
            }
            if (wr == l_true) {
                witness = m_seq.str.mk_string(str);
                m_trail.push_back(witness);
                m_factory->register_value(witness);
                return witness;
            }
            IF_VERBOSE(1, verbose_stream() << "witness extraction failed for " << mk_pp(var->get_expr(), m)
                << " : " << wr << " with len " << (has_len ? len_val.to_string() : "unknown") << "\n" << mk_pp(re_expr, m) << "\n");
            // Last resort: do not crash model construction.  model_validate (if
            // enabled) will flag an inconsistent witness; otherwise fall through
            // to the length-respecting fallback below.
        }

        // No regex constraint: try to respect the assigned length for the variable.
        // This prevents invalid models such as len(x)=1 with x="".
        arith_util arith(m);
        expr_ref len_expr(m_seq.str.mk_length(var->get_expr()), m);
        rational len_val;
        bool has_len = get_arith_value(len_expr, len_val);
        CTRACE(seq, !has_len, tout << "no value associated with " << mk_pp(len_expr, m) << "\n";);
        

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
                    w += zstring('a');
                expr* witness = m_seq.str.mk_string(w);
                m_factory->register_value(witness);
                return witness;
            }

            expr* base = m_seq.str.mk_string("a");
            expr* witness = m_seq.str.mk_power(base, arith.mk_int(len_val));
            m_factory->register_value(witness);
            return witness;
        }

        // no regex constraint or witness generation failed: use empty string
        return m_seq.str.mk_empty(srt);
    }

    lbool seq_model::derivative_witness(euf::snode const* re0, expr_ref& witness) const {
        SASSERT(re0 && re0->get_expr());
        sort* seq_sort = nullptr;
        if (!m_seq.is_re(re0->get_expr(), seq_sort))
            return l_undef;

        // Shortest-path BFS over the derivative automaton.
        // Each frontier item is (state, accepting-word-so-far).  A state is
        // accepting when re_nullable reports nullable.
        // The regex carries the length intersection (∩ Σ^n), so an accepting
        // run has exactly the requested length and the search is finite.
        vector<std::pair<euf::snode const*, zstring>> work;
        work.push_back({re0, zstring()});
        uint_set visited;
        visited.insert(re0->id());

        unsigned head = 0;
        const unsigned MAX_STATES = 100000;
        while (head < work.size() && head < MAX_STATES) {
            euf::snode const* st = work[head].first;
            zstring w = work[head].second;
            ++head;

            if (m_sg.re_nullable(st) == l_true) {
                witness = m_seq.str.mk_string(w);
                return l_true;
            }
            if (st->is_fail())
                continue;

            euf::snode_vector mts;
            m_sg.compute_minterms(st, mts);
            for (euf::snode const* mt : mts) {
                euf::snode const* d = m_sg.brzozowski_deriv(st, mt);
                if (!d || d->is_fail())
                    continue;
                if (visited.contains(d->id()))
                    continue;
                visited.insert(d->id());

                // Representative character of the minterm (must lie in mt so
                // that δ_ch(st) = d).  Minterms over the cycle alphabet are
                // ranges / to_re singletons / full_char.
                unsigned ch = 0;
                expr* me = mt->get_expr();
                expr* lo = nullptr, *hi = nullptr, *s = nullptr;
                if (m_seq.re.is_range(me, lo, hi))
                    m_sg.decode_re_char(lo, ch);
                else if (m_seq.re.is_to_re(me, s))
                    m_sg.decode_re_char(s, ch);
                // re.full_char and anything else: ch = 0 (a valid representative)

                work.push_back({d, w + zstring(ch)});
            }
        }
        return l_undef;
    }

    void seq_model::collect_var_regex_constraints(seq::nielsen_node const* sat_node) {
        SASSERT(sat_node);
        for (auto const& mem : sat_node->str_mems()) {
            SASSERT(mem.well_formed());
            if (mem.is_trivial(sat_node))
                continue; // empty string in nullable regex: already satisfied, no variable to constrain
            VERIFY(mem.is_primitive()); // everything else should have been eliminated already
            // A land-state view (paper §5.3) does not denote a plain regex on the
            // variable; mark it so mk_fresh_value builds its witness via the
            // product search (which respects the view AND any plain constraints).
            if (!mem.is_plain()) {
                m_view_vars.insert(var_key(mem.m_str));
                continue;
            }
            unsigned id = var_key(mem.m_str);
            euf::snode const* existing = nullptr;
            if (m_var_regex.find(id, existing) && existing) {
                // intersect with existing constraint:
                // build re.inter(existing, new_regex)
                expr* e1 = existing->get_expr();
                expr* e2 = mem.m_regex->get_expr();
                if (e1 && e2) {
                    expr_ref inter(m_seq.re.mk_inter(e1, e2), m);
                    euf::snode const* inter_sn = m_sg.mk(inter);
                    SASSERT(inter_sn);
                    m_var_regex.insert(id, inter_sn);
                }
            }
            else
                m_var_regex.insert(id, mem.m_regex);
        }
    }

    bool seq_model::validate_regex(tracked_str_mem const& mem, ::proto_model& mdl) {
        SASSERT(mem.well_formed());
        expr* s_expr = mem.m_str->get_expr();
        expr* r_expr = mem.m_regex->get_expr();

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


#if 0
// retained in case we want to reconstruct small power unfoldings.

    expr_ref seq_model::snode_to_value(euf::snode const* n, expr_ref_vector const& values) {
        SASSERT(n);
        if (n->is_empty()) {
            sort* srt = n->get_sort();
            if (!srt)
                srt = m_seq.str.mk_string_sort();
            return expr_ref(m_seq.str.mk_empty(srt), m);               
        }

        arith_util arith(m); 

        if (m.is_value(n->get_expr())) 
            return expr_ref(n->get_expr(), m);        

        if (n->is_char_or_unit()) {
            expr *e = nullptr;
            VERIFY(m_seq.str.is_unit(n->get_expr(), e));
            if (values.size() == 1) {
                unsigned c;
                expr *dval = values.get(0);
                if (m_seq.is_const_char(dval, c))
                    return expr_ref(m_seq.str.mk_string(zstring(c)), m);
                return expr_ref(m_seq.str.mk_unit(dval), m);
            }
            else if (m_seq.str.is_nth_u(e)) {
                auto arg = n->arg(0);
                auto var_val = get_var_value(arg->arg(0));
                auto index_val = int_value(arg->arg(1)->get_expr());
                expr_ref val(m_seq.str.mk_nth(var_val, arith.mk_int(index_val)), m);
                return expr_ref(m_seq.str.mk_unit(val), m);
            }
            else
                NOT_IMPLEMENTED_YET();
        }

        if (n->is_var()) {
            euf::snode const* replacement = nullptr;
            if (!m_var_replacement.find(n->id(), replacement))
                return expr_ref(get_var_value(n), m);            
            return mk_value_with_dependencies(replacement, values);
        }

        if (n->is_concat()) {
            expr_ref_vector es(m), vals(m);
            unsigned idx = 0;
            m_seq.str.get_concat(n->get_expr(), es);
            for (auto e : es) {
                if (m.is_value(e))
                    vals.push_back(e);
                else
                    vals.push_back(values[idx++]);
            }
            return expr_ref(m_seq.str.mk_concat(vals, n->get_sort()), m);
        }

        if (n->is_power()) {
            SASSERT(n->num_args() == 2);
            SASSERT(values.size() == 0);
            // Evaluate the base and exponent to produce a concrete string.
            // The base is a string snode; the exponent is an integer expression
            // whose value comes from the sat_path integer model.
            expr *base_val = n->arg(0)->get_expr();
            expr *exp_expr = n->arg(1)->get_expr();

            rational exp_val = int_value(exp_expr);
            
            
            if (exp_val.is_neg())
                exp_val = rational(0);

            // Build the repeated string: base^exp_val
            if (exp_val == 0) 
                return expr_ref(m_seq.str.mk_empty(n->get_sort()), m);
            
            TRACE(seq, tout << mk_pp(n->get_expr(), m) << '\n');
            // For small exponents, concatenate directly; for large ones,
            // return mk_power to avoid enormous AST chains.
            constexpr unsigned POWER_EXPAND_LIMIT = 10;
            if (exp_val > POWER_EXPAND_LIMIT)
                return expr_ref(m_seq.str.mk_power(base_val, arith.mk_int(exp_val)), m);
            unsigned n_val = exp_val.get_unsigned();
            expr_ref acc(base_val, m);
            for (unsigned i = 1; i < n_val; ++i)
                acc = m_seq.str.mk_concat(acc, base_val);
            return acc;
        }

        // fallback: use the underlying expression       
        return expr_ref(n->get_expr(), m);
    }
#endif