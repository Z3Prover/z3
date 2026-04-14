/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex.cpp

Abstract:

    Lazy regex membership processing for the Nielsen-based string solver.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/seq/seq_regex.h"

namespace seq {

    // NSB code review: change the stabilizers set to
    // add the regexes in the domain of m_stabilizers to a trail (expr_ref_vector
    // change the range to be a vector of expressions, not snodes
    // add regexes in the range of m_stabilizers to the trail
    // this is to ensure that the expressions are valid also after scope changes.
    // maybe all regexes entered are created at base level for quantifier free formulas
    // but we should not assume this. The sgraph also can change based on scope.
    // the Stabilizer data-structure persists across search.

    // Collect possible first characters of a syntactically known *string*
    // expression (the body of to_re). Regex operators (union, complement,
    // intersection, ...) are not expected here.
    void collect_possible_first_chars(seq_util& seq, euf::sgraph const& sg, expr* str,
                                      unsigned_vector& bounds, bool& may_be_empty) {
        may_be_empty = false;
        VERIFY(str);
        sort* re_sort = nullptr;
        VERIFY(!seq.is_re(str, re_sort));

        unsigned ch = 0;
        if (sg.decode_re_char(str, ch)) {
            bounds.push_back(ch);
            if (ch < zstring::max_char())
                bounds.push_back(ch + 1);
            return;
        }

        zstring s;
        if (seq.str.is_string(str, s)) {
            if (s.length() == 0) {
                may_be_empty = true;
                return;
            }
            unsigned first_ch = s[0];
            bounds.push_back(first_ch);
            if (first_ch < zstring::max_char())
                bounds.push_back(first_ch + 1);
            return;
        }

        expr* a = nullptr;
        expr* b = nullptr;
        if (seq.str.is_concat(str, a, b)) {
            bool a_may_be_empty = false;
            collect_possible_first_chars(seq, sg, a, bounds, a_may_be_empty);

            if (a_may_be_empty) {
                bool b_may_be_empty = false;
                collect_possible_first_chars(seq, sg, b, bounds, b_may_be_empty);
                may_be_empty = b_may_be_empty;
            }
            return;
        }

        UNREACHABLE();
    }


    // -----------------------------------------------------------------------
    // Stabilizer store
    // -----------------------------------------------------------------------

    void seq_regex::reset_stabilizers() {
        m_stabilizers.reset();
        m_self_stabilizing.reset();
    }

    void seq_regex::add_stabilizer(euf::snode* regex, euf::snode* stabilizer) {
        if (!regex || !stabilizer)
            return;

        unsigned id = regex->id();
        auto& stabs = m_stabilizers.insert_if_not_there(id, ptr_vector<euf::snode>());

        // De-duplicate by pointer equality (mirrors ZIPT Environment.AddStabilizer
        // which checks reference equality before adding).
        for (euf::snode* s : stabs)
            if (s == stabilizer)
                return;
        stabs.push_back(stabilizer);
    }

    euf::snode* seq_regex::get_stabilizer_union(euf::snode* regex) {
        if (!regex)
            return nullptr;

        if (!m_stabilizers.contains(regex->id()))
            return nullptr;

        auto& stabs = m_stabilizers[regex->id()];
        if (stabs.empty())
            return nullptr;

        // Single stabilizer: return it directly.
        if (stabs.size() == 1)
            return stabs[0];

        // Multiple stabilizers: build re.union chain.
        // union(s1, union(s2, ... union(sN-1, sN)...))
        seq_util& seq = m_sg.get_seq_util();
        euf::snode* result = stabs[stabs.size() - 1];
        for (unsigned i = stabs.size() - 1; i-- > 0; ) {
            expr* lhs = stabs[i]->get_expr();
            expr* rhs = result->get_expr();
            if (!lhs || !rhs)
                return nullptr;
            expr_ref un(seq.re.mk_union(lhs, rhs), m_sg.get_manager());
            result = m_sg.mk(un);
        }
        return result;
    }

    bool seq_regex::has_stabilizers(euf::snode* regex) const {
        if (!regex)
            return false;
        if (!m_stabilizers.contains(regex->id()))
            return false;
        return !m_stabilizers[regex->id()].empty();
    }

    ptr_vector<euf::snode> const* seq_regex::get_stabilizers(euf::snode* regex) const {
        if (!regex)
            return nullptr;
        if (!m_stabilizers.contains(regex->id()))
            return nullptr;
        return &m_stabilizers[regex->id()];
    }

    void seq_regex::set_self_stabilizing(euf::snode* regex) {
        if (regex)
            m_self_stabilizing.insert(regex->id());
    }

    bool seq_regex::is_self_stabilizing(euf::snode* regex) const {
        return regex && m_self_stabilizing.contains(regex->id());
    }

    // -----------------------------------------------------------------------
    // Self-stabilizing auto-detection
    // -----------------------------------------------------------------------

    bool seq_regex::compute_self_stabilizing(euf::snode* regex) const {
        if (!regex)
            return false;

        // R* is always self-stabilizing: D(c, R*) = D(c,R) · R*,
        // so R* appears as the tail of every derivative and acts as
        // its own stabilizer.
        if (regex->is_star())
            return true;

        // Σ* (full_seq, i.e., re.all / .*) is self-stabilizing:
        // D(c, Σ*) = Σ* for every character c.
        if (regex->is_full_seq())
            return true;

        // ∅ (fail / empty language) is trivially self-stabilizing:
        // it has no live derivatives, so the flag is vacuously true.
        if (regex->is_fail())
            return true;

        // Complement of full_seq is ∅ (complement of Σ*), which is
        // also trivially self-stabilizing.
        if (regex->is_complement() && regex->num_args() == 1 &&
            regex->arg(0)->is_full_seq())
            return true;

        // Loop with lo=0 and no upper bound behaves like R*
        // (r{0,} ≡ r*), so it is self-stabilizing.
        if (regex->is_loop() && regex->is_nullable()) {
            // A nullable loop with a star-like body: heuristic check.
            // Only mark as self-stabilizing if the body is a Kleene closure.
            // Loop(R, 0, ∞) ~ R* — but we rely on the sgraph to normalize
            // these, so only catch exact star nodes above.
        }

        return false;
    }

    // -----------------------------------------------------------------------
    // Self-stabilizing propagation through derivatives
    // -----------------------------------------------------------------------

    void seq_regex::propagate_self_stabilizing(euf::snode* parent, euf::snode* deriv) {
        if (!parent || !deriv)
            return;

        // If the derivative is already known to be self-stabilizing (either
        // inherently or from a prior propagation), nothing to do.
        if (is_self_stabilizing(deriv))
            return;

        // If the derivative is itself inherently self-stabilizing
        // (e.g., it is a star or full_seq), mark it now.
        if (compute_self_stabilizing(deriv)) {
            set_self_stabilizing(deriv);
            return;
        }

        // Rule 1: Star parent.
        // D(c, R*) = D(c, R) · R*. The derivative always contains the
        // R* tail, so it is self-stabilizing regardless of D(c,R).
        if (parent->is_star()) {
            set_self_stabilizing(deriv);
            return;
        }

        // Rule 2: Full_seq parent.
        // D(c, Σ*) = Σ*, and Σ* is self-stabilizing.
        // (The derivative should be Σ* itself; mark it for safety.)
        if (parent->is_full_seq()) {
            set_self_stabilizing(deriv);
            return;
        }

        // Check if parent is self-stabilizing (either inherently or marked).
        bool parent_ss = is_self_stabilizing(parent) || compute_self_stabilizing(parent);

        // Rule 3: Concat parent R · S.
        // D(c, R·S) = D(c,R)·S | (nullable(R) ? D(c,S) : ∅).
        // If S is self-stabilizing, the D(c,R)·S branch inherits it.
        // If the whole parent R·S is self-stabilizing, the derivative is too.
        if (parent->is_concat() && parent->num_args() == 2) {
            euf::snode* tail = parent->arg(1);
            bool tail_ss = is_self_stabilizing(tail) || compute_self_stabilizing(tail);
            if (tail_ss || parent_ss) {
                set_self_stabilizing(deriv);
                return;
            }
        }

        // Rule 4: Union parent R | S.
        // D(c, R|S) = D(c,R) | D(c,S).
        // Self-stabilizing if both children are self-stabilizing.
        if (parent->is_union() && parent->num_args() == 2) {
            euf::snode* lhs = parent->arg(0);
            euf::snode* rhs = parent->arg(1);
            bool lhs_ss = is_self_stabilizing(lhs) || compute_self_stabilizing(lhs);
            bool rhs_ss = is_self_stabilizing(rhs) || compute_self_stabilizing(rhs);
            if (lhs_ss && rhs_ss) {
                set_self_stabilizing(deriv);
                return;
            }
        }

        // Rule 5: Intersection parent R ∩ S.
        // D(c, R∩S) = D(c,R) ∩ D(c,S).
        // Self-stabilizing if both children are self-stabilizing.
        if (parent->is_intersect() && parent->num_args() == 2) {
            euf::snode* lhs = parent->arg(0);
            euf::snode* rhs = parent->arg(1);
            bool lhs_ss = is_self_stabilizing(lhs) || compute_self_stabilizing(lhs);
            bool rhs_ss = is_self_stabilizing(rhs) || compute_self_stabilizing(rhs);
            if (lhs_ss && rhs_ss) {
                set_self_stabilizing(deriv);
                return;
            }
        }

        // Rule 6: Complement parent ~R.
        // D(c, ~R) = ~D(c, R).
        // Preserves self-stabilizing from R.
        if (parent->is_complement() && parent->num_args() == 1) {
            euf::snode* inner = parent->arg(0);
            bool inner_ss = is_self_stabilizing(inner) || compute_self_stabilizing(inner);
            if (inner_ss) {
                set_self_stabilizing(deriv);
                return;
            }
        }

        // Rule 7: Generic self-stabilizing parent.
        // If the parent was explicitly marked self-stabilizing (e.g., via
        // a previous propagation), propagate to the derivative.
        if (parent_ss) {
            set_self_stabilizing(deriv);
            return;
        }
    }

    // -----------------------------------------------------------------------
    // Derivative with propagation
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::derivative_with_propagation(euf::snode* re, euf::snode* elem) {
        if (!re || !elem)
            return nullptr;
        euf::snode* deriv = derivative(re, elem);
        if (deriv)
            propagate_self_stabilizing(re, deriv);
        return deriv;
    }

    // -----------------------------------------------------------------------
    // Uniform derivative (symbolic character consumption)
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::try_uniform_derivative(euf::snode* regex) {
        if (!regex)
            return nullptr;

        // Quick exits: trivial regexes with known uniform derivatives.
        // Σ* (full_seq) has derivative Σ* for every character.
        if (regex->is_full_seq())
            return regex;
        // ∅ (fail) has derivative ∅ for every character — but this means
        // every character is rejected.  Return fail so the caller can
        // detect a conflict.
        if (regex->is_fail())
            return regex;

        // Compute minterms: the character-class partition of the alphabet
        // induced by the regex.
        euf::snode_vector minterms;
        m_sg.compute_minterms(regex, minterms);
        if (minterms.empty())
            return nullptr;

        // Compute the derivative for each non-empty minterm.  If all produce
        // the same result, the derivative is independent of the character
        // value and we can consume a symbolic character deterministically.
        euf::snode* uniform = nullptr;
        for (euf::snode* mt : minterms) {
            if (!mt || mt->is_fail())
                continue;  // empty character class — no character belongs to it
            euf::snode* deriv = m_sg.brzozowski_deriv(regex, mt);
            if (!deriv)
                return nullptr;  // derivative computation failed
            if (!uniform) {
                uniform = deriv;
            } else if (uniform->id() != deriv->id()) {
                return nullptr;  // different derivatives — not uniform
            }
        }
        return uniform;  // may be nullptr if all minterms were fail/empty
    }

    // -----------------------------------------------------------------------
    // Ground prefix consumption
    // -----------------------------------------------------------------------

    bool seq_regex::is_empty_regex(euf::snode* re) const {
        if (!re)
            return false;
        // direct empty language constant
        if (re->is_fail())
            return true;
        // kinds that are never empty
        if (re->is_star() || re->is_to_re() || re->is_range() ||
            re->is_full_char() || re->is_full_seq())
            return false;
        // loop with lo == 0 accepts ε
        if (re->is_loop() && re->is_nullable())
            return false;

        seq_util& seq = m_sg.get_seq_util();
        expr* e = re->get_expr();
        if (!e)
            return false;

        expr* r1, * r2;
        // union is empty iff both children are empty
        if (seq.re.is_union(e, r1, r2)) {
            SASSERT(re->num_args() == 2);
            return is_empty_regex(re->arg(0)) && is_empty_regex(re->arg(1));
        }
        // regex concat is empty if either child is empty
        if (seq.re.is_concat(e, r1, r2)) {
            SASSERT(re->num_args() == 2);
            return is_empty_regex(re->arg(0)) || is_empty_regex(re->arg(1));
        }
        // intersection is empty if either child is empty
        if (seq.re.is_intersection(e, r1, r2)) {
            SASSERT(re->num_args() == 2);
            if (is_empty_regex(re->arg(0)) || is_empty_regex(re->arg(1)))
                return true;
        }
        // complement of full_seq is empty
        if (re->is_complement() && re->num_args() == 1 && re->arg(0)->is_full_seq())
            return true;
        // loop(empty, lo, _) with lo > 0 is empty
        if (re->is_loop() && re->num_args() >= 1 && is_empty_regex(re->arg(0)))
            return !re->is_nullable(); // empty if not nullable (i.e., lo > 0)

        return false;
    }

    // -----------------------------------------------------------------------
    // BFS regex emptiness check — helper: collect character boundaries
    // This is faster than computing the actual minterms but probably not minimal
    // -----------------------------------------------------------------------
    void seq_regex::collect_char_boundaries(euf::snode* re, unsigned_vector& bounds) const {
        SASSERT(re && re->get_expr());

        seq_util& seq = m_sg.get_seq_util();
        expr* e = re->get_expr();

        // Range predicate re.range(lo, hi): boundary at lo and hi+1
        // Range arguments are string expressions (e.g., str.unit(ch))
        expr* lo_expr = nullptr;
        expr* hi_expr = nullptr;
        if (seq.re.is_range(e, lo_expr, hi_expr)) {
            unsigned lo = 0, hi = 0;
            if (m_sg.decode_re_char(lo_expr, lo))
                bounds.push_back(lo);
            if (m_sg.decode_re_char(hi_expr, hi) && hi < zstring::max_char())
                bounds.push_back(hi + 1);
            return;
        }

        // to_re(s): boundary at possible first characters of s
        expr* body = nullptr;
        if (seq.re.is_to_re(e, body)) {
            bool may_be_empty = false;
            collect_possible_first_chars(seq, m_sg, body, bounds, may_be_empty);
            return;
        }

        // Leaf nodes with no character discrimination
        if (re->is_fail() || re->is_full_char() || re->is_full_seq())
            return;

        // If we reached a leaf and none of the expected leaf forms matched,
        // this is a regex constructor we did not account for in boundary
        // extraction and should fail loudly in debug builds.
        if (re->num_args() == 0) {
            UNREACHABLE();
            return;
        }

        // Recurse into children (handles union, concat, star, loop, etc.)
        for (unsigned i = 0; i < re->num_args(); ++i) {
            collect_char_boundaries(re->arg(i), bounds);
        }
    }

    // -----------------------------------------------------------------------
    // BFS regex emptiness check — helper: alphabet representatives
    // Faster alternative of computing all min-terms and taking representatives of them
    // -----------------------------------------------------------------------
    bool seq_regex::get_alphabet_representatives(euf::snode* re, euf::snode_vector& reps) {
        if (!re || !re->get_expr())
            return false;

        seq_util& seq = m_sg.get_seq_util();
        unsigned max_c = seq.max_char();

        // Partition the alphabet using boundary points induced by regex
        // predicates; one representative per interval is sufficient.
        unsigned_vector bounds;
        bounds.push_back(0);
        if (max_c < UINT_MAX)
            bounds.push_back(max_c + 1);
        collect_char_boundaries(re, bounds);

        std::sort(bounds.begin(), bounds.end());
        unsigned_vector uniq;
        for (unsigned b : bounds) {
            if (uniq.empty() || uniq.back() != b)
                uniq.push_back(b);
        }
        bounds = uniq;

        for (unsigned i = 0; i + 1 < bounds.size(); ++i) {
            unsigned lo = bounds[i];
            unsigned hi = bounds[i + 1];
            if (lo <= max_c && lo < hi)
                reps.push_back(m_sg.mk_char(lo));
        }

        // Defensive fallback for degenerate inputs.
        if (reps.empty())
            reps.push_back(m_sg.mk_char(0));
        return true;
    }

    // -----------------------------------------------------------------------
    // BFS regex emptiness check
    // -----------------------------------------------------------------------

    // NSB review: we have similar functionality in seq_rewriter::some_seq_in_re
    // currently both these versions only relly work for strings not general sequences
    lbool seq_regex::is_empty_bfs(euf::snode* re, unsigned max_states) {
        if (!re)
            return l_undef;
        if (re->is_fail())
            return l_true;
        if (re->is_nullable())
            return l_false;
        // Structural quick checks for kinds that are never empty
        if (re->is_star() || re->is_full_char() || re->is_full_seq() || re->is_to_re() || re->is_range())
            return l_false;
        // Structural emptiness catches simple cases
        if (is_empty_regex(re))
            return l_true;
        // Only handle ground regexes; non-ground can't be fully explored
        if (!re->is_ground())
            return l_undef;
        // s_var snodes (unrecognized regex kinds, e.g. re.+) cannot be
        // efficiently explored: the alphabet partition is trivially {∅} and
        // derivative computations may be slow.  Report l_undef and let the
        // caller fall back to a more capable procedure.
        if (re->is_var())
            return l_undef;

        // BFS over the Brzozowski derivative automaton.
        // Each state is a derivative regex snode identified by its id.
        // We explore states by computing derivatives for representative
        // characters from the alphabet partition.
        uint_set visited;
        euf::snode_vector worklist;
        worklist.push_back(re);
        visited.insert(re->id());

        unsigned states_explored = 0;

        while (!worklist.empty()) {
            if (!m_sg.get_manager().inc())
                return l_undef;
            if (states_explored >= max_states)
                return l_undef;

            euf::snode* current = worklist.back();
            worklist.pop_back();
            ++states_explored;

            // Compute representative characters for current state's
            // alphabet partition. Each representative is a concrete
            // character snode whose equivalence class has identical
            // derivative behavior.
            euf::snode_vector reps;
            if (!get_alphabet_representatives(current, reps))
                return l_undef;

            if (reps.empty())
                // Nothing found = dead-end
                continue;

            for (euf::snode* ch : reps) {
                if (!m_sg.get_manager().inc())
                    return l_undef;
                // std::cout << "Deriving by " << snode_label_html(ch, sg().get_manager()) << std::endl;
                euf::snode* deriv = m_sg.brzozowski_deriv(current, ch);
                SASSERT(deriv);
                if (deriv->is_nullable())
                    return l_false; // found an accepting state
                if (deriv->is_fail())
                    continue; // dead-end, no need to explore further
                if (is_empty_regex(deriv))
                    continue; // structurally empty subtree
                if (!visited.contains(deriv->id())) {
                    visited.insert(deriv->id());
                    worklist.push_back(deriv);
                    // std::cout << "Found [" << deriv->id() << "]: " << snode_label_html(deriv, sg().get_manager()) << std::endl;
                }
            }
        }
        return l_true;
    }

    // -----------------------------------------------------------------------
    // Multi-regex intersection emptiness check
    // BFS over the product of Brzozowski derivative automata.
    // Mirrors ZIPT NielsenNode.CheckEmptiness (NielsenNode.cs:1429-1469)
    // -----------------------------------------------------------------------

    lbool seq_regex::check_intersection_emptiness(ptr_vector<euf::snode> const& regexes, unsigned max_states) {

        if (regexes.empty())
            return l_false; // empty intersection = full language (vacuously non-empty)

        // Single regex: delegate to is_empty_bfs
        if (regexes.size() == 1)
            return is_empty_bfs(regexes[0], max_states);

        seq_util& seq = m_sg.get_seq_util();
        ast_manager& mgr = m_sg.get_manager();

        euf::snode* result = regexes[0];
        for (unsigned i = 1; i < regexes.size(); ++i) {
            expr* r1 = result->get_expr();
            expr* r2 = regexes[i]->get_expr();
            SASSERT(r1 && r2);
            result = m_sg.mk(seq.re.mk_inter(r1, r2));
            SASSERT(result);
        }

        return is_empty_bfs(result, max_states);
    }

    // -----------------------------------------------------------------------
    // Language subset check: L(A) ⊆ L(B)
    // via intersection(A, complement(B)) = ∅
    // Mirrors ZIPT NielsenNode.IsLanguageSubset (NielsenNode.cs:1382-1385)
    // -----------------------------------------------------------------------

    lbool seq_regex::is_language_subset(euf::snode* subset_re, euf::snode* superset_re) {
        if (!subset_re || !superset_re)
            return l_undef;

        // Quick checks
        if (subset_re->is_fail() || is_empty_regex(subset_re))
            return l_true;  // ∅ ⊆ anything
        if (superset_re->is_full_seq())
            return l_true;  // anything ⊆ Σ*
        if (subset_re == superset_re)
            return l_true;  // L ⊆ L

        // Build complement(superset)
        seq_util& seq = m_sg.get_seq_util();
        ast_manager& mgr = m_sg.get_manager();
        expr* sup_expr = superset_re->get_expr();
        if (!sup_expr)
            return l_undef;
        expr_ref comp(seq.re.mk_complement(sup_expr), mgr);
        euf::snode* comp_sn = m_sg.mk(comp);
        if (!comp_sn)
            return l_undef;

        // Build intersection and check emptiness
        // subset ∩ complement(superset) should be empty for subset relation
        expr* sub_expr = subset_re->get_expr();
        if (!sub_expr)
            return l_undef;
        expr_ref inter(seq.re.mk_inter(sub_expr, comp.get()), mgr);
        euf::snode* inter_sn = m_sg.mk(inter);
        if (!inter_sn)
            return l_undef;

        return is_empty_bfs(inter_sn);
    }

    // -----------------------------------------------------------------------
    // Collect primitive regex intersection for a variable
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::collect_primitive_regex_intersection(
            euf::snode* var, nielsen_node const& node, dep_manager& dep_mgr, dep_tracker& dep) const {
        SASSERT(var);

        seq_util& seq = m_sg.get_seq_util();
        ast_manager& m = m_sg.get_manager();
        euf::snode* result = nullptr;

        for (auto const& mem : node.str_mems()) {
            // Primitive constraint: str is a single variable
            if (!mem.is_primitive())
                continue;
            euf::snode *first = mem.m_str->first();
            // NSB review: why is this "first" and not mem.m_str?
            SASSERT(first);
            if (first != var)
                continue;
            TRACE(seq, tout << mk_pp(first->get_expr(), m) << " " << mem_pp(m, mem) << " dep: " << mem.m_dep << "\n");

            if (!result) {
                result = mem.m_regex;
                dep = dep_mgr.mk_join(dep, mem.m_dep);
            }
            else {
                expr* r1 = result->get_expr();
                expr* r2 = mem.m_regex->get_expr();
                if (r1 && r2) {
                    expr_ref inter(seq.re.mk_inter(r1, r2), m);
                    result = m_sg.mk(inter);
                    dep = dep_mgr.mk_join(dep, mem.m_dep);
                }
            }
        }
        return result;
    }

    // -----------------------------------------------------------------------
    // Cycle detection
    // -----------------------------------------------------------------------

    bool seq_regex::detect_cycle(seq::str_mem const& mem) const {
        return extract_cycle(mem) != nullptr;
    }

    // -----------------------------------------------------------------------
    // Ground prefix consumption
    // -----------------------------------------------------------------------

    seq_regex::simplify_status seq_regex::simplify_ground_prefix(seq::str_mem& mem) {
        if (!mem.m_str || !mem.m_regex)
            return simplify_status::ok;

        while (mem.m_str && !mem.m_str->is_empty()) {
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_char())
                break;
            euf::snode* parent_re = mem.m_regex;
            euf::snode* deriv = m_sg.brzozowski_deriv(parent_re, first);
            if (!deriv)
                break;
            if (deriv->is_fail())
                return simplify_status::conflict;
            // propagate self-stabilizing flag from parent to derivative
            propagate_self_stabilizing(parent_re, deriv);
            mem.m_str = m_sg.drop_first(mem.m_str);
            mem.m_regex = deriv;
        }

        // check final state
        if (mem.m_str && mem.m_str->is_empty()) {
            if (mem.m_regex->is_nullable())
                return simplify_status::satisfied;
            return simplify_status::conflict;
        }

        return simplify_status::ok;
    }

    // -----------------------------------------------------------------------
    // Ground suffix consumption (best-effort)
    // -----------------------------------------------------------------------

    seq_regex::simplify_status seq_regex::simplify_ground_suffix(seq::str_mem& mem) {
        // Suffix consumption via reverse derivatives is complex.
        // For now, only handle the case where the entire string is ground:
        // consume all characters from the front (which covers trailing chars
        // when the string is fully ground).
        if (!mem.m_str || !mem.m_regex)
            return simplify_status::ok;
        if (!mem.m_str->is_ground())
            return simplify_status::ok;

        // If the string is ground, simplify_ground_prefix handles everything.
        return simplify_ground_prefix(mem);
    }

    // -----------------------------------------------------------------------
    // Trivial checks
    // -----------------------------------------------------------------------

    int seq_regex::check_trivial(seq::str_mem const& mem) const {
        if (!mem.m_str || !mem.m_regex)
            return 0;
        // regex is ∅ => always conflict
        if (is_empty_regex(mem.m_regex))
            return -1;
        // regex is Σ* => always satisfied
        if (is_full_regex(mem.m_regex))
            return 1;
        // empty string checks
        if (mem.m_str->is_empty()) {
            if (mem.m_regex->is_nullable())
                return 1;
            return -1;
        }
        return 0;
    }

    // -----------------------------------------------------------------------
    // Minterm computation with filtering
    // -----------------------------------------------------------------------

    void seq_regex::get_minterms(euf::snode* regex, euf::snode_vector& minterms) {
        if (!regex)
            return;

        // compute raw minterms from the regex predicates
        euf::snode_vector raw;
        m_sg.compute_minterms(regex, raw);

        // filter: keep only minterms that are non-fail (non-empty character class).
        // note: minterms are regex character-class expressions, not concrete
        // characters, so we cannot compute Brzozowski derivatives with them.
        // callers should compute derivatives using concrete or fresh chars.
        for (euf::snode* mt : raw) {
            if (!mt || mt->is_fail())
                continue;
            minterms.push_back(mt);
        }
    }

    // -----------------------------------------------------------------------
// Membership processing
    // -----------------------------------------------------------------------

    bool seq_regex::process_str_mem(seq::str_mem const& mem,
                                     vector<seq::str_mem>& out_mems) {
        if (!mem.m_str || !mem.m_regex)
            return true;
        // empty string: check nullable
        if (mem.m_str->is_empty())
            return mem.m_regex->is_nullable();

        // consume ground prefix: derive regex by each leading concrete char
        seq::str_mem working = mem;
        simplify_status st = simplify_ground_prefix(working);
        if (st == simplify_status::conflict)
            return false;
        if (st == simplify_status::satisfied)
            return true;

        // after ground prefix consumption, if the front is still a concrete
        // character we can take one more step (shouldn't happen after
        // simplify_ground_prefix, but guard defensively)
        euf::snode* first = working.m_str->first();
        if (first && first->is_char()) {
            seq::str_mem derived = derive(working, first);
            if (is_empty_regex(derived.m_regex))
                return false;
            out_mems.push_back(derived);
            return true;
        }

        // string starts with a non-ground element (variable or unit):
        // return the simplified constraint for the Nielsen graph to expand
        // via character-split modifiers.
        out_mems.push_back(working);
        return true;
    }

    // -----------------------------------------------------------------------
    // History recording
    // -----------------------------------------------------------------------

    seq::str_mem seq_regex::record_history(seq::str_mem const& mem, euf::snode* history_re) {
        // Build a history chain by prepending the new regex entry to the
        // existing history. Uses regex-concat as a cons cell:
        //   new_history = re.concat(history_re, old_history)
        // where arg(0) is the latest entry and arg(1) is the tail.
        // If old_history is nullptr, the new entry becomes the terminal leaf.
        euf::snode* new_history = history_re;
        if (mem.m_history && history_re) {
            expr* re_expr = history_re->get_expr();
            expr* old_expr = mem.m_history->get_expr();
            if (re_expr && old_expr) {
                seq_util& seq = m_sg.get_seq_util();
                expr_ref chain(seq.re.mk_concat(re_expr, old_expr), m_sg.get_manager());
                new_history = m_sg.mk(chain);
            }
        }
        return seq::str_mem(mem.m_str, mem.m_regex, new_history, mem.m_id, mem.m_dep);
    }

    // -----------------------------------------------------------------------
    // Cycle detection
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::extract_cycle(seq::str_mem const& mem) const {
        // Walk the history chain looking for a repeated regex.
        // A cycle exists when the current regex matches a regex in the history.
        if (!mem.m_regex || !mem.m_history)
            return nullptr;

        euf::snode* current = mem.m_regex;
        euf::snode* hist = mem.m_history;

        // Walk the history chain up to a bounded depth.
        // The history is structured as a chain of regex snapshots connected
        // via the sgraph's regex-concat: each level's arg(0) is a snapshot
        // and arg(1) is the tail. A leaf (non-concat) is a terminal entry.
        unsigned bound = 1000;
        while (hist && bound-- > 0) {
            euf::snode* entry = hist;
            euf::snode* tail = nullptr;

            // If the history node is a regex concat, decompose it:
            // arg(0) is the regex snapshot, arg(1) is the rest of the chain
            seq_util& seq = m_sg.get_seq_util();
            if (hist->is_concat() && hist->get_expr() &&
                seq.re.is_concat(hist->get_expr())) {
                entry = hist->arg(0);
                tail = hist->arg(1);
            }

            // Check pointer equality (fast, covers normalized regexes)
            if (entry == current)
                return entry;
            // Check expression-level equality as fallback
            if (entry->get_expr() && current->get_expr() &&
                entry->get_expr() == current->get_expr())
                return entry;

            hist = tail;
        }
        return nullptr;
    }

    // -----------------------------------------------------------------------
    // Stabilizer from cycle
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::stabilizer_from_cycle(euf::snode* cycle_regex,
                                                   euf::snode* current_regex) {
        if (!cycle_regex || !current_regex)
            return nullptr;

        expr* re_expr = cycle_regex->get_expr();
        if (!re_expr)
            return nullptr;

        seq_util& seq = m_sg.get_seq_util();
        expr_ref star_expr(seq.re.mk_star(re_expr), m_sg.get_manager());
        return m_sg.mk(star_expr);
    }

    // -----------------------------------------------------------------------
    // Extract cycle history tokens
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::extract_cycle_history(seq::str_mem const& current,
                                                   seq::str_mem const& ancestor) {
        // The history is built by simplify_and_init as a left-associative
        // string concat chain: concat(concat(concat(nil, c1), c2), c3).
        // Extract the tokens consumed since the ancestor.
        if (!current.m_history)
            return nullptr;

        unsigned cur_len = current.m_history->length();
        unsigned anc_len = ancestor.m_history ? ancestor.m_history->length() : 0;

        if (cur_len <= anc_len)
            return nullptr;

        if (anc_len == 0)
            return current.m_history;

        return m_sg.drop_left(current.m_history, anc_len);
    }

    // -----------------------------------------------------------------------
    // Get filtered stabilizer star
    // Mirrors ZIPT StrMem.GetFilteredStabilizerStar (StrMem.cs:228-243)
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::get_filtered_stabilizer_star(euf::snode* re,
                                                          euf::snode* excluded_char) {
        if (!re)
            return nullptr;

        ptr_vector<euf::snode> const* stabs = get_stabilizers(re);
        if (!stabs || stabs->empty())
            return nullptr;

        seq_util& seq = m_sg.get_seq_util();
        ast_manager& m = m_sg.get_manager();
        euf::snode* filtered_union = nullptr;

        for (euf::snode* s : *stabs) {
            if (!s)
                continue;
            // Keep only stabilizers whose language cannot start with excluded_char
            euf::snode* d = m_sg.brzozowski_deriv(s, excluded_char);
            if (d && d->is_fail()) {
                if (!filtered_union) {
                    filtered_union = s;
                } else {
                    expr* e1 = filtered_union->get_expr();
                    expr* e2 = s->get_expr();
                    if (e1 && e2) {
                        expr_ref u(seq.re.mk_union(e1, e2), m);
                        filtered_union = m_sg.mk(u);
                    }
                }
            }
        }

        if (!filtered_union)
            return nullptr;

        expr* fe = filtered_union->get_expr();
        if (!fe)
            return nullptr;
        expr_ref star_expr(seq.re.mk_star(fe), m);
        return m_sg.mk(star_expr);
    }

    // -----------------------------------------------------------------------
    // Strengthened stabilizer construction with sub-cycle detection
    // Mirrors ZIPT StrMem.StabilizerFromCycle (StrMem.cs:163-225)
    // -----------------------------------------------------------------------

    euf::snode* seq_regex::strengthened_stabilizer(euf::snode* cycle_regex,
                                                     euf::snode* cycle_history) {
        if (!cycle_regex || !cycle_history)
            return nullptr;

        // Flatten the history concat chain into a vector of character tokens.
        euf::snode_vector tokens;
        cycle_history->collect_tokens(tokens);

        if (tokens.empty())
            return nullptr;

        seq_util& seq = m_sg.get_seq_util();
        ast_manager& m = m_sg.get_manager();

        // Replay tokens on the cycle regex, detecting sub-cycles.
        // A sub-cycle is detected when the derivative returns to cycle_regex.
        svector<std::pair<unsigned, unsigned>> sub_cycles;
        unsigned cycle_start = 0;
        euf::snode* current_re = cycle_regex;

        for (unsigned i = 0; i < tokens.size(); ++i) {
            euf::snode* tok = tokens[i];
            if (!tok)
                return nullptr;

            euf::snode* deriv = m_sg.brzozowski_deriv(current_re, tok);
            if (!deriv)
                return nullptr;

            // Sub-cycle: derivative returned to the cycle entry regex
            if (deriv == cycle_regex ||
                (deriv->get_expr() && cycle_regex->get_expr() &&
                 deriv->get_expr() == cycle_regex->get_expr())) {
                sub_cycles.push_back(std::make_pair(cycle_start, i + 1));
                cycle_start = i + 1;
                current_re = cycle_regex;
            } else {
                current_re = deriv;
            }
        }

        // Remaining tokens that don't complete a sub-cycle
        if (cycle_start < tokens.size())
            sub_cycles.push_back(std::make_pair(cycle_start, tokens.size()));

        if (sub_cycles.empty())
            return nullptr;

        // Build a stabilizer body for each sub-cycle.
        // body = to_re(t0) · [filteredStar(R1, t1)] · to_re(t1) · ... · to_re(t_{n-1})
        euf::snode* overall_union = nullptr;

        for (auto const& sc : sub_cycles) {
            unsigned start = sc.first;
            unsigned end = sc.second;
            if (start >= end)
                continue;

            euf::snode* re_state = cycle_regex;
            euf::snode* body = nullptr;

            for (unsigned i = start; i < end; ++i) {
                euf::snode* tok = tokens[i];
                if (!tok)
                    break;

                // Insert filtered stabilizer star before each token after the first
                if (i > start) {
                    euf::snode* filtered = get_filtered_stabilizer_star(re_state, tok);
                    if (filtered) {
                        expr* fe = filtered->get_expr();
                        if (fe) {
                            if (!body) {
                                body = filtered;
                            } else {
                                expr* be = body->get_expr();
                                if (be) {
                                    expr_ref cat(seq.re.mk_concat(be, fe), m);
                                    body = m_sg.mk(cat);
                                }
                            }
                        }
                    }
                }

                // Convert char token to regex: to_re(unit(tok))
                expr* tok_expr = tok->get_expr();
                if (!tok_expr)
                    break;

                expr_ref unit_str(seq.str.mk_unit(tok_expr), m);
                expr_ref tok_re(seq.re.mk_to_re(unit_str), m);
                euf::snode* tok_re_sn = m_sg.mk(tok_re);

                if (!body) {
                    body = tok_re_sn;
                } else {
                    expr* be = body->get_expr();
                    expr* te = tok_re_sn->get_expr();
                    if (be && te) {
                        expr_ref cat(seq.re.mk_concat(be, te), m);
                        body = m_sg.mk(cat);
                    }
                }

                // Advance the regex state
                euf::snode* deriv = m_sg.brzozowski_deriv(re_state, tok);
                if (!deriv)
                    break;
                re_state = deriv;
            }

            if (!body)
                continue;

            if (!overall_union) {
                overall_union = body;
            } else {
                expr* oe = overall_union->get_expr();
                expr* be = body->get_expr();
                if (oe && be) {
                    expr_ref u(seq.re.mk_union(oe, be), m);
                    overall_union = m_sg.mk(u);
                }
            }
        }

        return overall_union;
    }

    // -----------------------------------------------------------------------
    // Stabilizer-based subsumption (enhanced)
    // Mirrors ZIPT StrMem.TrySubsume (StrMem.cs:354-386)
    // -----------------------------------------------------------------------

    bool seq_regex::try_subsume(str_mem const& mem, nielsen_node const& node) {
#if 0
        SASSERT(mem.m_str && mem.m_regex);

        // 1. Leading token must be a variable
        euf::snode* first = mem.m_str->first();
        if (!first || !first->is_var())
            return false;

        // 2. Must have stabilizers for the regex
        if (!has_stabilizers(mem.m_regex))
            return false;

        // 3. Build stabStar = star(union(all stabilizers for this regex))
        euf::snode* stab_union = get_stabilizer_union(mem.m_regex);
        if (!stab_union)
            return false;

        seq_util& seq = m_sg.get_seq_util();
        ast_manager& mgr = m_sg.get_manager();
        expr* su_expr = stab_union->get_expr();
        if (!su_expr)
            return false;
        expr_ref stab_star(seq.re.mk_star(su_expr), mgr);
        euf::snode* stab_star_sn = m_sg.mk(stab_star);
        if (!stab_star_sn)
            return false;

        // 4. Collect all primitive regex constraints on variable `first`
        euf::snode* x_range = collect_primitive_regex_intersection(first, node, dep);
        if (!x_range)
            return false;

        // 5. Check L(x_range) ⊆ L(stab_star)
        lbool result = is_language_subset(x_range, stab_star_sn);
        return result == l_true;
#else
        return false;
#endif
    }

    char_set seq_regex::minterm_to_char_set(expr* re_expr) {
        seq_util& seq = m_sg.get_seq_util();
        unsigned max_c = seq.max_char();

        if (!re_expr)
            return char_set::full(max_c);

        // full_char: the whole alphabet [0, max_char]
        if (seq.re.is_full_char(re_expr))
            return char_set::full(max_c);

        // range [lo, hi] (hi inclusive in Z3's regex representation)
        expr* lo_expr = nullptr;
        expr* hi_expr = nullptr;
        if (seq.re.is_range(re_expr, lo_expr, hi_expr)) {
            unsigned lo = 0, hi = 0;
            bool has_lo = false, has_hi = false;

            if (lo_expr) {
                if (m_sg.decode_re_char(lo_expr, lo)) {
                    has_lo = true;
                }
            }
            if (hi_expr) {
                if (m_sg.decode_re_char(hi_expr, hi)) {
                    has_hi = true;
                }
            }

            if (has_lo && has_hi) {
                SASSERT(lo <= hi);
                if (lo > hi)
                    return char_set();
                // char_range uses exclusive upper bound; Z3 hi is inclusive
                return char_set(char_range(lo, hi + 1));
            }
        }

        // complement: alphabet minus the inner set
        expr* inner = nullptr;
        if (seq.re.is_complement(re_expr, inner))
            return minterm_to_char_set(inner).complement(max_c);

        // union: characters present in either set
        expr* r1 = nullptr, *r2 = nullptr;
        if (seq.re.is_union(re_expr, r1, r2)) {
            char_set cs = minterm_to_char_set(r1);
            cs.add(minterm_to_char_set(r2));
            return cs;
        }

        // intersection: characters present in both sets
        if (seq.re.is_intersection(re_expr, r1, r2))
            return minterm_to_char_set(r1).intersect_with(minterm_to_char_set(r2));

        // difference: r1 minus r2 = r1 ∩ complement(r2)
        if (seq.re.is_diff(re_expr, r1, r2))
            return minterm_to_char_set(r1).intersect_with(
                       minterm_to_char_set(r2).complement(max_c));

        // to_re(str.unit(c)): singleton character set
        expr* str_arg = nullptr;
        unsigned char_val = 0;
        if (seq.re.is_to_re(re_expr, str_arg) && m_sg.decode_re_char(str_arg, char_val)) {
            char_set cs;
            cs.add(char_val);
            return cs;
        }

        // empty regex: no characters can appear
        if (seq.re.is_empty(re_expr))
            return char_set();

        // Unexpected minterm shape: we should fail loudly instead of silently
        // returning a conservative approximation.
        UNREACHABLE();
        return char_set::full(max_c);
    }

}


