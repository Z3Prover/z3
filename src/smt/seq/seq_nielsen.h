/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen.h

Abstract:

    Nielsen graph for string constraint solving.

    The Nielsen graph is used for solving word equations and regex
    membership constraints via Nielsen transformations. Each node
    contains a set of constraints (string equalities, regex memberships,
    integer equalities/inequalities) and edges represent substitutions
    that transform one constraint set into another.

    Key components:
    -- str_eq:  string equality constraint (lhs = rhs)
    -- str_mem: regex membership constraint (str in regex)
    -- nielsen_subst: variable substitution (var -> replacement)
    -- nielsen_edge: graph edge with substitutions and side constraints
    -- nielsen_node: graph node with constraint set and outgoing edges
    -- nielsen_graph: the overall Nielsen transformation graph

Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/euf/euf_mam.h"
#include "ast/euf/euf_sgraph.h"
#include "ast/rewriter/arith_rewriter.h"
#include "model/model.h"
#include "util/lbool.h"
#include "util/dependency.h"
#include "util/map.h"
#include "util/obj_ref_hashtable.h"
#include "util/rational.h"
#include "util/uint_set.h"
#include "util/vector.h"
#include <unordered_set>
#include <set>
#include <vector>

namespace smt { class enode; }

namespace seq {

    // forward declarations
    class nielsen_node;
    class nielsen_edge;
    class nielsen_graph;
    class seq_parikh;
    class seq_regex;  // forward declaration (defined in smt/seq/seq_regex.h)

    std::string snode_label_html(euf::snode const* n,
        obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m, bool html_escape);

    std::string snode_label_html(euf::snode const* n, ast_manager& m, bool html_escape);

    // simplification result for constraint processing
    enum class simplify_result {
        proceed,               // no change, continue
        conflict,              // constraint is unsatisfiable
        satisfied,             // constraint is trivially satisfied
        restart,               // constraint was simplified, restart
        restart_and_satisfied, // simplified and satisfied
    };

    // reason for backtracking in the Nielsen graph
    enum class backtrack_reason {
        unevaluated,
        extended,
        symbol_clash,
        parikh_image,
        arithmetic,
        regex,
        sibling,
        regex_widening,
        character_range,
        smt,
        external,
        children_failed,
    };

    // source of a dependency: identifies an input constraint by kind and index.
    // kind::eq means a string equality, kind::mem means a regex membership.
    // index is the 0-based position in the input eq or mem list respectively.

    using enode_pair = std::pair<smt::enode *, smt::enode *>;
    using literal_vector = svector<sat::literal>;
    using enode_pair_vector = svector<enode_pair>;
    using dep_source = std::variant<sat::literal, enode_pair>;

    // Arena-based dependency manager: builds an immutable tree of dep_source
    // leaves joined by binary join nodes.  Memory is managed via a region;
    // call dep_manager::reset() to release all allocations at once.
    using dep_manager = scoped_dependency_manager<dep_source>;

    // dep_tracker is a pointer into the dep_manager's arena.
    // nullptr represents the empty dependency set.
    using dep_tracker = dep_manager::dependency*;

    /**
     * Abstract interface for an incremental solver used by nielsen_graph
     * to check integer/arithmetic feasibility of path constraints.
     *
     * Users of nielsen_graph can wrap smt::kernel or any other solver
     * to serve as the arithmetic back-end.  When no solver is provided,
     * integer feasibility checks are skipped (optimistically assumed feasible).
     */
    class sub_solver_i {
    public:
        virtual ~sub_solver_i() {}
        virtual lbool       check() = 0;
        virtual void        assert_expr(expr* e, dep_tracker dep = nullptr) = 0;
        virtual void        push() = 0;
        virtual void        pop(unsigned num_scopes) = 0;
        virtual void        get_model(model_ref& mdl) { mdl = nullptr; }
        virtual dep_tracker core() { return nullptr; }
        virtual void        reset() = 0;
    };

    class context_solver_i {
    public:
        virtual ~context_solver_i() {}

        bool m_should_internalize = false;

        // Optional bound queries on arithmetic expressions (non-strict integer bounds).
        // Default implementation reports "unsupported".
        virtual bool lower_bound(expr *e, rational &l, literal_vector &lits, enode_pair_vector &eqs) const {
            return false;
        }
        virtual bool upper_bound(expr *e, rational &hi, literal_vector &lits, enode_pair_vector &eqs) const {
            return false;
        }
        virtual bool current_value(expr *e, rational &v) const {
            return false;
        }
        virtual sat::literal literal_if_false(expr* e) {
            return sat::null_literal;
        }
        virtual void add_diseq_axiom(expr* e1, expr* e2) {}

    };

    // partition dep_source leaves from deps into enode pairs, sat literals,
    // and arithmetic <= dependencies.
    void deps_to_lits(dep_manager &dep_mgr, dep_tracker deps, svector<enode_pair> &eqs, svector<sat::literal> &lits);

    // suspended state of a lazy regex factorization (see apply_regex_factorization).
    struct rf_state;

    // decompose a membership constraint into a set of pairs of regex splits.
    // Eagerly materialises the full split-set (used by the eager propagation path
    // in theory_nseq::propagate_pos_mem); the lazy Nielsen path uses rf_state.
    std::pair<euf::snode const*, euf::snode const*> split_membership(euf::snode const* str, euf::snode const* regex, euf::sgraph& sg, unsigned threshold, split_set& result);

    // Lookahead oracle for the split engine: is the split's right component
    // `n_regex` prefix-compatible with the constant character sequence `c`?
    // The factorization picks a boundary so the tail starts with c, hence the
    // tail-regex ∇ must be able to match c as a prefix.  We use a *prefix* test
    // (not strict "starts-with"): we accept as soon as N accepts a prefix of c
    // (a suffix appended downstream can complete it).  This is sound to apply
    // during split generation — it never drops a viable split.
    bool split_lookahead_viable(expr* n_regex, euf::sgraph& sg, zstring const& c);

    // string equality constraint: lhs = rhs
    struct str_eq {
        ast_manager& m;
        euf::snode const* m_lhs; // assumed to be non-null
        euf::snode const* m_rhs; // assumed to be non-null
        dep_tracker m_dep;

        str_eq(ast_manager& m, euf::snode const* lhs, euf::snode const* rhs, dep_tracker const& dep):
            m(m), m_lhs(lhs), m_rhs(rhs), m_dep(dep) {
            SASSERT(well_formed());
            sort();
        }

        str_eq& operator=(const str_eq & other) {
            m_lhs = other.m_lhs;
            m_rhs = other.m_rhs;
            m_dep = other.m_dep;
            return *this;
        }

        bool operator==(const str_eq& other) const {
            return m_lhs->similar(other.m_lhs, m) && m_rhs->similar(other.m_rhs, m);
        }

        bool operator<(const str_eq& other) const {
            if (m_lhs != other.m_lhs)
                return m_lhs < other.m_lhs;
            return m_rhs < other.m_rhs;
        }

        unsigned hash() const {
            return 586947209 * m_lhs->assoc_hash() + m_rhs->assoc_hash();
        }

        // sort so that lhs <= rhs by snode id
        void sort();

        // check if both sides are empty (trivially satisfied)
        bool is_trivial() const;

        // check if the constraint contains a given variable
        bool contains_var(euf::snode const* var) const;

        bool well_formed() const {
            // assumed to be always true
            return m_lhs && m_rhs;
        }
    };

    struct eq_pp {
        str_eq const &eq;
        eq_pp(str_eq const &e) : eq(e) {}
    };

    inline std::ostream &operator<<(std::ostream &out, eq_pp const &p) {
        return out << snode_label_html(p.eq.m_lhs, p.eq.m, false)
            << " == "
            << snode_label_html(p.eq.m_rhs, p.eq.m, false);
    }

    // string disequality constraint: lhs != rhs
    struct str_deq {
        ast_manager& m;
        euf::snode const* m_lhs; // assumed to be non-null
        euf::snode const* m_rhs; // assumed to be non-null
        dep_tracker m_dep;

        str_deq(ast_manager& m, euf::snode const* lhs, euf::snode const* rhs, dep_tracker const& dep):
            m(m), m_lhs(lhs), m_rhs(rhs), m_dep(dep) {
            SASSERT(well_formed());
            sort();
        }

        str_deq& operator=(const str_deq & other) {
            m_lhs = other.m_lhs;
            m_rhs = other.m_rhs;
            m_dep = other.m_dep;
            return *this;
        }

        bool operator==(const str_deq& other) const {
            return m_lhs->similar(other.m_lhs, m) && m_rhs->similar(other.m_rhs, m);
        }

        bool operator<(const str_deq& other) const {
            if (m_lhs != other.m_lhs)
                return m_lhs < other.m_lhs;
            return m_rhs < other.m_rhs;
        }

        unsigned hash() const {
            return 891170543 * m_lhs->assoc_hash() + m_rhs->assoc_hash();
        }

        void sort() {
            if (m_lhs->id() > m_rhs->id()) {
                std::swap(m_lhs, m_rhs);
            }
        }

        bool contains_var(euf::snode const* var) const {
            return m_lhs->collect_tokens().contains(var) || m_rhs->collect_tokens().contains(var);
        }

        bool well_formed() const {
            // assumed to be always true
            return m_lhs && m_rhs;
        }
    };

    struct deq_pp {
        str_deq const &deq;
        deq_pp(str_deq const &e) : deq(e) {}
    };

    inline std::ostream &operator<<(std::ostream &out, deq_pp const &p) {
        return out << snode_label_html(p.deq.m_lhs, p.deq.m, false)
            << " != "
            << snode_label_html(p.deq.m_rhs, p.deq.m, false);
    }

    // kind of a regex membership constraint (paper §5.3, "land-state views"):
    //  - plain:     ordinary u ∈ r
    //  - stab_view: land-state view  u ∈_{Q,{s}} r   (acceptance set F={s})
    //               (the stabilizer is the special case s = r).
    // For a view, m_regex holds the *current derivative state* (a plain regex;
    // starts at the head r) and m_root holds the landing/acceptance state s.
    // Q is identified by the ν-index m_nu over the partial DFA
    // (projection_state_in_Q).  m_regex is always a plain regex.
    // The old two-mode `no_loop` cycle guard has been removed: landing
    // decomposition (paper §5.3) needs no guard.
    enum class mem_kind : unsigned char { plain, stab_view };

    // regex membership constraint: str in regex
    struct str_mem {
        ast_manager& m;
        euf::snode const* m_str; // assumed to be non-null
        euf::snode const* m_regex; // assumed to be non-null (plain regex = current run state)
        dep_tracker m_dep;

        // land-state view annotation (paper §5.3)
        mem_kind          m_kind = mem_kind::plain;
        euf::snode const* m_root = nullptr;  // landing/acceptance state s (view F={s}; stabilizer: s=head)
        unsigned          m_nu = 0;          // ν: snapshot index identifying Q

        str_mem(ast_manager& m, euf::snode const* str, euf::snode const* regex, dep_tracker const& dep):
            m(m), m_str(str), m_regex(regex), m_dep(dep) {}

        str_mem& operator=(const str_mem& other) {
            m_str = other.m_str;
            m_regex = other.m_regex;
            m_dep = other.m_dep;
            m_kind = other.m_kind;
            m_root = other.m_root;
            m_nu = other.m_nu;
            return *this;
        }

        // factory for a land-state view  str ∈_{Q_ν,{root}} state  (m_regex=state,
        // root = landing/acceptance state s; the stabilizer is state=root=head).
        static str_mem mk_view(ast_manager& m, euf::snode const* str, euf::snode const* state,
                               euf::snode const* root, unsigned nu, dep_tracker const& dep) {
            str_mem r(m, str, state, dep);
            r.m_kind = mem_kind::stab_view; r.m_root = root; r.m_nu = nu;
            return r;
        }

        bool is_plain() const { return m_kind == mem_kind::plain; }
        bool is_view()  const { return m_kind == mem_kind::stab_view; }

        bool operator==(const str_mem& other) const {
            return m_str->similar(other.m_str, m) && m_regex == other.m_regex
                && m_kind == other.m_kind && m_root == other.m_root
                && m_nu == other.m_nu;
        }

        bool operator<(const str_mem& other) const {
            // Regex-factorization heuristic: order primarily by the estimated
            // automaton size of the regex so that the cheapest membership is
            // factorized first (see snode::regex_weight / sgraph::compute_regex_weight).
            // The remaining pointer comparisons are just deterministic tie-breakers
            // to keep this a total order for canonicalization/sorting.
            const unsigned w1 = m_regex->regex_weight();
            const unsigned w2 = other.m_regex->regex_weight();
            if (w1 != w2)
                return w1 < w2;
            if (m_str != other.m_str)
                return m_str < other.m_str;
            return m_regex < other.m_regex;
        }

        unsigned hash() const {
            return 381416603 * m_str->assoc_hash() + m_regex->assoc_hash();
        }

        // check if the constraint has the form x in R with x a single variable
        bool is_primitive() const;

        // TODO: These two functions need to aware of the truth of the ite-guards of the symbolic derivations
        bool is_trivial(nielsen_node const* n) const;

        bool is_contradiction(nielsen_node const* n) const;

        // check if the constraint contains a given variable
        bool contains_var(euf::snode const* var) const;

        bool well_formed() const {
            // assumed to be always true
            return m_str && m_regex;
        }
    };

    struct mem_pp {
        str_mem const& mem;
        mem_pp(str_mem const& mem) : mem(mem) {}
    };
    inline std::ostream &operator<<(std::ostream &out, mem_pp const &p) {
        return out
            << snode_label_html(p.mem.m_str, p.mem.m, false)
            << " in "
            << snode_label_html(p.mem.m_regex, p.mem.m, false);
    }

    // string variable substitution: var -> replacement
    // (can be used as well to substitute arbitrary nodes - like powers)
    struct nielsen_subst {
        euf::snode const* m_var;
        euf::snode const* m_replacement;
        dep_tracker m_dep;

        nielsen_subst(): m_var(nullptr), m_replacement(nullptr), m_dep(nullptr) {}
        nielsen_subst(euf::snode const* var, euf::snode const* repl, dep_tracker const& dep):
            m_var(var), m_replacement(repl), m_dep(dep) {
            SASSERT(var != nullptr);
            SASSERT(repl != nullptr);
            // var may be s_var or s_power; sgraph::subst uses pointer identity matching
            SASSERT(var->is_var() || var->is_power() || var->is_unit());
            SASSERT(!var->is_unit() || repl->is_char_or_unit());
            SASSERT(!repl->collect_tokens().contains(var)); // for now - maybe we want to drop this later again
        }

        // an eliminating substitution does not contain the variable in the replacement
        bool is_eliminating() const;

        bool is_char_subst() const;

        bool operator==(nielsen_subst const& other) const {
            return m_var == other.m_var && m_replacement == other.m_replacement;
        }
    };

    // -----------------------------------------------
    // integer constraint: equality or inequality over length expressions
    // -----------------------------------------------

    // integer constraint stored per nielsen_node, tracking arithmetic
    // relationships between length variables and power exponents.
    struct constraint {
        expr_ref    fml;   // the formula (eq, le, or ge, unit-diseq expression)
        dep_tracker dep;   // tracks which input constraints contributed

        static expr_ref simplify(expr* f, ast_manager& m) {
            //arith_rewriter th(m);
            //th_rewriter th(m);
            expr_ref fml(f, m);
            //th(fml);
            return fml;
        }

        constraint(ast_manager& m):
            fml(m), dep(nullptr) {}

        constraint(expr* f, dep_tracker const& d, ast_manager& m):
            fml(simplify(f, m)), dep(d) {}

        std::ostream& display(std::ostream& out) const;
    };

    // kind of length constraint determines propagation strategy
    enum class length_kind {
        nonneg,   // len(x) >= 0: unconditional axiom
        eq,       // len(lhs) = len(rhs): conditional on string equality
        bound     // Parikh bound: conditional on regex membership
    };

    // arithmetic length constraint derived from string equations
    struct length_constraint {
        expr_ref    m_expr;  // arithmetic expression (e.g., len(x) + len(y) = len(a) + 1)
        dep_tracker m_dep;   // tracks which input constraints contributed
        length_kind m_kind;  // determines propagation strategy

        length_constraint(ast_manager& m): m_expr(m), m_dep(nullptr), m_kind(length_kind::nonneg) {}
        length_constraint(expr* e, dep_tracker const& dep, length_kind kind, const bool internal, ast_manager& m):
            m_expr(e, m), m_dep(dep), m_kind(kind) {}

        constraint to_constraint() const {
            return constraint(m_expr, m_dep, m_expr.get_manager());
        }
    };

    // edge in the Nielsen graph connecting two nodes
    class nielsen_edge {
        nielsen_node*           m_src;
        nielsen_node*           m_tgt;
        const char* const       m_rule_name;
        vector<nielsen_subst>   m_subst;
        vector<constraint>      m_side_constraints;  // side constraints: integer equalities/inequalities
        bool                    m_is_progress;     // does this edge represent progress?
        bool                    m_len_constraints_computed = false; // lazily computed substitution length constraints

    public:
        nielsen_edge(nielsen_node* src, nielsen_node* tgt, const char* rule, bool is_progress);

        nielsen_node* src() const { return m_src; }
        nielsen_node* tgt() const { return m_tgt; }
        const char* rule_name() const { return m_rule_name; }

        void set_tgt(nielsen_node* tgt) { m_tgt = tgt; }

        // don't forget to add the substitution
        // applying it only to the node is NOT sufficient (otw. length counters are not in sync)
        vector<nielsen_subst> const& subst() const { return m_subst; }
        void add_subst(nielsen_subst const& s);

        void add_side_constraint(constraint const& ic) {
            if (ic.fml.m().is_true(ic.fml))
                return;
            expr* a, * b;
            if (ic.fml.m().is_and(ic.fml, a, b)) {
                add_side_constraint(constraint(a, ic.dep, ic.fml.m()));
                add_side_constraint(constraint(b, ic.dep, ic.fml.m()));
                return;
            }
            m_side_constraints.push_back(ic);
        }
        vector<constraint> const& side_constraints() const { return m_side_constraints; }

        bool is_progress() const { return m_is_progress; }

        bool len_constraints_computed() const { return m_len_constraints_computed; }
        void set_len_constraints_computed(bool v) { m_len_constraints_computed = v; }

        bool operator==(nielsen_edge const& other) const {
            return m_src == other.m_src && m_tgt == other.m_tgt;
        }
    };

    // node in the Nielsen graph
    class nielsen_node {
        friend class nielsen_graph;

        unsigned                m_id;
        nielsen_graph&          m_graph;

        // constraints at this node
        vector<str_eq>     m_str_eq;        // string equalities
        vector<str_deq>    m_str_deq;       // string disequalities
        vector<str_mem>    m_str_mem;       // regex memberships
        vector<constraint> m_constraints;   // integer equalities/inequalities
        sat::literal m_conflict_external_literal = sat::null_literal;
        dep_tracker  m_conflict_internal = nullptr;

        // character constraints
        // key: snode id of the s_unit symbolic character
        u_map<std::pair<char_set, dep_tracker>>            m_char_ranges;   // ?c in [lo, hi)

        // edges
        ptr_vector<nielsen_edge> m_outgoing;
        nielsen_edge*           m_parent_edge = nullptr;

        // status flags
        bool                    m_is_general_conflict = false;
        bool                    m_is_extended = false;
        backtrack_reason        m_reason = backtrack_reason::unevaluated;
        bool                    m_is_progress = false;
        bool                    m_node_len_constraints_generated = false; // true after generate_node_length_constraints runs

        unsigned                m_hash = 0; // 0 ... unset

        nielsen_node*            m_parent = this;

        // DFS bookkeeping for the subsumption (loop-cut) rule.
        //  m_dfs_path_pos:    structural depth (= cur_path.size()) of this node while
        //                     it is on the active DFS path; read by a descendant that
        //                     loops back to it as a sibling.
        //  m_subtree_lowlink: minimum structural depth that this node's UNSAT closure
        //                     escapes to via sibling cuts below it (Tarjan-style
        //                     lowlink).  UINT_MAX means "no cut escapes" — the unsat
        //                     is self-contained.  Only meaningful when the node's last
        //                     result was unsat.
        unsigned                m_dfs_path_pos    = 0;
        unsigned                m_subtree_lowlink = UINT_MAX;
        //  m_subtree_has_cut: a sibling loop-cut occurred somewhere in this node's
        //  closed subtree.  A cut defers to an ancestor whose ARITHMETIC side
        //  constraints differ, so it is only a valid UNSAT witness inside a closure
        //  that uses string-only reasons throughout.  When a cut coexists with a
        //  non-string-only (arithmetic / external) conflict the subtree result is
        //  NOT a sound UNSAT — search_dfs reports unknown instead.
        bool                    m_subtree_has_cut = false;

        // true once this node has been proven UNSAT for reasons that depend only
        // on its string/regex constraints (not on arithmetic / Parikh / external
        // context).  Such an unsat is a property of the node's string signature
        // and is safe to memoize in the transposition table (m_unsat_node_cache).
        bool                    m_unsat_cacheable = false;

        // Parikh filter: set to true once apply_parikh_to_node has been applied
        // to this node. Prevents duplicate constraint generation across DFS runs.
        bool                    m_parikh_applied = false;

        // Lazy regex factorization continuation.  Set only on a "remaining splits"
        // child created by apply_regex_factorization: it carries the suspended
        // split iterator so factorization resumes from the next split when this
        // node is extended.  Owned by nielsen_graph::m_rf_states (raw pointer here).
        rf_state*               m_rf_cont = nullptr;
        // Sticky marker: true once this node was ever created as a factorization
        // continuation (child B), even after its iterator has been consumed
        // (m_rf_cont reset to null when the node is extended).  The subsumption
        // loop-cut and unsat-cache exemptions (§1.6b) are a PERMANENT structural
        // property of a continuation node — it aliases its parent's string
        // signature yet is not a recurrence — so they must survive the hot-restart
        // re-traversal, where m_rf_cont is already null.  See search_dfs.
        bool                    m_is_rf_cont = false;
        // number of constraints inherited from the parent node at clone time.
        // constraints[0..m_parent_ic_count) are already asserted at the
        // parent's solver scope; only [m_parent_ic_count..end) need to be
        // asserted when this node's solver scope is entered.
        unsigned                m_parent_ic_count = 0;

    public:
        nielsen_node(nielsen_graph& graph, unsigned id);

        unsigned id() const { return m_id; }
        nielsen_graph& graph() const { return m_graph; }

        // constraint access
        vector<str_eq> const& str_eqs() const { return m_str_eq; }
        vector<str_eq>& str_eqs() { return m_str_eq; }
        vector<str_deq> const& str_deqs() const { return m_str_deq; }
        vector<str_deq>& str_deqs() { return m_str_deq; }
        vector<str_mem> const& str_mems() const { return m_str_mem; }
        vector<str_mem>& str_mems() { return m_str_mem; }

        void add_str_eq(const str_eq& eq);
        void add_str_deq(const str_deq& deq);
        void add_str_mem(const str_mem& mem);
        void add_constraint(const constraint &ic);

        vector<constraint> const& constraints() const { return m_constraints; }
        vector<constraint>& constraints() { return m_constraints; }

        bool is_external_conflict() const { return m_conflict_external_literal != sat::null_literal; }

        sat::literal get_external_conflict_literal() const { return m_conflict_external_literal; }

        // Query current bounds for a variable from the arithmetic subsolver.
        // Falls der Subsolver keinen Bound liefert, werden konservative Defaults
        // 0 / UINT_MAX verwendet.
        bool lower_bound(expr* e, rational& lo, dep_tracker& dep);
        bool upper_bound(expr* e, rational& up, dep_tracker& dep);

        // character constraint access
        u_map<std::pair<char_set, dep_tracker>>& char_ranges() { return m_char_ranges; }
        u_map<std::pair<char_set, dep_tracker>> const &char_ranges() const {
            return m_char_ranges;
        }

        // add a character range constraint for a symbolic char.
        // intersects with existing range; sets conflict if result is empty.
        void add_char_range(euf::snode const* sym_char, char_set const& range, dep_tracker dep);

        // edge access
        ptr_vector<nielsen_edge> const& outgoing() const { return m_outgoing; }
        void add_outgoing(nielsen_edge* e) { m_outgoing.push_back(e); }

        nielsen_edge* parent_edge() const { return m_parent_edge; }
        void set_parent_edge(nielsen_edge* e) { m_parent_edge = e; }

        // lazy regex factorization continuation (see m_rf_cont).
        rf_state* rf_cont() const { return m_rf_cont; }
        void set_rf_cont(rf_state* s) { m_rf_cont = s; if (s) m_is_rf_cont = true; }
        // Sticky: true if this node was ever a factorization continuation, even
        // after its iterator has been consumed.  Drives the loop-cut / unsat-cache
        // exemptions so they persist across the hot-restart re-traversal.
        bool is_rf_cont() const { return m_is_rf_cont; }

        // returns 0 if hash is unknown
        unsigned hash() const {
            return m_hash;
        }

        // status
        bool is_general_conflict() const { return m_is_general_conflict; }
        void set_general_conflict() {
            m_is_general_conflict = true;
        }

        bool is_extended() const { return m_is_extended; }
        void set_extended(const bool v) {
            m_is_extended = v;
        }

        bool is_currently_conflict() const {
            return is_general_conflict() ||
                m_conflict_external_literal != sat::null_literal ||
                // a sibling (loop-cut / subsumption) conflict counts even when the
                // node was never extended (a cut leaf has no children).
                reason() == backtrack_reason::sibling ||
                (reason() != backtrack_reason::unevaluated && m_is_extended);
        }

        void clear_local_conflict() {
            SASSERT(!is_general_conflict());
            m_reason = backtrack_reason::unevaluated;
            m_conflict_internal = nullptr;
            m_conflict_external_literal = sat::null_literal;
        }

        backtrack_reason reason() const { return m_reason; }

        void clear_reason() { m_reason = backtrack_reason::unevaluated; }

        void set_child_conflict() {
            SASSERT(m_reason == backtrack_reason::unevaluated);
            SASSERT(!m_conflict_internal);
            SASSERT(m_conflict_external_literal == sat::null_literal);
            m_reason = backtrack_reason::children_failed;
        }

        void set_conflict(backtrack_reason r, dep_tracker confl);

        void set_external_conflict(sat::literal lit, dep_tracker confl);

        bool is_progress() const { return m_is_progress; }

        // clone constraints from a parent node
        void clone_from(nielsen_node const& parent);

        // apply a substitution to all constraints
        void apply_subst(euf::sgraph& sg, nielsen_subst const& s);

        // Transposition table helpers (node memoization of string-only UNSAT).
        // after computing the signature we should not change the node anymore
        // the hash disregards length constraints on purpose for subsumption checks
        unsigned canonize_and_compute_node_hash();

        unsigned canonize_and_compute_final_node_hash() {
            if (m_hash)
                return m_hash;
            m_hash = canonize_and_compute_node_hash();
            return m_hash;
        }

        // check if two nodes are equivalent modulo side-constraints
        // (actually subset checks would be better but we currently do not track this)
        bool is_node_sibling(nielsen_node const* n);

        // simplify all constraints at this node and initialize status.
        // Uses cur_path for LP solver queries during deterministic power cancellation.
        // Returns proceed, conflict, satisfied, or restart.
        simplify_result simplify_and_init(ptr_vector<nielsen_edge> const& cur_path);

        // Consume leading concrete/symbolic characters of a land-state view
        // membership (paper §5.3): gate on Q_ν, step with the ordinary
        // derivative, keeping the annotation.  Returns true if the view died
        // (left Q or derivative collapsed to ∅) — caller reports a regex conflict.
        bool consume_view(str_mem& mem);

        // true if all str_eqs are trivial and there are no str_mems
        bool is_satisfied() const;

        // true if ANY equality/disequality/membership references a rigid (defined) op
        // snode (str.replace, str.replace_all, str.replace_re*). Used to defer to the
        // axiom layer (FC_GIVEUP) before searching: these terms are not free variables
        // but are pinned by the recfun/axiom layer, and the Nielsen modifiers would
        // substitute/unify them as if free, discarding their definition and producing
        // invalid models.
        bool references_rigid() const;

        // render constraint set as an HTML fragment for DOT node labels.
        std::ostream& to_html(std::ostream& out, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m) const;

        std::ostream& to_html(std::ostream& out, ast_manager& m) const;

    private:
        // Helper: handle one empty vs one non-empty side of a string equality.
        // Collects tokens from non_empty_side; if any token causes a conflict
        // (is a concrete character or an unexpected kind), sets conflict flags
        // and returns true. Otherwise returns false.
        bool check_empty_side_conflict(euf::sgraph& sg, euf::snode const* non_empty_side,
                                       dep_tracker const& dep);

        // Length bounds are queried from the arithmetic subsolver when needed.
    };

    struct nielsen_node_hash {
        // outputs the hash without side-constraints
        unsigned operator()(nielsen_node* n) const {
            const unsigned h = n->hash();
            if (h == 0)
                return n->canonize_and_compute_node_hash();
            return h;
        }
    };

    struct nielsen_node_eq {
        unsigned operator()(nielsen_node* n1, nielsen_node* n2) const {
            return n1->is_node_sibling(n2);
        }
    };

    // search statistics collected during Nielsen graph solving
    struct nielsen_stats {
        unsigned m_num_solve_calls     = 0;
        unsigned m_num_eager_calls     = 0;
        unsigned m_num_dfs_nodes       = 0;
        unsigned m_num_sat             = 0;
        unsigned m_num_unsat           = 0;
        unsigned m_num_unknown         = 0;
        unsigned m_num_simplify_conflict = 0;
        unsigned m_num_extensions      = 0;
        unsigned m_num_fresh_vars      = 0;
        unsigned m_num_arith_infeasible = 0;
        unsigned m_max_depth           = 0;
        // modifier application counts
        unsigned m_mod_det             = 0;
        unsigned m_mod_power_epsilon   = 0;
        unsigned m_mod_num_cmp         = 0;
        unsigned m_mod_split_power_elim = 0;
        unsigned m_mod_const_num_unwinding = 0;
        unsigned m_mod_regex_if_split = 0;
        unsigned m_mod_eq_split        = 0;
        unsigned m_mod_star_intr       = 0;
        unsigned m_mod_cycle_subsumption = 0;
        unsigned m_mod_view_land       = 0;
        unsigned m_mod_gpower_intr     = 0;
        unsigned m_mod_regex_factorization = 0;
        unsigned m_mod_const_nielsen   = 0;
        unsigned m_mod_regex_var_split = 0;
        unsigned m_mod_signature_split = 0;
        unsigned m_mod_power_split     = 0;
        unsigned m_mod_var_nielsen     = 0;
        unsigned m_mod_var_num_unwinding_eq = 0;
        unsigned m_mod_var_num_unwinding_mem = 0;
        unsigned m_ax_diseq = 0;
        // subsumption rule
        unsigned m_num_sibling_cut     = 0; // loop-cut leaves (deferred to an ancestor)
        unsigned m_num_sibling_closure = 0; // subtrees closed as string-only sibling conflicts
        void reset() { memset(this, 0, sizeof(nielsen_stats)); }
    };

    struct unsigned_eq {
        bool operator()(unsigned x, unsigned y) const { return x == y; }
    };

    // the overall Nielsen transformation graph
    class nielsen_graph {
        friend class nielsen_node;
        friend class nielsen_edge;

        // Edge endpoints are stored as expr* (not snode const*) because the cache
        // must survive sgraph pops.  snodes are allocated in a region that is
        // never freed, but their m_expr field is owned by the egraph trail and
        // becomes dangling on pop.  We pin the referenced expressions via
        // m_partial_dfa_pin so their ids stay stable, and we recover an snode
        // at the current scope via m_sg.mk(expr) only when we actually need one.
        struct partial_dfa_edge {
            expr* m_src = nullptr;
            //expr* m_label = nullptr; // one-character regex label (char/minterm)
            expr* m_dst = nullptr;
        };

        struct partial_dfa_edge_key {
            unsigned m_src = 0;
            unsigned m_label = 0;
            unsigned m_dst = 0;

            bool operator==(partial_dfa_edge_key const& o) const {
                return m_src == o.m_src && m_label == o.m_label && m_dst == o.m_dst;
            }
        };

        struct partial_dfa_edge_key_hash {
            size_t operator()(partial_dfa_edge_key const& k) const {
                size_t h = k.m_src;
                h = (h * 1315423911u) ^ static_cast<size_t>(k.m_label + 0x9e3779b9u);
                h = (h * 2654435761u) ^ static_cast<size_t>(k.m_dst + 0x85ebca6bu);
                return h;
            }
        };

        ast_manager&                  m;
        arith_util                    a;
        seq_util&                     m_seq;
        euf::sgraph&                  m_sg;
        th_rewriter                   m_rw;
        arith_rewriter                m_a_rw;
        skolem                        m_sk;
        ptr_vector<nielsen_node>      m_nodes;
        ptr_vector<nielsen_edge>      m_edges;
        nielsen_node*                 m_root = nullptr;
        nielsen_node*                 m_sat_node = nullptr;
        ptr_vector<nielsen_edge>      m_sat_path;
        unsigned                      m_depth_bound = 0;
        unsigned                      m_max_search_depth = 0;
        unsigned                      m_max_nodes = 0;          // 0 = unlimited
        bool                          m_parikh_enabled = true;
        bool                          m_signature_split = false;
        unsigned                      m_regex_factorization_threshold = 1;
        bool                          m_regex_factorization_eager = false;
        bool                          m_regex_dynamic_decomposition = true;
        unsigned                      m_harvest = 0;            // 0 = disabled (benchmark-harvest bound)
        std::string                   m_harvest_dir = ".";
        unsigned                      m_harvest_counter = 0;    // file index; spans reset()/blocking iterations
        std::unordered_set<unsigned>  m_harvested_hashes;       // dedup by structural hash; NOT cleared in reset()
        unsigned                      m_fresh_cnt = 0;
        nielsen_stats                 m_stats;


        // -----------------------------------------------
        // Integer subsolver (abstract interface)
        // -----------------------------------------------
        sub_solver_i& m_length_solver;

        // -----------------------------------------------
        // Interface to solver context
        // -----------------------------------------------
        context_solver_i &m_context_solver;

        // Constraint.Shared: guards re-assertion of root-level constraints.
        // Set to true after assert_root_constraints_to_solver() is first called.
        bool                          m_root_constraints_asserted = false;

        // Parikh image filter: generates modular length constraints from regex
        // memberships.  Allocated in the constructor; owned by this graph.
        seq_parikh*                   m_parikh = nullptr;

        // Regex membership module: stabilizers, emptiness checks, language
        // inclusion, derivatives. Allocated in the constructor; owned by this graph.
        seq_regex*              m_seq_regex = nullptr;

        // Persistent split engine driving the lazy regex factorization
        // (apply_regex_factorization).  A single instance kept here so the
        // suspended split iterators stored in m_rf_states stay valid across
        // search_dfs recursion and iterative deepening.
        seq_rewriter            m_split_rw;
        // Owns the suspended factorization continuations (rf_state); nodes hold
        // raw pointers into this pool.  Freed in reset().
        ptr_vector<rf_state>    m_rf_states;


        // Maps each variable to its current length term
        // ptr_vector<euf::snode>        m_length_trail;
        // u_map<euf::snode *>           m_length_info;
        u_map<unsigned>               m_mod_cnt;

        // Arena for dep_tracker nodes.  Declared mutable so that const methods
        // (e.g., explain_conflict) can call mk_join / linearize.
        mutable dep_manager           m_dep_mgr;

        // Global partial derivative DFA (monotone across DFS/backtracking and
        // across sgraph push/pop).  States are regex expressions (pinned in
        // m_partial_dfa_pin); edges are discovered derivatives labeled by
        // one-character regexes (concrete chars or minterms).
        // All maps below are keyed by expr->get_id(): stable for as long as
        // the expression is pinned, unlike snode->id() which is reused on pop.
        vector<partial_dfa_edge>      m_partial_dfa_edges;
        std::unordered_map<unsigned, unsigned_vector> m_partial_dfa_out;
        std::unordered_map<partial_dfa_edge_key, unsigned, partial_dfa_edge_key_hash> m_partial_dfa_edge_index;
        // Pins every expression referenced by m_partial_dfa_edges so the
        // egraph cannot release them on pop.  We never shrink this — the
        // cache is meant to be monotone.
        expr_ref_vector               m_partial_dfa_pin;
        // Monotone snapshot index ν, bumped whenever a new view state set is
        // recorded (mark_reachable_projection_edges).  A view's Q is the EXACT
        // snapshot stored under its ν in m_projection_snapshots (the paper's
        // "recorded state set Q" of a view, Implementation Aspects).
        unsigned                      m_projection_extract_idx = 0;
        // ν → the snapshot of Q taken when the view index was minted.  The
        // state exprs are pinned via m_partial_dfa_pin, so the stored expr*
        // (and their ids) stay valid across sgraph pops.
        struct projection_snapshot {
            uint_set         m_ids;    // expr ids of the states of Q
            ptr_vector<expr> m_states; // the states themselves
        };
        std::unordered_map<unsigned, projection_snapshot> m_projection_snapshots;
        // head expr id → (partial-DFA edge count at snapshot time, ν).  The
        // partial DFA only grows, so an unchanged edge count means the head's
        // reachable set — hence its snapshot — is unchanged and ν is reused
        // instead of minting a fresh snapshot per decomposition.
        std::unordered_map<unsigned, std::pair<unsigned, unsigned>> m_projection_head_cache;
        // Expr ids of regex states whose full reachable automaton has already
        // been recorded into the partial DFA (lazy, once-per-component Q growth;
        // see ensure_automaton_explored).
        uint_set                      m_explored_automaton;

        // Active-path index for the subsumption rule, keyed structurally (nodes
        // with identical string constraints share a bucket).  While a node is on
        // the DFS path it is pushed onto its bucket and popped on leaving, so a
        // non-empty bucket for the current node holds exactly the ancestor(s) it
        // is a sibling of — i.e. a loop back up the Nielsen tree.
        std::unordered_map<nielsen_node*, vector<nielsen_node*>, nielsen_node_hash, nielsen_node_eq> m_siblings;

        // Transposition table: structural signatures of nodes already proven
        // UNSAT for string/regex-only reasons.  A node whose signature is present
        // is unsatisfiable regardless of how it was reached, so the DFS can prune
        // it without re-exploring its subtree (turns the search tree into the
        // finite DAG the termination proof bounds).  See compute_node_signature.
        std::unordered_set<nielsen_node*, nielsen_node_hash, nielsen_node_eq> m_unsat_node_cache;
        unsigned m_num_cache_hits = 0;

        // Incremental eager-closure chain state (see eager_begin / eager_close).
        // The chain is a single deterministic path root → … → m_eager_leaf;
        // m_eager_substs is its composed substitution (root→leaf order), applied to
        // late-arriving constraints so they land in leaf coordinates.
        bool                  m_eager_active = false;
        nielsen_node*         m_eager_leaf = nullptr;
        vector<nielsen_subst> m_eager_substs;

        // apply the accumulated chain substitution to a single snode, joining the
        // substitutions' deps into `dep`.
        euf::snode const* eager_rewrite(euf::snode const* s, dep_tracker& dep);


    public:
        // Construct with a caller-supplied solver.  Ownership is NOT transferred;
        // the caller is responsible for keeping the solver alive.
        nielsen_graph(euf::sgraph& sg, sub_solver_i& solver, context_solver_i& ctx);
        ~nielsen_graph();


        ast_manager& get_manager() const {
            return m;
        }
        
        euf::sgraph& sg() const { return m_sg; }
        seq_util& seq() { return m_seq; }
        seq_util const& seq() const { return m_seq; }

        // true iff regex `state` is part of the explored subautomaton snapshot
        // `nu` — i.e. state ∈ Q_ν (a partial-DFA edge incident to `state` was
        // marked with an index in [1, nu]).  Used to gate view/guard derivation.
        bool projection_state_in_Q(expr* state, unsigned nu);

        // node management
        nielsen_node* mk_node();
        nielsen_node* mk_child(nielsen_node* parent);

        // edge management
        nielsen_edge* mk_edge(nielsen_node *src, nielsen_node *tgt, const char *rule, bool is_progress);

        // root node access
        nielsen_node* root() const { return m_root; }
        void set_root(nielsen_node* n) {
            SASSERT(n);
            m_root = n;
        }

        // satisfying leaf node (set by solve() when result is sat)
        nielsen_node* sat_node() const { return m_sat_node; }
        void set_sat_node(nielsen_node* n) {
            SASSERT(n);
            SASSERT(!m_sat_node);
            SASSERT(m_sat_path.empty());
            m_sat_node = n;
        }

        void clear_sat_node() {
            m_sat_node = nullptr;
            m_sat_path.clear();
            m_conflict_sources.reset();
        }

        // creates a new root for the graph
        void create_root() {
            SASSERT(!root());
            set_root(mk_node());
            SASSERT(m_root != nullptr);
            SASSERT(m_root->id() == 0);
            SASSERT(m_nodes[0] == m_root);
        }

        // path of edges from root to sat_node (set when sat_node is set)
        ptr_vector<nielsen_edge> const& sat_path() const { return m_sat_path; }

        // Model construction (called by seq_model): build a concrete word for
        // `var` satisfying ALL its primitive constraints on `node` simultaneously
        // (plain regexes AND land-state views), by a shortest-accepting-word
        // product search.  If len != UINT_MAX the word is forced to that exact
        // length (Σ^len factor).  Returns true and sets `out` on success.  Used
        // for view-constrained variables at a SAT leaf, where a land-state view
        // (F={s}, s≠head) does not denote a plain regex and ε may be inadmissible.
        bool product_witness(euf::snode const* var, nielsen_node const& node,
                             unsigned len, zstring& out);

        // add constraints to the root node from external solver
        void add_str_eq(euf::snode const* lhs, euf::snode const* rhs, smt::enode* l, smt::enode* r) const;
        void add_str_deq(euf::snode const* lhs, euf::snode const* rhs, sat::literal l) const;
        void add_str_mem(euf::snode const* str, euf::snode const* regex, sat::literal l) const;

        // test-friendly overloads (no external dependency tracking)
        void add_str_eq(euf::snode const* lhs, euf::snode const* rhs) const;
        void add_str_deq(euf::snode const* lhs, euf::snode const* rhs) const;
        void add_str_mem(euf::snode const* str, euf::snode const* regex) const;

        // access all nodes
        ptr_vector<nielsen_node> const& nodes() const { return m_nodes; }
        unsigned num_nodes() const { return m_nodes.size(); }

        // maximum overall search depth (0 = unlimited)
        void set_max_search_depth(unsigned d) { m_max_search_depth = d; }

        // maximum total DFS nodes per solve() call (0 = unlimited)
        void set_max_nodes(unsigned n) { m_max_nodes = n; }
        
        // enable/disable Parikh image verification constraints
        void set_parikh_enabled(bool e) { m_parikh_enabled = e; }

        void set_signature_split(bool e) { m_signature_split = e; }
        
        void set_regex_factorization_threshold(unsigned max) { m_regex_factorization_threshold = max; }
        void set_regex_factorization_eager(bool e) { m_regex_factorization_eager = e; }
        void set_regex_dynamic_decomposition(bool e) { m_regex_dynamic_decomposition = e; }

        // benchmark-harvest mode (intentionally unsound; for benchmark generation only).
        // m_harvest > 0 = bound on non-progress Nielsen extension steps before dumping the
        // current node as an .smt2 benchmark; 0 = disabled (normal sound reasoning).
        void set_harvest(unsigned b) { m_harvest = b; }
        void set_harvest_dir(std::string d) { m_harvest_dir = std::move(d); }
        bool harvest_mode() const { return m_harvest > 0; }
        // write a snapshot of `n` (regex memberships + residual word equations) to an
        // .smt2 file, deduplicated by structural hash.  Terms are cleaned for portability
        // (see clean_harvest_expr); the internal integer/length constraints are dropped.
        void harvest_node(nielsen_node const* n);

        // Rewrite `e` into portable SMT-LIB: peel seq.slice(...) applications to their
        // root variable (first argument, chased until non-slice — matching the sgraph
        // hashing convention).  Sets ok=false if the term still contains an nseq-internal
        // skolem that cannot be represented (e.g. a power token); the node is then skipped.
        expr_ref clean_harvest_expr(expr* e, bool& ok);

        // display for debugging
        std::ostream& display(std::ostream& out) const;

        std::ostream &display(std::ostream &out, nielsen_node const *n) const;

        // output the graph in graphviz DOT format.
        // nodes on the sat_path are highlighted green; conflict nodes red/darkred.
        std::ostream& to_dot(std::ostream& out) const;

        std::string to_dot() const;

        std::ostream& partial_dfa_to_dot(std::ostream& out, euf::snode const* start_state, bool keep_names) const;

        std::string partial_dfa_to_dot(euf::snode const* start_state, bool keep_names) const;

        // reset all nodes and state
        void reset();

        // search result returned by solve() / search_dfs()
        enum class search_result { sat, unsat, unknown };

        // main search entry point: iterative deepening DFS
        search_result solve();

        // ---- Incremental eager structural closure -----------------------------
        // The deterministic Nielsen chain is grown incrementally as constraints
        // arrive (driven by theory_nseq::eager_structural_check), so we do NOT
        // rebuild from scratch on every propagation.  Lifecycle:
        //   eager_begin()      — start a fresh chain (reset + root + empty subst);
        //   eager_add_str_*()  — fold one new constraint into the current LEAF,
        //                        rewriting it through the chain's accumulated
        //                        substitution so it lands in leaf coordinates;
        //   eager_close()      — drive simplify_and_init (EMPTY path ⇒ no LP/arith
        //                        passes) + single-child apply_det_modifier from the
        //                        leaf to a fixpoint, extending the chain.
        // Returns unsat (conflict_sources() = the conflict node's own deps) on a
        // purely structural contradiction (symbol clash / empty-side / regex fail /
        // widening); unknown otherwise.  Sound for early-conflict detection because
        // the current set is a SUBSET of any completion.  Bails on
        // references_rigid() (det substitution of a rigid defined op is unsound).
        // reset()/pop (eager_invalidate) discard the chain; never declares SAT.
        bool eager_active() const { return m_eager_active && m_root != nullptr; }
        void eager_begin();
        void eager_invalidate() { m_eager_active = false; m_eager_leaf = nullptr; m_eager_substs.reset(); }
        nielsen_node* eager_leaf() const { return m_eager_leaf; }
        void eager_add_str_eq(euf::snode const* lhs, euf::snode const* rhs, smt::enode* l, smt::enode* r);
        void eager_add_str_deq(euf::snode const* lhs, euf::snode const* rhs, sat::literal lit);
        void eager_add_str_mem(euf::snode const* str, euf::snode const* regex, sat::literal lit);
        search_result eager_close();

        // generate child nodes by applying modifier rules
        // returns true if at least one child was generated
        bool generate_extensions(nielsen_node *node);

        // conflict sources extracted after solve() returns unsat
        vector<dep_source, false> const& conflict_sources() const { return m_conflict_sources; }

        // explain a conflict: partition the dep_source leaves into str_eq indices
        // (kind::eq) and str_mem indices (kind::mem).
        // Must be called after solve() returns unsat.
        void test_aux_explain_conflict(svector<enode_pair> &eqs,
                              svector<sat::literal> &mem_literals) const;


        // accumulated search statistics
        nielsen_stats const& stats() const { return m_stats; }
        void reset_stats() { m_stats.reset(); }
        void collect_statistics(::statistics& st) const;

        // generate arithmetic length constraints from the root node's string
        // equalities and regex memberships. For each non-trivial equation lhs = rhs,
        // produces len(lhs) = len(rhs) by expanding concatenations into sums.
        // For each regex membership str in regex, produces Parikh interval
        // constraints: len(str) >= min_len and len(str) <= max_len.
        // Also generates len(x) >= 0 for each variable appearing in the equations.
        void generate_length_constraints(vector<length_constraint>& constraints);

        // build an arithmetic expression representing the length of an snode tree.
        // concatenations are expanded to sums, chars to 1, empty to 0,
        // variables to (str.len var_expr).
        expr_ref compute_length_expr(euf::snode const* n);

        // compute Parikh length interval [min_len, max_len] for a regex snode.
        // uses seq_util::rex min_length/max_length on the underlying expression.
        // max_len == UINT_MAX means unbounded.
        void compute_regex_length_interval(euf::snode const* regex, unsigned& min_len, unsigned& max_len) const;

        // accessor for the seq_regex module
        seq_regex* seq_regex_module() const { return m_seq_regex; }

        dep_manager& dep_mgr() { return m_dep_mgr; }
        dep_manager const& dep_mgr() const { return m_dep_mgr; }

        // Add a dependency leaf for lhs <= rhs and join it to dep.
        void add_le_dependency(dep_tracker dep, nielsen_node* n, expr* lhs, expr* rhs) const;

        void assert_to_subsolver(const constraint& c) const;

        void assert_to_subsolver(expr* e) const;

        // Assert the constraints of `node` that are new relative to its
        // parent (indices [m_parent_ic_count..end)) into the current solver scope.
        // Called by search_dfs after simplify_and_init so that the newly derived
        // bounds become visible to subsequent check() and check_lp_le() calls.
        void assert_node_side_constraints(nielsen_node* node) const;

    private:

        vector<dep_source, false> m_conflict_sources;

        // collect dependency information from conflicting constraints
        dep_tracker collect_conflict_deps() const;

        search_result search_dfs(nielsen_node *node, ptr_vector<nielsen_edge>& path, unsigned depth = 0);

        // Union of all constraint deps of a node (sound over-approx conflict).
        dep_tracker node_all_deps(nielsen_node const* n) const;
        // True iff the node's UNSAT depends only on string/regex constraints.
        bool node_unsat_string_only(nielsen_node const* n) const;

        // Regex widening: overapproximate `str` by replacing variables with
        // the intersection of their primitive regex constraints (or Σ* if
        // unconstrained), replacing symbolic chars with their char ranges,
        // then checking if the approximation intersected with `regex` is empty.
        // Returns true if widening detects infeasibility (UNSAT).
        // Decided at the constraint level by check_concat_product_emptiness
        // (one factor per token of Ω(str), one component for the right-hand
        // side); land-state views participate exactly, both as the widened
        // membership and as pinned constraints inside Ω.
        bool check_regex_widening(nielsen_node const& node, str_mem const& mem, dep_tracker& dep);

        // Check regex feasibility at a leaf node: for each variable with
        // multiple primitive regex constraints, check that the intersection
        // of all its regexes is non-empty.
        // l_true: feasible; l_false: some intersection empty (dep set);
        // l_undef: product-search budget exhausted — must not be treated as SAT.
        lbool check_leaf_regex(nielsen_node const& node, dep_tracker& dep);

        // -------------------------------------------------------------------
        // Synchronous product over plain / view / guard / co-view components
        // (paper Section 3.3, "Deciding the intersection check").  Each
        // component carries its own acceptance + (gated) one-character law;
        // the product is empty iff no reachable tuple is simultaneously
        // accepting.  m_regex always being a plain regex, the derivative is
        // the ordinary Brzozowski one and only acceptance / the Q-gate differ.
        // -------------------------------------------------------------------
        struct prod_comp {
            mem_kind          m_kind = mem_kind::plain;
            bool              m_complemented = false; // ~stab co-view (kind==stab_view)
            euf::snode const* m_state = nullptr;      // current plain regex state
            euf::snode const* m_root = nullptr;       // land-state view acceptance state s
            unsigned          m_nu = 0;               // ν (Q snapshot)
            bool              m_sink = false;         // co-view became Σ*
            bool              m_dead = false;         // language collapsed to ∅

            static prod_comp mk_plain(euf::snode const* s) { prod_comp c; c.m_state = s; return c; }
            static prod_comp mk_view(euf::snode const* s, euf::snode const* root, unsigned nu, bool compl_) {
                prod_comp c;
                c.m_kind = mem_kind::stab_view;
                c.m_state = s;
                c.m_root = root;
                c.m_nu = nu;
                c.m_complemented = compl_;
                return c;
            }
        };

        // l_true = empty, l_false = non-empty (a simultaneously accepting tuple
        // was reached), l_undef = budget exhausted / inconclusive.
        // Implemented as a thin wrapper over check_concat_product_emptiness
        // (single factor holding the tuple, trivially accepting Σ* rhs).
        lbool check_product_emptiness(vector<prod_comp> const& comps, unsigned max_states);

        // Concatenation-aware variant (paper, "Pruning incrementally during
        // construction"): emptiness of  (L(F_0)·…·L(F_{k-1})) ⊓ L(rhs),  where
        // each factor F_i is the intersection of its components (an empty
        // component list denotes Σ*) and rhs is one further component consumed
        // synchronously with the whole concatenation.  Used by regex widening;
        // no closed-form regex for the concatenation is ever built, and view
        // components participate exactly via their gated one-character law.
        // l_true = empty, l_false = a common word exists, l_undef = budget
        // exhausted / undecided acceptance (callers must NOT prune on it).
        lbool check_concat_product_emptiness(vector<vector<prod_comp>> const& factors,
                                             prod_comp const& rhs, unsigned max_states);

        // acceptance / single-character step of one product component.
        lbool comp_accepting(prod_comp const& c) const;
        prod_comp comp_step(prod_comp const& c, euf::snode const* mt);

        // Shared pieces of the synchronous product engines (tuple-emptiness
        // wrapper, concatenation-aware search, witness search):
        // visited-key encoding of one component;
        static void prod_comp_key(prod_comp const& c, std::vector<unsigned>& key);
        // all-components-accepting test of a tuple (l_true: all accept,
        // l_false: some component rejects, l_undef: undecided);
        lbool tuple_accepting(vector<prod_comp> const& cs) const;
        // step every component of a tuple by one joint minterm; false iff a
        // component died (the successor tuple is then to be discarded);
        bool step_tuple(vector<prod_comp> const& cur, euf::snode const* mt, vector<prod_comp>& nxt);
        // joint first-character partition of the live (non-sink, non-dead)
        // component states, optionally including one extra component.
        void joint_minterms(vector<prod_comp> const& comps, prod_comp const* extra, euf::snode_vector& mts);

        // Build the product components for variable `var` from the node's
        // primitive memberships (plain / land-state view).  Joins their deps.
        bool collect_var_components(euf::snode const* var, nielsen_node const& node,
                                    vector<prod_comp>& out, dep_tracker& dep);

        // -------------------------------------------------------------------
        // Partial DFA projection helpers
        // -------------------------------------------------------------------

        // Record a discovered derivative edge src→dst in the global partial DFA
        // (edges are deduplicated by (src,dst); transition labels are unused).
        void record_partial_derivative_edge(euf::snode const* src_re, euf::snode const* dst_re);

        // Trigger gate for the cycle machinery: does some non-empty recorded
        // path lead from head_re back to head_re in the partial DFA?
        bool head_on_cycle(euf::snode const* head_re) const;

        // Landing decomposition (paper §5.3): Q is the set of explored states
        // forward-reachable from the head r in the partial DFA G, not merely r's
        // SCC.  These generalize the SCC helpers above.

        // Collect (into Q, as expr ids) every state forward-reachable from
        // head_re over the recorded partial-DFA edges.  Always includes head_re.
        void collect_reachable_from_head(euf::snode const* head_re, uint_set& Q) const;

        // Mark every forward-reachable edge from head_re with a monotone
        // extraction index ν (only previously-unmarked edges), bumping ν iff
        // something new was marked.  Returns the ν identifying this Q
        // (0 if there is nothing marked, i.e. no reachable edge).
        unsigned mark_reachable_projection_edges(euf::snode const* head_re);

        // Collect the snode handles of every state of Q_ν — the states incident
        // to a partial-DFA edge with extraction index in [1, ν].  This is the
        // enumeration counterpart of the membership test projection_state_in_Q
        // (keep the two in sync); used to enumerate the landing states of the
        // land-only view decomposition.
        void collect_projection_states(unsigned nu, svector<euf::snode const*>& out);

        // Length abstraction of the land-state views over one gated region:
        // BFS distances d(·) from a head state over the recorded in-Q_ν edges
        // (each edge consumes exactly one character/minterm), plus the stride
        //     g = gcd over reachable in-Q edges (u,v) of (d(u) + 1 − d(v)).
        // By the telescoping/potential argument, EVERY gated walk head→v has
        // length ≡ d(v) (mod g); g = 0 means every such walk has length exactly
        // d(v).  Sound because at ν-minting time compute_frontier has saturated
        // the in-Q edges (every one-character transition among Q states is
        // recorded), and edges are only ever added.
        struct view_len_info {
            u_map<unsigned> m_dist;       // expr id → shortest gated distance from the head
            unsigned        m_stride = 0; // 0 ⇒ walk lengths are exact
            bool            m_ok = false; // snapshot found and head ∈ Q_ν
        };
        void compute_view_length_info(unsigned nu, expr* from, view_len_info& info);

        // Emit the length side constraints for a variable pinned to the view
        // L_{Q_ν,{to}}(head) onto the branch edge e:  len ≥ min and
        // stride | (len − min)  (collapsed to len = min when exact).  For a
        // landing target outside Q_ν (view landing at root ∉ Q_ν) the final
        // hop may be an UNRECORDED transition from any reachable in-Q state,
        // so only the conservative variant (min = 1, stride weakened by the
        // gcd of all reachable distances) is sound.  These ride the normal
        // side-constraint channel: branch-locally enforced by the subsolver
        // (check_int_feasibility) and surfaced to the outer solver at a SAT
        // leaf via add_nielsen_assumptions — keeping the outer arith model's
        // len(x) realizable in the view, which seq_model::mk_fresh_value
        // relies on (a non-realizable length forces a witness of a different
        // length: an inconsistent model).
        void add_view_length_constraints(nielsen_edge* e, view_len_info const& info, unsigned nu,
                                         euf::snode const* pinned, expr* to, dep_tracker const& dep);

        // A frontier edge (p, mt, q): p ∈ Q, mt a minterm of p, q = δ_mt(p) ∉ Q
        // and q ≠ ⊥.  The escape candidates of the landing decomposition.
        struct frontier_edge {
            euf::snode const* m_src;   // p ∈ Q
            euf::snode const* m_mt;    // minterm
            euf::snode const* m_dst;   // q = δ_mt(p) ∉ Q
        };

        // One lazy exploration step around Q: for each p ∈ Qstates, take every
        // minterm derivative δ_mt(p).  If δ_mt(p) ∈ Q record the internal edge
        // (closing cycles); otherwise (and ≠ ⊥) append it to out_frontier.
        // Q holds expr ids (as produced by collect_reachable_from_head);
        // Qstates are the corresponding snode handles (including the head).
        void compute_frontier(uint_set const& Q, svector<euf::snode const*> const& Qstates,
                              vector<frontier_edge>& out_frontier);

        euf::snode const* get_slice(euf::snode const* v, expr* left, expr* right);

        euf::snode const* get_tail(euf::snode const* v, expr* cnt, bool fwd = true);

        euf::snode const* get_tail(euf::snode const* v, unsigned cnt, bool fwd = true);

        // Apply the Parikh image filter to a node: generate modular length
        // constraints from regex memberships and append them to the node's
        // constraints.  Also performs a lightweight feasibility pre-check;
        // if a Parikh conflict is detected the node's conflict flag is set with
        // backtrack_reason::parikh_image.
        //
        // Guarded by node.m_parikh_applied so that constraints are generated
        // only once per node across DFS iterations.
        void apply_parikh_to_node(nielsen_node& node) const;

        // simplify expression and create a node from simplified expression.
        euf::snode const* mk_rewrite(expr *e) const;

        // create a fresh variable with a unique name and the given sequence sort
        euf::snode const* mk_fresh_var(sort* s);

        // deterministic modifier: var = ε, same-head cancel
        bool apply_det_modifier(nielsen_node* node);

        // const nielsen modifier: char vs var (2 branches per case)
        bool apply_const_nielsen(nielsen_node* node);

        // variable Nielsen modifier: var vs var, all progress (3 branches)
        bool apply_var_nielsen(nielsen_node* node);

        // eq split modifier: splits a regex-free equation at a chosen index into
        // two shorter equalities with optional padding (single progress child).
        bool apply_eq_split(nielsen_node* node);

        // helper: classify whether a token has variable (symbolic) length
        // returns true for variables, powers, etc.; false for chars, units, string literals
        bool token_has_variable_length(euf::snode const* tok) const;

        // helper: get the constant length of a token (only valid when !token_has_variable_length)
        unsigned token_const_length(euf::snode const* tok) const;

        // helper: find a split point in a regex-free equation.
        // returns true if a valid split point is found, with results in out params.
        bool find_eq_split_point(
            euf::snode_vector const& lhs_toks,
            euf::snode_vector const& rhs_toks,
            unsigned& out_lhs_idx,
            unsigned& out_rhs_idx,
            int& out_padding) const;

        // power epsilon modifier: for a power token u^n in an equation,
        // branch: (1) base u = ε, (2) power is empty (n = 0 semantics).
        bool apply_power_epsilon(nielsen_node* node);

        // numeric comparison modifier: for equations involving power tokens
        // u^m and u^n with the same base, branch on m < n vs n <= m.
        bool apply_num_cmp(nielsen_node* node);

        // CommPower-based power elimination split: when one side starts with
        // a power w^p and CommPower finds c base-pattern occurrences on the
        // other side but the ordering between p and c is unknown, branch:
        //   (1) p < c   (2) c ≤ p
        // After branching, simplify_and_init's CommPower pass resolves the
        // cancellation deterministically.
        bool apply_split_power_elim(nielsen_node* node);

        // constant numeric unwinding: for a power token u^n vs a constant
        // (non-variable), branch: (1) n = 0 (u^n = ε), (2) n >= 1 (peel one u).
        bool apply_const_num_unwinding(nielsen_node* node);

        // regex if split: for str_mem s ∈ R where R decomposes as ite(c, th, el),
        // branch into s ∈ th under condition c, and s ∈ el under condition ¬c.
        bool apply_regex_if_split(nielsen_node* node);

        // landing decomposition (paper §5.3): the core branching rule for a
        // plain non-primitive membership x·u ∈ R (u ≠ ε, x a variable, R ground).
        // Splits x by WHERE its value lands in the explored region Q (states
        // forward-reachable from R):
        //   - land-at-s (for each s ∈ Q): pin x ∈_{Q,{s}} R and advance to u ∈ s
        //     (no split; s = R is stabilizer/cycle absorption);
        //   - escape-via-(p,a) (for each frontier edge): x → x1·a·x2 with
        //     x1 ∈_{Q,{p}} R, advancing to x2·u ∈ δ_a(p) and growing Q.
        // By the frontier partition (Lemma 4.7) these branches are exhaustive and
        // disjoint; character unwinding is the degenerate Q = {R} case.  Replaces
        // the old split-and-guard apply_cycle_decomposition.
        bool apply_landing_decomposition(nielsen_node* node);

        // Land-only decomposition of a NON-PRIMITIVE view constraint (paper
        // §5.3, "Landing decomposition on view constraints"): a substitution
        // applied throughout the node (an escape, a Nielsen split, a power
        // introduction) can hit a pinned variable and turn its primitive view
        // into  y·u ∈_{Q_ν,F} p  with a leading variable y.  Character-
        // unwinding y (regex_var_split) would re-introduce exactly the
        // cycle-unrolling divergence views exist to prevent, so instead:
        //   - p ∉ Q_ν (degenerate): L_{Q_ν,F}(p) ⊆ {ε} — conflict if p ∉ F or
        //     a character remains, else force the LHS variables to ε;
        //   - p ∈ Q_ν: branch on the landing state s of y over Q_ν ∪ F only
        //     (no escapes: every admissible LHS value keeps its proper-prefix
        //     states inside Q_ν and lands in F, so y's own landing state lies
        //     in Q_ν ∪ F), pinning y ∈_{Q_ν,{s}} p and advancing the residual
        //     to  u ∈_{Q_ν,F} s.
        // Removes the leading variable, introduces no fresh variables and
        // branches over finitely many states, so the paper's termination
        // argument extends unchanged.
        bool apply_view_landing_decomposition(nielsen_node* node);

        // cycle subsumption: for a str_mem x·rest ∈ R where x is constrained
        // to L(Reg_x) ⊆ L(stabilizer of R), simplify to rest ∈ R.
        // Fires without the novelty guard, using the current partial DFA state.
        bool apply_cycle_subsumption(nielsen_node* node);

        // BFS of Brzozowski derivatives from root_re up to `depth` steps,
        // eagerly recording concrete minterm edges in the partial DFA so that
        // head_on_cycle can find cycles without first waiting for
        // concrete children to record them one level at a time.
        // Lazily record the complete reachable automaton of root_re into the
        // partial DFA, once per regex component (cached in m_explored_automaton).
        void ensure_automaton_explored(euf::snode const* root_re);

        // generalized power introduction: for an equation where one head is
        // a variable v and the other side has ground prefix + a variable x
        // forming a cycle back to v, introduce v = base^n · suffix.
        bool apply_gpower_intr(nielsen_node* node);

        // generalized regex factorization (Boolean closure derivation rule).
        // Lazy: instead of materialising every split ⟨Δ,∇⟩ at once and branching
        // N-way, it pulls the splits one at a time from a suspended iterator and
        // branches binary — child A applies the next feasible split (head∈Δ,
        // tail∈∇, original membership dropped); child B keeps the membership and
        // carries the SAME iterator (rf_state) so factorization resumes from the
        // next split.  When the iterator is exhausted the membership's split
        // disjunction is refuted → the continuation node is a regex conflict.
        bool apply_regex_factorization(nielsen_node* node);

        // Build a suspended factorization (boundary head/tail + split iterator)
        // for `mem`.  Returns null if the regex shape is unsupported (the engine
        // cannot even start a split).  Allocated into m_rf_states.
        rf_state* mk_rf_state(nielsen_node* node, str_mem const& mem);

        enum class rf_step_result { branched, conflict, gaveup };
        // Pull the next feasible split from `st` and, on success, create the two
        // children of `node` (see apply_regex_factorization).  On exhaustion sets
        // `conflict_dep` and returns conflict; on engine give-up returns gaveup.
        rf_step_result rf_step(nielsen_node* node, rf_state* st, dep_tracker& conflict_dep);

        // helper for apply_gpower_intr: fires the substitution.
        // `fwd=true` uses left-to-right decomposition; `fwd=false`
        bool fire_gpower_intro(nielsen_node* node, str_eq const& eq,
                               euf::snode const* var, euf::snode_vector const& ground_prefix_orig, bool fwd);

        // heuristic string equation splitting. Left to right scanning for shortest prefix with matching variables.
        bool apply_signature_split(nielsen_node* node);

        // regex variable split: for str_mem x·s ∈ R where x is a variable,
        // split using minterms: x → ε, or x → c·x' for each minterm c.
        // More general than regex_char_split, uses minterm partitioning.
        bool apply_regex_var_split(nielsen_node* node);

        // power split: for a variable x facing a power token u^n,
        // branch: x = u^m · prefix(u) with m < n, or x = u^n · x.
        bool apply_power_split(nielsen_node* node);

        // variable numeric unwinding: for a power token u^n vs a variable,
        // branch: (1) n = 0 (u^n = ε), (2) n >= 1 (peel one u).
        bool apply_var_num_unwinding_eq(nielsen_node* node);

        bool apply_var_num_unwinding_mem(nielsen_node* node);

        bool axiomatize_diseq(nielsen_node* node);

        // find the first power token in any str_eq at this node
        static euf::snode const* find_power_token(nielsen_node* node);

        // find a power token facing a constant (char/non-var) token at either end
        // of an equation; returns orientation via `fwd` (true=head, false=tail).
        static bool find_power_vs_non_var(nielsen_node* node, euf::snode const*& power, euf::snode const*& other_head, str_eq const*& eq_out, bool& fwd);

        // find a power token facing a variable token at either end of an
        // equation; returns orientation via `fwd` (true=head, false=tail).
        static bool find_power_vs_var(nielsen_node* node, euf::snode const*& power, euf::snode const*& var_head, str_eq const*& eq_out, bool& fwd);

        static bool find_power_vs_var(nielsen_node* node, euf::snode const*& power, str_mem const*& mem_out, bool& fwd);

        // -----------------------------------------------
        // Integer feasibility subsolver methods
        // -----------------------------------------------

        // Constraint.Shared: assert all root-level length/Parikh constraints to
        // m_solver at the base level (outside push/pop). Called once at the start
        // of solve(). Makes derived constraints immediately visible to m_solver
        // for arithmetic pruning at every DFS node, not just the root.
        void assert_root_constraints_to_solver();

        // Generate |LHS| = |RHS| length constraints for a non-root node's own
        // string equalities and add them as constraints on the node.
        // Called once per node (guarded by m_node_len_constraints_generated).
        // Uses compute_length_expr (mod-count-aware) so that variables with
        // non-zero modification counts get fresh length variables.
        void generate_node_length_constraints(nielsen_node* node);

        // check integer feasibility of the constraints along the current path.
        // returns true if feasible (including unknown), false only if l_false.
        // Precondition: all path constraints have been incrementally asserted to
        // m_solver by search_dfs via push/pop, so a plain check() suffices.
        // l_undef (resource limit / timeout) is treated as feasible so that the
        // search continues rather than reporting a false unsatisfiability.
        bool check_int_feasibility() const;

        dep_tracker get_subsolver_dependency(nielsen_node* n) const;

        // check whether lhs <= rhs is implied by the path constraints.
        // temporarily asserts NOT(lhs <= rhs)
        // and returns true iff the result is unsatisfiable (i.e., lhs <= rhs is
        // entailed).  Path constraints are already in the solver incrementally.
        bool check_lp_le(expr* lhs, expr* rhs, nielsen_node* n, dep_tracker& dep);

        // create an integer constraint: lhs <kind> rhs
        constraint mk_constraint(expr *fml, dep_tracker const &dep) const;

        // get the exponent expression from a power snode (arg(1))
        static expr * get_power_exponent(euf::snode const* power);

        // -----------------------------------------------
        // Modification counter methods for substitution length tracking.
        // -----------------------------------------------

        // Get or create a fresh symbolic character variable for the given variable
        expr_ref get_or_create_char_var(euf::snode const* var);

        // Get or create a fresh integer variable for gpower n (full exponent) for the given variable
        expr_ref get_or_create_gpower_n_var(euf::snode const* var);

        // Get or create a fresh integer variable for gpower m (partial exponent) for the given variable
        expr_ref get_or_create_gpower_m_var(euf::snode const* var);

        // Compute and add |x| = |u| length constraints to an edge for all
        // its non-eliminating substitutions. Uses current m_mod_cnt.
        // Temporarily bumps m_mod_cnt for RHS computation, then restores.
        // Called lazily on first edge traversal in search_dfs.
        void add_subst_length_constraints(nielsen_edge* e);
    };

}

template <> struct std::hash<seq::str_eq> {
    unsigned operator()(seq::str_eq& eq) const noexcept {
        return eq.hash();
    }
};

template <> struct std::hash<seq::str_deq> {
    unsigned operator()(seq::str_deq& deq) const noexcept {
        return deq.hash();
    }
};

template <> struct std::hash<seq::str_mem> {
    unsigned operator()(seq::str_mem& mem) const noexcept {
        return mem.hash();
    }
};