/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen.h

Abstract:

    Nielsen graph for string constraint solving.

    Ports the constraint types and Nielsen graph structures from
    ZIPT (https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT/Constraints)
    into Z3's smt/seq framework.

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

    -----------------------------------------------------------------------
    ZIPT PORT COMPARISON SUMMARY
    -----------------------------------------------------------------------

    The ZIPT reference is organized as follows (all under ZIPT/Constraints/):
      NielsenGraph.cs          -- the graph manager class
      NielsenNode.cs           -- node class + BacktrackReasons enum
      NielsenEdge.cs           -- edge class with string and character substitutions
      ConstraintElement/
        Constraint.cs          -- abstract base for all constraints
        StrEqBase.cs           -- abstract base for StrEq and StrMem
        StrEq.cs               -- string equality with full simplification/splitting
        StrMem.cs              -- regex membership with Brzozowski derivatives
        IntEq.cs               -- integer equality over length polynomials
        IntLe.cs               -- integer inequality over length polynomials
      Modifier/                -- ~15 modifier types driving graph expansion

    A. PORTED FAITHFULLY
    --------------------
    1. backtrack_reason enum (BacktrackReasons): all eleven values (Unevaluated,
       Extended, SymbolClash, ParikhImage, Subsumption, Arithmetic, Regex,
       RegexWidening, CharacterRange, SMT, ChildrenFailed) are present with
       identical semantics.

    2. simplify_result enum (SimplifyResult): all five values (Proceed, Conflict,
       Satisfied, Restart, RestartAndSatisfied) are present with identical semantics.
       Note: RestartAndSatisfied is declared but not yet exercised in this port.

    3. nielsen_node status fields and accessors: m_is_general_conflict,
       m_is_extended, m_reason, m_eval_idx map directly to IsGeneralConflict,
       IsExtended, CurrentReason, evalIdx. The is_currently_conflict() predicate
       faithfully mirrors IsCurrentlyConflict (GeneralConflict || (reason !=
       Unevaluated && IsExtended)).

    4. nielsen_node::reset_counter() mirrors NielsenNode.ResetCounter() exactly.

    5. nielsen_node::clone_from() mirrors the copy constructor
       NielsenNode(graph, parent) for str_eq and str_mem constraints.

    6. nielsen_edge identity (operator==) mirrors NielsenEdge.Equals(): both
       compare by source and target node pointer identity.

    7. nielsen_graph::inc_run_idx() mirrors the RunIdx increment in NielsenGraph.
       Check(), including the UINT_MAX overflow guard that calls reset_counter()
       on all nodes.

    8. str_eq::sort() mirrors StrEqBase.SortStr(): swaps lhs/rhs when lhs > rhs.
       (Z3 compares by snode id; ZIPT compares Str lexicographically.)

    9. str_eq::is_trivial() mirrors the trivially-satisfied check when both sides
       are empty.

    10. str_mem fields (m_str, m_regex, m_history, m_id, m_dep) mirror StrMem
        fields (Str, Regex, History, Id, Reason) faithfully, including the unique
        identifier used for cycle tracking.

    11. str_mem::is_primitive() mirrors StrMem.IsPrimitiveRegex(): single variable
        on the left side of the membership constraint.

    12. nielsen_subst::is_eliminating() mirrors the logic behind
        NielsenEdge.BumpedModCount: a substitution is non-eliminating (bumps the
        modification counter) when the substituted variable appears in the
        replacement.

    13. nielsen_graph::mk_edge() faithfully mirrors NielsenEdge construction: it
        links src to tgt and registers the outgoing edge.

    B. PORTED WITH ALGORITHMIC CHANGES
    ------------------------------------
    1. dep_tracker (DependencyTracker): ZIPT's DependencyTracker is a .NET
       class using a BitArray-like structure for tracking constraint origins.
       Z3's dep_tracker uses a dense bitvector stored as svector<unsigned>
       (32-bit words). The merge/is_superset/empty semantics are equivalent,
       but the representation is more cache-friendly and avoids managed-heap
       allocation.

    2. Substitution application (nielsen_node::apply_subst): ZIPT uses an
       immutable, functional style -- Apply() returns a new constraint if
       changed, using C# reference equality to detect no-ops. Z3 uses
       in-place mutation via sgraph::subst(), modifying the constraint vectors
       directly. The functional change also propagates the substitution's
       dependency to the merged constraint.

    3. Node constraint containers: ZIPT's NielsenNode stores str_eq constraints
       in NList<StrEq> (a sorted list for O(log n) subsumption lookup) and str_mem
       constraints in Dictionary<uint, StrMem> (keyed by id for O(1) cycle lookup).
       Z3 uses plain vector<str_eq> and vector<str_mem>, which is simpler.

    4. nielsen_edge substitution list: ZIPT's NielsenEdge carries two substitution
       lists -- Subst (string-level, mapping string variables to strings) and
       SubstC (character-level, mapping symbolic character variables to concrete
       characters). Z3's nielsen_edge carries a single vector<nielsen_subst>,
       covering only string-level substitutions; character substitutions are not
       represented.

    5. nielsen_graph node registry: ZIPT keeps nodes in a HashSet<NielsenNode> plus
       a Dictionary<NList<StrEq>, List<NielsenNode>> for subsumption candidate
       lookup. Z3 uses a ptr_vector<nielsen_node>, simplifying memory management.

    6. nielsen_graph::display() vs NielsenGraph.ToDot(): ZIPT outputs a DOT-format
       graph with color highlighting for the current satisfying path. Z3 outputs
       plain human-readable text with node/edge details but no DOT syntax or path
       highlighting.

    7. str_eq::contains_var() / str_mem::contains_var(): ZIPT performs occurrence
       checks through StrManager.Subst() (which uses hash-consing and reference
       equality). Z3 walks the snode tree via collect_tokens(), which is correct
       but re-traverses the DAG on every call.

    C. NOT PORTED
    -------------
    The following ZIPT components are absent from this implementation.
    They represent the algorithmic core of the search procedure and
    are expected to be ported in subsequent work.

    Constraint simplification and propagation:
    - Constraint.SimplifyAndPropagate() / SimplifyAndPropagateInternal(): the
      main constraint-driven simplification loop is not ported. str_eq and
      str_mem have no Simplify methods.
    - StrEq.SimplifyDir() / SimplifyFinal() / AddDefinition(): forward/backward
      simplification passes, including Makanin-style prefix cancellation, power
      token handling, and variable definition propagation.
    - StrEq.GetNielsenDep() / SplitEq(): the Nielsen dependency analysis and
      equation-splitting heuristic used to choose the best split point.
    - StrMem.SimplifyCharRegex() / SimplifyDir(): Brzozowski derivative-based
      simplification consuming ground prefixes/suffixes of the string.
    - StrMem.TrySubsume(): stabilizer-based subsumption (not ported, not needed).
    - StrMem.ExtractCycle() / StabilizerFromCycle(): cycle detection over the
      search path and extraction of a Kleene-star stabilizer to generalize the
      cycle. This is the key termination argument for regex membership.
    - StrMem.Extend(): the splitting driver that produces the next modifier
      (RegexVarSplitModifier, RegexCharSplitModifier, StarIntrModifier, etc.).

    Integer constraints:
    - IntEq / IntLe: integer equality and inequality constraints over Presburger
      arithmetic polynomials (PDD<BigInteger>) are entirely absent. The Z3 port
      has no ConstraintsIntEq or ConstraintsIntLe in nielsen_node.
    - IntBounds / VarBoundWatcher: per-variable integer interval bounds and the
      watcher mechanism that reruns bound propagation when a string variable is
      substituted are not ported.
    - AddLowerIntBound() / AddHigherIntBound(): incremental interval tightening
      with restart signaling is not ported.

    Character-level handling:
    - CharSubst: character-level variable substitution (symbolic char -> concrete
      char) is absent. ZIPT uses this to handle symbolic character tokens
      (SymCharToken) that represent a single unknown character.
    - SymCharToken / CharacterSet: symbolic character tokens with associated
      character range constraints (CharRanges) are not ported.
    - DisEqualities: per-node character disequality constraints used for conflict
      detection during character substitution are not ported.

    Modifier hierarchy (Constraints/Modifier/):
    - 13 Modifier subclasses driving graph expansion are ported as
      apply_* methods in generate_extensions, matching ZIPT's TypeOrder
      priority: DetModifier(1), PowerEpsilonModifier(2), NumCmpModifier(3),
      ConstNumUnwindingModifier(4), EqSplitModifier(5), StarIntrModifier(6),
      GPowerIntrModifier(7), ConstNielsenModifier(8), RegexCharSplitModifier(9),
      RegexVarSplitModifier(10), PowerSplitModifier(11), VarNielsenModifier(12),
      VarNumUnwindingModifier(13).
    - NOT PORTED: DirectedNielsenModifier, DecomposeModifier, CombinedModifier.
    - NumCmp, ConstNumUnwinding, VarNumUnwinding are approximated (no PDD
      integer polynomial infrastructure; power tokens are replaced with ε
      or peeled with fresh variables instead of exact exponent arithmetic).

    Search procedure:
    - NielsenGraph.Check() / NielsenNode.GraphExpansion(): ported as
      nielsen_graph::solve() (iterative deepening, starting at depth 3,
      incrementing by 1 per failure, bounded by smt.nseq.max_depth) and
      search_dfs() (depth-bounded DFS with eval_idx cycle detection and
      node status tracking).
    - NielsenNode.SimplifyAndInit(): ported as
      nielsen_node::simplify_and_init() with prefix matching, symbol clash,
      empty propagation, and Brzozowski derivative consumption.
    - NielsenGraph.FindExisting() / subsumption cache lookup: not ported,
      not needed.

    Auxiliary infrastructure:
    - LocalInfo: thread-local search bookkeeping (current path, modification
      counts, regex occurrence cache for cycle detection, current node pointer)
      is not ported.
    - NielsenGraph.SubSolver / InnerStringPropagator: the auxiliary Z3 solver
      for arithmetic lemma generation and the inner string propagator for
      model-based refinement are not ported.
    - PowerToken: word-repetition tokens of the form u^n (distinct from regex
      Kleene star) are not represented in Z3's snode.
    - GetSignature(): the constraint-pair signature used for subsumption
      candidate matching is not ported.
    - Constraint.Shared: the flag indicating whether a constraint should be
      forwarded to the outer solver is not ported.
    - Interpretation: the model-extraction class mapping string and integer
      variables to concrete values is not ported.
    -----------------------------------------------------------------------

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-02
    Clemens Eisenhofer 2026-03-02

--*/

#pragma once

#include "util/vector.h"
#include "util/uint_set.h"
#include "util/map.h"
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/euf/euf_sgraph.h"
#include "math/lp/lar_solver.h"
#include <functional>

namespace seq {

    // forward declarations
    class nielsen_node;
    class nielsen_edge;
    class nielsen_graph;

    // simplification result for constraint processing
    // mirrors ZIPT's SimplifyResult enum
    enum class simplify_result {
        proceed,               // no change, continue
        conflict,              // constraint is unsatisfiable
        satisfied,             // constraint is trivially satisfied
        restart,               // constraint was simplified, restart
        restart_and_satisfied, // simplified and satisfied
    };

    // reason for backtracking in the Nielsen graph
    // mirrors ZIPT's BacktrackReasons enum
    enum class backtrack_reason {
        unevaluated,
        extended,
        symbol_clash,
        parikh_image,
        subsumption,  // not used; retained for enum completeness
        arithmetic,
        regex,
        regex_widening,
        character_range,
        smt,
        children_failed,
    };

    // dependency tracker: bitvector tracking which input constraints
    // contributed to deriving a given constraint
    // mirrors ZIPT's DependencyTracker
    class dep_tracker {
        svector<unsigned> m_bits;
    public:
        dep_tracker() = default;
        explicit dep_tracker(unsigned num_bits);
        dep_tracker(unsigned num_bits, unsigned set_bit);

        void merge(dep_tracker const& other);
        bool is_superset(dep_tracker const& other) const;
        bool empty() const;

        // collect indices of all set bits into 'indices'
        void get_set_bits(unsigned_vector& indices) const;

        bool operator==(dep_tracker const& other) const { return m_bits == other.m_bits; }
        bool operator!=(dep_tracker const& other) const { return !(*this == other); }
    };

    // -----------------------------------------------
    // character range and set types
    // mirrors ZIPT's CharacterRange and CharacterSet
    // -----------------------------------------------

    // half-open character interval [lo, hi)
    // mirrors ZIPT's CharacterRange
    struct char_range {
        unsigned m_lo;
        unsigned m_hi; // exclusive

        char_range(): m_lo(0), m_hi(0) {}
        char_range(unsigned c): m_lo(c), m_hi(c + 1) {}
        char_range(unsigned lo, unsigned hi): m_lo(lo), m_hi(hi) { SASSERT(lo <= hi); }

        bool is_empty() const { return m_lo == m_hi; }
        bool is_unit()  const { return m_hi == m_lo + 1; }
        unsigned length() const { return m_hi - m_lo; }
        bool contains(unsigned c) const { return c >= m_lo && c < m_hi; }

        bool operator==(char_range const& o) const { return m_lo == o.m_lo && m_hi == o.m_hi; }
        bool operator<(char_range const& o) const {
            return m_lo < o.m_lo || (m_lo == o.m_lo && m_hi < o.m_hi);
        }
    };

    // sorted list of non-overlapping character intervals
    // mirrors ZIPT's CharacterSet
    class char_set {
        svector<char_range> m_ranges;
    public:
        char_set() = default;
        explicit char_set(char_range const& r) { if (!r.is_empty()) m_ranges.push_back(r); }

        static char_set full(unsigned max_char) { return char_set(char_range(0, max_char + 1)); }

        bool is_empty() const { return m_ranges.empty(); }
        bool is_full(unsigned max_char) const {
            return m_ranges.size() == 1 && m_ranges[0].m_lo == 0 && m_ranges[0].m_hi == max_char + 1;
        }
        bool is_unit() const { return m_ranges.size() == 1 && m_ranges[0].is_unit(); }
        unsigned first_char() const { SASSERT(!is_empty()); return m_ranges[0].m_lo; }

        svector<char_range> const& ranges() const { return m_ranges; }

        // total number of characters in the set
        unsigned char_count() const;

        // membership test via binary search
        bool contains(unsigned c) const;

        // add a single character
        void add(unsigned c);

        // union with another char_set
        void add(char_set const& other);

        // intersect with another char_set, returns the result
        char_set intersect_with(char_set const& other) const;

        // complement relative to [0, max_char]
        char_set complement(unsigned max_char) const;

        // check if two sets are disjoint
        bool is_disjoint(char_set const& other) const;

        bool operator==(char_set const& other) const { return m_ranges == other.m_ranges; }

        char_set clone() const { char_set r; r.m_ranges = m_ranges; return r; }

        std::ostream& display(std::ostream& out) const;
    };

    // -----------------------------------------------
    // character-level substitution
    // mirrors ZIPT's CharSubst
    // -----------------------------------------------

    // maps a symbolic char (s_unit snode) to a concrete or symbolic char
    struct char_subst {
        euf::snode* m_var;  // the symbolic char being substituted (s_unit)
        euf::snode* m_val;  // replacement: s_char (concrete) or s_unit (symbolic)

        char_subst(): m_var(nullptr), m_val(nullptr) {}
        char_subst(euf::snode* var, euf::snode* val):
            m_var(var), m_val(val) {
            SASSERT(var && var->is_unit());
            SASSERT(val && (val->is_char() || val->is_unit()));
        }

        // true when the replacement is a concrete character
        bool is_eliminating() const { return m_val && m_val->is_char(); }

        bool operator==(char_subst const& o) const {
            return m_var == o.m_var && m_val == o.m_val;
        }
    };

    // string equality constraint: lhs = rhs
    // mirrors ZIPT's StrEq (both sides are regex-free snode trees)
    struct str_eq {
        euf::snode* m_lhs;
        euf::snode* m_rhs;
        dep_tracker m_dep;

        str_eq(): m_lhs(nullptr), m_rhs(nullptr) {}
        str_eq(euf::snode* lhs, euf::snode* rhs, dep_tracker const& dep):
            m_lhs(lhs), m_rhs(rhs), m_dep(dep) {}

        bool operator==(str_eq const& other) const {
            return m_lhs == other.m_lhs && m_rhs == other.m_rhs;
        }

        // sort so that lhs <= rhs by snode id
        void sort();

        // check if both sides are empty (trivially satisfied)
        bool is_trivial() const;

        // check if the constraint contains a given variable
        bool contains_var(euf::snode* var) const;
    };

    // regex membership constraint: str in regex
    // mirrors ZIPT's StrMem
    struct str_mem {
        euf::snode* m_str;
        euf::snode* m_regex;
        euf::snode* m_history;  // tracks derivation history for cycle detection
        unsigned    m_id;       // unique identifier
        dep_tracker m_dep;

        str_mem(): m_str(nullptr), m_regex(nullptr), m_history(nullptr), m_id(UINT_MAX) {}
        str_mem(euf::snode* str, euf::snode* regex, euf::snode* history, unsigned id, dep_tracker const& dep):
            m_str(str), m_regex(regex), m_history(history), m_id(id), m_dep(dep) {}

        bool operator==(str_mem const& other) const {
            return m_id == other.m_id && m_str == other.m_str && m_regex == other.m_regex;
        }

        // check if the constraint has the form x in R with x a single variable
        bool is_primitive() const;

        // check if the constraint contains a given variable
        bool contains_var(euf::snode* var) const;
    };

    // string variable substitution: var -> replacement
    // mirrors ZIPT's Subst
    struct nielsen_subst {
        euf::snode* m_var;
        euf::snode* m_replacement;
        dep_tracker m_dep;

        nielsen_subst(): m_var(nullptr), m_replacement(nullptr) {}
        nielsen_subst(euf::snode* var, euf::snode* repl, dep_tracker const& dep):
            m_var(var), m_replacement(repl), m_dep(dep) {
            SASSERT(var != nullptr);
            SASSERT(repl != nullptr);
            // var may be s_var or s_power; sgraph::subst uses pointer identity matching
            SASSERT(var->is_var() || var->is_power());
        }

        // an eliminating substitution does not contain the variable in the replacement
        bool is_eliminating() const;

        bool operator==(nielsen_subst const& other) const {
            return m_var == other.m_var && m_replacement == other.m_replacement;
        }
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

        length_constraint(ast_manager& m): m_expr(m), m_kind(length_kind::nonneg) {}
        length_constraint(expr* e, dep_tracker const& dep, length_kind kind, ast_manager& m):
            m_expr(e, m), m_dep(dep), m_kind(kind) {}
    };

    // -----------------------------------------------
    // integer constraint: equality or inequality over length expressions
    // mirrors ZIPT's IntEq and IntLe
    // -----------------------------------------------

    enum class int_constraint_kind {
        eq,   // lhs = rhs
        le,   // lhs <= rhs
        ge,   // lhs >= rhs
    };

    // integer constraint stored per nielsen_node, tracking arithmetic
    // relationships between length variables and power exponents.
    // mirrors ZIPT's IntEq / IntLe over Presburger arithmetic polynomials.
    struct int_constraint {
        expr_ref             m_lhs;    // left-hand side (arithmetic expression)
        expr_ref             m_rhs;    // right-hand side (arithmetic expression)
        int_constraint_kind  m_kind;   // eq, le, or ge
        dep_tracker          m_dep;    // tracks which input constraints contributed

        int_constraint(ast_manager& m):
            m_lhs(m), m_rhs(m), m_kind(int_constraint_kind::eq) {}
        int_constraint(expr* lhs, expr* rhs, int_constraint_kind kind, dep_tracker const& dep, ast_manager& m):
            m_lhs(lhs, m), m_rhs(rhs, m), m_kind(kind), m_dep(dep) {}

        std::ostream& display(std::ostream& out) const;
    };

    // edge in the Nielsen graph connecting two nodes
    // mirrors ZIPT's NielsenEdge
    class nielsen_edge {
        nielsen_node*           m_src;
        nielsen_node*           m_tgt;
        vector<nielsen_subst>   m_subst;
        vector<char_subst>      m_char_subst;     // character-level substitutions (mirrors ZIPT's SubstC)
        ptr_vector<str_eq>      m_side_str_eq;    // side constraints: string equalities
        ptr_vector<str_mem>     m_side_str_mem;    // side constraints: regex memberships
        vector<int_constraint>  m_side_int;        // side constraints: integer equalities/inequalities
        bool                    m_is_progress;     // does this edge represent progress?
    public:
        nielsen_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress);

        nielsen_node* src() const { return m_src; }
        nielsen_node* tgt() const { return m_tgt; }

        void set_tgt(nielsen_node* tgt) { m_tgt = tgt; }

        vector<nielsen_subst> const& subst() const { return m_subst; }
        void add_subst(nielsen_subst const& s) { m_subst.push_back(s); }

        vector<char_subst> const& char_substs() const { return m_char_subst; }
        void add_char_subst(char_subst const& s) { m_char_subst.push_back(s); }

        void add_side_str_eq(str_eq* eq) { m_side_str_eq.push_back(eq); }
        void add_side_str_mem(str_mem* mem) { m_side_str_mem.push_back(mem); }
        void add_side_int(int_constraint const& ic) { m_side_int.push_back(ic); }

        ptr_vector<str_eq> const& side_str_eq() const { return m_side_str_eq; }
        ptr_vector<str_mem> const& side_str_mem() const { return m_side_str_mem; }
        vector<int_constraint> const& side_int() const { return m_side_int; }

        bool is_progress() const { return m_is_progress; }

        bool operator==(nielsen_edge const& other) const {
            return m_src == other.m_src && m_tgt == other.m_tgt;
        }
    };

    // node in the Nielsen graph
    // mirrors ZIPT's NielsenNode
    class nielsen_node {
        friend class nielsen_graph;

        unsigned                m_id;
        nielsen_graph*          m_graph;

        // constraints at this node
        vector<str_eq>          m_str_eq;     // string equalities
        vector<str_mem>         m_str_mem;    // regex memberships
        vector<int_constraint>  m_int_constraints;  // integer equalities/inequalities (mirrors ZIPT's IntEq/IntLe)

        // character constraints (mirrors ZIPT's DisEqualities and CharRanges)
        // key: snode id of the s_unit symbolic character
        u_map<ptr_vector<euf::snode>>  m_char_diseqs;  // ?c != {?d, ?e, ...}
        u_map<char_set>                m_char_ranges;   // ?c in [lo, hi)

        // edges
        ptr_vector<nielsen_edge> m_outgoing;
        nielsen_node*           m_backedge = nullptr;
        nielsen_edge*           m_parent_edge = nullptr;

        // status flags
        bool                    m_is_general_conflict = false;
        bool                    m_is_extended = false;
        backtrack_reason        m_reason = backtrack_reason::unevaluated;
        bool                    m_is_progress = false;

        // evaluation index for run tracking
        unsigned                m_eval_idx = 0;

    public:
        nielsen_node(nielsen_graph* graph, unsigned id);

        unsigned id() const { return m_id; }
        nielsen_graph* graph() const { return m_graph; }

        // constraint access
        vector<str_eq> const& str_eqs() const { return m_str_eq; }
        vector<str_eq>& str_eqs() { return m_str_eq; }
        vector<str_mem> const& str_mems() const { return m_str_mem; }
        vector<str_mem>& str_mems() { return m_str_mem; }

        void add_str_eq(str_eq const& eq) { m_str_eq.push_back(eq); }
        void add_str_mem(str_mem const& mem) { m_str_mem.push_back(mem); }
        void add_int_constraint(int_constraint const& ic) { m_int_constraints.push_back(ic); }

        vector<int_constraint> const& int_constraints() const { return m_int_constraints; }
        vector<int_constraint>& int_constraints() { return m_int_constraints; }

        // character constraint access (mirrors ZIPT's DisEqualities / CharRanges)
        u_map<ptr_vector<euf::snode>> const& char_diseqs() const { return m_char_diseqs; }
        u_map<char_set> const& char_ranges() const { return m_char_ranges; }

        // add a character range constraint for a symbolic char.
        // intersects with existing range; sets conflict if result is empty.
        void add_char_range(euf::snode* sym_char, char_set const& range);

        // add a character disequality: sym_char != other
        void add_char_diseq(euf::snode* sym_char, euf::snode* other);

        // apply a character-level substitution to all constraints.
        // checks disequalities and ranges; sets conflict on violation.
        void apply_char_subst(euf::sgraph& sg, char_subst const& s);

        // edge access
        ptr_vector<nielsen_edge> const& outgoing() const { return m_outgoing; }
        void add_outgoing(nielsen_edge* e) { m_outgoing.push_back(e); }

        nielsen_node* backedge() const { return m_backedge; }
        void set_backedge(nielsen_node* n) { m_backedge = n; }

        nielsen_edge* parent_edge() const { return m_parent_edge; }
        void set_parent_edge(nielsen_edge* e) { m_parent_edge = e; }

        // status
        bool is_general_conflict() const { return m_is_general_conflict; }
        void set_general_conflict(bool v) { m_is_general_conflict = v; }

        bool is_extended() const { return m_is_extended; }
        void set_extended(bool v) { m_is_extended = v; }

        bool is_currently_conflict() const {
            return m_is_general_conflict ||
                (m_reason != backtrack_reason::unevaluated && m_is_extended);
        }

        backtrack_reason reason() const { return m_reason; }
        void set_reason(backtrack_reason r) { m_reason = r; }

        bool is_progress() const { return m_is_progress; }

        unsigned eval_idx() const { return m_eval_idx; }
        void set_eval_idx(unsigned idx) { m_eval_idx = idx; }
        void reset_counter() { m_eval_idx = 0; }

        // clone constraints from a parent node
        void clone_from(nielsen_node const& parent);

        // apply a substitution to all constraints
        void apply_subst(euf::sgraph& sg, nielsen_subst const& s);

        // simplify all constraints at this node and initialize status.
        // Returns proceed, conflict, satisfied, or restart.
        simplify_result simplify_and_init(nielsen_graph& g);

        // true if all str_eqs are trivial and there are no str_mems
        bool is_satisfied() const;

        // true if any constraint has opaque (s_other) terms that
        // the Nielsen graph cannot decompose
        bool has_opaque_terms() const;

        // render constraint set as an HTML fragment for DOT node labels.
        // mirrors ZIPT's NielsenNode.ToHtmlString()
        std::ostream& display_html(std::ostream& out, ast_manager& m) const;

    private:
        // Helper: handle one empty vs one non-empty side of a string equality.
        // Collects tokens from non_empty_side; if any token causes a conflict
        // (is a concrete character or an unexpected kind), sets conflict flags
        // and returns true. Otherwise substitutes all variables to empty,
        // sets changed=true, and returns false.
        bool handle_empty_side(euf::sgraph& sg, euf::snode* non_empty_side,
                               dep_tracker const& dep, bool& changed);
    };

    // search statistics collected during Nielsen graph solving
    struct nielsen_stats {
        unsigned m_num_solve_calls     = 0;
        unsigned m_num_dfs_nodes       = 0;
        unsigned m_num_sat             = 0;
        unsigned m_num_unsat           = 0;
        unsigned m_num_unknown         = 0;
        unsigned m_num_simplify_conflict = 0;
        unsigned m_num_extensions      = 0;
        unsigned m_num_fresh_vars      = 0;
        unsigned m_max_depth           = 0;
        // modifier application counts
        unsigned m_mod_det             = 0;
        unsigned m_mod_power_epsilon   = 0;
        unsigned m_mod_num_cmp         = 0;
        unsigned m_mod_const_num_unwinding = 0;
        unsigned m_mod_eq_split        = 0;
        unsigned m_mod_star_intr       = 0;
        unsigned m_mod_gpower_intr     = 0;
        unsigned m_mod_const_nielsen   = 0;
        unsigned m_mod_regex_char_split = 0;
        unsigned m_mod_regex_var_split = 0;
        unsigned m_mod_power_split     = 0;
        unsigned m_mod_var_nielsen     = 0;
        unsigned m_mod_var_num_unwinding = 0;
        void reset() { memset(this, 0, sizeof(nielsen_stats)); }
    };

    // the overall Nielsen transformation graph
    // mirrors ZIPT's NielsenGraph
    class nielsen_graph {
        euf::sgraph&                  m_sg;
        region                        m_region;
        ptr_vector<nielsen_node>      m_nodes;
        ptr_vector<nielsen_edge>      m_edges;
        nielsen_node*                 m_root = nullptr;
        nielsen_node*                 m_sat_node = nullptr;
        svector<nielsen_edge*>        m_sat_path;
        unsigned                      m_run_idx = 0;
        unsigned                      m_depth_bound = 0;
        unsigned                      m_max_search_depth = 0;
        unsigned                      m_next_mem_id = 0;
        unsigned                      m_fresh_cnt = 0;
        unsigned                      m_num_input_eqs = 0;
        unsigned                      m_num_input_mems = 0;
        nielsen_stats                 m_stats;

        // external cancellation callback: returns true if solving should abort
        std::function<bool()>         m_cancel_fn;

        // -----------------------------------------------
        // Integer subsolver using lp::lar_solver
        // Replaces ZIPT's SubSolver (auxiliary Z3 instance)
        // with Z3's native LP solver for integer feasibility.
        // -----------------------------------------------
        scoped_ptr<lp::lar_solver>    m_lp_solver;
        u_map<lp::lpvar>              m_expr2lpvar;    // maps expr id → LP variable
        unsigned                      m_lp_ext_cnt = 0; // external variable counter for LP solver

    public:
        nielsen_graph(euf::sgraph& sg);
        ~nielsen_graph();

        euf::sgraph& sg() { return m_sg; }

        // node management
        nielsen_node* mk_node();
        nielsen_node* mk_child(nielsen_node* parent);

        // edge management
        nielsen_edge* mk_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress);

        // root node access
        nielsen_node* root() const { return m_root; }
        void set_root(nielsen_node* n) { m_root = n; }

        // satisfying leaf node (set by solve() when result is sat)
        nielsen_node* sat_node() const { return m_sat_node; }
        // path of edges from root to sat_node (set when sat_node is set)
        svector<nielsen_edge*> const& sat_path() const { return m_sat_path; }

        // add constraints to the root node from external solver
        void add_str_eq(euf::snode* lhs, euf::snode* rhs);
        void add_str_mem(euf::snode* str, euf::snode* regex);

        // run management
        unsigned run_idx() const { return m_run_idx; }
        void inc_run_idx();

        // access all nodes
        ptr_vector<nielsen_node> const& nodes() const { return m_nodes; }
        unsigned num_nodes() const { return m_nodes.size(); }

        // maximum overall search depth (0 = unlimited)
        void set_max_search_depth(unsigned d) { m_max_search_depth = d; }

        // set a cancellation callback; solve() checks this periodically
        void set_cancel_fn(std::function<bool()> fn) { m_cancel_fn = std::move(fn); }

        // generate next unique regex membership id
        unsigned next_mem_id() { return m_next_mem_id++; }

        // number of input constraints (for dep_tracker bit mapping)
        unsigned num_input_eqs() const { return m_num_input_eqs; }
        unsigned num_input_mems() const { return m_num_input_mems; }

        // display for debugging
        std::ostream& display(std::ostream& out) const;

        // output the graph in graphviz DOT format.
        // nodes on the sat_path are highlighted green; conflict nodes red/darkred.
        // mirrors ZIPT's NielsenGraph.ToDot()
        std::ostream& to_dot(std::ostream& out) const;

        // reset all nodes and state
        void reset();

        // search result returned by solve() / search_dfs()
        enum class search_result { sat, unsat, unknown };

        // main search entry point: iterative deepening DFS
        search_result solve();

        // generate child nodes by applying modifier rules
        // returns true if at least one child was generated
        bool generate_extensions(nielsen_node *node);

        // collect dependency information from conflicting constraints
        void collect_conflict_deps(dep_tracker& deps) const;

        // explain a conflict: partition the set bits into str_eq indices
        // (bits 0..num_eqs-1) and str_mem indices (bits num_eqs..num_eqs+num_mems-1).
        // Must be called after solve() returns unsat.
        void explain_conflict(unsigned_vector& eq_indices, unsigned_vector& mem_indices) const;

        // accumulated search statistics
        nielsen_stats const& stats() const { return m_stats; }
        void reset_stats() { m_stats.reset(); }

        // generate arithmetic length constraints from the root node's string
        // equalities and regex memberships. For each non-trivial equation lhs = rhs,
        // produces len(lhs) = len(rhs) by expanding concatenations into sums.
        // For each regex membership str in regex, produces Parikh interval
        // constraints: len(str) >= min_len and len(str) <= max_len.
        // Also generates len(x) >= 0 for each variable appearing in the equations.
        void generate_length_constraints(vector<length_constraint>& constraints);

    private:
        search_result search_dfs(nielsen_node* node, unsigned depth, svector<nielsen_edge*>& cur_path);

        // create a fresh variable with a unique name
        euf::snode* mk_fresh_var();

        // create a fresh symbolic character: seq.unit(fresh_char_const)
        // analogous to ZIPT's SymCharToken creation
        euf::snode* mk_fresh_char_var();

        // deterministic modifier: var = ε, same-head cancel
        bool apply_det_modifier(nielsen_node* node);

        // const nielsen modifier: char vs var (2 branches per case)
        bool apply_const_nielsen(nielsen_node* node);

        // variable Nielsen modifier: var vs var, all progress (3 branches)
        bool apply_var_nielsen(nielsen_node* node);

        // eq split modifier: splits a regex-free equation at a chosen index into
        // two shorter equalities with optional padding (single progress child).
        // Mirrors ZIPT's EqSplitModifier + StrEq.SplitEq.
        bool apply_eq_split(nielsen_node* node);

        // helper: classify whether a token has variable (symbolic) length
        // returns true for variables, powers, etc.; false for chars, units, string literals
        bool token_has_variable_length(euf::snode* tok) const;

        // helper: get the constant length of a token (only valid when !token_has_variable_length)
        unsigned token_const_length(euf::snode* tok) const;

        // helper: find a split point in a regex-free equation.
        // ports ZIPT's StrEq.SplitEq algorithm.
        // returns true if a valid split point is found, with results in out params.
        bool find_eq_split_point(
            euf::snode_vector const& lhs_toks,
            euf::snode_vector const& rhs_toks,
            unsigned& out_lhs_idx,
            unsigned& out_rhs_idx,
            int& out_padding) const;

        // apply regex character split modifier to a node.
        // for a str_mem constraint x·s ∈ R where x is a variable:
        //   (1) x → c·z for each char c accepted by R at first position
        //   (2) x → ε (x is empty)
        // returns true if children were generated.
        bool apply_regex_char_split(nielsen_node* node);

        // power epsilon modifier: for a power token u^n in an equation,
        // branch: (1) base u = ε, (2) power is empty (n = 0 semantics).
        // mirrors ZIPT's PowerEpsilonModifier
        bool apply_power_epsilon(nielsen_node* node);

        // numeric comparison modifier: for equations involving power tokens
        // u^m and u^n with the same base, branch on m < n vs n <= m.
        // mirrors ZIPT's NumCmpModifier
        bool apply_num_cmp(nielsen_node* node);

        // constant numeric unwinding: for a power token u^n vs a constant
        // (non-variable), branch: (1) n = 0 (u^n = ε), (2) n >= 1 (peel one u).
        // mirrors ZIPT's ConstNumUnwindingModifier
        bool apply_const_num_unwinding(nielsen_node* node);

        // star introduction: for a str_mem x·s ∈ R where a cycle is detected
        // (backedge exists), introduce stabilizer: x ∈ base* with x split.
        // mirrors ZIPT's StarIntrModifier
        bool apply_star_intr(nielsen_node* node);

        // generalized power introduction: for a variable x matched against
        // a ground repeated pattern, introduce x = base^n · prefix(base)
        // with fresh power variable n and side constraint n >= 0.
        // mirrors ZIPT's GPowerIntrModifier
        bool apply_gpower_intr(nielsen_node* node);

        // regex variable split: for str_mem x·s ∈ R where x is a variable,
        // split using minterms: x → ε, or x → c·x' for each minterm c.
        // More general than regex_char_split, uses minterm partitioning.
        // mirrors ZIPT's RegexVarSplitModifier
        bool apply_regex_var_split(nielsen_node* node);

        // power split: for a variable x facing a power token u^n,
        // branch: x = u^m · prefix(u) with m < n, or x = u^n · x.
        // mirrors ZIPT's PowerSplitModifier
        bool apply_power_split(nielsen_node* node);

        // variable numeric unwinding: for a power token u^n vs a variable,
        // branch: (1) n = 0 (u^n = ε), (2) n >= 1 (peel one u).
        // mirrors ZIPT's VarNumUnwindingModifier
        bool apply_var_num_unwinding(nielsen_node* node);

        // collect concrete first-position characters from a regex snode
        void collect_first_chars(euf::snode* re, euf::snode_vector& chars);

        // find the first power token in any str_eq at this node
        euf::snode* find_power_token(nielsen_node* node) const;

        // find a power token facing a constant (char) head
        bool find_power_vs_const(nielsen_node* node, euf::snode*& power, euf::snode*& other_head, str_eq const*& eq_out) const;

        // find a power token facing a variable head
        bool find_power_vs_var(nielsen_node* node, euf::snode*& power, euf::snode*& var_head, str_eq const*& eq_out) const;

        // build an arithmetic expression representing the length of an snode tree.
        // concatenations are expanded to sums, chars to 1, empty to 0,
        // variables to (str.len var_expr).
        expr_ref compute_length_expr(euf::snode* n);

        // compute Parikh length interval [min_len, max_len] for a regex snode.
        // uses seq_util::rex min_length/max_length on the underlying expression.
        // max_len == UINT_MAX means unbounded.
        void compute_regex_length_interval(euf::snode* regex, unsigned& min_len, unsigned& max_len);

        // -----------------------------------------------
        // LP integer subsolver methods
        // -----------------------------------------------

        // initialize the LP solver fresh for a feasibility check
        void lp_solver_reset();

        // get or create an LP variable for an arithmetic expression
        lp::lpvar lp_ensure_var(expr* e);

        // add an int_constraint to the LP solver
        void lp_add_constraint(int_constraint const& ic);

        // collect int_constraints along the path from root to the given node,
        // including constraints from edges and nodes.
        void collect_path_int_constraints(nielsen_node* node,
                                          svector<nielsen_edge*> const& cur_path,
                                          vector<int_constraint>& out);

        // check integer feasibility of the constraints along the current path.
        // returns true if feasible, false if infeasible.
        bool check_int_feasibility(nielsen_node* node, svector<nielsen_edge*> const& cur_path);

        // create an integer constraint: lhs <kind> rhs
        int_constraint mk_int_constraint(expr* lhs, expr* rhs, int_constraint_kind kind, dep_tracker const& dep);

        // get the exponent expression from a power snode (arg(1))
        expr* get_power_exponent(euf::snode* power);

        // create a fresh integer variable expression (for power exponents)
        expr_ref mk_fresh_int_var();
    };

}
