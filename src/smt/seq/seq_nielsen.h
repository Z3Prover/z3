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
       Z3 uses scoped_dependency_manager<dep_source> (an arena-based binary
       join tree from util/dependency.h) where each leaf carries a dep_source
       value identifying the originating eq or mem constraint by kind and index.

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
    - IntBounds / VarBoundWatcher: ZIPT-style cached interval maps and eager
      watcher propagation are not stored in nielsen_node; bounds are queried
      from the arithmetic subsolver on demand.
    - AddLowerIntBound() / AddHigherIntBound(): incremental interval tightening
      — PORTED as the above add_lower/upper_int_bound methods.

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
      forwarded to the outer solver — PORTED as
      nielsen_graph::assert_root_constraints_to_solver(), called at the start
      of solve() to make all root-level length/Parikh constraints immediately
      visible to m_solver.
    - Interpretation: the model-extraction class mapping string and integer
      variables to concrete values is not ported.
    -----------------------------------------------------------------------

Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#pragma once

#include "util/vector.h"
#include "util/uint_set.h"
#include "util/dependency.h"
#include "util/map.h"
#include "util/lbool.h"
#include "util/rational.h"
#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/euf/euf_sgraph.h"
#include <map>
#include "model/model.h"
#include "util/obj_ref_hashtable.h"
#include "util/uint_map.h"

namespace smt {
    class enode;
}

namespace seq {

    // forward declarations
    class nielsen_node;
    class nielsen_edge;
    class nielsen_graph;
    class seq_parikh;
    class seq_regex;  // forward declaration (defined in smt/seq/seq_regex.h)

    std::string snode_label_html(euf::snode const* n, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m);

    std::string snode_label_html(euf::snode const* n, ast_manager& m);

    /**
     * Abstract interface for an incremental solver used by nielsen_graph
     * to check integer/arithmetic feasibility of path constraints.
     *
     * Users of nielsen_graph can wrap smt::kernel or any other solver
     * to serve as the arithmetic back-end.  When no solver is provided,
     * integer feasibility checks are skipped (optimistically assumed feasible).
     */
    class simple_solver {
    public:
        virtual ~simple_solver() {}
        virtual lbool   check() = 0;
        virtual void    assert_expr(expr* e) = 0;
        virtual void    push() = 0;
        virtual void    pop(unsigned num_scopes) = 0;
        virtual void    get_model(model_ref& mdl) { mdl = nullptr; }
        virtual lbool   check_with_assumptions(expr_ref_vector& assumptions, expr_ref_vector& core) { return l_undef; }
        // Optional bound queries on arithmetic expressions (non-strict integer bounds).
        // Default implementation reports "unsupported".
        virtual bool    lower_bound(expr* e, rational& lo) const { return false; }
        virtual bool    upper_bound(expr* e, rational& hi) const { return false; }
        virtual bool current_value(expr *e, rational &v) const { return false; }
        
        virtual void    reset() = 0;
    };

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
        external,
        children_failed,
    };

    inline std::ostream& operator<<(std::ostream& out, backtrack_reason r) {
        switch (r) {
        case backtrack_reason::unevaluated: return out << "unevaluated";
        case backtrack_reason::extended: return out << "extended";
        case backtrack_reason::symbol_clash: return out << "symbol_clash";
        case backtrack_reason::parikh_image: return out << "parikh_image";
        case backtrack_reason::subsumption: return out << "subsumption";
        case backtrack_reason::arithmetic: return out << "arithmetic";
        case backtrack_reason::regex: return out << "regex";
        case backtrack_reason::regex_widening: return out << "regex_widening";
        case backtrack_reason::character_range: return out << "char range";
        case backtrack_reason::children_failed: return out << "children_failed";
        case backtrack_reason::external: return out << "external";
        case backtrack_reason::smt: return out << "smt";
        default: return out << "<tbd reason>";
        }
    }

    // source of a dependency: identifies an input constraint by kind and index.
    // kind::eq means a string equality, kind::mem means a regex membership.
    // index is the 0-based position in the input eq or mem list respectively.

    using enode_pair = std::pair<smt::enode *, smt::enode *>;

    // arithmetic implication dependency: lhs <= rhs
    struct le {
        expr_ref lhs;
        expr_ref rhs;
        bool operator==(le const &other) const {
            return lhs == other.lhs && rhs == other.rhs;         
        }
    };

    using dep_source = std::variant<sat::literal, enode_pair, le>;


    // Arena-based dependency manager: builds an immutable tree of dep_source
    // leaves joined by binary join nodes.  Memory is managed via a region;
    // call dep_manager::reset() to release all allocations at once.
    using dep_manager = scoped_dependency_manager<dep_source>;

    // dep_tracker is a pointer into the dep_manager's arena.
    // nullptr represents the empty dependency set.
    using dep_tracker = dep_manager::dependency*;

    // partition dep_source leaves from deps into enode pairs, sat literals,
    // and arithmetic <= dependencies.
    void deps_to_lits(dep_tracker deps,
                      svector<enode_pair>& eqs,
                      svector<sat::literal>& lits,
                      vector<le>& les);

    // string equality constraint: lhs = rhs
    // mirrors ZIPT's StrEq (both sides are regex-free snode trees)
    struct str_eq {
        euf::snode* m_lhs;
        euf::snode* m_rhs;
        dep_tracker m_dep;

        str_eq(euf::snode* lhs, euf::snode* rhs, dep_tracker const& dep): 
            m_lhs(lhs), m_rhs(rhs), m_dep(dep) {
            SASSERT(well_formed());
        }

        bool operator==(str_eq const& other) const {
            return m_lhs == other.m_lhs && m_rhs == other.m_rhs;
        }

        // sort so that lhs <= rhs by snode id
        void sort();

        // check if both sides are empty (trivially satisfied)
        bool is_trivial() const;

        // check if the constraint contains a given variable
        bool contains_var(euf::snode* var) const;

        bool well_formed() const {
            return !!m_lhs && !!m_rhs;
        }
    };

    struct eq_pp {
        str_eq const &eq;
        ast_manager &m;
        eq_pp(str_eq const &e, ast_manager &m) : eq(e), m(m) {}
    };

    inline std::ostream &operator<<(std::ostream &out, eq_pp const &p) {
        return out << mk_pp(p.eq.m_lhs->get_expr(), p.m) << " == " << mk_pp(p.eq.m_rhs->get_expr(), p.m) << "\n";
    }

    // regex membership constraint: str in regex
    // mirrors ZIPT's StrMem
    struct str_mem {
        euf::snode* m_str;
        euf::snode* m_regex;
        dep_tracker m_dep;

        // str_mem(): m_str(nullptr), m_regex(nullptr), m_dep(nullptr) {}
        str_mem(euf::snode* str, euf::snode* regex, dep_tracker const& dep):
            m_str(str), m_regex(regex), m_dep(dep) {}

        bool operator==(str_mem const& other) const {
            return m_str == other.m_str && m_regex == other.m_regex;
        }

        // check if the constraint has the form x in R with x a single variable
        bool is_primitive() const;

        // TODO: These two functions need to aware of the truth of the ite-guards of the symbolic derivations
        bool is_trivial(nielsen_node const* n) const;

        bool is_contradiction(nielsen_node const* n) const;

        // check if the constraint contains a given variable
        bool contains_var(euf::snode* var) const;

        bool well_formed() const {
            return !!m_str && !!m_regex;
        }
    };

    struct mem_pp {
        ast_manager &m;
        str_mem const& mem;
        mem_pp(ast_manager &m, str_mem const&mem) : m(m), mem(mem) {}
    };
    inline std::ostream &operator<<(std::ostream &out, mem_pp const &p) {
        return out << mk_pp(p.mem.m_str->get_expr(), p.m) << " in " << mk_pp(p.mem.m_regex->get_expr(), p.m) << "\n";
    }

    // string variable substitution: var -> replacement
    // (can be used as well to substitute arbitrary nodes - like powers)
    // mirrors ZIPT's Subst
    struct nielsen_subst {
        euf::snode* m_var;
        euf::snode* m_replacement;
        euf::snode *m_length = nullptr; // representation of length if this is a sequence variable, null otherwise.
        dep_tracker m_dep;

        nielsen_subst(): m_var(nullptr), m_replacement(nullptr), m_dep(nullptr) {}
        nielsen_subst(euf::snode* var, euf::snode* repl, euf::snode* length, dep_tracker const& dep):
            m_var(var), m_replacement(repl), m_length(length), m_dep(dep) {
            SASSERT(var != nullptr);
            SASSERT(repl != nullptr);
            // var may be s_var or s_power; sgraph::subst uses pointer identity matching
            SASSERT(var->is_var() || var->is_power() || var->is_unit());
            SASSERT(!var->is_unit() || repl->is_char_or_unit());
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
    // mirrors ZIPT's IntEq and IntLe
    // -----------------------------------------------

    // integer constraint stored per nielsen_node, tracking arithmetic
    // relationships between length variables and power exponents.
    // mirrors ZIPT's IntEq / IntLe over Presburger arithmetic polynomials.
    struct constraint {
        expr_ref    fml;   // the formula (eq, le, or ge, unit-diseq expression)
        dep_tracker dep;   // tracks which input constraints contributed

        static expr_ref simplify(expr* f, ast_manager& m) {
            th_rewriter th(m);
            expr_ref fml(f, m);
            th(fml);
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
        length_constraint(expr* e, dep_tracker const& dep, length_kind kind, ast_manager& m):
            m_expr(e, m), m_dep(dep), m_kind(kind) {}

        constraint to_constraint() const {
            return constraint(m_expr, m_dep, m_expr.get_manager());
        }
    };

    // edge in the Nielsen graph connecting two nodes
    // mirrors ZIPT's NielsenEdge
    class nielsen_edge {
        nielsen_node*           m_src;
        nielsen_node*           m_tgt;
        vector<nielsen_subst>   m_subst;
        vector<constraint>      m_side_constraints;  // side constraints: integer equalities/inequalities
        bool                    m_is_progress;     // does this edge represent progress?
        bool                    m_len_constraints_computed = false; // lazily computed substitution length constraints
    public:
        nielsen_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress);

        nielsen_node* src() const { return m_src; }
        nielsen_node* tgt() const { return m_tgt; }

        void set_tgt(nielsen_node* tgt) { m_tgt = tgt; }

        // don't forget to add the substitution
        // applying it only to the node is NOT sufficient (otw. length counters are not in sync)
        vector<nielsen_subst> const& subst() const { return m_subst; }
        void add_subst(nielsen_subst const& s);

        void add_side_constraint(constraint const& ic) { m_side_constraints.push_back(ic); }
        vector<constraint> const& side_constraints() const { return m_side_constraints; }

        bool is_progress() const { return m_is_progress; }

        bool len_constraints_computed() const { return m_len_constraints_computed; }
        void set_len_constraints_computed(bool v) { m_len_constraints_computed = v; }

        bool operator==(nielsen_edge const& other) const {
            return m_src == other.m_src && m_tgt == other.m_tgt;
        }
    };

    // node in the Nielsen graph
    // mirrors ZIPT's NielsenNode
    class nielsen_node {
        friend class nielsen_graph;

        unsigned                m_id;
        nielsen_graph&          m_graph;

        // constraints at this node
        vector<str_eq>     m_str_eq;        // string equalities
        vector<str_mem>    m_str_mem;       // regex memberships
        vector<constraint> m_constraints;   // integer equalities/inequalities (mirrors ZIPT's IntEq/IntLe)
        sat::literal m_conflict_external_literal = sat::null_literal;
        dep_tracker  m_conflict_internal = nullptr;


        // character constraints (mirrors ZIPT's DisEqualities and CharRanges)
        // key: snode id of the s_unit symbolic character
        u_map<std::pair<char_set, dep_tracker>>            m_char_ranges;   // ?c in [lo, hi)

        // edges
        ptr_vector<nielsen_edge> m_outgoing;
        nielsen_node*           m_backedge = nullptr;
        nielsen_edge*           m_parent_edge = nullptr;

        // status flags
        bool                    m_is_general_conflict = false;
        bool                    m_is_extended = false;
        backtrack_reason        m_reason = backtrack_reason::unevaluated;
        bool                    m_is_progress = false;
        bool                    m_node_len_constraints_generated = false; // true after generate_node_length_constraints runs

        // evaluation index for run tracking
        unsigned                m_eval_idx = 0;

        // Parikh filter: set to true once apply_parikh_to_node has been applied
        // to this node. Prevents duplicate constraint generation across DFS runs.
        bool                    m_parikh_applied = false;
        // number of constraints inherited from the parent node at clone time.
        // constraints[0..m_parent_ic_count) are already asserted at the
        // parent's solver scope; only [m_parent_ic_count..end) need to be
        // asserted when this node's solver scope is entered.
        unsigned                m_parent_ic_count = 0;

        // RegexOccurrence: maps (regex snode id, str_mem id) → node id where
        // this regex was last seen on the current DFS path.
        // Used for precise cycle detection with history-length-based progress.
        // Mirrors ZIPT LocalInfo.RegexOccurrence (LocalInfo.cs:34)
        std::map<std::pair<unsigned, unsigned>, unsigned> m_regex_occurrence;
        

    public:
        nielsen_node(nielsen_graph& graph, unsigned id);

        unsigned id() const { return m_id; }
        nielsen_graph& graph() const { return m_graph; }

        // constraint access
        vector<str_eq> const& str_eqs() const { return m_str_eq; }
        vector<str_eq>& str_eqs() { return m_str_eq; }
        vector<str_mem> const& str_mems() const { return m_str_mem; }
        vector<str_mem>& str_mems() { return m_str_mem; }

        void add_str_eq(str_eq const& eq);
        void add_str_mem(str_mem const& mem);
        void add_constraint(constraint const &ic);

        vector<constraint> const& constraints() const { return m_constraints; }
        vector<constraint>& constraints() { return m_constraints; }

        sat::literal get_external_conflict_literal() const { return m_conflict_external_literal; }

        // Query current bounds for a variable from the arithmetic subsolver.
        // Falls der Subsolver keinen Bound liefert, werden konservative Defaults
        // 0 / UINT_MAX verwendet.
        bool lower_bound(expr* e, rational& lo, dep_tracker& dep);
        bool upper_bound(expr* e, rational& up, dep_tracker& dep);

        // character constraint access (mirrors ZIPT's CharRanges)
        u_map<std::pair<char_set, dep_tracker>> char_ranges() const { return m_char_ranges; }

        // add a character range constraint for a symbolic char.
        // intersects with existing range; sets conflict if result is empty.
        void add_char_range(euf::snode* sym_char, char_set const& range, dep_tracker dep);

        // edge access
        ptr_vector<nielsen_edge> const& outgoing() const { return m_outgoing; }
        void add_outgoing(nielsen_edge* e) { m_outgoing.push_back(e); }

        nielsen_node* backedge() const { return m_backedge; }
        void set_backedge(nielsen_node* n) { m_backedge = n; }

        nielsen_edge* parent_edge() const { return m_parent_edge; }
        void set_parent_edge(nielsen_edge* e) { m_parent_edge = e; }

        // status
        bool is_general_conflict() const { return m_is_general_conflict; }
        void set_general_conflict() {
            m_is_general_conflict = true;
        }

        bool is_extended() const { return m_is_extended; }
        void set_extended(bool v) {
            m_is_extended = v;
        }

        bool is_currently_conflict() const {
            return is_general_conflict() ||
                m_conflict_external_literal != sat::null_literal ||
                (reason() != backtrack_reason::unevaluated && m_is_extended);
        }

        void clear_local_conflict() {
            SASSERT(!is_general_conflict());
            m_reason = backtrack_reason::unevaluated;
            m_conflict_internal = nullptr;
            m_conflict_external_literal = sat::null_literal;
        }

        backtrack_reason reason() const { return m_reason; }

        void set_child_conflict() {
            SASSERT(m_reason == backtrack_reason::unevaluated);
            SASSERT(!m_conflict_internal);
            SASSERT(m_conflict_external_literal == sat::null_literal);
            m_reason = backtrack_reason::children_failed;
        }

        void set_conflict(const backtrack_reason r, const dep_tracker confl) {
            if (m_conflict_internal != nullptr && m_conflict_external_literal == sat::null_literal)
                return;
            // We prefer internal conflicts (we need it as a justification for general conflicts)
            TRACE(seq, tout << "internal conflict " << r << "\n");
            m_reason = r;
            m_conflict_internal = confl;
            m_conflict_external_literal = sat::null_literal;
        }

        void set_external_conflict(sat::literal lit, dep_tracker confl) {
            if (m_reason != backtrack_reason::unevaluated)
                return;
            TRACE(seq, tout << "external conflict " << lit << "\n");
            m_reason = backtrack_reason::external;
            m_conflict_external_literal = ~lit;
            m_conflict_internal = confl;
        }

        bool is_progress() const { return m_is_progress; }

        unsigned eval_idx() const { return m_eval_idx; }
        void set_eval_idx(unsigned idx) { m_eval_idx = idx; }
        void reset_counter() { m_eval_idx = 0; }

        // clone constraints from a parent node
        void clone_from(nielsen_node const& parent);

        // Regex occurrence tracking: record current regex state for cycle detection.
        // Returns true if a cycle is detected (same regex seen before on this path).
        bool track_regex_occurrence(unsigned regex_id, unsigned mem_id);

        // Get the regex occurrence map (for undo on backtrack).
        std::map<std::pair<unsigned, unsigned>, unsigned> const& regex_occurrence() const {
            return m_regex_occurrence;
        }

        // apply a substitution to all constraints
        void apply_subst(euf::sgraph& sg, nielsen_subst const& s);

        // simplify all constraints at this node and initialize status.
        // Uses cur_path for LP solver queries during deterministic power cancellation.
        // Returns proceed, conflict, satisfied, or restart.
        simplify_result simplify_and_init(ptr_vector<nielsen_edge> const& cur_path);

        // true if all str_eqs are trivial and there are no str_mems
        bool is_satisfied() const;

        // render constraint set as an HTML fragment for DOT node labels.
        // mirrors ZIPT's NielsenNode.ToHtmlString()
        std::ostream& to_html(std::ostream& out, obj_map<expr, std::string>& names, uint64_t& next_id, ast_manager& m) const;

        std::ostream& to_html(std::ostream& out, ast_manager& m) const;

    private:
        // Helper: handle one empty vs one non-empty side of a string equality.
        // Collects tokens from non_empty_side; if any token causes a conflict
        // (is a concrete character or an unexpected kind), sets conflict flags
        // and returns true. Otherwise returns false.
        bool check_empty_side_conflict(euf::sgraph& sg, euf::snode* non_empty_side,
                                       dep_tracker const& dep);

        // Length bounds are queried from the arithmetic subsolver when needed.
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
        unsigned m_mod_gpower_intr     = 0;
        unsigned m_mod_regex_factorization = 0;
        unsigned m_mod_const_nielsen   = 0;
        unsigned m_mod_regex_var_split = 0;
        unsigned m_mod_signature_split = 0;
        unsigned m_mod_power_split     = 0;
        unsigned m_mod_var_nielsen     = 0;
        unsigned m_mod_var_num_unwinding_eq = 0;
        unsigned m_mod_var_num_unwinding_mem = 0;
        void reset() { memset(this, 0, sizeof(nielsen_stats)); }
    };

    struct unsigned_eq {
        bool operator()(unsigned x, unsigned y) const { return x == y; }
    };

    // the overall Nielsen transformation graph
    // mirrors ZIPT's NielsenGraph
    class nielsen_graph {
        friend class nielsen_node;
        friend class nielsen_edge;
        ast_manager&                  m;
        arith_util                    a;
        seq_util&                     m_seq;
        euf::sgraph&                  m_sg;
        ptr_vector<nielsen_node>      m_nodes;
        ptr_vector<nielsen_edge>      m_edges;
        nielsen_node*                 m_root = nullptr;
        nielsen_node*                 m_sat_node = nullptr;
        ptr_vector<nielsen_edge>      m_sat_path;
        unsigned                      m_run_idx = 0;
        unsigned                      m_depth_bound = 0;
        unsigned                      m_max_search_depth = 0;
        unsigned                      m_max_nodes = 0;          // 0 = unlimited
        bool                          m_parikh_enabled = true;
        bool                          m_signature_split = false;
        bool                          m_regex_factorization = true;
        unsigned                      m_fresh_cnt = 0;
        nielsen_stats                 m_stats;


        // -----------------------------------------------
        // Integer subsolver (abstract interface)
        // When m_solver is null, check_int_feasibility skips arithmetic checking
        // and optimistically assumes feasibility.
        // -----------------------------------------------
        simple_solver&                m_solver;
        simple_solver&                m_core_solver;

        // Constraint.Shared: guards re-assertion of root-level constraints.
        // Set to true after assert_root_constraints_to_solver() is first called.
        bool                          m_root_constraints_asserted = false;

        // Parikh image filter: generates modular length constraints from regex
        // memberships.  Allocated in the constructor; owned by this graph.
        seq_parikh*                   m_parikh = nullptr;

        // Regex membership module: stabilizers, emptiness checks, language
        // inclusion, derivatives. Allocated in the constructor; owned by this graph.
        seq::seq_regex*              m_seq_regex = nullptr;

        // Callback to check that literals assumed in branches are not already assigned to false.
        // returns the literal that is assigned to false, otherwise returns a null_literal
        std::function<sat::literal(expr *)> m_literal_if_false;

        // Maps each variable to its current length term

        ptr_vector<euf::snode>        m_length_trail;
        u_map<euf::snode *>           m_length_info;
        u_map<unsigned>               m_mod_cnt;

        // Arena for dep_tracker nodes.  Declared mutable so that const methods
        // (e.g., explain_conflict) can call mk_join / linearize.
        mutable dep_manager           m_dep_mgr;

        std::ostream &display(std::ostream &out, nielsen_node const* n) const;

    public:
        // Construct with a caller-supplied solver.  Ownership is NOT transferred;
        // the caller is responsible for keeping the solver alive.
        nielsen_graph(euf::sgraph& sg, simple_solver& solver, simple_solver &core_solver);
        ~nielsen_graph();

        void set_literal_if_false(std::function<sat::literal(expr* e)> const& lif) {
            m_literal_if_false = lif;
        }

        ast_manager &get_manager() {
            return m;
        }
        
        euf::sgraph& sg() { return m_sg; }
        seq_util& seq() { return m_seq; }
        seq_util const& seq() const { return m_seq; }

        // node management
        nielsen_node* mk_node();
        nielsen_node* mk_child(nielsen_node* parent);

        // edge management
        nielsen_edge* mk_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress);

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
            m_sat_node = n;
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

        // add constraints to the root node from external solver
        void add_str_eq(euf::snode* lhs, euf::snode* rhs, smt::enode* l, smt::enode* r);
        void add_str_mem(euf::snode* str, euf::snode* regex, sat::literal l);

        // test-friendly overloads (no external dependency tracking)
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

        // maximum total DFS nodes per solve() call (0 = unlimited)
        void set_max_nodes(unsigned n) { m_max_nodes = n; }
        
        // enable/disable Parikh image verification constraints
        void set_parikh_enabled(bool e) { m_parikh_enabled = e; }

        void set_signature_split(bool e) { m_signature_split = e; }
        
        void set_regex_factorization(bool e) { m_regex_factorization = e; }

        // display for debugging
        std::ostream& display(std::ostream& out) const;

        // output the graph in graphviz DOT format.
        // nodes on the sat_path are highlighted green; conflict nodes red/darkred.
        // mirrors ZIPT's NielsenGraph.ToDot()
        std::ostream& to_dot(std::ostream& out) const;

        std::string to_dot() const;

        // reset all nodes and state
        void reset();

        // search result returned by solve() / search_dfs()
        enum class search_result { sat, unsat, unknown };

        // main search entry point: iterative deepening DFS
        search_result solve();

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
        expr_ref compute_length_expr(euf::snode* n);

        // compute Parikh length interval [min_len, max_len] for a regex snode.
        // uses seq_util::rex min_length/max_length on the underlying expression.
        // max_len == UINT_MAX means unbounded.
        void compute_regex_length_interval(euf::snode* regex, unsigned& min_len, unsigned& max_len);

        // accessor for the seq_regex module
        seq_regex* seq_regex_module() const { return m_seq_regex; }

        dep_manager& dep_mgr() { return m_dep_mgr; }
        dep_manager const& dep_mgr() const { return m_dep_mgr; }

        // Add a dependency leaf for lhs <= rhs and join it to dep.
        void add_le_dependency(dep_tracker& dep, nielsen_node* n, expr* lhs, expr* rhs);

        // Assert the constraints of `node` that are new relative to its
        // parent (indices [m_parent_ic_count..end)) into the current solver scope.
        // Called by search_dfs after simplify_and_init so that the newly derived
        // bounds become visible to subsequent check() and check_lp_le() calls.
        void assert_node_new_int_constraints(nielsen_node* node);

    private:

        vector<dep_source, false> m_conflict_sources;

        // collect dependency information from conflicting constraints
        dep_tracker collect_conflict_deps() const;

        search_result search_dfs(nielsen_node *node, ptr_vector<nielsen_edge>& path, unsigned depth = 0);

        // Regex widening: overapproximate `str` by replacing variables with
        // the intersection of their primitive regex constraints (or Σ* if
        // unconstrained), replacing symbolic chars with their char ranges,
        // then checking if the approximation intersected with `regex` is empty.
        // Returns true if widening detects infeasibility (UNSAT).
        // Mirrors ZIPT NielsenNode.CheckRegexWidening (NielsenNode.cs:1350-1380)
        bool check_regex_widening(nielsen_node const& node, str_mem const& mem, dep_tracker& dep);

        // Check regex feasibility at a leaf node: for each variable with
        // multiple primitive regex constraints, check that the intersection
        // of all its regexes is non-empty.
        // Returns true if all constraints are feasible.
        // Mirrors ZIPT NielsenNode.CheckRegex)
        bool check_leaf_regex(nielsen_node const& node, dep_tracker& dep);

        // Apply the Parikh image filter to a node: generate modular length
        // constraints from regex memberships and append them to the node's
        // constraints.  Also performs a lightweight feasibility pre-check;
        // if a Parikh conflict is detected the node's conflict flag is set with
        // backtrack_reason::parikh_image.
        //
        // Guarded by node.m_parikh_applied so that constraints are generated
        // only once per node across DFS iterations.
        void apply_parikh_to_node(nielsen_node& node);

        // simplify expression and create a node from simplified expression.
        euf::snode *mk_rewrite(expr *e);

        // create a fresh variable with a unique name and the given sequence sort
        euf::snode* mk_fresh_var(sort* s);

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

        // power epsilon modifier: for a power token u^n in an equation,
        // branch: (1) base u = ε, (2) power is empty (n = 0 semantics).
        // mirrors ZIPT's PowerEpsilonModifier
        bool apply_power_epsilon(nielsen_node* node);

        // numeric comparison modifier: for equations involving power tokens
        // u^m and u^n with the same base, branch on m < n vs n <= m.
        // mirrors ZIPT's NumCmpModifier
        bool apply_num_cmp(nielsen_node* node);

        // CommPower-based power elimination split: when one side starts with
        // a power w^p and CommPower finds c base-pattern occurrences on the
        // other side but the ordering between p and c is unknown, branch:
        //   (1) p < c   (2) c ≤ p
        // After branching, simplify_and_init's CommPower pass resolves the
        // cancellation deterministically.
        // mirrors ZIPT's SplitPowerElim + NumCmpModifier
        bool apply_split_power_elim(nielsen_node* node);

        // constant numeric unwinding: for a power token u^n vs a constant
        // (non-variable), branch: (1) n = 0 (u^n = ε), (2) n >= 1 (peel one u).
        // mirrors ZIPT's ConstNumUnwindingModifier
        bool apply_const_num_unwinding(nielsen_node* node);

        // regex if split: for str_mem s ∈ R where R decomposes as ite(c, th, el),
        // branch into s ∈ th under condition c, and s ∈ el under condition ¬c.
        bool apply_regex_if_split(nielsen_node* node);

        // star introduction: for a str_mem x·s ∈ R where a cycle is detected
        // (backedge exists), introduce stabilizer: x ∈ base* with x split.
        // mirrors ZIPT's StarIntrModifier
        bool apply_star_intr(nielsen_node* node);

        // generalized power introduction: for an equation where one head is
        // a variable v and the other side has ground prefix + a variable x
        // forming a cycle back to v, introduce v = base^n · suffix.
        // mirrors ZIPT's GPowerIntrModifier
        bool apply_gpower_intr(nielsen_node* node);

        // generalized regex factorization (Boolean closure derivation rule)
        bool apply_regex_factorization(nielsen_node* node);

        // helper for apply_gpower_intr: fires the substitution.
        // `fwd=true` uses left-to-right decomposition; `fwd=false` mirrors ZIPT's
        // backward (right-to-left) direction.
        bool fire_gpower_intro(nielsen_node* node, str_eq const& eq,
                               euf::snode* var, euf::snode_vector const& ground_prefix_orig, bool fwd);

        // heuristic string equation splitting. Left to right scanning for shortest prefix with matching variables.
        bool apply_signature_split(nielsen_node* node);

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
        bool apply_var_num_unwinding_eq(nielsen_node* node);

        bool apply_var_num_unwinding_mem(nielsen_node* node);

        // find the first power token in any str_eq at this node
        euf::snode* find_power_token(nielsen_node* node) const;

        // find a power token facing a constant (char/non-var) token at either end
        // of an equation; returns orientation via `fwd` (true=head, false=tail).
        bool find_power_vs_non_var(nielsen_node* node, euf::snode*& power, euf::snode*& other_head, str_eq const*& eq_out, bool& fwd) const;

        // find a power token facing a variable token at either end of an
        // equation; returns orientation via `fwd` (true=head, false=tail).
        bool find_power_vs_var(nielsen_node* node, euf::snode*& power, euf::snode*& var_head, str_eq const*& eq_out, bool& fwd) const;

        bool find_power_vs_var(nielsen_node* node, euf::snode*& power, str_mem const*& mem_out, bool& fwd) const;

        // -----------------------------------------------
        // Integer feasibility subsolver methods
        // -----------------------------------------------

        // Constraint.Shared: assert all root-level length/Parikh constraints to
        // m_solver at the base level (outside push/pop). Called once at the start
        // of solve(). Makes derived constraints immediately visible to m_solver
        // for arithmetic pruning at every DFS node, not just the root.
        // Mirrors ZIPT's Constraint.Shared forwarding mechanism.
        void assert_root_constraints_to_solver();

        // Generate |LHS| = |RHS| length constraints for a non-root node's own
        // string equalities and add them as constraints on the node.
        // Called once per node (guarded by m_node_len_constraints_generated).
        // Uses compute_length_expr (mod-count-aware) so that variables with
        // non-zero modification counts get fresh length variables.
        // Mirrors ZIPT's Constraint.Shared forwarding for per-node equations.
        void generate_node_length_constraints(nielsen_node* node);

        // check integer feasibility of the constraints along the current path.
        // returns true if feasible (including unknown), false only if l_false.
        // Precondition: all path constraints have been incrementally asserted to
        // m_solver by search_dfs via push/pop, so a plain check() suffices.
        // l_undef (resource limit / timeout) is treated as feasible so that the
        // search continues rather than reporting a false unsatisfiability.
        bool check_int_feasibility();

        dep_tracker get_subsolver_dependency(nielsen_node* n);

        // check whether lhs <= rhs is implied by the path constraints.
        // mirrors ZIPT's NielsenNode.IsLe(): temporarily asserts NOT(lhs <= rhs)
        // and returns true iff the result is unsatisfiable (i.e., lhs <= rhs is
        // entailed).  Path constraints are already in the solver incrementally.
        bool check_lp_le(expr* lhs, expr* rhs, nielsen_node* n, dep_tracker& dep);

        // create an integer constraint: lhs <kind> rhs
        constraint mk_constraint(expr* fml, dep_tracker const& dep);

        // get the exponent expression from a power snode (arg(1))
        expr* get_power_exponent(euf::snode* power);

        // -----------------------------------------------
        // Modification counter methods for substitution length tracking.
        // mirrors ZIPT's NielsenEdge.IncModCount / DecModCount and
        // NielsenNode constructor length assertion logic.
        // -----------------------------------------------

        // Get or create a fresh symbolic character variable for the given variable
        expr_ref get_or_create_char_var(euf::snode* var);

        // Get or create a fresh integer variable for gpower n (full exponent) for the given variable
        expr_ref get_or_create_gpower_n_var(euf::snode* var);

        // Get or create a fresh integer variable for gpower m (partial exponent) for the given variable
        expr_ref get_or_create_gpower_m_var(euf::snode* var);

        // Compute and add |x| = |u| length constraints to an edge for all
        // its non-eliminating substitutions. Uses current m_mod_cnt.
        // Temporarily bumps m_mod_cnt for RHS computation, then restores.
        // Called lazily on first edge traversal in search_dfs.
        void add_subst_length_constraints(nielsen_edge* e);

        // Bump modification counts for an edge's non-eliminating substitutions.
        // Called when entering an edge during DFS.
        void inc_edge_mod_counts(nielsen_edge* e);

        // Restore modification counts for an edge's non-eliminating substitutions.
        // Called when backtracking from an edge during DFS.
        void dec_edge_mod_counts(nielsen_edge* e);
    };

}
