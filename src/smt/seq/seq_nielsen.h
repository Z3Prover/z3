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

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-02
    Clemens Eisenhofer 2026-03-02

--*/

#pragma once

#include "util/vector.h"
#include "util/uint_set.h"
#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/euf/euf_sgraph.h"

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
        subsumption,
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

        bool operator==(dep_tracker const& other) const { return m_bits == other.m_bits; }
        bool operator!=(dep_tracker const& other) const { return !(*this == other); }
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
            m_var(var), m_replacement(repl), m_dep(dep) {}

        // an eliminating substitution does not contain the variable in the replacement
        bool is_eliminating() const;

        bool operator==(nielsen_subst const& other) const {
            return m_var == other.m_var && m_replacement == other.m_replacement;
        }
    };

    // edge in the Nielsen graph connecting two nodes
    // mirrors ZIPT's NielsenEdge
    class nielsen_edge {
        nielsen_node*           m_src;
        nielsen_node*           m_tgt;
        vector<nielsen_subst>   m_subst;
        ptr_vector<str_eq>      m_side_str_eq;    // side constraints: string equalities
        ptr_vector<str_mem>     m_side_str_mem;    // side constraints: regex memberships
        bool                    m_is_progress;     // does this edge represent progress?
    public:
        nielsen_edge(nielsen_node* src, nielsen_node* tgt, bool is_progress);

        nielsen_node* src() const { return m_src; }
        nielsen_node* tgt() const { return m_tgt; }

        void set_tgt(nielsen_node* tgt) { m_tgt = tgt; }

        vector<nielsen_subst> const& subst() const { return m_subst; }
        void add_subst(nielsen_subst const& s) { m_subst.push_back(s); }

        void add_side_str_eq(str_eq* eq) { m_side_str_eq.push_back(eq); }
        void add_side_str_mem(str_mem* mem) { m_side_str_mem.push_back(mem); }

        ptr_vector<str_eq> const& side_str_eq() const { return m_side_str_eq; }
        ptr_vector<str_mem> const& side_str_mem() const { return m_side_str_mem; }

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

        // edges
        ptr_vector<nielsen_edge> m_outgoing;
        nielsen_node*           m_backedge = nullptr;

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

        // edge access
        ptr_vector<nielsen_edge> const& outgoing() const { return m_outgoing; }
        void add_outgoing(nielsen_edge* e) { m_outgoing.push_back(e); }

        nielsen_node* backedge() const { return m_backedge; }
        void set_backedge(nielsen_node* n) { m_backedge = n; }

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
    };

    // the overall Nielsen transformation graph
    // mirrors ZIPT's NielsenGraph
    class nielsen_graph {
        euf::sgraph&                  m_sg;
        region                        m_region;
        ptr_vector<nielsen_node>      m_nodes;
        ptr_vector<nielsen_edge>      m_edges;
        nielsen_node*                 m_root = nullptr;
        unsigned                      m_run_idx = 0;
        unsigned                      m_depth_bound = 0;
        unsigned                      m_next_mem_id = 0;

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

        // add constraints to the root node from external solver
        void add_str_eq(euf::snode* lhs, euf::snode* rhs);
        void add_str_mem(euf::snode* str, euf::snode* regex);

        // run management
        unsigned run_idx() const { return m_run_idx; }
        void inc_run_idx();

        // access all nodes
        ptr_vector<nielsen_node> const& nodes() const { return m_nodes; }
        unsigned num_nodes() const { return m_nodes.size(); }

        // depth bound for iterative deepening
        unsigned depth_bound() const { return m_depth_bound; }
        void set_depth_bound(unsigned d) { m_depth_bound = d; }

        // generate next unique regex membership id
        unsigned next_mem_id() { return m_next_mem_id++; }

        // display for debugging
        std::ostream& display(std::ostream& out) const;

        // reset all nodes and state
        void reset();
    };

}
