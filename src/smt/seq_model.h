/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_model.h

Abstract:

    Model construction for the Nielsen-based string solver (theory_nseq).

    After the Nielsen graph search returns sat, this module extracts
    variable-to-value assignments from the satisfying leaf node and
    builds model_value_proc callbacks for the SMT model generator.

    The workflow is:
      1. init() — allocate seq_factory, register existing string literals,
         and extract variable assignments from the satisfying Nielsen node.
      2. mk_value(enode*) — return a model_value_proc that lazily builds
         the concrete value for a given enode.
      3. finalize() — clean up temporary state.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "smt/seq/seq_state.h"   // tracked_str_mem
#include "model/seq_factory.h"

class proto_model;

namespace smt {

    class enode;
    class model_generator;
    struct tracked_str_mem;
    class model_value_proc;
    class seq_snode_value_proc;

    class seq_model {
        friend class seq_snode_value_proc;

        ast_manager&    m;
        context&        m_ctx;
        seq_util&       m_seq;
        seq_rewriter&   m_rewriter;
        euf::sgraph&    m_sg;

        // factory for generating fresh string/regex values
        seq_factory*    m_factory = nullptr;

        // variable assignments extracted from the satisfying Nielsen node.
        // maps snode id -> expr* (concrete value)
        u_map<expr*> m_var_values;

        // trail for GC protection of generated expressions
        expr_ref_vector m_trail;

        // integer variable model from sat_path constraints
        model_ref m_int_model;
        model_generator* m_mg = nullptr;

        // per-variable regex constraints: maps snode id -> intersected regex snode.
        // collected during init() from the state's str_mem list.
        u_map<euf::snode*> m_var_regex;

    public:
        seq_model(ast_manager& m, context& ctx, seq_util& seq,
                   seq_rewriter& rw, euf::sgraph& sg);

        // Phase 1: initialize model construction.
        // Allocates seq_factory, registers it with mg, collects
        // existing string literals, and extracts variable assignments
        // from the satisfying Nielsen leaf node.
        void init(model_generator& mg, seq::nielsen_graph& nielsen);

        // Phase 2: build a model_value_proc for the given enode.
        // Returns nullptr if the enode is not a sequence/string sort.
        model_value_proc* mk_value(enode* n, model_generator& mg);

        // Phase 3: clean up temporary model construction state.
        void finalize(model_generator& mg);

        // Validate that model assignments satisfy all regex membership
        // constraints from the state.  Checks positive and negative
        // memberships.  Returns true if all constraints pass.
        bool validate_regex(tracked_str_mem const& mem, ::proto_model& mdl);

    private:
        // extract variable assignments from the sat path (root-to-leaf edges).
        // Composes substitutions along the path to compute final var values.
        void extract_assignments(ptr_vector<seq::nielsen_edge> const& sat_path);

        // recursively substitute known variable assignments into an snode tree.
        // Returns a concrete Z3 expression.
        expr_ref snode_to_value(euf::snode* n, model_generator& mg);

        // Same as above, but optionally uses pre-evaluated model values for
        // enode dependencies (provided by model_generator).
        expr_ref snode_to_value(euf::snode* n, model_generator& mg, obj_map<enode, expr*> const* dep_values);

        // Collect enode dependencies required to evaluate an snode value.
        void collect_dependencies(euf::snode* n, obj_hashtable<enode>& seen, ptr_vector<enode>& deps) const;

        // register all string literals appearing in the constraint store
        // with the factory to avoid collisions with fresh values.
        void register_existing_values(seq::nielsen_graph& nielsen);

        // look up or compute the value for an snode variable.
        // If no assignment exists, delegates to mk_fresh_value.
        expr* get_var_value(euf::snode* var, obj_map<enode, expr*> const* dep_values = nullptr);

        // generate a fresh value for a variable, respecting regex
        // membership constraints. If the variable has associated
        // regex constraints (collected during init), generates a
        // witness satisfying the intersection; otherwise falls back
        // to a plain fresh value from the factory.
        expr* mk_fresh_value(euf::snode* var, obj_map<enode, expr*> const* dep_values = nullptr);

        // collect per-variable regex constraints from the state.
        // For each positive str_mem, records the regex (or intersects
        // with existing) into m_var_regex keyed by the string snode id.
        void collect_var_regex_constraints(seq::nielsen_node const* sat_node);
    };

}
