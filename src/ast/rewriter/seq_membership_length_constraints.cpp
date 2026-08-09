/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_membership_length_constraints.cpp

Abstract:

    Consistency checks for sequence membership constraints based on lengths.

--*/

#include "ast/rewriter/seq_membership_length_constraints.h"
#include "ast/rewriter/seq_rewriter.h"

namespace seq {

lbool membership_length_constraints::check(
    constraint_vector const& constraints,
    atom_vectors const& atoms,
    bucket_vectors const& buckets) {
    m_core.reset();
    SASSERT(constraints.size() == atoms.size());
    if (constraints.size() != atoms.size())
        return l_true;

    obj_map<expr, unsigned> var_min_lengths;
    obj_map<expr, void*> var_dependencies;
    for (unsigned i = 0; i < constraints.size(); ++i) {
        atom_vector const& bucket = atoms[i];
        if (bucket.size() != 1 || !bucket[0].is_var())
            continue;
        auto const& [term, regex, dependency] = constraints[i];
        auto info = m_rw.u().re.get_info(regex);
        if (!info.is_known())
            continue;
        expr* var = bucket[0].var.get();
        unsigned current = 0;
        if (!var_min_lengths.find(var, current) || info.min_length > current) {
            var_min_lengths.insert(var, info.min_length);
            var_dependencies.insert(var, dependency);
        }
    }

    for (bucket_vector const& variable_buckets : buckets) {
        for (bucket const& b : variable_buckets) {
            auto state_info = m_rw.u().re.get_info(b.state);
            if (!state_info.is_known())
                continue;
            unsigned bucket_min_length = state_info.min_length;
            if (b.target) {
                auto target_info = m_rw.u().re.get_info(b.target);
                if (!target_info.is_known() || target_info.max_length == UINT_MAX)
                    continue;
                bucket_min_length = state_info.min_length > target_info.max_length ?
                    state_info.min_length - target_info.max_length : 0;
            }
            unsigned current = 0;
            if (!var_min_lengths.find(b.var, current) || bucket_min_length > current) {
                var_min_lengths.insert(b.var, bucket_min_length);
                var_dependencies.insert(b.var, b.dependency);
            }
        }
    }

    auto add_dependency = [&](void* dependency) {
        if (!dependency)
            return;
        for (void* existing : m_core)
            if (existing == dependency)
                return;
        m_core.push_back(dependency);
    };

    for (unsigned i = 0; i < constraints.size(); ++i) {
        auto const& [term, regex, dependency] = constraints[i];
        auto info = m_rw.u().re.get_info(regex);
        if (!info.is_known() || info.max_length == UINT_MAX)
            continue;
        m_core.reset();
        unsigned min_length = 0;
        for (atom const& a : atoms[i]) {
            if (!a.is_var()) {
                min_length = add_truncate(min_length, 1);
                continue;
            }
            unsigned var_min_length = 0;
            if (!var_min_lengths.find(a.var.get(), var_min_length))
                continue;
            min_length = add_truncate(min_length, var_min_length);
            void* var_dependency = nullptr;
            if (var_dependencies.find(a.var.get(), var_dependency))
                add_dependency(var_dependency);
        }
        if (min_length <= info.max_length)
            continue;
        add_dependency(dependency);
        return l_false;
    }
    m_core.reset();
    return l_true;
}

}
