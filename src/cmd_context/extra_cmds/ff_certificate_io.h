#pragma once
#include "cmd_context/cmd_context.h"
#include "ast/ff_decl_plugin.h"
#include "math/ff/ff_certificate.h"
#include <unordered_map>
#include <unordered_set>
#include <set>

// Shared frontend/output for the standalone and SAT-integrated proof commands.
// This is producer code: independent replay binds every exported input and step.
class ff_certificate_io {
    cmd_context& ctx;
    ast_manager& m;
    ff_util field;
    sort* field_sort;
    std::unordered_map<expr*, ff::polynomial> cache;
    std::unordered_map<expr*, unsigned> variable_ids;
    size_t cached_terms = 0, cache_limit;
public:
    ptr_vector<expr> variables;
    ff_certificate_io(cmd_context& ctx, sort* s, size_t limit = SIZE_MAX) :
        ctx(ctx), m(ctx.m()), field(m), field_sort(s), cache_limit(limit) {}

    ff::polynomial encode(expr* root, ff::engine& arithmetic) {
        ptr_vector<expr> pending; pending.push_back(root);
        while (!pending.empty()) {
            if (!m.inc()) throw ff::exhausted();
            expr* t = pending.back();
            if (cache.contains(t)) { pending.pop_back(); continue; }
            if (!is_app(t) || t->get_sort() != field_sort)
                throw cmd_exception("finite-field certificates require pure field terms");
            app* a = to_app(t);
            if (!is_uninterp_const(a) && a->get_family_id() != field.get_fid())
                throw cmd_exception("finite-field certificates do not yet certify theory combination");
            bool ready = true;
            for (expr* arg : *a) if (!cache.contains(arg)) { pending.push_back(arg); ready = false; }
            if (!ready) continue;
            rational value;
            ff::polynomial f;
            if (field.is_numeral(t, value)) f = arithmetic.constant(value);
            else if (is_uninterp_const(t)) {
                if (variables.size() >= 100000) throw ff::exhausted();
                variable_ids.emplace(t, variables.size());
                f = arithmetic.variable(variables.size()); variables.push_back(t);
            }
            else if (a->get_decl_kind() == OP_FF_NEG)
                f = arithmetic.scale(cache.at(a->get_arg(0)), rational(-1));
            else if (a->get_decl_kind() == OP_FF_ADD || a->get_decl_kind() == OP_FF_MUL || a->get_decl_kind() == OP_FF_BITSUM) {
                bool mul = a->get_decl_kind() == OP_FF_MUL;
                f = arithmetic.constant(rational(mul ? 1 : 0));
                rational weight(1);
                for (expr* arg : *a) {
                    f = mul ? arithmetic.mul(f, cache.at(arg)) : arithmetic.add(std::move(f), cache.at(arg), weight);
                    if (a->get_decl_kind() == OP_FF_BITSUM) weight = mod(rational(2) * weight, field.modulus(field_sort));
                }
            }
            else throw cmd_exception("unsupported finite-field certificate operator");
            for (auto const& [mon, c] : f) cached_terms += 1 + mon.size();
            if (cached_terms > cache_limit) throw ff::exhausted{"normalization-storage"};
            cache.emplace(t, std::move(f));
        }
        return cache.at(root);
    }

    ff::polynomial equation(expr* e, ff::engine& arithmetic) {
        expr *a, *b;
        if (!m.is_eq(e, a, b) || a->get_sort() != field_sort)
            throw cmd_exception("expected an equality in the certificate field");
        auto lhs = encode(a, arithmetic), rhs = encode(b, arithmetic);
        return arithmetic.add(std::move(lhs), rhs, rational(-1));
    }

    std::vector<unsigned> support(expr* e) {
        std::set<unsigned> result;
        std::unordered_set<expr*> visited;
        ptr_vector<expr> pending; pending.push_back(e);
        while (!pending.empty()) {
            if (!m.inc()) throw ff::exhausted();
            expr* t = pending.back(); pending.pop_back();
            if (!visited.insert(t).second) continue;
            auto it = variable_ids.find(t);
            if (it != variable_ids.end()) result.insert(it->second);
            else if (is_app(t)) for (expr* a : *to_app(t)) pending.push_back(a);
        }
        return {result.begin(), result.end()};
    }

    void display(std::ostream& out, std::vector<ff::polynomial> const& equations,
                 ff::certificate const& proof, std::set<unsigned> const* required = nullptr) {
        auto check_output = [&]() {
            if (!m.inc() || out.tellp() > 32 * 1024 * 1024) throw ff::exhausted();
        };
        std::set<unsigned> used;
        if (required) {
            used = *required;
            for (auto const& f : equations) for (auto const& [mon, c] : f) used.insert(mon.begin(), mon.end());
            for (auto const& n : proof.nodes) used.insert(n.factor.begin(), n.factor.end());
        }
        else for (unsigned v = 0; v < variables.size(); ++v) used.insert(v);
        std::vector<unsigned> ids(variables.size(), ~0u);
        out << "(ff-certificate\n :version 1\n :modulus " << field.modulus(field_sort) << "\n :variables (";
        unsigned next = 0;
        for (unsigned v : used) {
            if (!m.inc() || v >= variables.size()) throw ff::exhausted();
            ids[v] = next++; ctx.display(out, variables[v]); out << ' ';
        }
        out << ")\n :inputs (";
        for (auto const& f : equations) {
            if (!m.inc()) throw ff::exhausted();
            out << "\n  (";
            for (auto const& [mon, c] : f) {
                out << '(' << c;
                for (unsigned v : mon) out << ' ' << ids[v];
                out << ')'; check_output();
            }
            out << ')';
        }
        out << ")\n :nodes (";
        for (auto const& n : proof.nodes) {
            check_output();
            if (n.kind == ff::certificate::rule::input) out << "\n  (input " << n.left << ')';
            else if (n.kind == ff::certificate::rule::add) out << "\n  (add " << n.left << ' ' << n.right << ')';
            else {
                out << "\n  (mul " << n.left << ' ' << n.coefficient << " (";
                for (unsigned v : n.factor) out << ids[v] << ' ';
                out << "))";
            }
        }
        out << ")\n :root " << proof.root << ")\n";
    }
};
