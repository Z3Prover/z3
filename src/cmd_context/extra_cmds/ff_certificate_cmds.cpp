/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_certificate_cmds.cpp

Abstract:

    ff-certify command: reconstructs and prints a standalone polynomial
    ideal-membership certificate (see ff_certificate.h) from the field
    equations currently asserted in the command context.

Author:

    Romain Soulat

--*/
#include "cmd_context/cmd_context.h"
#include "cmd_context/parametric_cmd.h"
#include "ast/ff_decl_plugin.h"
#include "math/ff/ff_certificate.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include <sstream>
#include <unordered_map>

namespace {
    class ff_certify_cmd : public parametric_cmd {
    public:
        ff_certify_cmd() : parametric_cmd("ff-certify") {}
        char const *get_usage() const override { return "(<keyword> <value>)*"; }
        char const *get_main_descr() const override {
            return "reconstruct a standalone polynomial contradiction from current field equations";
        }
        void init_pdescrs(cmd_context &, param_descrs &d) override {
            d.insert("max_steps", CPK_UINT, "maximum polynomial operations", "2000000");
            d.insert("max_terms", CPK_UINT, "maximum terms per polynomial", "4096");
            d.insert("max_nodes", CPK_UINT, "maximum derivation DAG nodes", "100000");
            d.insert("timeout", CPK_UINT, "certificate reconstruction timeout in milliseconds", "10000");
        }
        void execute(cmd_context &ctx) override {
            ast_manager &m = ctx.m();
            ff_util field(m);
            cancel_eh<reslimit> cancel(m.limit());
            scoped_ctrl_c interrupt(cancel);
            scoped_timer timer(m_params.get_uint("timeout", 10000), &cancel);
            try {
                // Read assertions directly: no unsupported preprocessing can
                // become an implicit assumption of the exported certificate.
                ptr_vector<expr> todo, literals;
                for (expr *f : ctx.assertions()) todo.push_back(f);
                std::reverse(todo.begin(), todo.end());
                sort *s = nullptr;
                while (!todo.empty()) {
                    if (!m.inc()) throw ff::exhausted();
                    expr *f = todo.back(); todo.pop_back();
                    if (m.is_and(f)) {
                        app *a = to_app(f);
                        for (unsigned i = a->get_num_args(); i-- > 0;) todo.push_back(a->get_arg(i));
                        continue;
                    }
                    expr *a, *b;
                    if (!m.is_eq(f, a, b) || !field.is_ff(a))
                        throw cmd_exception("ff-certify supports only conjunctions of field equalities");
                    if (s && s != a->get_sort())
                        throw cmd_exception("ff-certify requires one field per certificate");
                    s = a->get_sort();
                    if (literals.size() >= 4096) throw ff::exhausted();
                    literals.push_back(f);
                }
                if (!s) throw cmd_exception("ff-certify requires field equations");
                auto const &prime = field.modulus(s);
                if (prime.get_num_bits() > 4096)
                    throw cmd_exception("ff-certify modulus exceeds the certificate profile");
                ff::engine arithmetic(prime, m.limit(), m_params.get_uint("max_steps", 2000000),
                                      m_params.get_uint("max_terms", 4096), false, false, false);
                ptr_vector<expr> variables;
                std::unordered_map<expr *, ff::polynomial> cache;
                auto encode = [&](expr *root) {
                    ptr_vector<expr> pending; pending.push_back(root);
                    while (!pending.empty()) {
                        if (!m.inc()) throw ff::exhausted();
                        expr *t = pending.back();
                        if (cache.contains(t)) { pending.pop_back(); continue; }
                        if (!is_app(t) || t->get_sort() != s)
                            throw cmd_exception("ff-certify requires pure field terms");
                        app *a = to_app(t);
                        if (!is_uninterp_const(a) && a->get_family_id() != field.get_fid())
                            throw cmd_exception("ff-certify does not yet certify theory combination");
                        bool ready = true;
                        for (expr *arg : *a) if (!cache.contains(arg)) { pending.push_back(arg); ready = false; }
                        if (!ready) continue;
                        rational value;
                        ff::polynomial f;
                        if (field.is_numeral(t, value)) f = arithmetic.constant(value);
                        else if (is_uninterp_const(t)) {
                            f = arithmetic.variable(variables.size()); variables.push_back(t);
                        }
                        else if (a->get_decl_kind() == OP_FF_NEG)
                            f = arithmetic.scale(cache.at(a->get_arg(0)), rational(-1));
                        else if (a->get_decl_kind() == OP_FF_ADD || a->get_decl_kind() == OP_FF_MUL ||
                                 a->get_decl_kind() == OP_FF_BITSUM) {
                            bool mul = a->get_decl_kind() == OP_FF_MUL;
                            f = arithmetic.constant(rational(mul ? 1 : 0));
                            rational weight(1);
                            for (expr *arg : *a) {
                                f = mul ? arithmetic.mul(f, cache.at(arg)) : arithmetic.add(std::move(f), cache.at(arg), weight);
                                if (a->get_decl_kind() == OP_FF_BITSUM) weight = mod(rational(2) * weight, prime);
                            }
                        }
                        else throw cmd_exception("ff-certify: unsupported field operator");
                        cache.emplace(t, std::move(f));
                    }
                    return cache.at(root);
                };
                std::vector<ff::polynomial> equations;
                for (expr *literal : literals) {
                    auto *eq = to_app(literal);
                    auto lhs = encode(eq->get_arg(0));
                    auto rhs = encode(eq->get_arg(1));
                    equations.push_back(arithmetic.add(std::move(lhs), rhs, rational(-1)));
                }
                ff::certificate proof;
                if (!ff::certify(arithmetic, equations, proof, m_params.get_uint("max_nodes", 100000))) {
                    ctx.regular_stream() << "(ff-certificate-unavailable no-polynomial-refutation)\n";
                    return;
                }
                // Buffer the entire object so cancellation cannot leave a
                // truncated object that looks like a successful certificate.
                std::ostringstream out;
                out << "(ff-certificate\n :version 1\n :modulus " << prime << "\n :variables (";
                for (expr *v : variables) { ctx.display(out, v); out << ' '; }
                out << ")\n :inputs (";
                for (auto const &f : equations) {
                    if (!m.inc()) throw ff::exhausted();
                    out << "\n  (";
                    for (auto const &[mon, c] : f) {
                        out << '(' << c;
                        for (unsigned v : mon) out << ' ' << v;
                        out << ')';
                    }
                    out << ')';
                }
                out << ")\n :nodes (";
                for (auto const &n : proof.nodes) {
                    if (!m.inc()) throw ff::exhausted();
                    if (n.kind == ff::certificate::rule::input) out << "\n  (input " << n.left << ')';
                    else if (n.kind == ff::certificate::rule::add) out << "\n  (add " << n.left << ' ' << n.right << ')';
                    else {
                        out << "\n  (mul " << n.left << ' ' << n.coefficient << " (";
                        for (unsigned v : n.factor) out << v << ' ';
                        out << "))";
                    }
                }
                out << ")\n :root " << proof.root << ")\n";
                ctx.regular_stream() << out.str();
            }
            catch (ff::exhausted const &) {
                ctx.regular_stream() << "(ff-certificate-unavailable budget)\n";
            }
        }
    };
}
void install_ff_certificate_cmds(cmd_context &ctx) { ctx.insert(alloc(ff_certify_cmd)); }
