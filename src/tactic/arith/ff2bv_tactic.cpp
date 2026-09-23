#include "tactic/arith/ff2bv_tactic.h"
#include "tactic/tactical.h"
#include "ast/ff_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/converters/model_converter.h"
#include "ast/ast_translation.h"
#include "model/model_evaluator.h"
#include <unordered_map>

namespace {
    class ff_model_converter : public model_converter {
        ast_manager &m;
        expr_ref_vector m_original, m_encoded;

    public:
        explicit ff_model_converter(ast_manager &m) : m(m), m_original(m), m_encoded(m) {}
        void add(expr *original, expr *encoded) {
            m_original.push_back(original);
            m_encoded.push_back(encoded);
        }
        void operator()(model_ref &mdl) override {
            ff_util ff(m);
            bv_util bv(m);
            // Evaluate all encodings before removing any auxiliary interpretations.
            expr_ref_vector values(m);
            model_evaluator eval(*mdl);
            eval.set_model_completion(true);
            for (expr *e : m_encoded) {
                expr_ref value(m);
                eval(e, value);
                values.push_back(value);
            }
            for (unsigned i = 0; i < m_original.size(); ++i) {
                rational value;
                unsigned width;
                if (!bv.is_numeral(values.get(i), value, width))
                    throw tactic_exception("ff2bv: incomplete bit-vector model");
                mdl->register_decl(to_app(m_original.get(i))->get_decl(),
                                   ff.mk_numeral(value, m_original.get(i)->get_sort()));
                mdl->unregister_decl(to_app(m_encoded.get(i))->get_decl());
            }
        }
        model_converter *translate(ast_translation &tr) override {
            auto *result = alloc(ff_model_converter, tr.to());
            for (unsigned i = 0; i < m_original.size(); ++i)
                result->add(tr(m_original.get(i)), tr(m_encoded.get(i)));
            return result;
        }
        void display(std::ostream &out) override {
            out << "(ff2bv-model-converter)";
        }
    };

    class ff_encoder {
        ast_manager &m;
        ff_util ff;
        bv_util bv;
        th_rewriter simplify;
        obj_map<expr, expr *> cache;
        expr_ref_vector pins;

    public:
        expr_ref_vector bounds;
        ref<ff_model_converter> mc;
        explicit ff_encoder(ast_manager &m)
            : m(m), ff(m), bv(m), simplify(m), pins(m), bounds(m), mc(alloc(ff_model_converter, m)) {}

        expr_ref reduce(expr *x, sort *field, unsigned wide) {
            // Unsigned remainder chooses the canonical residue in [0,p-1].
            // It fits in w bits, so extracting the low w bits loses no value.
            unsigned w = ff.width(field);
            expr_ref p(bv.mk_numeral(ff.modulus(field), wide), m);
            expr_ref r(bv.mk_bv_urem(x, p), m);
            if (wide != w)
                r = bv.mk_extract(w - 1, 0, r);
            simplify(r);
            return r;
        }
        expr_ref binary(expr *a, expr *b, sort *field, bool mul) {
            // Canonical inputs satisfy 0<=a,b<p<=2^w. Their sum fits in
            // w+1 bits and product in 2*w bits, so widening BEFORE arithmetic
            // prevents BV overflow from changing the subsequent reduction mod p.
            unsigned w = ff.width(field), wide = mul ? 2 * w : w + 1;
            expr_ref x(bv.mk_zero_extend(wide - w, a), m), y(bv.mk_zero_extend(wide - w, b), m);
            expr_ref r(mul ? bv.mk_bv_mul(x, y) : bv.mk_bv_add(x, y), m);
            return reduce(r, field, wide);
        }
        expr_ref encode_app(app *a) {
            expr_ref_vector args(m);
            for (expr *e : *a)
                args.push_back(cache.find(e));
            sort *s = a->get_sort();
            expr_ref r(m);
            rational value;
            if (ff.is_numeral(a, value))
                return expr_ref(bv.mk_numeral(value, ff.width(s)), m);
            if (ff.is_ff(s) && is_uninterp_const(a)) {
                // The bound makes BV values bijective with canonical field
                // representatives; without it BV equality would distinguish
                // different encodings of the same field element.
                r = m.mk_fresh_const("ff", bv.mk_sort(ff.width(s)));
                // p=2 is a power of two: every one-bit value is already in range.
                if (!ff.modulus(s).is_power_of_two())
                    bounds.push_back(bv.mk_ult(r, bv.mk_numeral(ff.modulus(s), ff.width(s))));
                mc->add(a, r);
                return r;
            }
            if (a->get_family_id() == ff.get_fid()) {
                switch (a->get_decl_kind()) {
                case OP_FF_NEG: {
                    // For canonical x, 0<=p-x<=p: no unsigned underflow.
                    // (p-x) mod p equals -x, including the special case x=0.
                    unsigned w = ff.width(s);
                    expr_ref x(bv.mk_zero_extend(1, args.get(0)), m);
                    r = bv.mk_bv_sub(bv.mk_numeral(ff.modulus(s), w + 1), x);
                    return reduce(r, s, w + 1);
                }
                case OP_FF_ADD:
                case OP_FF_MUL:
                    r = args.get(0);
                    for (unsigned i = 1; i < args.size(); ++i)
                        r = binary(r, args.get(i), s, a->get_decl_kind() == OP_FF_MUL);
                    return r;
                case OP_FF_BITSUM:
                    // Horner form also handles characteristic two and long bit sums.
                    // a_0+2*(a_1+2*(...)) = sum(2^i*a_i) by distributivity.
                    // Reduction at each step preserves this field identity;
                    // neither Boolean inputs nor a no-wrap bound is needed.
                    r = args.back();
                    for (unsigned i = args.size() - 1; i-- > 0;) {
                        r = binary(r, r, s, false);
                        r = binary(r, args.get(i), s, false);
                    }
                    return r;
                default: throw tactic_exception("ff2bv: unsupported field operator");
                }
            }
            // Rebuild polymorphic Boolean operators at their translated sorts.
            if (m.is_eq(a))
                r = m.mk_eq(args.get(0), args.get(1));
            else if (m.is_distinct(a))
                r = m.mk_distinct(args.size(), args.data());
            else if (m.is_ite(a))
                r = m.mk_ite(args.get(0), args.get(1), args.get(2));
            else {
                if (ff.is_ff(s))
                    throw tactic_exception("ff2bv: uninterpreted field functions are not QF_FF");
                for (expr *e : *a)
                    if (ff.is_ff(e))
                        throw tactic_exception("ff2bv: unsupported field consumer");
                r = m.mk_app(a->get_decl(), args.size(), args.data());
            }
            simplify(r);
            return r;
        }
        expr_ref operator()(expr *root) {
            // Iterative DAG traversal: shared circuit wires are encoded once.
            ptr_vector<expr> todo;
            todo.push_back(root);
            while (!todo.empty()) {
                if (!m.inc())
                    throw tactic_exception(m.limit().get_cancel_msg());
                expr *e = todo.back();
                if (cache.contains(e)) {
                    todo.pop_back();
                    continue;
                }
                if (!is_app(e))
                    throw tactic_exception("ff2bv supports quantifier-free formulas only");
                bool ready = true;
                for (expr *arg : *to_app(e))
                    if (!cache.contains(arg)) {
                        todo.push_back(arg);
                        ready = false;
                    }
                if (!ready)
                    continue;
                expr_ref r = encode_app(to_app(e));
                cache.insert(e, r);
                pins.push_back(r);
                todo.pop_back();
            }
            return expr_ref(cache.find(root), m);
        }
    };

    class ff2bv_tactic : public tactic {
        ast_manager &m;
        unsigned m_calls = 0;

    public:
        explicit ff2bv_tactic(ast_manager &m) : m(m) {}
        char const *name() const override {
            return "ff2bv";
        }
        tactic *translate(ast_manager &target) override {
            return alloc(ff2bv_tactic, target);
        }
        void cleanup() override {}
        void collect_statistics(statistics &st) const override {
            st.update("ff bv fallback calls", m_calls);
        }
        void reset_statistics() override {
            m_calls = 0;
        }
        void operator()(goal_ref const &g, goal_ref_buffer &result) override {
            ++m_calls;
            if (g->proofs_enabled())
                throw tactic_exception("QF_FF certificates are not supported in v1");
            ff_encoder encoder(m);
            // Build a separate goal so unsupported input leaves the original intact.
            goal_ref out = alloc(goal, *g, true);
            for (unsigned i = 0; i < g->size(); ++i)
                out->assert_expr(encoder(g->form(i)), nullptr, g->dep(i));
            for (expr *bound : encoder.bounds)
                out->assert_expr(bound);
            if (g->models_enabled())
                out->add(encoder.mc.get());
            g->reset_all();
            g->copy_from(*out);
            g->inc_depth();
            result.push_back(g.get());
        }
    };
    class has_ff_probe : public probe {
    public:
        result operator()(goal const &g) override {
            bool found = false;
            ff_util ff(g.m());
            auto visitor = [&](expr *e) { found |= ff.is_ff(e); };
            for (unsigned i = 0; i < g.size() && !found; ++i)
                for_each_expr(visitor, g.form(i));
            return found;
        }
    };
}  // namespace
tactic *mk_ff2bv_tactic(ast_manager &m, params_ref const &) {
    return alloc(ff2bv_tactic, m);
}
probe *mk_has_ff_probe() {
    return alloc(has_ff_probe);
}
