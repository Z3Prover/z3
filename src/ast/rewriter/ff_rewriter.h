#pragma once
#include "ast/ff_decl_plugin.h"
#include "ast/occurs.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/z3_exception.h"
#include <map>
#include <vector>
#include <algorithm>

// Shared by simplification and model evaluation. This normalizes sums and
// products without distributing products of symbolic sums or cancelling unknown factors.
// All identities are in F_p. Inverse-based rules require p prime and a nonzero
// constant coefficient; accepting a large modulus is not a primality certificate.
class ff_rewriter {
    ast_manager &m;
    ff_util u;
    struct expr_order {
        bool operator()(expr *a, expr *b) const {
            return a->get_id() < b->get_id();
        }
    };
    struct monomial_order {
        family_id fid;
        bool operator()(expr *a, expr *b) const {
            bool am = is_app_of(a, fid, OP_FF_MUL), bm = is_app_of(b, fid, OP_FF_MUL);
            unsigned na = am ? to_app(a)->get_num_args() : 1;
            unsigned nb = bm ? to_app(b)->get_num_args() : 1;
            if (na != nb)
                return na < nb;
            for (unsigned i = 0; i < na; ++i) {
                expr *x = am ? to_app(a)->get_arg(i) : a;
                expr *y = bm ? to_app(b)->get_arg(i) : b;
                if (x != y)
                    return x->get_id() < y->get_id();
            }
            return false;
        }
    };
    // A coefficient-free product can be temporary. Order by its retained
    // factors, not by the temporary product's recyclable AST id.
    using coefficients = std::map<expr *, rational, monomial_order>;

    expr_ref product(expr_ref_vector const &factors, rational const &c, sort *s) {
        // 0*t = 0 and 1*t = t. The empty product is 1, so a product with no
        // symbolic factors denotes c itself; a singleton needs no MUL node.
        expr_ref_vector args(m);
        if (c.is_zero())
            return expr_ref(u.mk_numeral(c, s), m);
        if (!c.is_one() || factors.empty())
            args.push_back(u.mk_numeral(c, s));
        args.append(factors);
        if (args.size() == 1)
            return expr_ref(args.get(0), m);
        return expr_ref(u.mk_app(OP_FF_MUL, args.size(), args.data()), m);
    }

    // Children have already been rewritten. Temporary products must remain
    // referenced while their raw pointers serve as coefficient-map keys.
    // Associativity and distributivity give k*(a+b) = k*a+k*b. Extract only
    // numerical scalars: a product of symbolic sums remains an atomic term.
    // Reducing coefficients modulo p preserves their value in F_p.
    void collect(expr *e, rational scale, rational const &p, coefficients &terms, rational &constant,
                 expr_ref_vector &pins, unsigned &count) {
        std::vector<std::pair<expr *, rational>> todo;
        todo.emplace_back(e, scale);
        while (!todo.empty()) {
            if (!m.inc())
                throw default_exception("canceled");
            auto [a, factor] = todo.back();
            todo.pop_back();
            if (is_app_of(a, u.get_fid(), OP_FF_ADD)) {
                for (expr *arg : *to_app(a))
                    todo.emplace_back(arg, factor);
                continue;
            }
            rational value;
            if (u.is_numeral(a, value)) {
                constant = mod(constant + factor * value, p);
                continue;
            }
            rational coeff = factor;
            expr_ref base(a, m);
            if (is_app_of(a, u.get_fid(), OP_FF_MUL)) {
                expr_ref_vector factors(m);
                for (expr *arg : *to_app(a)) {
                    if (u.is_numeral(arg, value))
                        coeff = mod(coeff * value, p);
                    else
                        factors.push_back(arg);
                }
                base = product(factors, rational(1), a->get_sort());
                pins.push_back(base);
            }
            if (is_app_of(base, u.get_fid(), OP_FF_ADD)) {
                for (expr *arg : *to_app(base))
                    todo.emplace_back(arg, coeff);
                continue;
            }
            if (u.is_numeral(base, value))
                constant = mod(constant + coeff * value, p);
            else {
                ++count;
                // c*t+d*t = (c+d)*t, including t-t = 0. This is additive
                // cancellation and does not assume that t is nonzero.
                auto [it, fresh] = terms.try_emplace(base.get(), rational(0));
                it->second = mod(it->second + coeff, p);
                if (it->second.is_zero())
                    terms.erase(it);
            }
        }
    }

    expr_ref sum(coefficients const &terms, rational const &constant, sort *s) {
        // Addition is commutative, 0+t = t, and an empty sum is 0. Reordering
        // summands and omitting zero coefficients therefore preserve the term.
        expr_ref_vector args(m);
        if (!constant.is_zero())
            args.push_back(u.mk_numeral(constant, s));
        for (auto const &[term, coeff] : terms) {
            expr_ref_vector factors(m);
            // Flatten a monomial when restoring its coefficient.
            if (is_app_of(term, u.get_fid(), OP_FF_MUL))
                for (expr *arg : *to_app(term))
                    factors.push_back(arg);
            else
                factors.push_back(term);
            args.push_back(product(factors, coeff, s));
        }
        if (args.empty())
            return expr_ref(u.mk_numeral(rational(0), s), m);
        if (args.size() == 1)
            return expr_ref(args.get(0), m);
        return expr_ref(u.mk_app(OP_FF_ADD, args.size(), args.data()), m);
    }

    rational inverse(rational a, rational const &p) {
        // 1 and -1 are self-inverse (also in F_2). Otherwise extended Euclid
        // yields t*a + k*p = 1, hence t*a = 1 in F_p for nonzero a.
        if (a.is_one() || a == p - rational(1))
            return a;
        rational r = p, t(0), s(1);
        while (!a.is_zero()) {
            if (!m.inc())
                throw default_exception("canceled");
            rational q = div(r, a), next = r - q * a;
            r = a;
            a = next;
            next = t - q * s;
            t = s;
            s = next;
        }
        // The sort contract requires p prime; the caller supplies nonzero a.
        SASSERT(r.is_one());
        return mod(t, p);
    }

public:
    explicit ff_rewriter(ast_manager &m) : m(m), u(m) {}
    family_id get_fid() const {
        return u.get_fid();
    }

    br_status mk_eq_core(expr *a, expr *b, expr_ref &out) {
        rational const &p = u.modulus(a->get_sort());
        coefficients terms(monomial_order{u.get_fid()});
        rational constant(0);
        expr_ref_vector pins(m);
        unsigned count = 0;
        // a=b iff a-b=0. If all symbolic summands cancel, this is exactly
        // the test that the remaining canonical constant is zero.
        collect(a, rational(1), p, terms, constant, pins, count);
        collect(b, rational(-1), p, terms, constant, pins, count);
        if (terms.empty()) {
            out = m.mk_bool_val(constant.is_zero());
            return BR_DONE;
        }
        if (terms.size() == 1) {
            // c*t+k=0 iff t=-k/c because c is a nonzero field constant.
            // t may itself be a product or sum; no factor of t is cancelled.
            auto const &[base, coeff] = *terms.begin();
            expr_ref value(u.mk_numeral(mod(-constant * inverse(coeff, p), p), a->get_sort()), m);
            out = m.mk_eq(base, value);
            return BR_DONE;
        }
        // Expose affine wire definitions to solve-eqs even when a circuit
        // exporter writes t = c - a*x. Prefer a wire absent from the other
        // terms: orienting x = x*y + z would hide the usable definition of z.
        // For a nonzero constant c, c*x+r=0 iff x=-c^{-1}*r. The occurs
        // check makes this a nonrecursive definition usable for substitution.
        // Preferring an existing left side or a unit coefficient is only a
        // choice of orientation, not an additional algebraic premise.
        auto pivot = terms.end();
        bool pivot_unit = false;
        expr *preferred = nullptr;
        if (is_uninterp_const(a) != is_uninterp_const(b)) {
            expr *v = is_uninterp_const(a) ? a : b;
            expr *rhs = v == a ? b : a;
            if (!occurs(v, rhs))
                preferred = v;
        }
        for (auto it = terms.begin(); it != terms.end(); ++it) {
            if (!is_uninterp_const(it->first))
                continue;
            if (preferred && it->first != preferred)
                continue;
            bool unit = it->second.is_one() || it->second == p - rational(1);
            if (pivot_unit && !unit)
                continue;
            bool safe = true;
            for (auto const &[term, coeff] : terms)
                if (term != it->first && occurs(it->first, term)) {
                    safe = false;
                    break;
                }
            if (safe) {
                pivot = it;
                pivot_unit = unit;
            }
        }
        if (pivot != terms.end()) {
            expr_ref var(pivot->first, m);
            rational factor = mod(-inverse(pivot->second, p), p);
            terms.erase(pivot);
            for (auto &[term, coeff] : terms)
                coeff = mod(coeff * factor, p);
            expr_ref rhs = sum(terms, mod(constant * factor, p), a->get_sort());
            out = m.mk_eq(var, rhs);
            return BR_DONE;
        }
        // Avoid expanding an ordinary x=y or changing equalities that contain
        // no cancellable summands. Never cancel a symbolic multiplicative factor.
        // The residual equation sum(c_i*t_i)=-k is the same a-b=0 identity.
        // In particular, x*y=x*z cannot become y=z without knowing x != 0.
        if (terms.size() >= count)
            return BR_FAILED;
        expr_ref left = sum(terms, rational(0), a->get_sort());
        expr_ref right(u.mk_numeral(mod(-constant, p), a->get_sort()), m);
        out = m.mk_eq(left, right);
        return BR_DONE;
    }

    br_status mk_app_core(func_decl *f, unsigned n, expr *const *args, expr_ref &out) {
        auto kind = f->get_decl_kind();
        if (kind == OP_FF_NUM)
            return BR_FAILED;
        sort *s = f->get_range();
        rational const &p = u.modulus(s);
        if (kind == OP_FF_ADD) {
            coefficients terms(monomial_order{u.get_fid()});
            rational constant(0);
            expr_ref_vector pins(m);
            unsigned count = 0;
            for (unsigned i = 0; i < n; ++i)
                collect(args[i], rational(1), p, terms, constant, pins, count);
            out = sum(terms, constant, s);
            return BR_DONE;
        }
        if (kind == OP_FF_MUL || kind == OP_FF_NEG) {
            // -t=(-1)*t; associativity flattens products and commutativity
            // permits sorting their factors. Fold constants modulo p, stop
            // at the annihilator 0, and use (-1)*(-1)=1 for double negation.
            rational coeff(kind == OP_FF_NEG ? -1 : 1), value;
            expr_ref_vector factors(m);
            ptr_vector<expr> todo;
            for (unsigned i = 0; i < n; ++i)
                todo.push_back(args[i]);
            while (!todo.empty()) {
                if (!m.inc())
                    throw default_exception("canceled");
                expr *a = todo.back();
                todo.pop_back();
                if (u.is_numeral(a, value))
                    coeff = mod(coeff * value, p);
                else if (is_app_of(a, u.get_fid(), OP_FF_MUL))
                    for (expr *arg : *to_app(a))
                        todo.push_back(arg);
                else
                    factors.push_back(a);
                if (coeff.is_zero())
                    break;
            }
            ptr_vector<expr> ordered;
            for (expr *e : factors)
                ordered.push_back(e);
            std::sort(ordered.begin(), ordered.end(), expr_order());
            expr_ref_vector sorted(m);
            for (expr *e : ordered)
                sorted.push_back(e);
            out = product(sorted, mod(coeff, p), s);
            return BR_DONE;
        }
        if (kind == OP_FF_BITSUM) {
            // Preserve bit positions: removing a zero operand would change weights.
            // By definition bitsum(a_0,...,a_n)=sum(2^i*a_i) in F_p.
            // Constant evaluation needs neither Boolean arguments nor a no-wrap
            // bound; it does not infer either condition for symbolic arguments.
            rational value, total(0), weight(1);
            for (unsigned i = 0; i < n; ++i) {
                if (!u.is_numeral(args[i], value))
                    return BR_FAILED;
                total = mod(total + weight * value, p);
                weight = mod(weight * rational(2), p);
            }
            out = u.mk_numeral(total, s);
            return BR_DONE;
        }
        return BR_FAILED;
    }
};
