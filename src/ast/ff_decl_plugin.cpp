#include "ast/ff_decl_plugin.h"
#include "util/z3_exception.h"

namespace {
    rational pow_mod(rational a, rational n, rational const &p, reslimit &limit) {
        rational r(1);
        while (!n.is_zero()) {
            if (!limit.inc())
                throw default_exception("canceled");
            if (!mod(n, rational(2)).is_zero())
                r = mod(r * a, p);
            n = div(n, rational(2));
            a = mod(a * a, p);
        }
        return r;
    }
    bool probable_prime(rational const &p, reslimit &limit) {
        if (!p.is_int() || p < rational(2))
            return false;
        for (unsigned q : {2u, 3u, 5u, 7u, 11u, 13u, 17u, 19u, 23u, 29u, 31u, 37u}) {
            if (p == rational(q))
                return true;
            if (mod(p, rational(q)).is_zero())
                return false;
        }
        rational d = p - rational(1);
        unsigned s = 0;
        while (mod(d, rational(2)).is_zero()) {
            d = div(d, rational(2));
            ++s;
        }
        auto witness = [&](unsigned base) {
            rational a = mod(rational(base), p);
            if (a.is_zero())
                return false;
            rational x = pow_mod(a, d, p, limit);
            if (x.is_one() || x == p - rational(1))
                return false;
            for (unsigned i = 1; i < s; ++i) {
                if (!limit.inc())
                    throw default_exception("canceled");
                x = mod(x * x, p);
                if (x == p - rational(1))
                    return false;
            }
            return true;
        };
        // These seven bases give a deterministic test for p < 2^64.
        for (unsigned b : {2u, 325u, 9375u, 28178u, 450775u, 9780504u, 1795265022u})
            if (witness(b))
                return false;
        if (!p.is_uint64())
            for (unsigned b = 2; b < 66; ++b)
                if (witness(b))
                    return false;
        return true;
    }
}  // namespace

sort *ff_decl_plugin::mk_sort(decl_kind k, unsigned n, parameter const *ps) {
    ast_manager &m = *m_manager;
    if (k != FINITE_FIELD_SORT || n != 1 || (!ps[0].is_int() && !ps[0].is_rational()))
        m.raise_exception("FiniteField expects one prime integer modulus");
    rational p = ps[0].is_int() ? rational(ps[0].get_int()) : ps[0].get_rational();
    bool checked = false;
    for (auto const &q : m_checked_moduli)
        if (p == q)
            checked = true;
    if (!checked) {
        if (!probable_prime(p, m.limit()))
            m.raise_exception("FiniteField modulus must be prime");
        m_checked_moduli.push_back(p);
    }
    parameter q(p);
    sort_size size = p.is_uint64() ? sort_size(p.get_uint64()) : sort_size::mk_very_big();
    return m.mk_sort(symbol("FiniteField"), sort_info(m_family_id, k, size, 1, &q));
}

func_decl *ff_decl_plugin::mk_func_decl(decl_kind k, unsigned n, parameter const *ps, unsigned arity,
                                        sort *const *domain, sort *range) {
    ast_manager &m = *m_manager;
    ff_util u(m);
    if (k == OP_FF_NUM) {
        if (arity || n != 1 || !ps[0].is_rational() || !ps[0].get_rational().is_int() || !range || !u.is_ff(range))
            m.raise_exception("invalid finite-field numeral");
        // Integer numerals differing by a multiple of p denote the same field
        // element. Canonical residues also normalize negative numeral syntax.
        parameter q(mod(ps[0].get_rational(), u.modulus(range)));
        return m.mk_func_decl(symbol("ff"), 0u, static_cast<sort *const *>(nullptr), range,
                              func_decl_info(m_family_id, k, 1, &q));
    }
    if (n || (k == OP_FF_NEG ? arity != 1 : arity < 2))
        m.raise_exception("incorrect finite-field operator arity");
    if (!u.is_ff(domain[0]))
        m.raise_exception("finite-field arguments expected");
    for (unsigned i = 1; i < arity; ++i)
        if (domain[i] != domain[0])
            m.raise_exception("finite-field arguments must have the same modulus");
    if (range && range != domain[0])
        m.raise_exception("finite-field result sort mismatch");
    char const *name;
    switch (k) {
    case OP_FF_ADD: name = "ff.add"; break;
    case OP_FF_MUL: name = "ff.mul"; break;
    case OP_FF_NEG: name = "ff.neg"; break;
    case OP_FF_BITSUM: name = "ff.bitsum"; break;
    default: m.raise_exception("unknown finite-field operator"); return nullptr;
    }
    func_decl_info info(m_family_id, k);
    if (k == OP_FF_ADD || k == OP_FF_MUL) {
        // Field addition and multiplication are associative and commutative,
        // so generic AST flattening/reordering preserves their meaning.
        // bitsum is positional and must not inherit these attributes.
        info.set_associative();
        info.set_flat_associative();
        info.set_commutative();
        // One declaration for every arity, as for Z3's arithmetic AC operators.
        // Rewriting an n-ary application must not retain an n-specific symbol.
        return m.mk_func_decl(symbol(name), 2, domain, domain[0], info);
    }
    return m.mk_func_decl(symbol(name), arity, domain, domain[0], info);
}
void ff_decl_plugin::get_op_names(svector<builtin_name> &ns, symbol const &) {
    ns.push_back(builtin_name("ff.add", OP_FF_ADD));
    ns.push_back(builtin_name("ff.mul", OP_FF_MUL));
    ns.push_back(builtin_name("ff.neg", OP_FF_NEG));
    ns.push_back(builtin_name("ff.bitsum", OP_FF_BITSUM));
}
void ff_decl_plugin::get_sort_names(svector<builtin_name> &ns, symbol const &) {
    ns.push_back(builtin_name("FiniteField", FINITE_FIELD_SORT));
}
expr *ff_decl_plugin::get_some_value(sort *s) {
    return ff_util(*m_manager).mk_numeral(rational(0), s);
}
