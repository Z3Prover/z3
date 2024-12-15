#include "ast/ast.h"
#include "util/vector.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "util/scoped_ptr_vector.h"
#include "util/uint_set.h"
#include "ast/reg_decl_plugins.h"

struct test_seq {

    test_seq(ast_manager& m) :
        m(m),
        seq(m),
        a(m)
    {
    }

    struct value {
        value(ast_manager& m) : evalue(m) {}
        zstring  svalue;
        expr_ref evalue;
    };

    struct eval {
        eval(ast_manager& m) :
            val0(m), val1(m) {
        }
        value val0;
        value val1;
        bool is_value = false;
        unsigned min_length = 0;
        unsigned max_length = UINT_MAX;
        ptr_vector<expr> lhs, rhs;
    };

    ast_manager& m;
    seq_util seq;
    arith_util a;
    scoped_ptr_vector<eval> m_values;
    indexed_uint_set m_chars;
    bool m_initialized = false;

    struct str_update {
        expr* e;
        zstring value;
        double m_score;
    };
    struct int_update {
        expr* e;
        rational value;
        double m_score;
    };
    vector<str_update> m_str_updates;


    enum op_t {
        add, del, copy
    };
    enum side_t {
        left, right
    };
    struct string_update {
        side_t side;
        op_t op;
        unsigned i, j;
    };
    struct string_instance {
        zstring s;
        bool_vector is_value;
        bool_vector prev_is_var;
        bool_vector next_is_var;

        bool can_add(unsigned i) const {
            return !is_value[i] || prev_is_var[i];
        }
    };
    svector<string_update> m_string_updates;


    bool is_value(expr* e) {
        if (seq.is_seq(e))
            return get_eval(e).is_value;
        return m.is_value(e);
    }

    void init_string_instance(ptr_vector<expr> const& es, string_instance& a) {
        bool prev_is_var = false;
        for (auto x : es) {
            auto const& val = strval0(x);
            auto len = val.length();
            bool is_val = is_value(x);
            a.s += val;
            if (!prev_is_var && !is_val && !a.next_is_var.empty())
                a.next_is_var.back() = true;
            for (unsigned i = 0; i < len; ++i) {
                a.is_value.push_back(is_val);
                a.prev_is_var.push_back(false);
                a.next_is_var.push_back(false);
            }
            if (len > 0 && is_val && prev_is_var && !a.is_value.empty())
                a.prev_is_var[a.prev_is_var.size() - len] = true;
            prev_is_var = !is_val;
        }
    }


    /**
    * \brief edit distance with update calculation
    */
    unsigned edit_distance_with_updates(string_instance const& a, string_instance const& b) {
        unsigned n = a.s.length();
        unsigned m = b.s.length();
        vector<unsigned_vector> d(n + 1); // edit distance
        vector<unsigned_vector> u(n + 1); // edit distance with updates.
        m_string_updates.reset();
        for (unsigned i = 0; i <= n; ++i) {
            d[i].resize(m + 1, 0);
            u[i].resize(m + 1, 0);
        }
        for (unsigned i = 0; i <= n; ++i)
            d[i][0] = i, u[i][0] = i;
        for (unsigned j = 0; j <= m; ++j)
            d[0][j] = j, u[0][j] = j;
        for (unsigned j = 1; j <= m; ++j) {
            for (unsigned i = 1; i <= n; ++i) {
                if (a.s[i - 1] == b.s[j - 1]) {
                    d[i][j] = d[i - 1][j - 1];
                    u[i][j] = u[i - 1][j - 1];
                }
                else {
                    u[i][j] = 1 + std::min(u[i - 1][j], std::min(u[i][j - 1], u[i - 1][j - 1]));
                    d[i][j] = 1 + std::min(d[i - 1][j], std::min(d[i][j - 1], d[i - 1][j - 1]));

                    if (d[i - 1][j] < u[i][j] && a.can_add(i - 1)) {
                        m_string_updates.reset();
                        u[i][j] = d[i - 1][j];
                    }
                    if (d[i][j - 1] < u[i][j] && b.can_add(j - 1)) {
                        m_string_updates.reset();
                        u[i][j] = d[i][j - 1];
                    }

                    if (d[i - 1][j - 1] < u[i][j] && (!a.is_value[i - 1] || !b.is_value[j - 1])) {
                        m_string_updates.reset();
                        u[i][j] = d[i - 1][j - 1];
                    }

                    if (d[i - 1][j] == u[i][j] && a.can_add(i - 1))
                        add_string_update(side_t::left, op_t::add, j - 1, i - 1);

                    if (d[i][j - 1] == u[i][j] && b.can_add(j - 1))
                        add_string_update(side_t::right, op_t::add, i - 1, j - 1);

                    if (d[i][j - 1] < u[i][j] && b.next_is_var[j - 1] && j == m)
                        add_string_update(side_t::right, op_t::add, i - 1, j);

                    if (d[i - 1][j] < u[i][j] && a.next_is_var[i - 1] && i == n)
                        add_string_update(side_t::left, op_t::add, j - 1, i);

                    if (d[i - 1][j] == u[i][j] && !a.is_value[i - 1])
                        add_string_update(side_t::left, op_t::del, i - 1, 0);

                    if (d[i][j - 1] == u[i][j] && !b.is_value[j - 1])
                        add_string_update(side_t::right, op_t::del, j - 1, 0);

                    if (d[i - 1][j - 1] == u[i][j] && !a.is_value[i - 1])
                        add_string_update(side_t::left, op_t::copy, j - 1, i - 1);

                    if (d[i - 1][j - 1] == u[i][j] && !b.is_value[j - 1])
                        add_string_update(side_t::right, op_t::copy, i - 1, j - 1);
                }
            }
        }
        return u[n][m];
    }

    void add_string_update(side_t side, op_t op, unsigned i, unsigned j) { m_string_updates.push_back({ side, op, i, j }); }


    eval& get_eval(expr* e) {
        unsigned id = e->get_id();
        m_values.reserve(id + 1);
        if (!m_values[id]) {
            m_values.set(id, alloc(eval, m));
            zstring s;
            bool is_string = seq.str.is_string(e, s);
            m_values[id]->is_value = is_string;
            if (is_string)
                m_values[id]->val0.svalue = s;
        }
        return *m_values[id];
    }

    eval* get_eval(expr* e) const {
        unsigned id = e->get_id();
        return m_values.get(id, nullptr);
    }

    ptr_vector<expr> const& lhs(expr* eq) {
        auto& ev = get_eval(eq);
        if (ev.lhs.empty()) {
            expr* x, * y;
            VERIFY(m.is_eq(eq, x, y));
            seq.str.get_concat(x, ev.lhs);
            seq.str.get_concat(y, ev.rhs);
        }
        return ev.lhs;
    }

    ptr_vector<expr> const& concats(expr* x) {
        auto& ev = get_eval(x);
        if (ev.lhs.empty())
            seq.str.get_concat(x, ev.lhs);
        return ev.lhs;
    }

    ptr_vector<expr> const& rhs(expr* eq) {
        lhs(eq);
        auto& e = get_eval(eq);
        return e.rhs;
    }

    zstring& strval0(expr* e) {
        SASSERT(seq.is_string(e->get_sort()));
        return get_eval(e).val0.svalue;
    }

    bool repair_down_str_eq_edit_distance_incremental(app* eq) {
        auto const& L = lhs(eq);
        auto const& R = rhs(eq);
        string_instance a, b;
        verbose_stream() << "eq\n";
        for (auto x : L)
            verbose_stream() << mk_pp(x, m) << "\n";
        init_string_instance(L, a);
        init_string_instance(R, b);

        verbose_stream() << a.s << " == " << b.s << "\n";
        if (a.s == b.s)
            return true;

        unsigned diff = edit_distance_with_updates(a, b);


        verbose_stream() << "diff \"" << a.s << "\" \"" << b.s << "\" diff " << diff << " updates " << m_string_updates.size() << "\n";
#if 1
        for (auto const& [side, op, i, j] : m_string_updates) {
            switch (op) {
            case op_t::del:
                if (side == side_t::left)
                    verbose_stream() << "del " << a.s[i] << " @ " << i << " left\n";
                else
                    verbose_stream() << "del " << b.s[i] << " @ " << i << " right\n";
                break;
            case op_t::add:
                if (side == side_t::left)
                    verbose_stream() << "add " << b.s[i] << " @ " << j << " left\n";
                else
                    verbose_stream() << "add " << a.s[i] << " @ " << j << " right\n";
                break;
            case op_t::copy:
                if (side == side_t::left)
                    verbose_stream() << "copy " << b.s[i] << " @ " << j << " left\n";
                else
                    verbose_stream() << "copy " << a.s[i] << " @ " << j << " right\n";
                break;
            }
        }
#endif
        auto delete_char = [&](auto const& es, unsigned i) {
            for (auto x : es) {
                auto const& value = strval0(x);
                if (i >= value.length())
                    i -= value.length();
                else {
                    if (!is_value(x))
                        m_str_updates.push_back({ x, value.extract(0, i) + value.extract(i + 1, value.length()), 1 });
                    break;
                }
            }
            };

        auto add_char = [&](auto const& es, unsigned j, uint32_t ch) {
            for (auto x : es) {
                auto const& value = strval0(x);
                //verbose_stream() << "add " << j << " " << value << " " << value.length() << " " << is_value(x) << "\n";
                if (j > value.length() || (j == value.length() && j > 0)) {
                    j -= value.length();
                    continue;
                }
                if (!is_value(x))
                    m_str_updates.push_back({ x, value.extract(0, j) + zstring(ch) + value.extract(j, value.length()), 1 });
                if (j < value.length())
                    break;
            }
            };

        auto copy_char = [&](auto const& es, unsigned j, uint32_t ch) {
            for (auto x : es) {
                auto const& value = strval0(x);
                if (j >= value.length())
                    j -= value.length();
                else {
                    if (!is_value(x))
                        m_str_updates.push_back({ x, value.extract(0, j) + zstring(ch) + value.extract(j + 1, value.length()), 1 });
                    break;
                }
            }
            };

        for (auto& [side, op, i, j] : m_string_updates) {
            if (op == op_t::del && side == side_t::left)
                delete_char(L, i);
            else if (op == op_t::del && side == side_t::right)
                delete_char(R, i);
            else if (op == op_t::add && side == side_t::left)
                add_char(L, j, b.s[i]);
            else if (op == op_t::add && side == side_t::right)
                add_char(R, j, a.s[i]);
            else if (op == op_t::copy && side == side_t::left)
                copy_char(L, j, b.s[i]);
            else if (op == op_t::copy && side == side_t::right)
                copy_char(R, j, a.s[i]);
        }
        for (auto const& [e, value, score] : m_str_updates) {
            verbose_stream() << mk_pp(e, m) << " := " << value << "\n";
        }
        return true;
    }

};

void tst_sls_seq_plugin() {
    ast_manager m;
    reg_decl_plugins(m);
    test_seq ts(m);
    seq_util seq(m);
    expr_ref_vector ls(m), rs(m);
    sort* S = seq.str.mk_string_sort();
    expr_ref x(m.mk_const("x", S), m);
    expr_ref y(m.mk_const("y", S), m);
    expr_ref z(m.mk_const("z", S), m);
    expr_ref a(seq.str.mk_string("a"), m);
    expr_ref b(seq.str.mk_string("b"), m);
    expr_ref c(seq.str.mk_string("c"), m);

    ls.push_back(x).push_back(a).push_back(y);
    rs.push_back(b).push_back(c).push_back(z);
    expr_ref l(seq.str.mk_concat(ls, S), m);
    expr_ref r(seq.str.mk_concat(rs, S), m);
    app_ref eq(m.mk_eq(l, r), m);
    verbose_stream() << eq << "\n";
    ts.repair_down_str_eq_edit_distance_incremental(eq);
}