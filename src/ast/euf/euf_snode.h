/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_snode.h

Abstract:

    snode layer for sequence/string graph

    Encapsulates strings in the style of euf_enode.h.
    Maps Z3 sequence expressions to a ZIPT-style representation where
    strings are composed of tokens (characters, variables, powers, regex, etc.)
    organized as a binary tree of concatenations.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/

#pragma once

#include <iterator>
#include "util/vector.h"
#include "util/region.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_axioms.h"

namespace euf {

    class sgraph;
    class snode;

    typedef ptr_vector<snode const> snode_vector;

    enum class snode_kind {
        s_empty,       // empty string (OP_SEQ_EMPTY or empty string constant)
        s_char,        // concrete character unit (OP_SEQ_UNIT wrapping a char literal)
        s_var,         // string variable (uninterpreted constant of string sort)
        s_unit,        // generic unit (OP_SEQ_UNIT with non-literal character)
        s_concat,      // concatenation of two snodes (OP_SEQ_CONCAT)
        s_power,       // string exponentiation s^n (OP_SEQ_POWER)
        s_star,        // Kleene star r* (OP_RE_STAR)
        s_plus,        // Kleene plus  r+ (OP_RE_PLUS)
        s_loop,        // bounded loop r{lo,hi} (OP_RE_LOOP)
        s_union,       // union r1|r2 (OP_RE_UNION)
        s_intersect,   // intersection r1&r2 (OP_RE_INTERSECT)
        s_complement,  // complement ~r (OP_RE_COMPLEMENT)
        s_fail,        // empty language (OP_RE_EMPTY_SET)
        s_full_char,   // full character set (OP_RE_FULL_CHAR_SET)
        s_full_seq,    // full sequence set r=.* (OP_RE_FULL_SEQ_SET)
        s_range,       // character range [lo,hi] (OP_RE_RANGE)
        s_ite,         // ite (OP_ITE)
        s_to_re,       // string to regex (OP_SEQ_TO_RE)
        s_in_re,       // regex membership (OP_SEQ_IN_RE)
        s_projection   // projection operator π_{Q,F}(state) (re.proj skolem)
    };

    // Skolem decl-name marking a regex projection operator π_{Q,F}(state).
    // The skolem has signature re.proj(state : RegLan, root : RegLan, nu : Int)
    // where F = {root} (singleton accepting state) and nu identifies the
    // explored subautomaton snapshot Q (see seq_nielsen partial DFA).
    inline symbol re_proj_name() { return symbol("re.proj"); }

    class snode {
        expr *m_expr = nullptr; // assumed to be non-null
        snode_kind m_kind = snode_kind::s_var;
        unsigned m_id = UINT_MAX;
        unsigned m_num_args = 0;

        // metadata flags, analogous to ZIPT's Str/StrToken properties
        bool m_ground = true;        // no uninterpreted string variables
        bool m_regex_free = true;    // no regex constructs
        bool m_is_classical = true;  // classical regular expression
        bool m_has_projection = false; // contains a projection operator (re.proj)
        unsigned m_level = 0;        // tree depth/level (0 for empty, 1 for singletons)
        unsigned m_length = 0;       // token count, number of leaf tokens in the tree

        // hash matrix for associativity-respecting hashing (2x2 polynomial hash matrix)
        // all zeros means not cached, non-zero means cached
        unsigned m_hash_matrix[2][2] = {{0, 0}, {0, 0}};

        snode const* m_args[0];  // variable-length array, allocated via get_snode_size(num_args)

        friend class sgraph;

        static unsigned get_snode_size(unsigned num_args) {
            return sizeof(snode) + num_args * sizeof(snode *);
        }

        static snode *mk(region &r, expr *e, snode_kind k, unsigned id, unsigned num_args, snode const** args) {
            void *mem = r.allocate(get_snode_size(num_args));
            snode * n = new (mem) snode();
            n->m_expr = e;
            n->m_kind = k;
            n->m_id = id;
            n->m_num_args = num_args;
            for (unsigned i = 0; i < num_args; ++i) {
                n->m_args[i] = args[i];
            }
            return n;
        }

    public:
        expr* get_expr() const {
            return m_expr; // assumed to be non-null
        }
        snode_kind kind() const {
            return m_kind;
        }
        unsigned id() const {
            return m_id;
        }

        unsigned num_args() const {
            return m_num_args;
        }

        snode const* arg(const unsigned i) const {
            SASSERT(i < m_num_args);
            return m_args[i];
        }

        snode const* arg0() const {
            return arg(0);
        }

        // Iterator over the leaf tokens of this snode, modulo concatenation
        // (analogous to first()/last()/at()): an s_concat tree is flattened to
        // its leaf tokens in left-to-right order, empty nodes are skipped, and
        // any non-concat node yields itself as a single token.
        // O(1) amortized per token, O(tree height) auxiliary memory.
        class token_iterator {
            snode_vector m_stack;        // pending subtrees, top == back()
            snode const* m_current = nullptr;  // current token, nullptr == end

            void advance() {
                while (!m_stack.empty()) {
                    snode const* n = m_stack.back();
                    m_stack.pop_back();
                    if (n->is_concat()) {
                        m_stack.push_back(n->arg(1));
                        m_stack.push_back(n->arg(0));
                    }
                    else if (!n->is_empty()) {
                        m_current = n;
                        return;
                    }
                }
                m_current = nullptr;
            }

        public:
            using iterator_category = std::input_iterator_tag;
            using value_type = snode *;
            using difference_type = std::ptrdiff_t;
            using pointer = snode * const *;
            using reference = snode *;

            token_iterator() = default; // end iterator
            explicit token_iterator(snode *root) {
                m_stack.push_back(root);
                advance();
            }

            snode const* operator*() const { return m_current; }
            token_iterator &operator++() { advance(); return *this; }
            token_iterator operator++(int) { token_iterator t = *this; advance(); return t; }
            bool operator==(token_iterator const &o) const { return m_current == o.m_current; }
            bool operator!=(token_iterator const &o) const { return m_current != o.m_current; }
        };

        token_iterator begin() const {
            return token_iterator(const_cast<snode *>(this));
        }

        static token_iterator end() {
            return token_iterator();
        }

        // TODO: Track regex being "classical" (no complement, intersection, fail)
        bool is_ground() const {
            return m_ground;
        }
        bool is_regex_free() const {
            return m_regex_free;
        }
        bool is_classical() const {
            return m_is_classical;
        }
        // true iff this regex (sub)tree contains a projection operator (re.proj).
        bool has_projection() const {
            return m_has_projection;
        }
        unsigned level() const {
            return m_level;
        }
        unsigned length() const {
            return m_length;
        }

        // associativity-respecting hash: cached if the 2x2 matrix is non-zero.
        // M[0][0] = HASH_BASE^(num_leaves) which is always nonzero since HASH_BASE
        // is odd and gcd(odd, 2^32) = 1, so the check is safe.
        bool has_cached_hash() const {
            return m_hash_matrix[0][0] != 0;
        }
        unsigned assoc_hash() const {
            return m_hash_matrix[0][1];
        }

        bool is_empty() const {
            return m_kind == snode_kind::s_empty;
        }
        bool is_char() const {
            return m_kind == snode_kind::s_char;
        }
        bool is_var() const {
            return m_kind == snode_kind::s_var;
        }
        bool is_unit() const {
            return m_kind == snode_kind::s_unit;
        }
        bool is_char_or_unit() const {
            return m_kind == snode_kind::s_char || m_kind == snode_kind::s_unit;
        }
        bool is_concat() const {
            return m_kind == snode_kind::s_concat;
        }
        bool is_power() const {
            return m_kind == snode_kind::s_power;
        }
        bool is_star() const {
            return m_kind == snode_kind::s_star;
        }
        bool is_plus() const {
            return m_kind == snode_kind::s_plus;
        }
        bool is_loop() const {
            return m_kind == snode_kind::s_loop;
        }
        bool is_union() const {
            return m_kind == snode_kind::s_union;
        }
        bool is_intersect() const {
            return m_kind == snode_kind::s_intersect;
        }
        bool is_complement() const {
            return m_kind == snode_kind::s_complement;
        }
        bool is_fail() const {
            return m_kind == snode_kind::s_fail;
        }
        bool is_full_char() const {
            return m_kind == snode_kind::s_full_char;
        }
        bool is_full_seq() const {
            return m_kind == snode_kind::s_full_seq;
        }
        bool is_range() const {
            return m_kind == snode_kind::s_range;
        }
        bool is_ite() const {
            return m_kind == snode_kind::s_ite;
        }
        bool is_to_re() const {
            return m_kind == snode_kind::s_to_re;
        }
        bool is_in_re() const {
            return m_kind == snode_kind::s_in_re;
        }
        bool is_string() const {
            // constant string (we assume a flat concatenation)
            return is_concat() && std::ranges::all_of(begin(), end(),
                    [](const snode * const arg) { return arg->is_char(); });
        }

        bool is_string(zstring& str, seq_util& seq) const {
            // constant string (we assume a flat concatenation)
            // TODO: Optimize
            if (!is_concat())
                return false;
            str.reset();
            for (snode const* c : *this) {
                unsigned val;
                if (!c->is_char())
                    return false;
                expr* d = to_app(c->get_expr())->get_arg(0);
                VERIFY(seq.is_const_char(d, val));
                str += zstring(val);
            }
            return true;
        }
        bool is_projection() const {
            return m_kind == snode_kind::s_projection;
        }

        // is this a leaf token (analogous to ZIPT's StrToken as opposed to Str)
        bool is_token() const {
            switch (m_kind) {
            case snode_kind::s_empty:
            case snode_kind::s_concat: return false;
            default: return true;
            }
        }

        sort* get_sort() const {
            return m_expr ? m_expr->get_sort() : nullptr;
        }

        // analogous to ZIPT's Str.First / Str.Last
        snode const *first() const {
            snode const* s = this;
            while (s->is_concat())
                s = s->arg(0);
            return s;
        }

        snode const *last() const {
            snode const* s = this;
            while (s->is_concat())
                s = s->arg(1);
            return s;
        }

        snode const* first() {
            snode const* s = this;
            while (s->is_concat())
                s = s->arg(0);
            return s;
        }

        snode const* last() {
            snode const* s = this;
            while (s->is_concat())
                s = s->arg(1);
            return s;
        }

        // collect all leaf tokens in left-to-right order
        void collect_tokens(snode_vector &tokens) const {
            if (is_concat()) {
                arg(0)->collect_tokens(tokens);
                arg(1)->collect_tokens(tokens);
            }
            else if (!is_empty())
                tokens.push_back(this);
        }

        snode_vector collect_tokens() const {
            snode_vector tokens;
            collect_tokens(tokens);
            return tokens;
        }

        // access the i-th token (0-based, left-to-right order)
        // returns nullptr if i >= length()
        snode const* at(const unsigned i) const {
            if (is_concat()) {
                unsigned left_len = arg(0)->length();
                if (i < left_len)
                    return arg(0)->at(i);
                return arg(1)->at(i - left_len);
            }
            if (is_empty())
                return nullptr;
            return i == 0 ? this : nullptr;
        }
    };

}

struct spp {
    euf::snode const* n;
    ast_manager &m;
    spp(euf::snode const* n, ast_manager &m) : n(n), m(m) {}
};

inline std::ostream &operator<<(std::ostream &out, spp const&p) {
    return out << mk_pp(p.n->get_expr(), p.m);
}

