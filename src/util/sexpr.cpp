/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sexpr.h

Abstract:

    Generic sexpr
    
Author:

    Leonardo (leonardo) 2011-07-28

Notes:

--*/
#include "util/sexpr.h"
#include "util/vector.h"
#include "util/buffer.h"

#ifdef _MSC_VER
#pragma warning(disable : 4200)
#pragma warning(disable : 4355)
#endif

struct sexpr_composite : public sexpr {
    unsigned m_num_chilren;
    sexpr *  m_children[0];
    sexpr_composite(unsigned num_children, sexpr * const * children, unsigned line, unsigned pos):
        sexpr(kind_t::COMPOSITE, line, pos),
        m_num_chilren(num_children) {
        for (unsigned i = 0; i < num_children; i++) {
            m_children[i] = children[i];
            children[i]->inc_ref();
        }
    }
};

struct sexpr_numeral : public sexpr {
    rational m_val;
    sexpr_numeral(kind_t k, rational const & val, unsigned line, unsigned pos):
        sexpr(k, line, pos),
        m_val(val) {
    }
    sexpr_numeral(rational const & val, unsigned line, unsigned pos):
        sexpr(kind_t::NUMERAL, line, pos),
        m_val(val) {
    }
};

struct sexpr_bv : public sexpr_numeral {
    unsigned m_size;
    sexpr_bv(rational const & val, unsigned size, unsigned line, unsigned pos):
        sexpr_numeral(kind_t::BV_NUMERAL, val, line, pos),
        m_size(size) {
    }
};

struct sexpr_string : public sexpr {
    std::string m_val;
    sexpr_string(std::string const & val, unsigned line, unsigned pos):
        sexpr(kind_t::STRING, line, pos),
        m_val(val) {
    }
    sexpr_string(char const * val, unsigned line, unsigned pos):
        sexpr(kind_t::STRING, line, pos),
        m_val(val) {
    }
};

struct sexpr_symbol : public sexpr {
    symbol m_val;
    sexpr_symbol(bool keyword, symbol const & val, unsigned line, unsigned pos):
        sexpr(keyword ? kind_t::KEYWORD : kind_t::SYMBOL, line, pos),
        m_val(val) {
    }
};

sexpr::sexpr(kind_t k, unsigned line, unsigned pos):
    m_kind(k),
    m_ref_count(0),
    m_line(line),
    m_pos(pos) {
}

rational const & sexpr::get_numeral() const {
    SASSERT(is_numeral() || is_bv_numeral());
    return static_cast<sexpr_numeral const *>(this)->m_val;
}

unsigned sexpr::get_bv_size() const {
    SASSERT(is_bv_numeral());
    return static_cast<sexpr_bv const *>(this)->m_size;
}

symbol sexpr::get_symbol() const {
    SASSERT(is_symbol() || is_keyword());
    return static_cast<sexpr_symbol const *>(this)->m_val;
}

std::string const & sexpr::get_string() const {
    SASSERT(is_string());
    return static_cast<sexpr_string const *>(this)->m_val;
}

unsigned sexpr::get_num_children() const {
    SASSERT(is_composite());
    return static_cast<sexpr_composite const *>(this)->m_num_chilren;
}

sexpr * sexpr::get_child(unsigned idx) const {
    SASSERT(idx < get_num_children());
    return static_cast<sexpr_composite const *>(this)->m_children[idx];
}

sexpr * const * sexpr::get_children() const {
    SASSERT(is_composite());
    return static_cast<sexpr_composite const *>(this)->m_children;
}

void sexpr::display_atom(std::ostream & out) const {
    switch (get_kind()) {
    case sexpr::kind_t::COMPOSITE:
        UNREACHABLE();
    case sexpr::kind_t::NUMERAL:
        out << static_cast<sexpr_numeral const *>(this)->m_val;
        break;
    case sexpr::kind_t::BV_NUMERAL: {
        out << '#';
        unsigned bv_size = static_cast<sexpr_bv const *>(this)->m_size;
        rational val  = static_cast<sexpr_bv const *>(this)->m_val;
        sbuffer<char> buf;
        unsigned sz = 0;
        if (bv_size % 4 == 0) {
            out << 'x';
            while (val.is_pos()) {
                rational c = val % rational(16);
                val = div(val, rational(16));
                SASSERT(rational(0) <= c && c < rational(16));
                if (c <= rational(9))
                    buf.push_back('0' + c.get_unsigned());
                else
                    buf.push_back('a' + (c.get_unsigned() - 10));
                sz+=4;
            }
            while (sz < bv_size) {
                buf.push_back('0');
                sz+=4;
            }
        }
        else {
            out << 'b';
            while (val.is_pos()) {
                rational c = val % rational(2);
                val = div(val, rational(2));
                SASSERT(rational(0) <= c && c < rational(2));
                if (c.is_zero())
                    buf.push_back('0');
                else
                    buf.push_back('1');
                sz += 1;
            }
            while (sz < bv_size) {
                buf.push_back('0');
                sz += 1;
            }
        }
        std::reverse(buf.begin(), buf.end());
        buf.push_back(0);
        out << buf.data();
        break;
    }
    case sexpr::kind_t::STRING:
        out << "\"" << escaped(static_cast<sexpr_string const *>(this)->m_val.c_str()) << "\"";
        break;
    case sexpr::kind_t::SYMBOL:
    case sexpr::kind_t::KEYWORD:
        out << static_cast<sexpr_symbol const *>(this)->m_val;
        break;
    default:
        UNREACHABLE();
    }
}

void sexpr::display(std::ostream & out) const {
    if (!is_composite())
        display_atom(out);
    vector<std::pair<sexpr_composite const *, unsigned> > todo;
    todo.push_back(std::make_pair(static_cast<sexpr_composite const *>(this), 0));
    while (!todo.empty()) {
    loop:
        sexpr_composite const * n = todo.back().first;
        unsigned & idx = todo.back().second;
        unsigned num = n->get_num_children();
        if (num == 0)
            out << "(";
        while (idx < num) {
            sexpr const * child = n->get_child(idx);
            if (idx == 0)
                out << "(";
            else
                out << " ";
            idx++;
            if (child->is_composite()) {
                todo.push_back(std::make_pair(static_cast<sexpr_composite const *>(child), 0));
                goto loop;
            }
            else {
                child->display_atom(out);
            }
        }
        out << ")";
        todo.pop_back();
    }
}

void sexpr_manager::del(sexpr * n) {
    m_to_delete.push_back(n);
    while (!m_to_delete.empty()) {
        sexpr * n = m_to_delete.back();
        m_to_delete.pop_back();
        switch (n->get_kind()) {
        case sexpr::kind_t::COMPOSITE: {
            unsigned num = n->get_num_children();
            for (unsigned i = 0; i < num; i++) {
                sexpr * child = n->get_child(i);
                SASSERT(child->m_ref_count > 0);
                child->m_ref_count--;
                if (child->m_ref_count == 0)
                    m_to_delete.push_back(child);
            }
            static_cast<sexpr_composite*>(n)->~sexpr_composite();
            m_allocator.deallocate(sizeof(sexpr_composite) + num * sizeof(sexpr*), n);
            break;
        }
        case sexpr::kind_t::NUMERAL:
            static_cast<sexpr_numeral*>(n)->~sexpr_numeral();
            m_allocator.deallocate(sizeof(sexpr_numeral), n);
            break;
        case sexpr::kind_t::BV_NUMERAL:
            static_cast<sexpr_bv*>(n)->~sexpr_bv();
            m_allocator.deallocate(sizeof(sexpr_bv), n);
            break;
        case sexpr::kind_t::STRING:
            static_cast<sexpr_string*>(n)->~sexpr_string();
            m_allocator.deallocate(sizeof(sexpr_string), n);
            break;
        case sexpr::kind_t::SYMBOL:
        case sexpr::kind_t::KEYWORD:
            static_cast<sexpr_symbol*>(n)->~sexpr_symbol();
            m_allocator.deallocate(sizeof(sexpr_symbol), n);
            break;
        default:
            UNREACHABLE();
        }
    }
}

sexpr_manager::sexpr_manager():
    m_allocator("sexpr-manager") {
}

sexpr * sexpr_manager::mk_composite(unsigned num_children, sexpr * const * children, unsigned line, unsigned pos) {
    void * mem = m_allocator.allocate(sizeof(sexpr_composite) + num_children * sizeof(sexpr*));
    return new (mem) sexpr_composite(num_children, children, line, pos);
}

sexpr * sexpr_manager::mk_numeral(rational const & val, unsigned line, unsigned pos) {
    return new (m_allocator.allocate(sizeof(sexpr_numeral))) sexpr_numeral(val, line, pos);
}

sexpr * sexpr_manager::mk_bv_numeral(rational const & val, unsigned bv_size, unsigned line, unsigned pos) {
    return new (m_allocator.allocate(sizeof(sexpr_bv))) sexpr_bv(val, bv_size, line, pos);
}

sexpr * sexpr_manager::mk_string(std::string const & val, unsigned line, unsigned pos) {
    return new (m_allocator.allocate(sizeof(sexpr_string))) sexpr_string(val, line, pos);
}

sexpr * sexpr_manager::mk_string(char const * val, unsigned line, unsigned pos) {
    return new (m_allocator.allocate(sizeof(sexpr_string))) sexpr_string(val, line, pos);
}

sexpr * sexpr_manager::mk_keyword(symbol const & val, unsigned line, unsigned pos) {
    return new (m_allocator.allocate(sizeof(sexpr_symbol))) sexpr_symbol(true, val, line, pos);
}

sexpr * sexpr_manager::mk_symbol(symbol const & val, unsigned line, unsigned pos) {
    return new (m_allocator.allocate(sizeof(sexpr_symbol))) sexpr_symbol(false, val, line, pos);
}

