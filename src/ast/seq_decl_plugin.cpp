/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_decl_plugin.h

Abstract:

    decl_plugin for the theory of sequences

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/bv_decl_plugin.h"
#include <sstream>

static bool is_hex_digit(char ch, unsigned& d) {
    if ('0' <= ch && ch <= '9') {
        d = ch - '0';
        return true;
    }
    if ('A' <= ch && ch <= 'F') {
        d = 10 + ch - 'A';
        return true;
    }
    if ('a' <= ch && ch <= 'f') {
        d = 10 + ch - 'a';
        return true;
    }
    return false;
}

static bool is_octal_digit(char ch, unsigned& d) {
    if ('0' <= ch && ch <= '7') {
        d = ch - '0';
        return true;
    }
    return false;
}

static bool is_escape_char(char const *& s, unsigned& result) {
    unsigned d1, d2, d3;
    if (*s != '\\' || *(s + 1) == 0) {
        return false;
    }
    if (*(s + 1) == 'x' &&
        is_hex_digit(*(s + 2), d1) && is_hex_digit(*(s + 3), d2)) {
        result = d1*16 + d2;
        s += 4;
        return true;
    }
    /* C-standard octal escapes: either 1, 2, or 3 octal digits,
     * stopping either at 3 digits or at the first non-digit character.
     */
    /* 1 octal digit */
    if (is_octal_digit(*(s + 1), d1) && !is_octal_digit(*(s + 2), d2)) {
        result = d1;
        s += 2;
        return true;
    }
    /* 2 octal digits */
    if (is_octal_digit(*(s + 1), d1) && is_octal_digit(*(s + 2), d2) &&
        !is_octal_digit(*(s + 3), d3)) {
        result = d1 * 8 + d2;
        s += 3;
        return true;
    }
    /* 3 octal digits */
    if (is_octal_digit(*(s + 1), d1) && is_octal_digit(*(s + 2), d2) &&
        is_octal_digit(*(s + 3), d3)) {
        result = d1*64 + d2*8 + d3;
        s += 4;
        return true;
    }
    switch (*(s + 1)) {
    case 'a':
        result = '\a';
        s += 2;
        return true;
    case 'b':
        result = '\b';
        s += 2;
        return true;
#if 0
    case 'e':
        result = '\e';
        s += 2;
        return true;
#endif
    case 'f':
        result = '\f';
        s += 2;
        return true;
    case 'n':
        result = '\n';
        s += 2;
        return true;
    case 'r':
        result = '\r';
        s += 2;
        return true;
    case 't':
        result = '\t';
        s += 2;
        return true;
    case 'v':
        result = '\v';
        s += 2;
        return true;
    default:
        result = *(s + 1);
        s += 2;
        return true;
    }
    return false;
}

zstring::zstring(encoding enc): m_encoding(enc) {}

zstring::zstring(char const* s, encoding enc): m_encoding(enc) {
    unsigned mask = 0xFF; // TBD for UTF
    while (*s) {
        unsigned ch;
        if (is_escape_char(s, ch)) {
            m_buffer.push_back(ch & mask);
        }
        else {
            m_buffer.push_back(*s & mask);
            ++s;
        }
    }
}

zstring::zstring(zstring const& other) {
    m_buffer = other.m_buffer;
    m_encoding = other.m_encoding;
}

zstring::zstring(unsigned sz, unsigned const* s, encoding enc) {
    m_buffer.append(sz, s);
    m_encoding = enc;
}

zstring::zstring(unsigned num_bits, bool const* ch) {
    SASSERT(num_bits == 8 || num_bits == 16);
    m_encoding = (num_bits == 8)?ascii:unicode;
    unsigned n = 0;
    for (unsigned i = 0; i < num_bits; ++i) {
        n |= (((unsigned)ch[i]) << i);
    }
    m_buffer.push_back(n);
}

zstring::zstring(unsigned ch, encoding enc) {
    m_encoding = enc;
    m_buffer.push_back(ch & ((enc == ascii)?0x000000FF:0x0000FFFF));
}

zstring& zstring::operator=(zstring const& other) {
    m_encoding = other.m_encoding;
    m_buffer.reset();
    m_buffer.append(other.m_buffer);
    return *this;
}

zstring zstring::replace(zstring const& src, zstring const& dst) const {
    zstring result(m_encoding);
    if (length() < src.length()) {
        return zstring(*this);
    }
    if (src.length() == 0) {
        return dst + zstring(*this);
    }
    bool found = false;
    for (unsigned i = 0; i < length(); ++i) {
        bool eq = !found && i + src.length() <= length();
        for (unsigned j = 0; eq && j < src.length(); ++j) {
            eq = m_buffer[i+j] == src[j];
        }
        if (eq) {
            result.m_buffer.append(dst.m_buffer);
            found = true;
            i += src.length() - 1;
        }
        else {
            result.m_buffer.push_back(m_buffer[i]);
        }
    }
    return result;
}

static const char esc_table[32][6] =
    { "\\x00", "\\x01", "\\x02", "\\x03", "\\x04", "\\x05", "\\x06", "\\x07", "\\x08", "\\x09", "\\n",   "\\v",   "\\f",   "\\r",   "\\x0E", "\\x0F",
      "\\x10", "\\x11", "\\x12", "\\x13", "\\x14", "\\x15", "\\x16", "\\x17", "\\x18", "\\x19", "\\x1A", "\\x1B", "\\x1C", "\\x1D", "\\x1E", "\\x1F"
};

std::string zstring::encode() const {
    SASSERT(m_encoding == ascii);
    std::ostringstream strm;
    for (unsigned i = 0; i < m_buffer.size(); ++i) {
        unsigned char ch = m_buffer[i];
        if (0 <= ch && ch < 32) {
            strm << esc_table[ch];
        }
        else if (ch == '\\') {
            strm << "\\\\";
        }
        else if (ch >= 128) {
            strm << "\\x" << std::hex << (unsigned)ch << std::dec; 
        }
        else {
            strm << (char)(ch);
        }
    }
    return strm.str();
}

std::string zstring::as_string() const {
    SASSERT(m_encoding == ascii);
    std::ostringstream strm;
    for (unsigned i = 0; i < m_buffer.size(); ++i) {
        unsigned char ch = m_buffer[i];
        strm << (char)(ch);        
    }
    return strm.str();
}


bool zstring::suffixof(zstring const& other) const {
    if (length() > other.length()) return false;
    bool suffix = true;
    for (unsigned i = 0; suffix && i < length(); ++i) {
        suffix = m_buffer[length()-i-1] == other[other.length()-i-1];
    }
    return suffix;
}

bool zstring::prefixof(zstring const& other) const {
    if (length() > other.length()) return false;
    bool prefix = true;
    for (unsigned i = 0; prefix && i < length(); ++i) {
        prefix = m_buffer[i] == other[i];
    }
    return prefix;
}

bool zstring::contains(zstring const& other) const {
    if (other.length() > length()) return false;
    unsigned last = length() - other.length();
    bool cont = false;
    for (unsigned i = 0; !cont && i <= last; ++i) {
        cont = true;
        for (unsigned j = 0; cont && j < other.length(); ++j) {
            cont = other[j] == m_buffer[j+i];
        }
    }
    return cont;
}

int zstring::indexof(zstring const& other, int offset) const {
    SASSERT(offset >= 0);
    if (static_cast<unsigned>(offset) <= length() && other.length() == 0) return offset;
    if (static_cast<unsigned>(offset) == length()) return -1;
    if (other.length() + offset > length()) return -1;
    unsigned last = length() - other.length();
    for (unsigned i = static_cast<unsigned>(offset); i <= last; ++i) {
        bool prefix = true;
        for (unsigned j = 0; prefix && j < other.length(); ++j) {
            prefix = m_buffer[i + j] == other[j];
        }
        if (prefix) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

int zstring::last_indexof(zstring const& other) const {
    if (other.length() == 0) return length();
    if (other.length() > length()) return -1;
    for (unsigned last = length() - other.length(); last-- > 0; ) {
        bool suffix = true;
        for (unsigned j = 0; suffix && j < other.length(); ++j) {
            suffix = m_buffer[last + j] == other[j];
        }
        if (suffix) {
            return static_cast<int>(last);
        }
    }
    return -1;
}

zstring zstring::extract(int offset, int len) const {
    zstring result(m_encoding);
    SASSERT(0 <= offset && 0 <= len);
    int last = std::min(offset+len, static_cast<int>(length()));
    for (int i = offset; i < last; ++i) {
        result.m_buffer.push_back(m_buffer[i]);
    }
    return result;
}

zstring zstring::operator+(zstring const& other) const {
    SASSERT(m_encoding == other.m_encoding);
    zstring result(*this);
    result.m_buffer.append(other.m_buffer);
    return result;
}

bool zstring::operator==(const zstring& other) const {
    // two strings are equal iff they have the same length and characters
    if (length() != other.length()) {
        return false;
    }
    for (unsigned i = 0; i < length(); ++i) {
        if (m_buffer[i] != other[i]) {
            return false;
        }
    }
    return true;
}

bool zstring::operator!=(const zstring& other) const {
    return !(*this == other);
}

std::ostream& operator<<(std::ostream &os, const zstring &str) {
    return os << str.encode();
}

bool operator<(const zstring& lhs, const zstring& rhs) {
    // This has the same semantics as strcmp()
    unsigned len = lhs.length();
    if (rhs.length() < len) {
        len = rhs.length();
    }
    for (unsigned i = 0; i < len; ++i) {
        unsigned Li = lhs[i];
        unsigned Ri = rhs[i];
        if (Li < Ri) {
            return true;
        } 
        else if (Li > Ri) {
            return false;
        } 
    }
    // at this point, all compared characters are equal,
    // so decide based on the relative lengths
    return lhs.length() < rhs.length();
}


seq_decl_plugin::seq_decl_plugin(): m_init(false),
                                    m_stringc_sym("String"),
                                    m_charc_sym("Char"),
                                    m_string(nullptr),
                                    m_char(nullptr),
                                    m_re(nullptr),
                                    m_has_re(false) {}

void seq_decl_plugin::finalize() {
    for (unsigned i = 0; i < m_sigs.size(); ++i)
        dealloc(m_sigs[i]);
    m_manager->dec_ref(m_string);
    m_manager->dec_ref(m_char);
    m_manager->dec_ref(m_re);
}

bool seq_decl_plugin::is_sort_param(sort* s, unsigned& idx) {
    return
        s->get_name().is_numerical() &&
        (idx = s->get_name().get_num(), true);
}

bool seq_decl_plugin::match(ptr_vector<sort>& binding, sort* s, sort* sP) {
    if (s == sP) return true;
    unsigned idx;
    if (is_sort_param(sP, idx)) {
        if (binding.size() <= idx) binding.resize(idx+1);
        if (binding[idx] && (binding[idx] != s)) return false;
        TRACE("seq_verbose", tout << "setting binding @ " << idx << " to " << mk_pp(s, *m_manager) << "\n";);
        binding[idx] = s;
        return true;
    }


    if (s->get_family_id() == sP->get_family_id() &&
        s->get_decl_kind() == sP->get_decl_kind() &&
        s->get_num_parameters() == sP->get_num_parameters()) {
        for (unsigned i = 0, sz = s->get_num_parameters(); i < sz; ++i) {
            parameter const& p = s->get_parameter(i);
            if (p.is_ast() && is_sort(p.get_ast())) {
                parameter const& p2 = sP->get_parameter(i);
                if (!match(binding, to_sort(p.get_ast()), to_sort(p2.get_ast()))) return false;
            }
        }
        return true;
    }
    else {
        TRACE("seq", tout << "Could not match " << mk_pp(s, *m_manager) << " and " << mk_pp(sP, *m_manager) << "\n";);
        return false;
    }
}

/*
  \brief match right associative operator.
*/
void seq_decl_plugin::match_right_assoc(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    ptr_vector<sort> binding;
    ast_manager& m = *m_manager;
    TRACE("seq_verbose",
          tout << sig.m_name << ": ";
          for (unsigned i = 0; i < dsz; ++i) tout << mk_pp(dom[i], m) << " ";
          if (range) tout << " range: " << mk_pp(range, m);
          tout << "\n";);
    if (dsz == 0) {
        std::ostringstream strm;
        strm << "Unexpected number of arguments to '" << sig.m_name << "' ";
        strm << "at least one argument expected " << dsz << " given";
        m.raise_exception(strm.str());
    }
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        SASSERT(dom[i]);
        is_match = match(binding, dom[i], sig.m_dom[0].get());
    }
    if (range && is_match) {
        is_match = match(binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort of function '" << sig.m_name << "' ";
        strm << "does not match the declared type. Given domain: ";
        for (unsigned i = 0; i < dsz; ++i) {
            strm << mk_pp(dom[i], m) << " ";
        }
        if (range) {
            strm << " and range: " << mk_pp(range, m);
        }
        m.raise_exception(strm.str());
    }
    range_out = apply_binding(binding, sig.m_range);
    SASSERT(range_out);
    TRACE("seq_verbose", tout << mk_pp(range_out, m) << "\n";);
}

void seq_decl_plugin::match(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    m_binding.reset();
    ast_manager& m = *m_manager;
    if (sig.m_dom.size() != dsz) {
        std::ostringstream strm;
        strm << "Unexpected number of arguments to '" << sig.m_name << "' ";
        strm << sig.m_dom.size() << " arguments expected " << dsz << " given";
        m.raise_exception(strm.str());
    }
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        is_match = match(m_binding, dom[i], sig.m_dom[i].get());
    }
    if (range && is_match) {
        is_match = match(m_binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort of polymorphic function '" << sig.m_name << "' ";
        strm << "does not match the declared type. ";
        strm << "\nGiven domain: ";
        for (unsigned i = 0; i < dsz; ++i) {
            strm << mk_pp(dom[i], m) << " ";
        }
        if (range) {
            strm << " and range: " << mk_pp(range, m);
        }
        strm << "\nExpected domain: ";
        for (unsigned i = 0; i < dsz; ++i) {
            strm << mk_pp(sig.m_dom[i].get(), m) << " ";
        }

        m.raise_exception(strm.str());
    }
    if (!range && dsz == 0) {
        std::ostringstream strm;
        strm << "Sort of polymorphic function '" << sig.m_name << "' ";
        strm << "is ambiguous. Function takes no arguments and sort of range has not been constrained";
        m.raise_exception(strm.str());
    }
    range_out = apply_binding(m_binding, sig.m_range);
    SASSERT(range_out);
}

sort* seq_decl_plugin::apply_binding(ptr_vector<sort> const& binding, sort* s) {
    unsigned i;
    if (is_sort_param(s, i)) {
        if (binding.size() <= i || !binding[i]) {
            m_manager->raise_exception("Expecting type parameter to be bound");
        }
        return binding[i];
    }
    if (is_sort_of(s, m_family_id, SEQ_SORT) || is_sort_of(s, m_family_id, RE_SORT)) {
        SASSERT(s->get_num_parameters() == 1);
        SASSERT(s->get_parameter(0).is_ast());
        SASSERT(is_sort(s->get_parameter(0).get_ast()));
        sort* p = apply_binding(binding, to_sort(s->get_parameter(0).get_ast()));
        parameter param(p);
        return mk_sort(s->get_decl_kind(), 1, &param);
    }
    return s;
}


void seq_decl_plugin::init() {
    if(m_init) return;
    ast_manager& m = *m_manager;
    m_init = true;
    sort* A = m.mk_uninterpreted_sort(symbol((unsigned)0));
    sort* strT = m_string;
    parameter paramA(A);
    parameter paramS(strT);
    sort* seqA = m.mk_sort(m_family_id, SEQ_SORT, 1, &paramA);
    parameter paramSA(seqA);
    sort* reA  = m.mk_sort(m_family_id, RE_SORT, 1, &paramSA);
    sort* reT  = m.mk_sort(m_family_id, RE_SORT, 1, &paramS);
    sort* boolT = m.mk_bool_sort();
    sort* intT  = arith_util(m).mk_int();
    sort* predA = array_util(m).mk_array_sort(A, boolT);
    sort* seqAseqA[2] = { seqA, seqA };
    sort* seqAreA[2] = { seqA, reA };
    sort* reAreA[2] = { reA, reA };
    sort* seqAint2T[3] = { seqA, intT, intT };
    sort* seq2AintT[3] = { seqA, seqA, intT };
    sort* str2T[2] = { strT, strT };
    sort* str3T[3] = { strT, strT, strT };
    sort* strTint2T[3] = { strT, intT, intT };
    sort* strTreT[2] = { strT, reT };
    sort* str2TintT[3] = { strT, strT, intT };
    sort* seqAintT[2] = { seqA, intT };
    sort* seq3A[3] = { seqA, seqA, seqA };
    sort* reTintT[2] = { reT, intT };
    m_sigs.resize(LAST_SEQ_OP);
    // TBD: have (par ..) construct and load parameterized signature from premable.
    m_sigs[OP_SEQ_UNIT]      = alloc(psig, m, "seq.unit",     1, 1, &A, seqA);
    m_sigs[OP_SEQ_EMPTY]     = alloc(psig, m, "seq.empty",    1, 0, nullptr, seqA);
    m_sigs[OP_SEQ_CONCAT]    = alloc(psig, m, "seq.++",       1, 2, seqAseqA, seqA);
    m_sigs[OP_SEQ_PREFIX]    = alloc(psig, m, "seq.prefixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUFFIX]    = alloc(psig, m, "seq.suffixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_CONTAINS]  = alloc(psig, m, "seq.contains", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_EXTRACT]   = alloc(psig, m, "seq.extract",  1, 3, seqAint2T, seqA);
    m_sigs[OP_SEQ_REPLACE]   = alloc(psig, m, "seq.replace",  1, 3, seq3A, seqA);
    m_sigs[OP_SEQ_INDEX]     = alloc(psig, m, "seq.indexof",  1, 3, seq2AintT, intT);
    m_sigs[OP_SEQ_LAST_INDEX] = alloc(psig, m, "seq.last_indexof",  1, 2, seqAseqA, intT);
    m_sigs[OP_SEQ_AT]        = alloc(psig, m, "seq.at",       1, 2, seqAintT, seqA);
    m_sigs[OP_SEQ_NTH]       = alloc(psig, m, "seq.nth",      1, 2, seqAintT, A);
    m_sigs[OP_SEQ_NTH_I]     = alloc(psig, m, "seq.nth_i",    1, 2, seqAintT, A);
    m_sigs[OP_SEQ_NTH_U]     = alloc(psig, m, "seq.nth_u",    1, 2, seqAintT, A);
    m_sigs[OP_SEQ_LENGTH]    = alloc(psig, m, "seq.len",      1, 1, &seqA, intT);
    m_sigs[OP_RE_PLUS]       = alloc(psig, m, "re.+",         1, 1, &reA, reA);
    m_sigs[OP_RE_STAR]       = alloc(psig, m, "re.*",         1, 1, &reA, reA);
    m_sigs[OP_RE_OPTION]     = alloc(psig, m, "re.opt",       1, 1, &reA, reA);
    m_sigs[OP_RE_RANGE]      = alloc(psig, m, "re.range",     1, 2, seqAseqA,  reA);
    m_sigs[OP_RE_CONCAT]     = alloc(psig, m, "re.++",        1, 2, reAreA, reA);
    m_sigs[OP_RE_UNION]      = alloc(psig, m, "re.union",     1, 2, reAreA, reA);
    m_sigs[OP_RE_INTERSECT]  = alloc(psig, m, "re.inter",     1, 2, reAreA, reA);
    m_sigs[OP_RE_LOOP]           = alloc(psig, m, "re.loop",    1, 1, &reA, reA);
    m_sigs[OP_RE_COMPLEMENT]     = alloc(psig, m, "re.complement", 1, 1, &reA, reA);
    m_sigs[OP_RE_EMPTY_SET]      = alloc(psig, m, "re.empty", 1, 0, nullptr, reA);
    m_sigs[OP_RE_FULL_SEQ_SET]   = alloc(psig, m, "re.all", 1, 0, nullptr, reA);
    m_sigs[OP_RE_FULL_CHAR_SET]  = alloc(psig, m, "re.allchar", 1, 0, nullptr, reA);
    m_sigs[OP_RE_OF_PRED]        = alloc(psig, m, "re.of.pred", 1, 1, &predA, reA);
    m_sigs[OP_SEQ_TO_RE]         = alloc(psig, m, "seq.to.re",  1, 1, &seqA, reA);
    m_sigs[OP_SEQ_IN_RE]         = alloc(psig, m, "seq.in.re", 1, 2, seqAreA, boolT);
    m_sigs[OP_STRING_CONST]      = nullptr;
    m_sigs[_OP_STRING_STRIDOF]   = alloc(psig, m, "str.indexof", 0, 3, str2TintT, intT);
    m_sigs[_OP_STRING_STRREPL]   = alloc(psig, m, "str.replace", 0, 3, str3T, strT);
    m_sigs[OP_STRING_ITOS]       = alloc(psig, m, "int.to.str", 0, 1, &intT, strT);
    m_sigs[OP_STRING_STOI]       = alloc(psig, m, "str.to.int", 0, 1, &strT, intT);
    m_sigs[OP_STRING_LT]         = alloc(psig, m, "str.<", 0, 2, str2T, boolT);
    m_sigs[OP_STRING_LE]         = alloc(psig, m, "str.<=", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_CONCAT]    = alloc(psig, m, "str.++", 1, 2, str2T, strT);
    m_sigs[_OP_STRING_LENGTH]    = alloc(psig, m, "str.len", 0, 1, &strT, intT);
    m_sigs[_OP_STRING_STRCTN]    = alloc(psig, m, "str.contains", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_CHARAT]    = alloc(psig, m, "str.at", 0, 2, strTint2T, strT);
    m_sigs[_OP_STRING_PREFIX]    = alloc(psig, m, "str.prefixof", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_SUFFIX]    = alloc(psig, m, "str.suffixof", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_IN_REGEXP]  = alloc(psig, m, "str.in.re", 0, 2, strTreT, boolT);
    m_sigs[_OP_STRING_TO_REGEXP]  = alloc(psig, m, "str.to.re", 0, 1, &strT, reT);
    m_sigs[_OP_REGEXP_EMPTY]      = alloc(psig, m, "re.nostr", 0, 0, nullptr, reT);
    m_sigs[_OP_REGEXP_FULL_CHAR]  = alloc(psig, m, "re.allchar", 0, 0, nullptr, reT);
    m_sigs[_OP_STRING_SUBSTR]     = alloc(psig, m, "str.substr", 0, 3, strTint2T, strT);
    m_sigs[_OP_RE_UNROLL]         = alloc(psig, m, "_re.unroll", 0, 2, reTintT, strT);
}

void seq_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    bv_util bv(*m);
    m_char = bv.mk_sort(8);
    m->inc_ref(m_char);
    parameter param(m_char);
    m_string = m->mk_sort(symbol("String"), sort_info(m_family_id, SEQ_SORT, 1, &param));
    m->inc_ref(m_string);
    parameter paramS(m_string);
    m_re = m->mk_sort(m_family_id, RE_SORT, 1, &paramS);
    m->inc_ref(m_re);
}

sort * seq_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    init();
    ast_manager& m = *m_manager;
    switch (k) {
    case SEQ_SORT:
        if (num_parameters != 1) {
            m.raise_exception("Invalid sequence sort, expecting one parameter");
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m.raise_exception("invalid sequence sort, parameter is not a sort");
        }
        if (parameters[0].get_ast() == m_char) {
            return m_string;
        }
        return m.mk_sort(symbol("Seq"), sort_info(m_family_id, SEQ_SORT, num_parameters, parameters));
    case RE_SORT: {
        if (num_parameters != 1) {
            m.raise_exception("Invalid regex sort, expecting one parameter");
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m.raise_exception("invalid regex sort, parameter is not a sort");
        }
        return m.mk_sort(symbol("RegEx"), sort_info(m_family_id, RE_SORT, num_parameters, parameters));
    }
    case _STRING_SORT:
        return m_string;
    default:
        UNREACHABLE();
        return nullptr;
    }
}

func_decl* seq_decl_plugin::mk_seq_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_string) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    match(*m_sigs[k], arity, domain, range, rng);
    return m.mk_func_decl(m_sigs[(domain[0] == m_string)?k_string:k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
}


func_decl* seq_decl_plugin::mk_str_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    match(*m_sigs[k], arity, domain, range, rng);
    return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k_seq));
}

func_decl* seq_decl_plugin::mk_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq, decl_kind k_string) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    if (arity == 0) {
        m.raise_exception("Invalid function application. At least one argument expected");
    }
    match_right_assoc(*m_sigs[k], arity, domain, range, rng);
    func_decl_info info(m_family_id, k_seq);
    info.set_right_associative(true);
    return m.mk_func_decl(m_sigs[(rng == m_string)?k_string:k_seq]->m_name, rng, rng, rng, info);
}

func_decl * seq_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {
    init();
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    switch(k) {
    case OP_SEQ_EMPTY:
        match(*m_sigs[k], arity, domain, range, rng);
        if (rng == m_string) {
            parameter param(symbol(""));
            return mk_func_decl(OP_STRING_CONST, 1, &param, 0, nullptr, m_string);
        }
        else {
            parameter param(rng.get());
            func_decl_info info(m_family_id, k, 1, &param);
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, info);
        }

    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_OF_PRED:
    case OP_RE_COMPLEMENT:
        m_has_re = true;
        // fall-through
    case OP_SEQ_UNIT:
    case OP_STRING_ITOS:
    case OP_STRING_STOI:
    case OP_STRING_LT:
    case OP_STRING_LE:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
        
    case _OP_REGEXP_FULL_CHAR:
        m_has_re = true;
        if (!range) range = m_re;
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(symbol("re.allchar"), arity, domain, rng, func_decl_info(m_family_id, OP_RE_FULL_CHAR_SET));

    case OP_RE_FULL_CHAR_SET:
        m_has_re = true;
        if (!range) range = m_re;
        if (range == m_re) {
            match(*m_sigs[k], arity, domain, range, rng);
            return m.mk_func_decl(symbol("re.allchar"), arity, domain, rng, func_decl_info(m_family_id, k));
        }
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, range, func_decl_info(m_family_id, k));

    case OP_RE_FULL_SEQ_SET:
        m_has_re = true;
        if (!range) range = m_re;
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, range, func_decl_info(m_family_id, k));        

    case _OP_REGEXP_EMPTY:
        m_has_re = true;
        if (!range) range = m_re;
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(symbol("re.nostr"), arity, domain, rng, func_decl_info(m_family_id, OP_RE_EMPTY_SET));

    case OP_RE_EMPTY_SET:
        m_has_re = true;
        if (!range) range = m_re;
        if (range == m_re) {
            match(*m_sigs[k], arity, domain, range, rng);
            return m.mk_func_decl(symbol("re.nostr"), arity, domain, rng, func_decl_info(m_family_id, k));
        }
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, range, func_decl_info(m_family_id, k));

    case OP_RE_LOOP:
        m_has_re = true;
        switch (arity) {
        case 1:
            match(*m_sigs[k], arity, domain, range, rng);
            if (num_parameters == 0 || num_parameters > 2 || !parameters[0].is_int() || (num_parameters == 2 && !parameters[1].is_int())) {
                m.raise_exception("Expecting two numeral parameters to function re-loop");
            }
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k, num_parameters, parameters));
        case 2:
            if (m_re != domain[0] || !arith_util(m).is_int(domain[1])) {
                m.raise_exception("Incorrect type of arguments passed to re.loop. Expecting regular expression and two integer parameters");
            }
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, domain[0], func_decl_info(m_family_id, k, num_parameters, parameters));
        case 3:
            if (m_re != domain[0] || !arith_util(m).is_int(domain[1]) || !arith_util(m).is_int(domain[2])) {
                m.raise_exception("Incorrect type of arguments passed to re.loop. Expecting regular expression and two integer parameters");
            }
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, domain[0], func_decl_info(m_family_id, k, num_parameters, parameters));
        default:
            m.raise_exception("Incorrect number of arguments passed to loop. Expected 1 regular expression and two integer parameters");
        }
        
    case _OP_RE_UNROLL:
        m_has_re = true;
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));

    case OP_STRING_CONST:
        if (!(num_parameters == 1 && arity == 0 && parameters[0].is_symbol())) {
            m.raise_exception("invalid string declaration");
        }
        return m.mk_const_decl(m_stringc_sym, m_string,
                               func_decl_info(m_family_id, OP_STRING_CONST, num_parameters, parameters));

    case OP_RE_UNION:
    case OP_RE_CONCAT:
    case OP_RE_INTERSECT:
        m_has_re = true;
        return mk_assoc_fun(k, arity, domain, range, k, k);

    case OP_SEQ_CONCAT:
        return mk_assoc_fun(k, arity, domain, range, k, _OP_STRING_CONCAT);

    case _OP_STRING_CONCAT:
        return mk_assoc_fun(k, arity, domain, range, OP_SEQ_CONCAT, k);

    case OP_SEQ_REPLACE:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_STRREPL);
    case _OP_STRING_STRREPL:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_REPLACE);

    case OP_SEQ_INDEX:
        if (arity == 2) {
            sort* dom[3] = { domain[0], domain[1], arith_util(m).mk_int() };
            sort_ref rng(m);
            match(*m_sigs[k], 3, dom, range, rng);
            return m.mk_func_decl(m_sigs[(dom[0] == m_string)?_OP_STRING_STRIDOF:k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
        }
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_STRIDOF);
    case _OP_STRING_STRIDOF:
        if (arity == 2) {
            sort* dom[3] = { domain[0], domain[1], arith_util(m).mk_int() };
            sort_ref rng(m);
            match(*m_sigs[k], 3, dom, range, rng);
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, OP_SEQ_INDEX));
        }
        return mk_str_fun(k, arity, domain, range, OP_SEQ_INDEX);
    case OP_SEQ_LAST_INDEX:
        if (arity != 2) {
            m.raise_exception("two arguments expected tin last_indexof");
        }
        else {
            return mk_seq_fun(k, arity, domain, range, OP_SEQ_LAST_INDEX);
        }
    case OP_SEQ_PREFIX:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_PREFIX);
    case _OP_STRING_PREFIX:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_PREFIX);

    case OP_SEQ_SUFFIX:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_SUFFIX);
    case _OP_STRING_SUFFIX:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_SUFFIX);

    case OP_SEQ_LENGTH:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_LENGTH);
    case _OP_STRING_LENGTH:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_LENGTH);

    case OP_SEQ_CONTAINS:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_STRCTN);
    case _OP_STRING_STRCTN:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_CONTAINS);

    case OP_SEQ_TO_RE:
        m_has_re = true;
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_TO_REGEXP);
    case _OP_STRING_TO_REGEXP:
        m_has_re = true;
        return mk_str_fun(k, arity, domain, range, OP_SEQ_TO_RE);

    case OP_SEQ_IN_RE:
        m_has_re = true;
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_IN_REGEXP);
    case _OP_STRING_IN_REGEXP:
        m_has_re = true;
        return mk_str_fun(k, arity, domain, range, OP_SEQ_IN_RE);

    case OP_SEQ_AT:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_CHARAT);
    case _OP_STRING_CHARAT:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_AT);

    case OP_SEQ_NTH:
    case OP_SEQ_NTH_I:
    case OP_SEQ_NTH_U:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));

    case OP_SEQ_EXTRACT:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_SUBSTR);
    case _OP_STRING_SUBSTR:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_EXTRACT);

    case _OP_SEQ_SKOLEM: {
        if (num_parameters != 1 || !parameters[0].is_symbol()) {
            m.raise_exception("one symbol parameter expected to skolem symbol");
        }
        symbol s = parameters[0].get_symbol();
        return m.mk_func_decl(s, arity, domain, range, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void seq_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    init();
    for (unsigned i = 0; i < m_sigs.size(); ++i) {
        if (m_sigs[i]) {
            op_names.push_back(builtin_name(m_sigs[i]->m_name.str().c_str(), i));
        }
    }
}

void seq_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    init();
    sort_names.push_back(builtin_name("Seq",   SEQ_SORT));
    sort_names.push_back(builtin_name("RegEx", RE_SORT));
    // SMT-LIB 2.5 compatibility
    sort_names.push_back(builtin_name("String", _STRING_SORT));
    sort_names.push_back(builtin_name("StringSequence", _STRING_SORT));
}

app* seq_decl_plugin::mk_string(symbol const& s) {
    zstring canonStr(s.bare_str());
    symbol canonSym(canonStr.encode().c_str());
    parameter param(canonSym);
    func_decl* f = m_manager->mk_const_decl(m_stringc_sym, m_string,
                                            func_decl_info(m_family_id, OP_STRING_CONST, 1, &param));
    return m_manager->mk_const(f);
}

app* seq_decl_plugin::mk_string(zstring const& s) {
    symbol sym(s.encode().c_str());
    parameter param(sym);
    func_decl* f = m_manager->mk_const_decl(m_stringc_sym, m_string,
                                            func_decl_info(m_family_id, OP_STRING_CONST, 1, &param));
    return m_manager->mk_const(f);
}


bool seq_decl_plugin::is_value(app* e) const {
    while (true) {
        if (is_app_of(e, m_family_id, OP_SEQ_EMPTY)) {
            return true;
        }
        if (is_app_of(e, m_family_id, OP_STRING_CONST)) {
            return true;
        }
        if (is_app_of(e, m_family_id, OP_SEQ_UNIT) &&
            m_manager->is_value(e->get_arg(0))) {
            return true;
        }
        if (is_app_of(e, m_family_id, OP_SEQ_CONCAT)) {
            bool first = true;
            for (expr* arg : *e) {
                if (first) {
                    first = false;
                }
                else if (is_app(arg) && !is_value(to_app(arg))) {
                    return false;
                }
            }
            if (!is_app(e->get_arg(0))) return false;            
            e = to_app(e->get_arg(0));
            continue;
        }
        return false;
    }
}

bool seq_decl_plugin::are_equal(app* a, app* b) const {
    if (a == b) return true;
    // handle concatenations
    return false;
}

bool seq_decl_plugin::are_distinct(app* a, app* b) const {
    if (a == b) {
        return false;
    }
    if (is_app_of(a, m_family_id, OP_STRING_CONST) &&
        is_app_of(b, m_family_id, OP_STRING_CONST)) {
        return true;
    }
    if (is_app_of(a, m_family_id, OP_SEQ_UNIT) && 
        is_app_of(b, m_family_id, OP_SEQ_UNIT)) {
        return m_manager->are_distinct(a->get_arg(0), b->get_arg(0));
    }
    if (is_app_of(a, m_family_id, OP_SEQ_EMPTY) && 
        is_app_of(b, m_family_id, OP_SEQ_UNIT)) {
        return true;
    }
    if (is_app_of(b, m_family_id, OP_SEQ_EMPTY) && 
        is_app_of(a, m_family_id, OP_SEQ_UNIT)) {
        return true;
    }    
    return false;
}


expr* seq_decl_plugin::get_some_value(sort* s) {
    seq_util util(*m_manager);
    if (util.is_seq(s)) {
        return util.str.mk_empty(s);
    }
    sort* seq;
    if (util.is_re(s, seq)) {
        return util.re.mk_to_re(util.str.mk_empty(seq));
    }
    UNREACHABLE();
    return nullptr;
}

app* seq_util::mk_skolem(symbol const& name, unsigned n, expr* const* args, sort* range) {
    SASSERT(range);
    parameter param(name);
    func_decl* f = m.mk_func_decl(get_family_id(), _OP_SEQ_SKOLEM, 1, &param, n, args, range);
    return m.mk_app(f, n, args);
}

app* seq_util::str::mk_string(zstring const& s) const { 
    return u.seq.mk_string(s); 
}

app*  seq_util::str::mk_char(zstring const& s, unsigned idx) const {
    bv_util bvu(m);
    return bvu.mk_numeral(s[idx], s.num_bits());
}

app*  seq_util::str::mk_char(char ch) const {
    zstring s(ch, zstring::ascii);
    return mk_char(s, 0);
}

bool seq_util::is_const_char(expr* e, unsigned& c) const {
    bv_util bv(m);
    rational r;    
    unsigned sz;
    return bv.is_numeral(e, r, sz) && sz == 8 && r.is_unsigned() && (c = r.get_unsigned(), true);
}

app* seq_util::mk_char(unsigned ch) const {
    bv_util bv(m);
    return bv.mk_numeral(rational(ch), 8);
}

app* seq_util::mk_le(expr* ch1, expr* ch2) const {
    bv_util bv(m);
    return bv.mk_ule(ch1, ch2);
}

app* seq_util::mk_lt(expr* ch1, expr* ch2) const {
    bv_util bv(m);
    return m.mk_not(bv.mk_ule(ch2, ch1));
}

bool seq_util::str::is_string(expr const* n, zstring& s) const {
    if (is_string(n)) {
        s = zstring(to_app(n)->get_decl()->get_parameter(0).get_symbol().bare_str());
        return true;
    }
    else {
        return false;
    }
}

bool seq_util::str::is_nth_i(expr const* n, expr*& s, unsigned& idx) const {
    expr* i = nullptr;
    if (!is_nth_i(n, s, i)) return false;
    return arith_util(m).is_unsigned(i, idx);
}

app* seq_util::str::mk_nth_i(expr* s, unsigned i) const {
    return mk_nth_i(s, arith_util(m).mk_int(i));
}

void seq_util::str::get_concat(expr* e, expr_ref_vector& es) const {
    expr* e1, *e2;
    while (is_concat(e, e1, e2)) {
        get_concat(e1, es);
        e = e2;
    }
    if (!is_empty(e)) {
        es.push_back(e);
    }
}

void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
    expr* e1, *e2;
    while (is_concat(e, e1, e2)) {
        get_concat_units(e1, es);
        e = e2;
    }
    zstring s;
    if (is_string(e, s)) {
        unsigned sz = s.length();
        for (unsigned j = 0; j < sz; ++j) {
            es.push_back(mk_unit(mk_char(s, j)));
        }        
    }
    else if (!is_empty(e)) {
        es.push_back(e);
    }
}

app* seq_util::str::mk_is_empty(expr* s) const {
    return m.mk_eq(s, mk_empty(get_sort(s)));
}


app* seq_util::re::mk_loop(expr* r, unsigned lo) {
    parameter param(lo);
    return m.mk_app(m_fid, OP_RE_LOOP, 1, &param, 1, &r);
}

app* seq_util::re::mk_loop(expr* r, unsigned lo, unsigned hi) {
    parameter params[2] = { parameter(lo), parameter(hi) };
    return m.mk_app(m_fid, OP_RE_LOOP, 2, params, 1, &r);
}

app* seq_util::re::mk_full_char(sort* s) {
    return m.mk_app(m_fid, OP_RE_FULL_CHAR_SET, 0, nullptr, 0, nullptr, s);
}

app* seq_util::re::mk_full_seq(sort* s) {
    return m.mk_app(m_fid, OP_RE_FULL_SEQ_SET, 0, nullptr, 0, nullptr, s);
}

app* seq_util::re::mk_empty(sort* s) {    
    return m.mk_app(m_fid, OP_RE_EMPTY_SET, 0, nullptr, 0, nullptr, s);
}

bool seq_util::re::is_loop(expr const* n, expr*& body, unsigned& lo, unsigned& hi)  {
    if (is_loop(n)) {
        app const* a = to_app(n);
        if (a->get_num_args() == 1 && a->get_decl()->get_num_parameters() == 2) {
            body = a->get_arg(0);
            lo = a->get_decl()->get_parameter(0).get_int();
            hi = a->get_decl()->get_parameter(1).get_int();
            return true;
        }
    }
    return false;
}

bool seq_util::re::is_loop(expr const* n, expr*& body, unsigned& lo)  {
    if (is_loop(n)) {
        app const* a = to_app(n);
        if (a->get_num_args() == 1 && a->get_decl()->get_num_parameters() == 1) {
            body = a->get_arg(0);
            lo = a->get_decl()->get_parameter(0).get_int();
            return true;
        }
    }
    return false;
}
