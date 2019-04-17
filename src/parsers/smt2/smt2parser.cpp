/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt2parser.h

Abstract:

    SMT 2.0 parser

Author:

    Leonardo de Moura (leonardo) 2011-03-01

Revision History:

--*/
#include "util/stack.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/has_free_vars.h"
#include "ast/ast_smt2_pp.h"
#include "parsers/smt2/smt2parser.h"
#include "parsers/smt2/smt2scanner.h"
#include "parsers/util/pattern_validation.h"
#include "parsers/util/parser_params.hpp"
#include<sstream>

namespace smt2 {
    typedef cmd_exception parser_exception;

    class parser {
        cmd_context &        m_ctx;
        params_ref           m_params;
        scanner              m_scanner;
        scanner::token       m_curr;
        cmd *                m_curr_cmd;
        stack                m_stack;
        struct local {
            expr *           m_term;
            unsigned         m_level;
            local():m_term(nullptr), m_level(0) {}
            local(expr * t, unsigned l):m_term(t), m_level(l) {}
        };
        symbol_table<local>  m_env;
        unsigned             m_num_bindings;

        dictionary<int>      m_sort_id2param_idx;
        dictionary<int>      m_dt_name2idx;
        dictionary<unsigned> m_dt_name2arity;
        svector<symbol>      m_dt_names;

        scoped_ptr<psort_ref_vector>      m_psort_stack;
        scoped_ptr<sort_ref_vector>       m_sort_stack;
        scoped_ptr<expr_ref_vector>       m_expr_stack;
        unsigned                          m_num_expr_frames;
        scoped_ptr<expr_ref_vector>       m_pattern_stack;
        scoped_ptr<expr_ref_vector>       m_nopattern_stack;
        svector<symbol>                   m_symbol_stack;
        vector<parameter>                 m_param_stack;
        scoped_ptr<sexpr_ref_vector>      m_sexpr_stack;

        scoped_ptr<bv_util>               m_bv_util;
        scoped_ptr<arith_util>            m_arith_util;
        scoped_ptr<datatype_util>         m_datatype_util;
        scoped_ptr<seq_util>              m_seq_util;      
        scoped_ptr<pattern_validator>     m_pattern_validator;
        scoped_ptr<var_shifter>           m_var_shifter;

        symbol               m_let;
        symbol               m_bang;
        symbol               m_forall;
        symbol               m_exists;
        symbol               m_lambda;
        symbol               m_as;
        symbol               m_not;
        symbol               m_root_obj;

        symbol               m_named;
        symbol               m_weight;
        symbol               m_qid;
        symbol               m_skid;
        symbol               m_ex_act;
        symbol               m_pattern;
        symbol               m_nopattern;
        symbol               m_lblneg;
        symbol               m_lblpos;

        symbol               m_assert;
        symbol               m_check_sat;
        symbol               m_define_fun;
        symbol               m_define_const;
        symbol               m_model_add;
        symbol               m_model_del;
        symbol               m_declare_fun;
        symbol               m_declare_const;
        symbol               m_define_sort;
        symbol               m_declare_sort;
        symbol               m_declare_datatypes;
        symbol               m_declare_datatype;
        symbol               m_par;
        symbol               m_push;
        symbol               m_pop;
        symbol               m_get_value;
        symbol               m_reset;
        symbol               m_check_sat_assuming;
        symbol               m_define_fun_rec;
        symbol               m_define_funs_rec;
        symbol               m_match;
        symbol               m_case;
        symbol               m_underscore;

        typedef std::pair<symbol, expr*> named_expr;
        named_expr           m_last_named_expr;

        ast_manager & m() const { return m_ctx.m(); }
        pdecl_manager & pm() const { return m_ctx.pm(); }
        sexpr_manager & sm() const { return m_ctx.sm(); }

        bool m_ignore_user_patterns;
        bool m_ignore_bad_patterns;
        bool m_display_error_for_vs;

        bool ignore_user_patterns() const { return m_ignore_user_patterns; }
        bool ignore_bad_patterns() const  { return m_ignore_bad_patterns; }
        bool use_vs_format() const        { return m_display_error_for_vs; }

        struct psort_frame {
            psort_decl *     m_decl;
            unsigned         m_spos; // position of m_psort_stack
            psort_frame(parser & p, psort_decl * d, unsigned spos):
                m_decl(d), m_spos(spos) {
            }
        };

        typedef psort_frame sort_frame;

        enum expr_frame_kind { EF_APP, EF_LET, EF_LET_DECL, EF_MATCH, EF_QUANT, EF_ATTR_EXPR, EF_PATTERN };

        struct expr_frame {
            expr_frame_kind m_kind;
            expr_frame(expr_frame_kind k):m_kind(k) {}
        };

        struct app_frame : public expr_frame {
            symbol   m_f;
            unsigned m_expr_spos;
            unsigned m_param_spos;
            bool     m_as_sort;
            app_frame(symbol const & f, unsigned expr_spos, unsigned param_spos, bool as_sort):
                expr_frame(EF_APP),
                m_f(f),
                m_expr_spos(expr_spos),
                m_param_spos(param_spos),
                m_as_sort(as_sort) {}
        };

        struct quant_frame : public expr_frame {
            quantifier_kind m_kind;
            symbol   m_qid;
            symbol   m_skid;
            unsigned m_weight;
            unsigned m_pat_spos;
            unsigned m_nopat_spos;
            unsigned m_sym_spos;
            unsigned m_sort_spos;
            unsigned m_expr_spos;
            quant_frame(quantifier_kind k, unsigned pat_spos, unsigned nopat_spos, unsigned sym_spos, unsigned sort_spos, unsigned expr_spos):
                expr_frame(EF_QUANT), m_kind(k), m_weight(1),
                m_pat_spos(pat_spos), m_nopat_spos(nopat_spos),
                m_sym_spos(sym_spos), m_sort_spos(sort_spos),
                m_expr_spos(expr_spos) {}
        };

        struct match_frame : public expr_frame {
            match_frame():expr_frame(EF_MATCH) {}
        };

        struct let_frame : public expr_frame {
            bool     m_in_decls;
            unsigned m_sym_spos;
            unsigned m_expr_spos;
            let_frame(unsigned sym_spos, unsigned expr_spos):expr_frame(EF_LET), m_in_decls(true), m_sym_spos(sym_spos), m_expr_spos(expr_spos) {}
        };

        struct let_decl_frame : public expr_frame {
            let_decl_frame():expr_frame(EF_LET_DECL) {}
        };

        struct attr_expr_frame : public expr_frame {
            expr_frame * m_prev;
            unsigned     m_sym_spos;
            unsigned     m_expr_spos;
            symbol       m_last_symbol;
            attr_expr_frame(expr_frame * prev, unsigned sym_spos, unsigned expr_spos):
                expr_frame(EF_ATTR_EXPR),
                m_prev(prev),
                m_sym_spos(sym_spos),
                m_expr_spos(expr_spos) {}
        };

        struct pattern_frame : public expr_frame {
            unsigned    m_expr_spos;
            pattern_frame(unsigned expr_spos):
                expr_frame(EF_PATTERN),
                m_expr_spos(expr_spos) {
            }
        };

        struct sexpr_frame {
            unsigned         m_spos; // position of m_sexpr_stack
            sexpr_frame(unsigned spos):
                m_spos(spos) {
            }
        };

        void reset_stack() {
            m_stack.reset();
        }

        psort_ref_vector & psort_stack() {
            if (m_psort_stack.get() == nullptr)
                m_psort_stack = alloc(psort_ref_vector, pm());
            return *(m_psort_stack.get());
        }

        sort_ref_vector & sort_stack() {
            if (m_sort_stack.get() == nullptr)
                m_sort_stack = alloc(sort_ref_vector, m());
            return *(m_sort_stack.get());
        }

        expr_ref_vector & expr_stack() {
            if (m_expr_stack.get() == nullptr)
                m_expr_stack = alloc(expr_ref_vector, m());
            return *(m_expr_stack.get());
        }

        template<typename T>
        static unsigned size(scoped_ptr<T> & v) {
            return v.get() == nullptr ? 0 : v->size();
        }

        template<typename T>
        static void shrink(scoped_ptr<T> & v, unsigned old_sz) {
            if (v.get() == nullptr) {
                SASSERT(old_sz == 0);
            }
            else {
                v->shrink(old_sz);
            }
        }

        expr_ref_vector & pattern_stack() {
            if (m_pattern_stack.get() == nullptr)
                m_pattern_stack = alloc(expr_ref_vector, m());
            return *(m_pattern_stack.get());
        }

        expr_ref_vector & nopattern_stack() {
            if (m_nopattern_stack.get() == nullptr)
                m_nopattern_stack = alloc(expr_ref_vector, m());
            return *(m_nopattern_stack.get());
        }

        svector<symbol> & symbol_stack() {
            return m_symbol_stack;
        }

        sexpr_ref_vector & sexpr_stack() {
            if (m_sexpr_stack.get() == nullptr)
                m_sexpr_stack = alloc(sexpr_ref_vector, sm());
            return *(m_sexpr_stack.get());
        }

        arith_util & autil() {
            if (m_arith_util.get() == nullptr)
                m_arith_util = alloc(arith_util, m());
            return *(m_arith_util.get());
        }

        datatype_util & dtutil() {
            if (m_datatype_util.get() == nullptr)
                m_datatype_util = alloc(datatype_util, m());
            return *(m_datatype_util.get());
        }

        seq_util & sutil() {
            if (m_seq_util.get() == nullptr)
                m_seq_util = alloc(seq_util, m());
            return *(m_seq_util.get());
        }

        bv_util & butil() {
            if (m_bv_util.get() == nullptr)
                m_bv_util = alloc(bv_util, m());
            return *(m_bv_util.get());
        }

        pattern_validator & pat_validator() {
            if (m_pattern_validator.get() == nullptr) {
                m_pattern_validator = alloc(pattern_validator, m());
            }
            return *(m_pattern_validator.get());
        }

        var_shifter & shifter() {
            if (m_var_shifter.get() == nullptr)
                m_var_shifter = alloc(var_shifter, m());
            return *(m_var_shifter.get());
        }

        unsigned            m_cache_end;
        std::vector<std::string> m_cached_strings;

        int m_num_open_paren;

        void scan_core() {
            m_cache_end = m_scanner.cache_size();
            m_curr      = m_scanner.scan();
        }

        void scan() {
            switch (m_curr) {
            case scanner::LEFT_PAREN: m_num_open_paren++; break;
            case scanner::RIGHT_PAREN: m_num_open_paren--; break;
            default: break;
            }
            scan_core();
        }

        void next() {
            if (m_curr != scanner::EOF_TOKEN)
                scan();
        }

        scanner::token curr() const { return m_curr; }

        // consume garbage
        // return true if managed to recover from the error...
        bool sync_after_error() {
            unsigned num_errors = 0;
            while (num_errors < 100) {
                try {
                    while (curr_is_rparen())
                        next();
                    if (m_num_open_paren < 0)
                        m_num_open_paren = 0;
                    if (curr() == scanner::EOF_TOKEN && m_num_open_paren == 0)
                        return true;
                    SASSERT(m_num_open_paren >= 0);
                    while (m_num_open_paren > 0 || !curr_is_lparen()) {
                        TRACE("sync", tout << "sync(): curr: " << curr() << "\n";
                              tout << "m_num_open_paren: " << m_num_open_paren << ", line: " << m_scanner.get_line() << ", pos: "
                              << m_scanner.get_pos() << "\n";);
                        if (curr() == scanner::EOF_TOKEN) {
                            return false;
                        }
                        SASSERT(m_num_open_paren >= 0);
                        next();
                        SASSERT(m_num_open_paren >= -1);
                        if (m_num_open_paren < 0)
                            m_num_open_paren = 0;
                        SASSERT(m_num_open_paren >= 0);
                    }
                    return true;
                }
                catch (scanner_exception & ex) {
                    SASSERT(ex.has_pos());
                    error(ex.line(), ex.pos(), ex.msg());
                    ++num_errors;
                }
            }
            return false;
        }

        void check_next(scanner::token t, char const * msg) {
            if (curr() == t) {
                next();
                return;
            }
            std::ostringstream str;
            str << msg << " got " << curr_id();
            throw parser_exception(str.str());
        }

        symbol const & curr_id() const { return m_scanner.get_id(); }
        rational curr_numeral() const { return m_scanner.get_number(); }
        unsigned curr_unsigned() {
            rational n = curr_numeral();
            if (!n.is_unsigned())
                throw parser_exception("invalid indexed identifier, index is too big to fit in an unsigned machine integer");
            return n.get_unsigned();
        }


        bool curr_is_identifier() const { return curr() == scanner::SYMBOL_TOKEN; }
        bool curr_is_keyword() const { return curr() == scanner::KEYWORD_TOKEN; }
        bool curr_is_string() const { return curr() == scanner::STRING_TOKEN; }
        bool curr_is_lparen() const { return curr() == scanner::LEFT_PAREN; }
        bool curr_is_rparen() const { return curr() == scanner::RIGHT_PAREN; }
        bool curr_is_int() const { return curr() == scanner::INT_TOKEN; }
        bool curr_is_float() const { return curr() == scanner::FLOAT_TOKEN; }

        bool curr_id_is_underscore() const { SASSERT(curr_is_identifier()); return curr_id() == m_underscore; }
        bool curr_id_is_as() const { SASSERT(curr_is_identifier()); return curr_id() == m_as; }
        bool curr_id_is_match() const { SASSERT(curr_is_identifier()); return curr_id() == m_match; }
        bool curr_id_is_case() const { return curr_id() == m_case; }
        bool curr_id_is_forall() const { SASSERT(curr_is_identifier()); return curr_id() == m_forall; }
        bool curr_id_is_exists() const { SASSERT(curr_is_identifier()); return curr_id() == m_exists; }
        bool curr_id_is_lambda() const { SASSERT(curr_is_identifier()); return curr_id() == m_lambda; }
        bool curr_id_is_bang() const { SASSERT(curr_is_identifier()); return curr_id() == m_bang; }
        bool curr_id_is_let() const { SASSERT(curr_is_identifier()); return curr_id() == m_let; }
        bool curr_id_is_root_obj() const { SASSERT(curr_is_identifier()); return curr_id() == m_root_obj; }
        void check_lparen(char const * msg) { if (!curr_is_lparen()) throw parser_exception(msg); }
        void check_lparen_next(char const * msg) { check_next(scanner::LEFT_PAREN, msg); }
        void check_rparen_next(char const * msg) { check_next(scanner::RIGHT_PAREN, msg); }
        void check_rparen(char const * msg) { if (!curr_is_rparen()) throw parser_exception(msg); }
        void check_id_next(symbol const & id, char const * msg) {
            if (!curr_is_identifier() || curr_id() != id)
                throw parser_exception(msg);
            next();
        }
        void check_underscore_next(char const * msg) { check_id_next(m_underscore, msg); }
        void check_as_next(char const * msg) { check_id_next(m_as, msg); }
        void check_identifier(char const * msg) { if (!curr_is_identifier()) throw parser_exception(msg); }
        void check_keyword(char const * msg) { if (!curr_is_keyword()) throw parser_exception(msg); }
        void check_string(char const * msg) { if (!curr_is_string()) throw parser_exception(msg); }
        void check_int(char const * msg) { if (!curr_is_int()) throw parser_exception(msg); }
        void check_int_or_float(char const * msg) { if (!curr_is_int() && !curr_is_float()) throw parser_exception(msg); }
        void check_float(char const * msg) { if (!curr_is_float()) throw parser_exception(msg); }
        symbol check_identifier_next(char const * msg) { check_identifier(msg); symbol s = curr_id(); next(); return s; }


        char const * m_current_file;
        void set_current_file(char const * s) { m_current_file = s; }

        void error(unsigned line, unsigned pos, char const * msg) {
            m_ctx.set_cancel(false);
            if (use_vs_format()) {
                m_ctx.diagnostic_stream() << "Z3(" << line << ", " << pos << "): ERROR: " << msg;
                if (msg[strlen(msg)-1] != '\n')
                    m_ctx.diagnostic_stream() << std::endl;
            }
            else {
                m_ctx.regular_stream() << "(error \"";
                if (m_current_file) m_ctx.regular_stream() << m_current_file << ": ";
                m_ctx.regular_stream()<< "line " << line << " column " << pos << ": " << escaped(msg, true) << "\")" << std::endl;
            }
            if (m_ctx.exit_on_error()) {
                // WORKAROUND: ASan's LeakSanitizer reports many false positives when
                // calling `exit()` so call `_Exit()` instead which avoids invoking leak
                // checking.
                _Exit(1);
            }
        }

        void error(char const * msg) {
            error(m_scanner.get_line(), m_scanner.get_pos(), msg);
        }

        void error_wo_pos(char const * msg) {
            if (use_vs_format()) {
                m_ctx.diagnostic_stream() << "Z3: ERROR: " << msg;
                if (msg[strlen(msg)-1] != '\n')
                    m_ctx.diagnostic_stream() << std::endl;
            }
            else {
                m_ctx.regular_stream() << "(error : " << escaped(msg, true) << "\")" << std::endl;
            }
        }

        void unknown_sort(symbol id, char const* context = "") {
            std::string msg = context;
            if (context[0]) msg += ": ";
            msg += "unknown sort '";
            msg += id.str() + "'";
            throw parser_exception(std::move(msg));
        }

        void consume_sexpr() {
            unsigned num_parens = 0;
            do {
                switch (curr()) {
                case scanner::LEFT_PAREN:
                    num_parens++;
                    break;
                case scanner::RIGHT_PAREN:
                    if (num_parens == 0)
                        throw parser_exception("invalid s-expression, unexpected ')'");
                    num_parens--;
                    break;
                case scanner::SYMBOL_TOKEN:
                case scanner::KEYWORD_TOKEN:
                case scanner::STRING_TOKEN:
                case scanner::INT_TOKEN:
                case scanner::FLOAT_TOKEN:
                case scanner::BV_TOKEN:
                    break;
                case scanner::EOF_TOKEN:
                    throw parser_exception("invalid s-expression, unexpected end of file");
                    break;
                default:
                    throw parser_exception("invalid s-expression, unexpected input");
                    break;
                }
                next();
            }
            while (num_parens > 0);
        }

        void parse_sexpr() {
            unsigned stack_pos  = sexpr_stack().size();
            (void)stack_pos;
            unsigned num_frames = 0;
            do {
                unsigned line = m_scanner.get_line();
                unsigned pos  = m_scanner.get_pos();
                switch (curr()) {
                case scanner::LEFT_PAREN: {
                    void * mem = m_stack.allocate(sizeof(sexpr_frame));
                    new (mem) sexpr_frame(sexpr_stack().size());
                    num_frames++;
                    break;
                }
                case scanner::RIGHT_PAREN: {
                    if (num_frames == 0)
                        throw parser_exception("invalid s-expression, unexpected ')'");
                    num_frames--;
                    sexpr_frame * fr = static_cast<sexpr_frame*>(m_stack.top());
                    unsigned spos = fr->m_spos;
                    unsigned epos = sexpr_stack().size();
                    SASSERT(epos >= spos);
                    unsigned num  = epos - spos;
                    if (num == 0)
                        throw parser_exception("invalid empty s-expression");
                    sexpr * r = sm().mk_composite(num, sexpr_stack().c_ptr() + spos, line, pos);
                    sexpr_stack().shrink(spos);
                    sexpr_stack().push_back(r);
                    m_stack.deallocate(fr);
                    break;
                }
                case scanner::SYMBOL_TOKEN:
                    sexpr_stack().push_back(sm().mk_symbol(curr_id(), line, pos));
                    break;
                case scanner::KEYWORD_TOKEN:
                    sexpr_stack().push_back(sm().mk_keyword(curr_id(), line, pos));
                    break;
                case scanner::STRING_TOKEN:
                    sexpr_stack().push_back(sm().mk_string(m_scanner.get_string(), line, pos));
                    break;
                case scanner::INT_TOKEN:
                case scanner::FLOAT_TOKEN:
                    sexpr_stack().push_back(sm().mk_numeral(curr_numeral(), line, pos));
                    break;
                case scanner::BV_TOKEN:
                    sexpr_stack().push_back(sm().mk_bv_numeral(curr_numeral(), m_scanner.get_bv_size(), line, pos));
                    break;
                case scanner::EOF_TOKEN:
                    throw parser_exception("invalid s-expression, unexpected end of file");
                    break;
                default:
                    throw parser_exception("invalid s-expression, unexpected input");
                    break;
                }
                next();
            }
            while (num_frames > 0);
            SASSERT(sexpr_stack().size() == stack_pos + 1);
        }

        sort * parse_sort_name(char const* context = "") {
            SASSERT(curr_is_identifier());
            symbol id = curr_id();
            psort_decl * d = m_ctx.find_psort_decl(id);
            if (d == nullptr)
                unknown_sort(id, context);
            if (!d->has_var_params() && d->get_num_params() != 0)
                throw parser_exception("sort constructor expects parameters");
            sort * r = d->instantiate(pm());
            if (r == nullptr)
                throw parser_exception("invalid sort application");
            next();
            return r;
        }

        psort * parse_psort_name(bool ignore_unknown_sort = false) {
            SASSERT(curr_is_identifier());
            symbol id = curr_id();
            psort_decl * d = m_ctx.find_psort_decl(id);
            if (d != nullptr) {
                if (!d->has_var_params() && d->get_num_params() != 0)
                    throw parser_exception("sort constructor expects parameters");
                next();
                return pm().mk_psort_app(d);
            }
            else {
                int idx = 0;
                if (m_sort_id2param_idx.find(id, idx)) {
                    next();
                    return pm().mk_psort_var(m_sort_id2param_idx.size(), idx);
                }
                else {
                    if (!ignore_unknown_sort) {
                        unknown_sort(id);
                        UNREACHABLE();
                    }
                    return nullptr;
                }
            }
        }

        sort * parse_indexed_sort() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id_is_underscore());
            next();
            symbol id = check_identifier_next("invalid indexed sort, symbol expected");
            psort_decl * d = m_ctx.find_psort_decl(id);
            if (d == nullptr)
                unknown_sort(id);
            sbuffer<unsigned> args;
            while (!curr_is_rparen()) {
                check_int("invalid indexed sort, integer or ')' expected");
                unsigned u = curr_unsigned();
                args.push_back(u);
                next();
            }
            sort * r = d->instantiate(pm(), args.size(), args.c_ptr());
            if (r == nullptr)
                throw parser_exception("invalid sort application");
            next();
            return r;
        }

        void push_psort_app_frame() {
            SASSERT(curr_is_identifier());
            symbol id = curr_id();
            psort_decl * d = m_ctx.find_psort_decl(id);
            if (d == nullptr) {
                unknown_sort(id);                                
            }
            next();
            void * mem      = m_stack.allocate(sizeof(psort_frame));
            new (mem) psort_frame(*this, d, psort_stack().size());
        }

        void pop_psort_app_frame() {
            SASSERT(curr_is_rparen());
            psort_frame * fr = static_cast<psort_frame*>(m_stack.top());
            psort_decl * d  = fr->m_decl;
            unsigned spos = fr->m_spos;
            unsigned epos = psort_stack().size();
            SASSERT(epos >= spos);
            unsigned num  = epos - spos;
            if (!d->has_var_params() && d->get_num_params() != num) {
                TRACE("smt2parser", tout << "num: " << num << ", d->get_num_params(): " << d->get_num_params() << "\n";);
                throw parser_exception("invalid number of parameters to sort constructor");
            }

            psort * r = pm().mk_psort_app(m_sort_id2param_idx.size(), d, num, psort_stack().c_ptr() + spos);
            psort_stack().shrink(spos);
            psort_stack().push_back(r);
            m_stack.deallocate(fr);
            next();
        }

        void parse_psort(bool ignore_unknown_sort = false) {
            unsigned stack_pos  = psort_stack().size();
            (void)stack_pos;
            unsigned num_frames = 0;
            do {
                if (curr_is_identifier()) {
                    psort_stack().push_back(parse_psort_name(false));
                }
                else if (curr_is_rparen()) {
                    if (num_frames == 0)
                        throw parser_exception("invalid sort, unexpected ')'");
                    pop_psort_app_frame();
                    num_frames--;
                }
                else {
                    check_lparen_next("invalid sort, symbol, '_' or '(' expected");
                    if (!curr_is_identifier())
                        throw parser_exception("invalid sort, symbol or '_' expected");
                    if (curr_id_is_underscore()) {
                        psort_stack().push_back(pm().mk_psort_cnst(parse_indexed_sort()));
                    }
                    else {
                        push_psort_app_frame();
                        num_frames++;
                    }
                }
            }
            while (num_frames > 0);
            SASSERT(psort_stack().size() == stack_pos + 1);
        }

        void push_sort_app_frame() {
            SASSERT(curr_is_identifier());
            symbol id = curr_id();
            psort_decl * d = m_ctx.find_psort_decl(id);
            if (d == nullptr)
                unknown_sort(id);
            next();
            void * mem      = m_stack.allocate(sizeof(sort_frame));
            new (mem) sort_frame(*this, d, sort_stack().size());
        }

        void pop_sort_app_frame() {
            SASSERT(curr_is_rparen());
            sort_frame * fr = static_cast<sort_frame*>(m_stack.top());
            psort_decl * d  = fr->m_decl;
            unsigned spos = fr->m_spos;
            unsigned epos = sort_stack().size();
            SASSERT(epos >= spos);
            unsigned num  = epos - spos;
            if (!d->has_var_params() && d->get_num_params() != num) {
                TRACE("smt2parser", tout << "num: " << num << ", d->get_num_params(): " << d->get_num_params() << "\n";);
                throw parser_exception("invalid number of parameters to sort constructor");
            }
            sort * r = d->instantiate(pm(), num, sort_stack().c_ptr() + spos);
            if (r == nullptr)
                throw parser_exception("invalid sort application");
            sort_stack().shrink(spos);
            sort_stack().push_back(r);
            m_stack.deallocate(fr);
            next();
        }

        void parse_sort(char const* context) {
            unsigned stack_pos  = sort_stack().size();
            (void)stack_pos;
            unsigned num_frames = 0;
            do {
                if (curr_is_identifier()) {
                    sort_stack().push_back(parse_sort_name(context));
                }
                else if (curr_is_rparen()) {
                    if (num_frames == 0) {
                        throw parser_exception(std::string(context) + " invalid sort, unexpected ')'");
                    }
                    pop_sort_app_frame();
                    num_frames--;
                }
                else {
                    check_lparen_next("invalid sort, symbol, '_' or '(' expected");
                    if (!curr_is_identifier())
                        throw parser_exception(std::string(context) + " invalid sort, symbol or '_' expected");
                    if (curr_id_is_underscore()) {
                        sort_stack().push_back(parse_indexed_sort());
                    }
                    else {
                        push_sort_app_frame();
                        num_frames++;
                    }
                }
            }
            while (num_frames > 0);
            SASSERT(sort_stack().size() == stack_pos + 1);
        }

        unsigned parse_sorts(char const* context) {
            unsigned sz = 0;
            check_lparen_next(context);
            while (!curr_is_rparen()) {
                parse_sort(context);
                sz++;
            }
            next();
            return sz;
        }

        unsigned parse_symbols() {
            unsigned sz = 0;
            check_lparen_next("invalid list of symbols, '(' expected");
            while (!curr_is_rparen()) {                
                m_symbol_stack.push_back(check_identifier_next("invalid list of symbols, symbol or ')' expected"));
                sz++;
            }
            next();
            return sz;
        }

        ptype parse_ptype() {
            SASSERT(curr_is_identifier());
            psort * p = parse_psort_name(true);
            ptype result;
            if (p != nullptr) {
                result = ptype(p);
            }
            else {
                // parse_psort_name failed, identifier was not consumed.
                int idx;
                if (m_dt_name2idx.find(curr_id(), idx)) {
                    result = ptype(idx);
                }
                else {
                    result = ptype(curr_id());
                }
                SASSERT(curr_is_identifier());
                next();
            }
            return result;
        }

        // [ '(' identifier sort ')' ]+
        void parse_accessor_decls(paccessor_decl_ref_buffer & a_decls) {
            while (!curr_is_rparen()) {
                check_lparen_next("invalid datatype declaration, '(' or ')' expected");
                symbol a_name = check_identifier_next("invalid accessor declaration, symbol (accessor name) expected");
                if (curr_is_identifier()) {                    
                    a_decls.push_back(pm().mk_paccessor_decl(m_sort_id2param_idx.size(), a_name, parse_ptype()));
                }
                else {
                    parse_psort(true);
                    a_decls.push_back(pm().mk_paccessor_decl(m_sort_id2param_idx.size(), a_name, ptype(psort_stack().back())));
                    psort_stack().pop_back();
                }
                check_rparen_next("invalid accessor declaration, ')' expected");
            }
        }

        // [ '(' identifier accessors ')' ]+
        void parse_constructor_decls(pconstructor_decl_ref_buffer & ct_decls) {
            while (!curr_is_rparen()) {
                if (curr_is_identifier()) {
                    symbol ct_name = curr_id();
                    std::string r_str = "is-";
                    r_str += curr_id().str();
                    symbol r_name(r_str.c_str());
                    next();
                    TRACE("datatype_parser_bug", tout << ct_name << " " << r_name << "\n";);
                    ct_decls.push_back(pm().mk_pconstructor_decl(m_sort_id2param_idx.size(), ct_name, r_name, 0, nullptr));
                }
                else {
                    check_lparen_next("invalid datatype declaration, '(' or ')' expected");
                    check_identifier("invalid constructor declaration, symbol (constructor name) expected");
                    symbol ct_name = curr_id();
                    std::string r_str = "is-";
                    r_str += curr_id().str();
                    symbol r_name(r_str.c_str());
                    next();
                    paccessor_decl_ref_buffer new_a_decls(pm());
                    parse_accessor_decls(new_a_decls);
                    ct_decls.push_back(pm().mk_pconstructor_decl(m_sort_id2param_idx.size(), ct_name, r_name, new_a_decls.size(), new_a_decls.c_ptr()));
                    check_rparen_next("invalid constructor declaration, ')' expected");
                }
            }
            if (ct_decls.empty())
                throw parser_exception("invalid datatype declaration, datatype does not have any constructors");
        }
        
        void parse_declare_datatypes() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_declare_datatypes);
            next();
            unsigned line = m_scanner.get_line();
            unsigned pos  = m_scanner.get_pos();
            m_dt_name2idx.reset();
            bool is_smt2_6 = parse_sort_decl_or_params();
            unsigned i = 0;
            pdatatype_decl_ref_buffer new_dt_decls(pm());
            check_lparen_next("invalid datatype declaration, '(' expected");
            pdatatype_decl_ref d(pm());                
            while (!curr_is_rparen()) {
                pconstructor_decl_ref_buffer new_ct_decls(pm());
                if (is_smt2_6) {
                    if (i >= m_dt_names.size()) {
                        throw parser_exception("invalid datatype declaration, too many data-type bodies defined");
                    }
                    symbol dt_name = m_dt_names[i];
                    parse_datatype_dec(nullptr, new_ct_decls);
                    d = pm().mk_pdatatype_decl(m_dt_name2arity.find(dt_name), dt_name, new_ct_decls.size(), new_ct_decls.c_ptr());
                }
                else {
                    check_lparen_next("invalid datatype declaration, '(' or ')' expected");
                    symbol dt_name = check_identifier_next("invalid datatype declaration, symbol (datatype name) expected");
                    m_dt_name2idx.insert(dt_name, i);
                    parse_constructor_decls(new_ct_decls);
                    d = pm().mk_pdatatype_decl(m_sort_id2param_idx.size(), dt_name, new_ct_decls.size(), new_ct_decls.c_ptr());
                    check_rparen_next("invalid datatype declaration, ')' expected");
                }
                new_dt_decls.push_back(d);
                i++;
            }
            if (i < m_dt_names.size()) {
                throw parser_exception("invalid datatype declaration, too few datatype definitions compared to declared sorts");
            }
            next();
            check_rparen("invalid datatype declaration");
            unsigned sz = new_dt_decls.size();
            if (sz == 0) {
                m_ctx.print_success();
                next();
                return;
            }
            else if (sz == 1) {
                check_missing(new_dt_decls[0], line, pos);
                new_dt_decls[0]->commit(pm());
            }
            else {
                SASSERT(sz > 1);
                pdatatypes_decl_ref dts(pm());
                dts = pm().mk_pdatatypes_decl(m_sort_id2param_idx.size(), sz, new_dt_decls.c_ptr());
                symbol missing;
                if (!pm().fix_missing_refs(dts, missing)) {
                    std::string err_msg = "invalid datatype declaration, unknown sort '";
                    err_msg += missing.str();
                    err_msg += "'";
                    throw parser_exception(std::move(err_msg), line, pos);
                }
                dts->commit(pm());
                m_ctx.insert_aux_pdecl(dts.get());
            }
            for (unsigned i = 0; i < sz; i++) {
                pdatatype_decl * d = new_dt_decls[i];
                symbol duplicated;
                check_duplicate(d, line, pos);
                if (!is_smt2_6) {
                    // datatypes are inserted up front in SMT2.6 mode, so no need to re-insert them.
                    m_ctx.insert(d);
                }
            }                
            TRACE("declare_datatypes", tout << "i: " << i << " new_dt_decls.size(): " << sz << "\n";
                  for (unsigned j = 0; j < new_dt_decls.size(); ++j) tout << new_dt_decls[j]->get_name() << "\n";);
            m_ctx.print_success();
            next();
        }

        // ( declare-datatype symbol datatype_dec) 
        void parse_declare_datatype() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_declare_datatype);
            next();
            unsigned line = m_scanner.get_line();
            unsigned pos  = m_scanner.get_pos();
            symbol dt_name = curr_id();
            next();

            m_dt_name2idx.reset();
            m_dt_name2idx.insert(dt_name, 0);

            m_sort_id2param_idx.reset();

            pdatatype_decl_ref d(pm());                
            pconstructor_decl_ref_buffer new_ct_decls(pm());
            parse_datatype_dec(&dt_name, new_ct_decls);
            d = pm().mk_pdatatype_decl(m_sort_id2param_idx.size(), dt_name, new_ct_decls.size(), new_ct_decls.c_ptr());
            
            check_missing(d, line, pos);
            check_duplicate(d, line, pos);

            d->commit(pm());
            check_rparen("invalid end of datatype declaration, ')' expected");
            m_ctx.print_success();
            next();
        }


        // datatype_dec ::= ( constructor_dec+ ) | ( par ( symbol+ ) ( constructor_dec+ ) )

        void parse_datatype_dec(symbol* dt_name, pconstructor_decl_ref_buffer & ct_decls) {
            check_lparen_next("invalid datatype declaration, '(' expected");
            if (curr_id() == m_par) {
                next();
                parse_sort_decl_params();
                check_lparen_next("invalid constructor declaration after par, '(' expected");
                unsigned sz = m_sort_id2param_idx.size();
                if (sz > 0 && dt_name) {
                    m_ctx.insert(pm().mk_psort_dt_decl(sz, *dt_name));
                }
                parse_constructor_decls(ct_decls);
                check_rparen_next("invalid datatype declaration, ')' expected");
            }
            else {
                if (dt_name) {
                    m_ctx.insert(pm().mk_psort_dt_decl(0, *dt_name));
                }
                parse_constructor_decls(ct_decls);
            }
            check_rparen_next("invalid datatype declaration, ')' expected");
        }

        void check_missing(pdatatype_decl* d, unsigned line, unsigned pos) {
            symbol missing;
            if (d->has_missing_refs(missing)) {
                std::string err_msg = "invalid datatype declaration, unknown sort '";
                err_msg += missing.str();
                err_msg += "'";
                throw parser_exception(std::move(err_msg), line, pos);
            }
        }

        void check_duplicate(pdatatype_decl* d, unsigned line, unsigned pos) {
            symbol duplicated;
            if (d->has_duplicate_accessors(duplicated)) {
                std::string err_msg = "invalid datatype declaration, repeated accessor identifier '";
                err_msg += duplicated.str();
                err_msg += "'";
                throw parser_exception(std::move(err_msg), line, pos);
            }
        }

        void name_expr(expr * n, symbol const & s) {
            TRACE("name_expr", tout << "naming: " << s << " ->\n" << mk_pp(n, m()) << "\n";);
            if (!is_ground(n) && has_free_vars(n))
                throw parser_exception("invalid named expression, expression contains free variables");
            m_ctx.insert(s, 0, nullptr, n);
            m_last_named_expr.first  = s;
            m_last_named_expr.second = n;
        }

        bool in_quant_ctx(attr_expr_frame * fr) {
            return fr != nullptr && fr->m_prev != nullptr && fr->m_prev->m_kind == EF_QUANT;
        }

        void check_in_quant_ctx(attr_expr_frame * fr) {
            if (!in_quant_ctx(fr))
                throw parser_exception("invalid attribute, not in the scope of a quantifier");
        }

        void process_last_symbol(attr_expr_frame * fr) {
            if (fr->m_last_symbol == symbol::null)
                return;
            if (fr->m_last_symbol == m_pattern) {
                expr * pat = expr_stack().back();
                if (pat == nullptr) {
                    if (!ignore_bad_patterns())
                        throw parser_exception("invalid empty pattern");
                }
                else {
                    if (!m().is_pattern(pat))
                        pat = m().mk_pattern(to_app(pat)); // unary pattern
                    SASSERT(m().is_pattern(pat));
                    pattern_stack().push_back(pat);
                }
                expr_stack().pop_back();
            }
            else if (fr->m_last_symbol == m_nopattern) {
                nopattern_stack().push_back(expr_stack().back());
                expr_stack().pop_back();
            }
            else {
                UNREACHABLE();
            }
        }

        void store_qid(attr_expr_frame * fr, symbol const & qid) {
            SASSERT(in_quant_ctx(fr));
            static_cast<quant_frame*>(fr->m_prev)->m_qid = qid;
        }

        void store_skid(attr_expr_frame * fr, symbol const & skid) {
            SASSERT(in_quant_ctx(fr));
            static_cast<quant_frame*>(fr->m_prev)->m_skid = skid;
        }

        void store_weight(attr_expr_frame * fr, unsigned w) {
            SASSERT(in_quant_ctx(fr));
            static_cast<quant_frame*>(fr->m_prev)->m_weight = w;
        }

        // parse expression state
        enum pe_state {
            PES_EXPR,  // expecting <expr>
            PES_DECL,  // expecting (<id> <expr>)
            PES_PATTERN,
            PES_CONTINUE
        };

        pe_state consume_attributes(attr_expr_frame * fr) {
            if (fr->m_expr_spos == expr_stack().size())
                return PES_EXPR; // didn't parse the expression yet.
            process_last_symbol(fr);
            while (true) {
                check_keyword("invalid attributed expression, keyword expected");
                symbol id = curr_id();
                fr->m_last_symbol = symbol::null;
                TRACE("consume_attributes", tout << "id: " << id << ", expr_stack().size(): " << expr_stack().size() << "\n";);
                if (id == m_named) {
                    next();                    
                    name_expr(expr_stack().back(), check_identifier_next("invalid attribute value, symbol expected"));
                }
                else if (id == m_lblpos || id == m_lblneg) {
                    next();
                    check_identifier("invalid attribute value, symbol expected");
                    if (!m().is_bool(expr_stack().back()))
                        throw parser_exception("invalid labeled expression, expression must have Bool sort");
                    expr * new_expr = m().mk_label(id == m_lblpos, curr_id(), expr_stack().back());
                    expr_stack().pop_back();
                    expr_stack().push_back(new_expr);
                    next();
                }
                else if (id == m_weight) {
                    check_in_quant_ctx(fr);
                    next();
                    check_int("invalid weight attribute, integer expected");
                    store_weight(fr, curr_unsigned());
                    next();
                }
                else if (id == m_skid) {
                    check_in_quant_ctx(fr);
                    next();                    
                    store_skid(fr, check_identifier_next("invalid attribute value, symbol expected"));
                }
                else if (id == m_qid) {
                    check_in_quant_ctx(fr);
                    next();
                    check_identifier("invalid attribute value, symbol expected");
                    store_qid(fr, curr_id());
                    next();
                }
                else if (id == m_pattern) {
                    if (!ignore_user_patterns()) {
                        check_in_quant_ctx(fr);
                        next();
                        fr->m_last_symbol = id;
                        return PES_PATTERN;
                    }
                    else {
                        // just consume pattern
                        next();
                        consume_sexpr();
                    }
                }
                else if (id == m_nopattern) {
                    if (!ignore_user_patterns()) {
                        check_in_quant_ctx(fr);
                        next();
                        fr->m_last_symbol = id;
                        return PES_EXPR;
                    }
                    else {
                        // just consume pattern
                        next();
                        consume_sexpr();
                    }
                }
                else {
                    std::ostringstream str;
                    str << "unknown attribute " << id;
                    warning_msg("%s", str.str().c_str());
                    next();
                    // just consume the
                    consume_sexpr();
                }
                if (curr_is_rparen())
                    return PES_CONTINUE;
            }
        }

        pe_state parse_expr_state() {
            if (m_num_expr_frames == 0)
                return PES_EXPR;
            expr_frame * fr = static_cast<expr_frame*>(m_stack.top());
            switch (fr->m_kind) {
            case EF_LET:
                return static_cast<let_frame*>(fr)->m_in_decls ? PES_DECL : PES_EXPR;
            case EF_ATTR_EXPR:
                return consume_attributes(static_cast<attr_expr_frame*>(fr));
            default:
                return PES_EXPR;
            }
        }

        void parse_numeral(bool is_int) {
            SASSERT(!is_int || curr_is_int());
            SASSERT(is_int || curr_is_float());
            TRACE("parse_numeral", tout << "curr(): " << curr() << ", curr_numeral(): " << curr_numeral() << ", is_int: " << is_int << "\n";);
            expr_stack().push_back(autil().mk_numeral(curr_numeral(), is_int && !m_ctx.numeral_as_real()));
            next();
        }

        void parse_bv_numeral() {
            SASSERT(curr() == scanner::BV_TOKEN);
            expr_stack().push_back(butil().mk_numeral(curr_numeral(), m_scanner.get_bv_size()));
            TRACE("parse_bv_numeral", tout << "new numeral: " << mk_pp(expr_stack().back(), m()) << "\n";);
            next();
        }

        void parse_string_const() {
            SASSERT(curr() == scanner::STRING_TOKEN);
            expr_stack().push_back(sutil().str.mk_string(symbol(m_scanner.get_string())));
            TRACE("smt2parser", tout << "new string: " << mk_pp(expr_stack().back(), m()) << "\n";);
            next();
        }

        void push_pattern_frame() {
            // TODO: It seems the only reliable way to parse patterns is:
            // Parse as an S-Expr, then try to convert it to an useful pattern.
            // If it is not possible, then discard pattern.
            // After this modification, the (PROMOTE) hack below can be removed.
            if (curr_is_lparen()) {
                next();
            }
            else {
                if (!ignore_bad_patterns())
                    throw parser_exception("invalid pattern, '(' expected");
                consume_sexpr();
                expr_stack().push_back(nullptr); // empty pattern
                return;
            }

            if (curr_is_lparen()) {
                // multi-pattern
                void * mem      = m_stack.allocate(sizeof(pattern_frame));
                new (mem) pattern_frame(expr_stack().size());
                m_num_expr_frames++;
            }
            else if (curr_is_rparen()) {
                next();
                expr_stack().push_back(nullptr); // empty pattern
            }
            else {
                // unary pattern
                // HACK: to consume & discard (PROMOTE)-like patterns that were incorrectly introduced in SMT-LIB 2.0
                // when Simplify benchmarks were converted into SMT2 ones.
                if (curr_is_identifier()) {
                    symbol id = curr_id();
                    func_decl * f = nullptr;
                    try {
                        f = m_ctx.find_func_decl(id);
                    }
                    catch (cmd_exception &) {
                    }
                    if (f && f->get_arity() == 0) {
                        if (!ignore_bad_patterns())
                            throw parser_exception("invalid constant pattern");
                        while (!curr_is_rparen())
                            consume_sexpr();
                        next();
                        expr_stack().push_back(nullptr); // empty pattern
                        return; // no frame is created
                    }
                }
                if (!curr_is_lparen() && !curr_is_identifier())
                    throw parser_exception("invalid pattern, '(' or identifier expected");
                push_app_frame();
            }
        }

        void push_let_decl_frame() {
            check_lparen_next("invalid let declaration, '(' expected");
            check_identifier("invalid let declaration, symbol expected");
            symbol_stack().push_back(curr_id());
            next();
            void * mem      = m_stack.allocate(sizeof(let_decl_frame));
            new (mem) let_decl_frame();
            m_num_expr_frames++;
        }

        unsigned parse_sorted_vars() {
            unsigned num = 0;
            unsigned sym_spos = symbol_stack().size();
            unsigned sort_spos = sort_stack().size();
            TRACE("parse_sorted_vars", tout << "[before] symbol_stack().size(): " << symbol_stack().size() << "\n";);
            check_lparen_next("invalid list of sorted variables, '(' expected");
            m_env.begin_scope();
            while (!curr_is_rparen()) {
                check_lparen_next("invalid sorted variable, '(' expected");
                check_identifier("invalid sorted variable, symbol expected");
                symbol_stack().push_back(curr_id());
                TRACE("parse_sorted_vars", tout << "push_back curr_id(): " << curr_id() << "\n";);
                next();
                parse_sort("invalid sorted variables");
                check_rparen_next("invalid sorted variable, ')' expected");
                num++;
            }
            next();
            TRACE("parse_sorted_vars", tout << "[after] symbol_stack().size(): " << symbol_stack().size() << "\n";);
            symbol const * sym_it  = symbol_stack().c_ptr() + sym_spos;
            sort * const * sort_it = sort_stack().c_ptr() + sort_spos;
            m_num_bindings += num;
            unsigned i = num;
            while (i > 0) {
                --i;
                var * v = m().mk_var(i, *sort_it);
                expr_stack().push_back(v); // prevent v from being deleted
                TRACE("parse_sorted_vars", tout << "registering " << *sym_it << " -> " << mk_pp(v, m()) << ", num: " << num << ", i: " << i << "\n";);
                m_env.insert(*sym_it, local(v, m_num_bindings));
                SASSERT(m_env.contains(*sym_it));
                ++sort_it;
                ++sym_it;
            }
            return num;
        }

        void push_let_frame() {
            next();
            check_lparen_next("invalid let declaration, '(' expected");
            void * mem = m_stack.allocate(sizeof(let_frame));
            new (mem) let_frame(symbol_stack().size(), expr_stack().size());
            m_num_expr_frames++;
        }

        void push_bang_frame(expr_frame * curr) {
            TRACE("consume_attributes", tout << "begin bang, expr_stack.size(): " << expr_stack().size() << "\n";);
            next();
            void * mem = m_stack.allocate(sizeof(attr_expr_frame));
            new (mem) attr_expr_frame(curr, symbol_stack().size(), expr_stack().size());
            m_num_expr_frames++;
        }

        void push_quant_frame(quantifier_kind k) {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id_is_forall() || curr_id_is_exists() || curr_id_is_lambda());
            SASSERT((k == forall_k) == curr_id_is_forall());
            SASSERT((k == exists_k) == curr_id_is_exists());
            SASSERT((k == lambda_k) == curr_id_is_lambda());
            next();
            void * mem      = m_stack.allocate(sizeof(quant_frame));
            new (mem) quant_frame(k, pattern_stack().size(), nopattern_stack().size(), symbol_stack().size(),
                                  sort_stack().size(), expr_stack().size());
            m_num_expr_frames++;
            unsigned num_vars = parse_sorted_vars();
            if (num_vars == 0)
                throw parser_exception("invalid quantifier, list of sorted variables is empty");
        }

        /**
         * SMT-LIB 2.6 pattern matches are of the form
         *
         *   (match t ((p1 t1) ... (pm+1 tm+1)))         
         *
         * precursor form is
         *
         *   (match t (case p1 t1) (case p2 t2) ... )
         *
         */
        void push_match_frame() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_match);
            next();
            void * mem = m_stack.allocate(sizeof(match_frame));
            new (mem) match_frame();
            unsigned num_frames = m_num_expr_frames;

            parse_expr();
            expr_ref t(expr_stack().back(), m());
            expr_stack().pop_back();
            expr_ref_vector patterns(m()), cases(m());
            sort* srt = m().get_sort(t);

            check_lparen_next("pattern bindings should be enclosed in a parenthesis");
            if (curr_id_is_case()) {
                while (curr_id_is_case()) {
                    next();
                    m_env.begin_scope();
                    unsigned num_bindings = m_num_bindings;
                    parse_match_pattern(srt);  
                    patterns.push_back(expr_stack().back());
                    expr_stack().pop_back();
                    parse_expr();
                    cases.push_back(expr_stack().back());
                    expr_stack().pop_back();
                    m_num_bindings = num_bindings;
                    m_env.end_scope();
                    check_rparen_next("invalid pattern binding, ')' expected");                    
                    if (curr_is_lparen()) {
                        next();
                    }
                }               
            }
            else {
                while (!curr_is_rparen()) {
                    m_env.begin_scope();
                    check_lparen_next("invalid pattern binding, '(' expected");                    
                    unsigned num_bindings = m_num_bindings;
                    parse_match_pattern(srt);  
                    patterns.push_back(expr_stack().back());
                    expr_stack().pop_back();
                    parse_expr();
                    cases.push_back(expr_stack().back());
                    expr_stack().pop_back();
                    m_num_bindings = num_bindings;
                    m_env.end_scope();
                    check_rparen_next("invalid pattern binding, ')' expected");
                }
                next();
            }
            m_num_expr_frames = num_frames + 1;
            expr_stack().push_back(compile_patterns(t, patterns, cases));
        }

        void pop_match_frame(match_frame* fr) {
            m_stack.deallocate(fr);
            m_num_expr_frames--;
        }

        expr_ref compile_patterns(expr* t, expr_ref_vector const& patterns, expr_ref_vector const& cases) {
            expr_ref result(m());
            var_subst sub(m(), false);
            TRACE("parse_expr", tout << "term\n" << expr_ref(t, m()) << "\npatterns\n" << patterns << "\ncases\n" << cases << "\n";);
            check_patterns(patterns, m().get_sort(t));
            for (unsigned i = patterns.size(); i > 0; ) {
                --i;
                expr_ref_vector subst(m());
                expr_ref cond = bind_match(t, patterns[i], subst);
                expr_ref new_case(m());
                if (subst.empty()) {
                    new_case = cases[i];
                }
                else {
                    new_case = sub(cases[i], subst.size(), subst.c_ptr());
                    inv_var_shifter inv(m());
                    inv(new_case, subst.size(), new_case);
                }
                if (result) {
                    result = m().mk_ite(cond, new_case, result);
                }
                else {
                    // pattern match binding is ignored.
                    result = new_case;
                }
            }
            TRACE("parse_expr", tout << result << "\n";);
            return result;
        }

        void check_patterns(expr_ref_vector const& patterns, sort* s) {
            if (!dtutil().is_datatype(s)) 
                throw parser_exception("pattern matching is only supported for algebraic datatypes");
            ptr_vector<func_decl> const& cons = *dtutil().get_datatype_constructors(s);
            for (expr * arg : patterns) if (is_var(arg)) return;
            if (patterns.size() < cons.size()) 
                throw parser_exception("non-exhaustive pattern match");
            ast_fast_mark1 marked;
            for (expr * arg : patterns) 
                marked.mark(to_app(arg)->get_decl(), true);
            for (func_decl * f : cons) 
                if (!marked.is_marked(f)) 
                    throw parser_exception("a constructor is missing from pattern match");        
        }

        // compute match condition and substitution
        // t is shifted by size of subst.
        expr_ref bind_match(expr* t, expr* pattern, expr_ref_vector& subst) {
            if (m().get_sort(t) != m().get_sort(pattern)) {
                std::ostringstream str;
                str << "sorts of pattern " << expr_ref(pattern, m()) << " and term " 
                    << expr_ref(t, m()) << " are not aligned";
                throw parser_exception(str.str());
            }
            expr_ref tsh(m());
            if (is_var(pattern)) {
                shifter()(t, 1, tsh);
                subst.push_back(tsh);
                return expr_ref(m().mk_true(), m());
            }
            else {
                SASSERT(is_app(pattern));
                func_decl * f = to_app(pattern)->get_decl();
                func_decl * r = dtutil().get_constructor_is(f);
                ptr_vector<func_decl> const * acc = dtutil().get_constructor_accessors(f);
                shifter()(t, acc->size(), tsh);
                for (func_decl* a : *acc) {
                    subst.push_back(m().mk_app(a, tsh));
                }
                return expr_ref(m().mk_app(r, t), m());
            }
        }

        /**
         * parse a match pattern
         * (C x1 .... xn)
         * C
         * _
         * x
         */
        
        void parse_match_pattern(sort * srt) {
            symbol C;
            svector<symbol> vars;
            expr_ref_vector args(m());
            
            if (curr_is_identifier()) {
                C = curr_id();
            }
            else if (curr_is_lparen()) {
                next();
                C = check_identifier_next("constructor symbol expected");
                while (!curr_is_rparen()) {
                    symbol v(check_identifier_next("variable symbol expected"));
                    if (v != m_underscore && vars.contains(v)) {
                        throw parser_exception("unexpected repeated variable in pattern expression");
                    } 
                    vars.push_back(v);
                }                
            }
            else {
                throw parser_exception("expecting a constructor, _, variable or constructor application");
            }
            next();
            
            // now have C, vars
            // look up constructor C, 
            // create bound variables based on constructor type.
            // store expression in expr_stack().
            // ensure that bound variables are adjusted to vars
            
            func_decl* f = nullptr;
            try {
                f = m_ctx.find_func_decl(C, 0, nullptr, vars.size(), nullptr, srt);
            }
            catch (cmd_exception &) {
                if (!args.empty()) {
                    throw;
                }
            }
            
            if (!f && !args.empty()) {
                throw parser_exception("expecting a constructor that has been declared");
            }
            if (!f) {
                m_num_bindings++;
                var * v  = m().mk_var(0, srt);
                if (C != m_underscore) {
                    m_env.insert(C, local(v, m_num_bindings));
                }
                expr_stack().push_back(v);
                return;
            }
            if (!dtutil().is_constructor(f)) {
                throw parser_exception("expecting a constructor");
            }
            if (f->get_arity() != vars.size()) {
                throw parser_exception("mismatching number of variables supplied to constructor");
            }
            m_num_bindings += vars.size();
            for (unsigned i = 0; i < vars.size(); ++i) {
                var * v = m().mk_var(i, f->get_domain(i));
                args.push_back(v);
                if (vars[i] != m_underscore) {
                    m_env.insert(vars[i], local(v, m_num_bindings));
                }
            }
            expr_stack().push_back(m().mk_app(f, args.size(), args.c_ptr()));
        }

        symbol parse_indexed_identifier_core() {
            check_underscore_next("invalid indexed identifier, '_' expected");
            check_identifier("invalid indexed identifier, symbol expected");
            symbol r = curr_id();
            next();
            while (!curr_is_rparen()) {
                if (curr_is_int()) {
                    if (!curr_numeral().is_unsigned()) {
                        m_param_stack.push_back(parameter(curr_numeral()));                       
                    }
                    else {
                        m_param_stack.push_back(parameter(curr_unsigned()));
                    }
                    next();
                }
                else if (curr_is_float()) {
                    m_param_stack.push_back(parameter(curr_numeral()));
                    next();
                }
                else if (curr_is_keyword()) {
                    m_param_stack.push_back(parameter(curr_id()));
                    next();
                }
                else if (curr_is_identifier() || curr_is_lparen()) {
                    m_param_stack.push_back(parameter(parse_func_decl_ref()));
                }
                else {
                    throw parser_exception("invalid indexed identifier, integer, identifier or '(' expected");
                }
            }
            next();
            return r;
        }

        symbol parse_indexed_identifier() {
            if (curr_is_identifier()) {
                symbol r = curr_id();
                next();
                return r;
            }
            check_lparen_next("invalid (indexed) identifier, '(_' or symbol expected");
            return parse_indexed_identifier_core();
        }

        // parse:
        //    'as' <identifier> <sort> ')'
        //    '_'  <identifier> <num>+ ')'
        //    'as' <identifier> '(' '_' <identifier> (<num>|<func-decl-ref>)+ ')' <sort> ')'
        symbol parse_qualified_identifier_core(bool & has_as) {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id_is_underscore() || curr_id_is_as());
            if (curr_id_is_underscore()) {
                has_as = false;
                return parse_indexed_identifier_core();
            }
            else {
                SASSERT(curr_id_is_as());
                has_as   = true;
                next();
                symbol r = parse_indexed_identifier();
                parse_sort("Invalid qualified identifier");
                check_rparen_next("invalid qualified identifier, ')' expected");
                return r;
            }
        }

        // parse:
        //    <identifier>
        //    '(' 'as' <identifier> <sort> ')'
        //    '(' '_'  <identifier> <num>+ ')'
        //    '(' 'as' <identifier '(' '_' <identifier> (<num>|<func-decl-ref>)+ ')' <sort> ')'
        symbol parse_qualified_identifier(bool & has_as) {
            SASSERT(curr_is_lparen() || curr_is_identifier());
            if (curr_is_identifier()) {
                has_as   = false;
                symbol r = curr_id();
                next();
                return r;
            }
            SASSERT(curr_is_lparen());
            next();
            if (!curr_is_identifier() || (!curr_id_is_underscore() && !curr_id_is_as()))
                throw parser_exception("invalid qualified/indexed identifier, '_' or 'as' expected");
            return parse_qualified_identifier_core(has_as);
        }

        void unknown_var_const_name(symbol id) {
            std::string msg = "unknown constant/variable '";
            msg += id.str() + "'";
            throw parser_exception(std::move(msg));
        }

        rational m_last_bv_numeral; // for bv, bvbin, bvhex

        // return true if *s == [0-9]+
        bool is_bv_decimal(char const * s) {
            TRACE("is_bv_num", tout << "is_bv_decimal: " << s << "\n";);
            SASSERT('0' <= *s && *s <= '9');
            rational & n = m_last_bv_numeral;
            n = rational(*s - '0');
            ++s;
            while ('0' <= *s && *s <= '9') {
                n *= rational(10);
                n += rational(*s - '0');
                ++s;
            }
            if (*s != 0)
                return false;
            return true;
        }

        // return true if *s == bin[0-1]+
        bool is_bv_binary(char const * s) {
            SASSERT(*s == 'b');
            ++s;
            if (*s != 'i') return false;
            ++s;
            if (*s != 'n') return false;
            ++s;
            rational & n = m_last_bv_numeral;
            unsigned i = 0;
            n = rational(0);
            while (*s == '0' || *s == '1') {
                n *= rational(2);
                n += rational(*s - '0');
                ++s;
                ++i;
            }
            if (*s != 0 || i == 0)
                return false;
            return true;
        }

        // return true if *s == hex[0-9,a-f,A-F]+
        bool is_bv_hex(char const * s) {
            SASSERT(*s == 'h');
            ++s;
            if (*s != 'e') return false;
            ++s;
            if (*s != 'x') return false;
            ++s;
            rational & n = m_last_bv_numeral;
            unsigned i = 0;
            n = rational(0);
            while (true) {
                if ('0' <= *s && *s <= '9') {
                    n *= rational(16);
                    n += rational(*s - '0');
                }
                else if ('a' <= *s && *s <= 'f') {
                    n *= rational(16);
                    n += rational(10 + (*s - 'a'));
                }
                else if ('A' <= *s && *s <= 'F') {
                    n *= rational(16);
                    n += rational(10 + (*s - 'A'));
                }
                else if (*s == 0) {
                    return i > 0;
                }
                else {
                    return false;
                }
                ++s;
                ++i;
            }
        }

        // Return true if
        //    n == bv[0-9]+  OR
        //    n == bvhex[0-9,a-f,A-F]+ OR
        //    n == bvbin[0-1]+
        // It store the bit-vector value in m_last_bv_numeral
        bool is_bv_num(symbol const & n) {
            char const * s = n.bare_str();
            if (*s != 'b') return false;
            s++;
            if (*s != 'v') return false;
            s++;
            if ('0' <= *s && *s <= '9')
                return is_bv_decimal(s);
            else if (*s == 'b')
                return is_bv_binary(s);
            else if (*s == 'h')
                return is_bv_hex(s);
            else
                return false;
        }

        void push_local(local const & l) {
            if (is_ground(l.m_term) || l.m_level == m_num_bindings) {
                expr_stack().push_back(l.m_term);
            }
            else {
                SASSERT(l.m_level <= m_num_bindings);
                expr_ref new_term(m());
                shifter()(l.m_term, m_num_bindings - l.m_level, new_term);
                expr_stack().push_back(new_term);
            }
        }

        // parse <identifier> as expression
        void parse_expr_name() {
            SASSERT(curr_is_identifier());
            symbol n = curr_id();
            local l;
            if (m_env.find(n, l)) {
                push_local(l);
            }
            else {
                expr_ref t_ref(m());
                m_ctx.mk_const(n, t_ref);
                expr_stack().push_back(t_ref.get());
            }
            next();
        }

        // if has_as == true, then the sort of t must be equal to sort_stack().pop_back()
        // if that is the case, pop the top of sort_stack()
        void check_qualifier(expr * t, bool has_as) {
            if (has_as) {
                sort * s = sort_stack().back();
                if (s != m().get_sort(t))
                    throw parser_exception("invalid qualified identifier, sort mismatch");
                sort_stack().pop_back();
            }
        }

        // parse
        //   'as' <identifier> <sort> ')'
        //   '_' <identifier> <num>+ ')'
        //   'as' '(' <identifier> (<num>|<func-decl-ref>)+ ')' <sort> ')'
        void parse_qualified_name() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id_is_as() || curr_id_is_underscore());
            TRACE("parse_qualified_name", tout << "parse_qualified_name() curr_id: " << curr_id() << "\n";);
            unsigned param_spos = m_param_stack.size();
            bool has_as;
            symbol r = parse_qualified_identifier_core(has_as);
            TRACE("parse_qualified_name", tout << "parse_qualified_name() r: " << r << "\n";);
            expr * t;
            local l;
            if (m_env.find(r, l)) {
                push_local(l);
                t = expr_stack().back();
                check_qualifier(t, has_as);
                if (m_param_stack.size() != param_spos)
                    throw parser_exception("invalid indexed identifier, symbol is a local declaration");
                return;
            }
            unsigned num_indices = m_param_stack.size() - param_spos;
            if (is_bv_num(r)) {
                if (num_indices != 1 || !m_param_stack.back().is_int())
                    throw parser_exception("invalid bit-vector constant, index expected");
                unsigned bv_size = m_param_stack.back().get_int();
                m_param_stack.pop_back();
                t = butil().mk_numeral(m_last_bv_numeral, bv_size);
                expr_stack().push_back(t);
                check_qualifier(t, has_as);
                return;
            }
            expr_ref t_ref(m());
            m_ctx.mk_app(r, 0, nullptr, num_indices, m_param_stack.c_ptr() + param_spos, has_as ? sort_stack().back() : nullptr, t_ref);
            m_param_stack.shrink(param_spos);
            expr_stack().push_back(t_ref.get());
            if (has_as) {
                check_qualifier(t_ref.get(), has_as);
            }
        }

        void parse_root_obj() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id_is_root_obj());
            next();
            parse_sexpr();
            sexpr * p = sexpr_stack().back();
            check_int("invalid root-obj, (unsigned) integer expected");
            rational idx = curr_numeral();
            if (!idx.is_unsigned())
                throw parser_exception("invalid root-obj, index must fit in an unsigned machine integer");
            unsigned u_idx = idx.get_unsigned();
            if (u_idx == 0)
                throw parser_exception("invalid root-obj, index must be >= 1");
            next();
            check_rparen_next("invalid root-obj, ')' expected");
            expr_stack().push_back(autil().mk_numeral(p, u_idx));
            sexpr_stack().pop_back();
        }

        void push_app_frame() {
            SASSERT(curr_is_lparen() || curr_is_identifier());
            unsigned param_spos  = m_param_stack.size();
            unsigned expr_spos  = expr_stack().size();
            bool     has_as;
            symbol   f = parse_qualified_identifier(has_as);
            void * mem      = m_stack.allocate(sizeof(quant_frame));
            new (mem) app_frame(f, expr_spos, param_spos, has_as);
            m_num_expr_frames++;
        }

        void push_expr_frame(expr_frame * curr) {
            SASSERT(curr_is_lparen());
            next();
            TRACE("push_expr_frame", tout << "push_expr_frame(), curr(): " << m_curr << "\n";);
            if (curr_is_identifier()) {
                TRACE("push_expr_frame", tout << "push_expr_frame(), curr_id(): " << curr_id() << "\n";);
                if (curr_id_is_let()) {
                    push_let_frame();
                }
                else if (curr_id_is_forall()) {
                    push_quant_frame(forall_k);
                }
                else if (curr_id_is_exists()) {
                    push_quant_frame(exists_k);
                }
                else if (curr_id_is_lambda()) {
                    push_quant_frame(lambda_k);
                }
                else if (curr_id_is_bang()) {
                    push_bang_frame(curr);
                }
                else if (curr_id_is_as() || curr_id_is_underscore()) {
                    parse_qualified_name();
                }
                else if (curr_id_is_root_obj()) {
                    parse_root_obj();
                }
                else if (curr_id_is_match()) {
                    push_match_frame();
                }
                else {
                    push_app_frame();
                }
            }
            else if (curr_is_lparen()) {
                push_app_frame();
            }
            else {
                throw parser_exception("invalid expression, '(' or symbol expected");
            }
        }

        void pop_app_frame(app_frame * fr) {
            SASSERT(expr_stack().size() >= fr->m_expr_spos);
            SASSERT(m_param_stack.size() >= fr->m_param_spos);
            if (expr_stack().size() == fr->m_expr_spos)
                throw parser_exception("invalid function application, arguments missing");
            unsigned num_args    = expr_stack().size() - fr->m_expr_spos;
            unsigned num_indices = m_param_stack.size() - fr->m_param_spos;
            expr_ref t_ref(m());
            local l;
            if (m_env.find(fr->m_f, l)) {
                push_local(l);
                t_ref = expr_stack().back();
                for (unsigned i = 0; i < num_args; ++i) {
                    expr* arg = expr_stack().get(fr->m_expr_spos + i);
                    expr* args[2] = { t_ref.get(), arg };
                    m_ctx.mk_app(symbol("select"), 
                                 2, 
                                 args,
                                 0,
                                 nullptr,
                                 nullptr,
                                 t_ref);
                }
            }
            else {
                m_ctx.mk_app(fr->m_f,
                             num_args,
                             expr_stack().c_ptr() + fr->m_expr_spos,
                             num_indices,
                             m_param_stack.c_ptr() + fr->m_param_spos,
                             fr->m_as_sort ? sort_stack().back() : nullptr,
                             t_ref);
            }
            expr_stack().shrink(fr->m_expr_spos);
            m_param_stack.shrink(fr->m_param_spos);
            if (fr->m_as_sort)
                sort_stack().pop_back();
            TRACE("pop_app_frame", tout << "new term: " << mk_pp(t_ref, m()) << "\n";);
            expr_stack().push_back(t_ref.get());
            m_stack.deallocate(fr);
            m_num_expr_frames--;
        }

        void pop_let_frame(let_frame * fr) {
            if (fr->m_in_decls) {
                m_env.begin_scope();
                fr->m_in_decls = false;
                SASSERT(symbol_stack().size() >= fr->m_sym_spos);
                SASSERT(expr_stack().size() >= fr->m_expr_spos);
                if (symbol_stack().size() - fr->m_sym_spos != expr_stack().size() - fr->m_expr_spos) {
                    throw parser_exception("malformed let expression");
                }
                unsigned num_decls = expr_stack().size() - fr->m_expr_spos;
                symbol * sym_it   = symbol_stack().c_ptr() + fr->m_sym_spos;
                expr ** expr_it   = expr_stack().c_ptr() + fr->m_expr_spos;
                expr ** expr_end  = expr_it + num_decls;
                for (; expr_it != expr_end; ++expr_it, ++sym_it) {
                    TRACE("let_frame", tout << "declaring: " << *sym_it << " " << mk_pp(*expr_it, m()) << "\n";);
                    m_env.insert(*sym_it, local(*expr_it, m_num_bindings));
                }
            }
            else {
                // the resultant expression is on the top of the stack
                TRACE("let_frame", tout << "let result expr: " << mk_pp(expr_stack().back(), m()) << "\n";);
                expr_ref r(m());
                if (expr_stack().empty())
                    throw parser_exception("invalid let expression");
                r = expr_stack().back();
                expr_stack().pop_back();
                // remove local declarations from the stack
                symbol_stack().shrink(fr->m_sym_spos);
                expr_stack().shrink(fr->m_expr_spos);
                m_env.end_scope();
                // put result back on the stack
                expr_stack().push_back(r.get());
                m_stack.deallocate(fr);
                m_num_expr_frames--;
            }
        }

        void pop_quant_frame(quant_frame * fr) {
            SASSERT(pattern_stack().size() >= fr->m_pat_spos);
            SASSERT(nopattern_stack().size() >= fr->m_nopat_spos);
            SASSERT(symbol_stack().size() >= fr->m_sym_spos);
            SASSERT(sort_stack().size() >= fr->m_sort_spos);
            SASSERT(symbol_stack().size() - fr->m_sym_spos == sort_stack().size() - fr->m_sort_spos);
            SASSERT(expr_stack().size() >= fr->m_expr_spos);
            unsigned num_decls  = sort_stack().size() - fr->m_sort_spos;
            if (expr_stack().size() - fr->m_expr_spos != num_decls /* variables */ + 1 /* result */)
                //throw parser_exception("invalid quantified expression, syntax error: (forall|exists|lambda ((<symbol> <sort>)*) <expr>) expected");
                throw parser_exception("invalid quantified expression, syntax error: (forall|exists ((<symbol> <sort>)*) <expr>) expected");
            unsigned begin_pats = fr->m_pat_spos;
            unsigned end_pats   = pattern_stack().size();
            unsigned j = begin_pats;
            for (unsigned i = begin_pats; i < end_pats; i++) {
                expr * pat = pattern_stack().get(i);
                if (!pat_validator()(num_decls, pat, m_scanner.get_line(), m_scanner.get_pos())) {
                    if (!ignore_bad_patterns())
                        throw parser_exception("invalid pattern");
                    continue;
                }
                pattern_stack().set(j, pat);
                j++;
            }
            end_pats = j;
            pattern_stack().shrink(end_pats);
            unsigned num_pats   = end_pats - begin_pats;
            unsigned num_nopats = nopattern_stack().size() - fr->m_nopat_spos;
            TRACE("parse_quantifier", tout << "weight: " << fr->m_weight << "\n";);
            TRACE("skid", tout << "fr->m_skid: " << fr->m_skid << "\n";);
            TRACE("parse_quantifier", tout << "body:\n" << mk_pp(expr_stack().back(), m()) << "\n";);
            if (fr->m_qid == symbol::null)
                fr->m_qid = symbol(m_scanner.get_line());
            if (fr->m_kind != lambda_k && !m().is_bool(expr_stack().back()))
                throw parser_exception("quantifier body must be a Boolean expression");
            quantifier* new_q = m().mk_quantifier(fr->m_kind,
                                      num_decls,
                                      sort_stack().c_ptr() + fr->m_sort_spos,
                                      symbol_stack().c_ptr() + fr->m_sym_spos,
                                      expr_stack().back(),
                                      fr->m_weight,
                                      fr->m_qid,
                                      fr->m_skid,
                                      num_pats, pattern_stack().c_ptr() + fr->m_pat_spos,
                                      num_nopats, nopattern_stack().c_ptr() + fr->m_nopat_spos
                                      );
            TRACE("mk_quantifier", tout << "id: " << new_q->get_id() << "\n" << mk_ismt2_pp(new_q, m()) << "\n";);
            TRACE("skid", tout << "new_q->skid: " << new_q->get_skid() << "\n";);
            expr_stack().shrink(fr->m_expr_spos);
            pattern_stack().shrink(fr->m_pat_spos);
            nopattern_stack().shrink(fr->m_nopat_spos);
            symbol_stack().shrink(fr->m_sym_spos);
            sort_stack().shrink(fr->m_sort_spos);
            m_env.end_scope();
            SASSERT(num_decls <= m_num_bindings);
            m_num_bindings -= num_decls;

            expr_stack().push_back(new_q);
            m_stack.deallocate(fr);
            m_num_expr_frames--;
        }

        void pop_attr_expr_frame(attr_expr_frame * fr) {
            process_last_symbol(fr);
            TRACE("consume_attributes", tout << "pop_attr_expr_frame, expr_stack.size(): " << expr_stack().size() << "\n";);
            // the resultant expression is already on the top of the stack.
            SASSERT(expr_stack().size() == fr->m_expr_spos + 1);
            m_stack.deallocate(fr);
            m_num_expr_frames--;
        }

        void pop_pattern_frame(pattern_frame * fr) {
            SASSERT(expr_stack().size() >= fr->m_expr_spos);
            if (expr_stack().size() == fr->m_expr_spos) {
                if (!ignore_bad_patterns())
                    throw parser_exception("invalid empty pattern");
                // ignoring empty pattern
                expr_stack().shrink(fr->m_expr_spos);
            }
            else {
                unsigned num   = expr_stack().size() - fr->m_expr_spos;
                expr * new_pat = m().mk_pattern(num, reinterpret_cast<app**>(expr_stack().c_ptr() + fr->m_expr_spos));
                expr_stack().shrink(fr->m_expr_spos);
                expr_stack().push_back(new_pat);
            }
            m_stack.deallocate(fr);
            m_num_expr_frames--;
        }

        void pop_expr_frame() {
            SASSERT(curr_is_rparen());
            expr_frame * fr = static_cast<expr_frame*>(m_stack.top());
            switch (fr->m_kind) {
            case EF_APP:
                pop_app_frame(static_cast<app_frame*>(fr));
                break;
            case EF_LET:
                pop_let_frame(static_cast<let_frame*>(fr));
                break;
            case EF_LET_DECL:
                m_stack.deallocate(static_cast<let_decl_frame*>(fr));
                m_num_expr_frames--;
                break;
            case EF_MATCH:
                pop_match_frame(static_cast<match_frame*>(fr));
                break;
            case EF_QUANT:
                pop_quant_frame(static_cast<quant_frame*>(fr));
                break;
            case EF_ATTR_EXPR:
                pop_attr_expr_frame(static_cast<attr_expr_frame*>(fr));
                break;
            case EF_PATTERN:
                pop_pattern_frame(static_cast<pattern_frame*>(fr));
                break;
            default:
                UNREACHABLE();
            }
            SASSERT(curr_is_rparen());
            next(); // consume ')'
        }

        void parse_expr() {
            m_num_expr_frames = 0;
            do {
                TRACE("parse_expr", tout << "curr(): " << curr() << ", m_num_expr_frames: " << m_num_expr_frames
                      << ", expr_stack().size(): " << expr_stack().size() << "\n";);
                if (curr_is_rparen()) {
                    if (m_num_expr_frames == 0)
                        throw parser_exception("invalid expression, unexpected ')'");
                    pop_expr_frame();
                }
                else {
                    pe_state st = parse_expr_state();
                    TRACE("consume_attributes", tout << "parse_expr_state: " << st << ", expr_stack.size(): " << expr_stack().size() << "\n";);
                    switch (st) {
                    case PES_EXPR:
                        switch (curr()) {
                        case scanner::SYMBOL_TOKEN:
                            parse_expr_name();
                            break;
                        case scanner::INT_TOKEN:
                            parse_numeral(true);
                            break;
                        case scanner::FLOAT_TOKEN:
                            parse_numeral(false);
                            break;
                        case scanner::BV_TOKEN:
                            parse_bv_numeral();
                            break;
                        case scanner::LEFT_PAREN:
                            push_expr_frame(m_num_expr_frames == 0 ? nullptr : static_cast<expr_frame*>(m_stack.top()));
                            break;
                        case scanner::KEYWORD_TOKEN:
                            throw parser_exception("invalid expression, unexpected keyword");
                        case scanner::STRING_TOKEN:
                            parse_string_const();
                            break;
                        default:
                            throw parser_exception("invalid expression, unexpected input");
                        }
                        break;
                    case PES_DECL:
                        push_let_decl_frame();
                        break;
                    case PES_PATTERN:
                        push_pattern_frame();
                        break;
                    case PES_CONTINUE:
                        // do nothing
                        break;
                    default:
                        UNREACHABLE();
                        break;
                    }
                }
            }
            while (m_num_expr_frames > 0 );
            SASSERT(!expr_stack().empty());
        }

        unsigned parse_exprs() {
            unsigned sz = 0;
            check_lparen_next("invalid list of terms, '(' expected");
            while (!curr_is_rparen()) {
                parse_expr();
                sz++;
            }
            next();
            return sz;
        }

        void parse_sort_decl_params() {
            m_sort_id2param_idx.reset();
            check_lparen_next("invalid sort declaration, parameters missing");
            unsigned i = 0;
            while (!curr_is_rparen()) {
                check_identifier("invalid sort parameter, symbol or ')' expected");
                m_sort_id2param_idx.insert(curr_id(), i);
                i++;
                next();
            }
            next();            
        }

        bool parse_sort_decl_or_params() {
            m_sort_id2param_idx.reset();
            m_dt_name2arity.reset();
            m_dt_name2idx.reset();
            m_dt_names.reset();
            check_lparen_next("invalid sort declaration, parameters missing");
            unsigned i = 0;
            bool first = true;
            bool is_decl = false;
            while (!curr_is_rparen()) {
                if (first) {
                    is_decl = curr_is_lparen();
                    first = false;                    
                }
                if (is_decl) {
                    check_lparen_next("invalid sort declaration, '(' expected");
                    symbol dt_name = check_identifier_next("invalid sort name, identified expected");
                    check_int("invalid sort declaration, arity expected");
                    unsigned u = curr_unsigned();
                    next();
                    m_dt_name2idx.insert(dt_name, i);
                    m_dt_name2arity.insert(dt_name, u);
                    m_dt_names.push_back(dt_name);
                    psort_decl * decl = pm().mk_psort_dt_decl(u, dt_name);
                    m_ctx.insert(decl);
                    check_rparen("invalid sort declaration, ')' expected");
                }
                else {
                    check_identifier("invalid sort parameter, symbol or ')' expected");
                    m_sort_id2param_idx.insert(curr_id(), i);
                }
                i++;
                next();
            }
            next(); 
            return is_decl;
        }

        void parse_declare_sort() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_declare_sort);
            next();

            check_identifier("invalid sort declaration, symbol expected");
            symbol id = curr_id();
            if (m_ctx.find_psort_decl(id) != nullptr)
                throw parser_exception("invalid sort declaration, sort already declared/defined");
            next();
            if (curr_is_rparen()) {
                psort_decl * decl = pm().mk_psort_user_decl(0, id, nullptr);
                m_ctx.insert(decl);
            }
            else {
                check_int("invalid sort declaration, arity (<numeral>) or ')' expected");
                unsigned u = curr_unsigned();
                psort_decl * decl = pm().mk_psort_user_decl(u, id, nullptr);
                m_ctx.insert(decl);
                next();
                check_rparen("invalid sort declaration, ')' expected");
            }
            m_ctx.print_success();
            next();
        }

        void parse_define_sort() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_define_sort);
            next();
            check_identifier("invalid sort definition, symbol expected");
            symbol id = curr_id();
            if (m_ctx.find_psort_decl(id) != nullptr)
                throw parser_exception("invalid sort definition, sort already declared/defined");
            next();
            parse_sort_decl_params();

            parse_psort();
            psort_decl * decl = pm().mk_psort_user_decl(m_sort_id2param_idx.size(), id, psort_stack().back());
            psort_stack().pop_back();
            m_ctx.insert(decl);
            check_rparen("invalid sort definition, ')' expected");
            m_ctx.print_success();
            next();
        }

        void parse_define(bool is_fun) {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == (is_fun ? m_define_fun : m_model_add));
            SASSERT(m_num_bindings == 0);
            next();
            check_identifier("invalid function/constant definition, symbol expected");
            symbol id = curr_id();
            next();
            unsigned sym_spos  = symbol_stack().size();
            unsigned sort_spos = sort_stack().size();
            unsigned expr_spos = expr_stack().size();
            unsigned num_vars  = parse_sorted_vars();
            parse_sort("Invalid function definition");
            parse_expr();
            if (m().get_sort(expr_stack().back()) != sort_stack().back())
                throw parser_exception("invalid function/constant definition, sort mismatch");
            sort* const* sorts = sort_stack().c_ptr() + sort_spos;
            expr* t = expr_stack().back();
            if (is_fun) {
                m_ctx.insert(id, num_vars, sorts, t);
            }
            else {
                m_ctx.model_add(id, num_vars, sorts, t);
            }
            check_rparen("invalid function/constant definition, ')' expected");
            // restore stacks & env
            symbol_stack().shrink(sym_spos);
            sort_stack().shrink(sort_spos);
            expr_stack().shrink(expr_spos);
            m_env.end_scope();
            SASSERT(num_vars == m_num_bindings);
            m_num_bindings = 0;
            m_ctx.print_success();
            next();
        }

        void parse_define_fun() {
            parse_define(true);
        }

        void parse_model_add() {
            parse_define(false);
        }

        void parse_model_del() {
            next();
            symbol id = curr_id();
            func_decl * f = m_ctx.find_func_decl(id);
            m_ctx.model_del(f);
            next();
            check_rparen_next("invalid model-del, ')' expected");
            m_ctx.print_success();
        }

        void parse_define_fun_rec() {
            // ( define-fun-rec hfun_defi )
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_define_fun_rec);
            SASSERT(m_num_bindings == 0);
            next();

            expr_ref_vector binding(m());
            svector<symbol> ids;
            func_decl_ref f(m());
            parse_rec_fun_decl(f, binding, ids);
            m_ctx.insert(f);
            parse_rec_fun_body(f, binding, ids);
            check_rparen("invalid function/constant definition, ')' expected");
            m_ctx.print_success();
            next();
        }

        void parse_define_funs_rec() {
            // ( define-funs-rec ( hfun_decin+1 ) ( htermin+1 ) )
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_define_funs_rec);
            SASSERT(m_num_bindings == 0);
            next();
            func_decl_ref_vector decls(m());
            vector<expr_ref_vector> bindings;
            vector<svector<symbol> > ids;
            expr_ref_vector bodies(m());
            parse_rec_fun_decls(decls, bindings, ids);
            for (unsigned i = 0; i < decls.size(); ++i) {
                m_ctx.insert(decls[i].get());
            }
            parse_rec_fun_bodies(decls, bindings, ids);

            check_rparen("invalid function/constant definition, ')' expected");
            m_ctx.print_success();
            next();
        }

        void parse_rec_fun_decls(func_decl_ref_vector& decls, vector<expr_ref_vector>& bindings, vector<svector<symbol> >& ids) {
            check_lparen("invalid recursive function definition, '(' expected");
            next();
            while (!curr_is_rparen()) {
                expr_ref_vector binding(m());
                svector<symbol> id;
                func_decl_ref f(m());

                check_lparen("invalid recursive function definition, '(' expected");
                next();

                parse_rec_fun_decl(f, binding, id);
                decls.push_back(f);
                bindings.push_back(binding);
                ids.push_back(id);

                check_rparen("invalid recursive function definition, ')' expected");
                next();
            }
            next();
        }

        recfun::promise_def parse_rec_fun_decl(func_decl_ref& f, expr_ref_vector& bindings, svector<symbol>& ids) {
            SASSERT(m_num_bindings == 0);
            check_identifier("invalid function/constant definition, symbol expected");
            symbol id = curr_id();
            next();
            unsigned sym_spos  = symbol_stack().size();
            unsigned sort_spos = sort_stack().size();
            unsigned expr_spos = expr_stack().size();
            unsigned num_vars  = parse_sorted_vars();
            SASSERT(num_vars == m_num_bindings);
            parse_sort("Invalid recursive function definition");
            recfun::promise_def pdef = m_ctx.decl_rec_fun(id, num_vars, sort_stack().c_ptr() + sort_spos, sort_stack().back());
            f = pdef.get_def()->get_decl();
            bindings.append(num_vars, expr_stack().c_ptr() + expr_spos);
            ids.append(num_vars, symbol_stack().c_ptr() + sym_spos);
            symbol_stack().shrink(sym_spos);
            sort_stack().shrink(sort_spos);
            expr_stack().shrink(expr_spos);
            m_env.end_scope();
            m_num_bindings = 0;
            return pdef;
        }

        void parse_rec_fun_bodies(func_decl_ref_vector const& decls, vector<expr_ref_vector> const& bindings, vector<svector<symbol> >const & ids) {
            unsigned i = 0;
            check_lparen("invalid recursive function definition, '(' expected");
            next();
            while (!curr_is_rparen() && i < decls.size()) {
                parse_rec_fun_body(decls[i], bindings[i], ids[i]);
                ++i;
            }

            if (i != decls.size()) {
                throw parser_exception("the number of declarations does not match number of supplied definitions");
            }
            check_rparen("invalid recursive function definition, ')' expected");
            next();
        }

        void parse_rec_fun_body(func_decl* f, expr_ref_vector const& bindings, svector<symbol> const& ids) {
            SASSERT(m_num_bindings == 0);
            expr_ref body(m());
            unsigned sym_spos  = symbol_stack().size();
            unsigned num_vars  = bindings.size();
            m_env.begin_scope();
            m_symbol_stack.append(ids.size(), ids.c_ptr());
            m_num_bindings = num_vars;
            for (unsigned i = 0; i < num_vars; ++i) {
                m_env.insert(ids[i], local(bindings[i], num_vars));
            }
            parse_expr();
            body = expr_stack().back();
            expr_stack().pop_back();
            symbol_stack().shrink(sym_spos);
            m_env.end_scope();
            m_num_bindings = 0;
            if (m().get_sort(body) != f->get_range()) {
                std::ostringstream buffer;
                buffer << "invalid function definition, sort mismatch. Expcected "
                       << mk_pp(f->get_range(), m()) << " but function body has sort "
                       << mk_pp(m().get_sort(body), m());
                throw parser_exception(buffer.str());
            }
            m_ctx.insert_rec_fun(f, bindings, ids, body);
        }


        void parse_define_const() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_define_const);
            SASSERT(m_num_bindings == 0);
            next();
            check_identifier("invalid constant definition, symbol expected");
            symbol id = curr_id();
            next();
            parse_sort("Invalid constant definition");
            parse_expr();
            if (m().get_sort(expr_stack().back()) != sort_stack().back())
                throw parser_exception("invalid constant definition, sort mismatch");
            m_ctx.insert(id, 0, nullptr, expr_stack().back());
            check_rparen("invalid constant definition, ')' expected");
            expr_stack().pop_back();
            sort_stack().pop_back();
            m_ctx.print_success();
            next();
        }

        void parse_declare_fun() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_declare_fun);
            next();
            check_identifier("invalid function declaration, symbol expected");
            symbol id = curr_id();
            next();
            unsigned spos = sort_stack().size();
            unsigned num_params = parse_sorts("Parsing function declaration. Expecting sort list '('");
            parse_sort("Invalid function declaration");
            func_decl_ref f(m());
            f = m().mk_func_decl(id, num_params, sort_stack().c_ptr() + spos, sort_stack().back());
            sort_stack().shrink(spos);
            m_ctx.insert(f);
            check_rparen("invalid function declaration, ')' expected");
            m_ctx.print_success();
            next();
        }

        void parse_declare_const() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_declare_const);
            next();
            check_identifier("invalid constant declaration, symbol expected");
            symbol id = curr_id();
            next();
            parse_sort("Invalid constant declaration");
            SASSERT(!sort_stack().empty());
            func_decl_ref c(m());
            c = m().mk_const_decl(id, sort_stack().back());
            TRACE("declare_const", tout << "declaring " << id << " "; pm().display(tout, sort_stack().back()); tout << "\n";);
            SASSERT(c.get() != 0);
            sort_stack().pop_back();
            m_ctx.insert(c);
            check_rparen("invalid constant declaration, ')' expected");
            m_ctx.print_success();
            next();
        }

        unsigned parse_opt_unsigned(unsigned def) {
            unsigned num;
            if (!curr_is_rparen()) {
                check_int("invalid push command, integer expected");
                rational n = curr_numeral();
                if (n.is_neg())
                    throw parser_exception("invalid push command, value is negative.");
                if (!n.is_unsigned())
                    throw parser_exception("invalid push command, value is too big to fit in an unsigned machine integer");
                num = n.get_unsigned();
                next();
            }
            else {
                num = def;
            }
            return num;
        }

        void parse_push() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_push);
            next();
            unsigned num = parse_opt_unsigned(1);
            m_ctx.push(num);
            check_rparen("invalid push command, ')' expected");
            m_ctx.print_success();
            next();
        }

        void parse_pop() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_pop);
            next();
            unsigned num = parse_opt_unsigned(1);
            m_ctx.pop(num);
            check_rparen("invalid pop command, ')' expected");
            m_ctx.print_success();
            next();
            TRACE("after_pop", tout << "expr_stack.size: " << expr_stack().size() << "\n"; m_ctx.dump_assertions(tout););
        }

        std::string m_assert_expr;

        void parse_assert() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_assert);
            m_last_named_expr.first  = symbol::null;
            m_last_named_expr.second = 0;
            if (m_ctx.interactive_mode()) {
                m_scanner.start_caching();
                m_cache_end = 0;
            }
            next();
            parse_expr();
            if (m_ctx.interactive_mode()) {
                m_assert_expr = m_scanner.cached_str(0, m_cache_end);
                m_scanner.stop_caching();
            }
            if (expr_stack().empty()) {
                throw cmd_exception("invalid assert command, expression required as argument");
            }
            expr * f = expr_stack().back();
            if (!m().is_bool(f)) {
                TRACE("smt2parser", tout << expr_ref(f, m()) << "\n";);
                throw cmd_exception("invalid assert command, term is not Boolean");
            }
            if (f == m_last_named_expr.second) {
                m_ctx.assert_expr(m_last_named_expr.first, f);
            }
            else {
                m_ctx.assert_expr(f);
            }
            if (m_ctx.interactive_mode()) {
                m_ctx.push_assert_string(m_assert_expr);
            }
            expr_stack().pop_back();
            check_rparen("invalid assert command, ')' expected");
            m_ctx.print_success();
            next();
        }

        void parse_assumptions() {
            while (!curr_is_rparen()) {
                bool sign;
                expr_ref t_ref(m());
                if (curr_is_lparen()) {
                    next();
                    check_id_next(m_not, "invalid check-sat command, 'not' expected, assumptions must be Boolean literals");
                    check_identifier("invalid check-sat command, literal expected");
                    sign = true;
                }
                else {
                    check_identifier("invalid check-sat command, literal or ')' expected");
                    sign = false;
                }
                symbol n = curr_id();
                next();
                m_ctx.mk_const(n, t_ref);
                if (!m().is_bool(t_ref))
                    throw parser_exception("invalid check-sat command, argument must be a Boolean literal");
                if (sign) {
                    if (!is_uninterp_const(t_ref))
                        throw parser_exception("invalid check-sat command, argument must be a Boolean literal");
                    t_ref = m().mk_not(t_ref.get());
                }
                else {
                    expr * arg;
                    if (!is_uninterp_const(t_ref) && !(m().is_not(t_ref, arg) && is_uninterp_const(arg)))
                        throw parser_exception("invalid check-sat command, argument must be a Boolean literal");
                }
                expr_stack().push_back(t_ref.get());
                if (sign)
                    check_rparen_next("invalid check-sat command, ')' expected");
            }
        }

        void parse_check_sat() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_check_sat);
            next();
            unsigned spos = expr_stack().size();
            parse_assumptions();
            m_ctx.check_sat(expr_stack().size() - spos, expr_stack().c_ptr() + spos);
            next();
            expr_stack().shrink(spos);
        }

        void parse_check_sat_assuming() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_check_sat_assuming);
            next();
            unsigned spos = expr_stack().size();
            check_lparen_next("invalid check-sat-assuming command, '(', expected");
            parse_assumptions();
            check_rparen_next("invalid check-sat-assuming command, ')', expected");
            m_ctx.check_sat(expr_stack().size() - spos, expr_stack().c_ptr() + spos);
            next();
            expr_stack().shrink(spos);
        }

        void parse_get_value() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_get_value);
            next();
            unsigned spos = expr_stack().size();
            unsigned cache_it = 0;

            m_scanner.start_caching();
            m_cache_end = 0;
            m_cached_strings.resize(0);

            check_lparen_next("invalid get-value command, '(' expected");
            while (!curr_is_rparen()) {
                parse_expr();
                if (!is_ground(expr_stack().back()))
                    throw cmd_exception("invalid get-value term, term must be ground and must not contain quantifiers");
                m_cached_strings.push_back(m_scanner.cached_str(cache_it, m_cache_end));
                cache_it = m_cache_end;
            }
            m_scanner.stop_caching();
            if (m_cached_strings.empty())
                throw cmd_exception("invalid get-value command, empty list of terms");
            next();
            unsigned index = 0;
            if (curr_is_keyword() && (curr_id() == ":model-index" || curr_id() == ":model_index")) {
                next();
                check_int("integer index expected to indexed model evaluation");
                index = curr_unsigned();
                next();
            }

            check_rparen("invalid get-value command, ')' expected");
            model_ref md;
            if (!m_ctx.is_model_available(md) || m_ctx.get_check_sat_result() == nullptr)
                throw cmd_exception("model is not available");
            if (index != 0) {
                m_ctx.get_opt()->get_box_model(md, index);
            }
            m_ctx.regular_stream() << "(";
            expr ** expr_it  = expr_stack().c_ptr() + spos;
            expr ** expr_end = expr_it + m_cached_strings.size();
            // md->compress();
            for (unsigned i = 0; expr_it < expr_end; expr_it++, i++) {
                model::scoped_model_completion _scm(md, true);
                expr_ref v = (*md)(*expr_it);
                if (i > 0)
                    m_ctx.regular_stream() << "\n ";
                m_ctx.regular_stream() << "(" << m_cached_strings[i] << " ";
                m_ctx.display(m_ctx.regular_stream(), v);
                m_ctx.regular_stream() << ")";
            }
            m_ctx.regular_stream() << ")" << std::endl;
            expr_stack().shrink(spos);
            next();
        }

        void parse_reset() {
            SASSERT(curr_is_identifier());
            SASSERT(curr_id() == m_reset);
            next();
            check_rparen("invalid reset command, ')' expected");
            m_ctx.reset();
            reset();
            m_ctx.print_success();
            next();
        }

        void parse_option_value() {
            switch (curr()) {
            case scanner::BV_TOKEN:
            case scanner::INT_TOKEN:
            case scanner::FLOAT_TOKEN:
                m_curr_cmd->set_next_arg(m_ctx, m_scanner.get_number());
                next();
                break;
            case scanner::SYMBOL_TOKEN:
                m_curr_cmd->set_next_arg(m_ctx, m_scanner.get_id());
                next();
                break;
            case scanner::STRING_TOKEN:
                m_curr_cmd->set_next_arg(m_ctx, m_scanner.get_string());
                next();
                break;
            default:
                throw parser_exception("invalid option value");
            }
        }

        // A func_decl reference is of the form:
        //      <symbol>
        //    | (<symbol> (<sort>+) sort)
        //    | ((_ <symbol> <num>+) (<sort>+) sort)
        func_decl * parse_func_decl_ref() {
            if (curr_is_identifier()) {
                symbol id = curr_id();
                func_decl * d = m_ctx.find_func_decl(id);
                next();
                return d;
            }
            else {
                check_lparen_next("invalid function declaration reference, symbol or '(' expected");
                symbol id;
                sbuffer<unsigned> indices;
                if (curr_is_identifier()) {
                    id = curr_id();
                    next();
                }
                else {
                    check_lparen_next("invalid function declaration reference, symbol or '(' expected");
                    check_underscore_next("invalid indexed function declaration reference, '_' expected");
                    check_identifier("invalid indexed function declaration reference, symbol expected");
                    id = curr_id();
                    next();
                    while (!curr_is_rparen()) {
                        check_int("invalid indexed function declaration reference, integer or ')' expected");
                        unsigned u = curr_unsigned();
                        indices.push_back(u);
                        next();
                    }
                    if (indices.empty())
                        throw parser_exception("invalid indexed function declaration reference, index expected");
                    next();
                }
                unsigned spos = sort_stack().size();
                parse_sorts("Invalid function name. Expecting sort list starting with '(' to disambiguate function name");
                unsigned domain_size = sort_stack().size() - spos;
                parse_sort("Invalid function name");
                func_decl * d = m_ctx.find_func_decl(id, indices.size(), indices.c_ptr(), domain_size, sort_stack().c_ptr() + spos, sort_stack().back());
                sort_stack().shrink(spos);
                check_rparen_next("invalid function declaration reference, ')' expected");
                return d;
            }
        }

        void parse_func_decl_refs(ptr_buffer<func_decl> & flist) {
            check_lparen_next("invalid list of function declaration references, '(' expected");
            while (!curr_is_rparen()) {
                flist.push_back(parse_func_decl_ref());
            }
            next();
        }

        void parse_next_cmd_arg() {
            SASSERT(m_curr_cmd != 0);
            cmd_arg_kind k = m_curr_cmd->next_arg_kind(m_ctx);
            switch (k) {
            case CPK_UINT: {
                check_int("invalid command argument, unsigned integer expected");
                unsigned u = curr_unsigned();
                m_curr_cmd->set_next_arg(m_ctx, u);
                next();
                break;
            }
            case CPK_BOOL: {
                check_identifier("invalid command argument, true/false expected");
                symbol val = curr_id();
                if (val != "true" && val != "false")
                    throw parser_exception("invalid command argument, true/false expected");
                m_curr_cmd->set_next_arg(m_ctx, val == "true");
                next();
                break;
            }
            case CPK_NUMERAL:
                check_int_or_float("invalid command argument, numeral expected");
                m_curr_cmd->set_next_arg(m_ctx, curr_numeral());
                next();
                break;
            case CPK_DECIMAL:
                check_float("invalid command argument, decimal expected");
                m_curr_cmd->set_next_arg(m_ctx, curr_numeral());
                next();
                break;
            case CPK_STRING:
                check_string("invalid command argument, string expected");
                m_curr_cmd->set_next_arg(m_ctx, m_scanner.get_string());
                next();
                break;
            case CPK_KEYWORD:
                check_keyword("invalid command argument, keyword expected");
                m_curr_cmd->set_next_arg(m_ctx, curr_id());
                next();
                break;
            case CPK_OPTION_VALUE:
                parse_option_value();
                break;
            case CPK_SYMBOL:
                check_identifier("invalid command argument, symbol expected");
                m_curr_cmd->set_next_arg(m_ctx, curr_id());
                next();
                return;
            case CPK_SYMBOL_LIST: {
                unsigned spos = m_symbol_stack.size();
                unsigned num  = parse_symbols();
                m_curr_cmd->set_next_arg(m_ctx, num, m_symbol_stack.c_ptr() + spos);
                break;
            }
            case CPK_SORT:
                parse_sort("invalid command argument, sort expected");
                m_curr_cmd->set_next_arg(m_ctx, sort_stack().back());
                return;
            case CPK_SORT_LIST: {
                unsigned spos = sort_stack().size();
                unsigned num = parse_sorts("expecting sort list starting with '('");
                m_curr_cmd->set_next_arg(m_ctx, num, sort_stack().c_ptr() + spos);
                break;
            }
            case CPK_EXPR:
                parse_expr();
                m_curr_cmd->set_next_arg(m_ctx, expr_stack().back());
                return;
            case CPK_EXPR_LIST: {
                unsigned spos = expr_stack().size();
                unsigned num = parse_exprs();
                m_curr_cmd->set_next_arg(m_ctx, num, expr_stack().c_ptr() + spos);
                break;
            }
            case CPK_FUNC_DECL: {
                func_decl * f = parse_func_decl_ref();
                m_curr_cmd->set_next_arg(m_ctx, f);
                return;
            }
            case CPK_FUNC_DECL_LIST: {
                ptr_buffer<func_decl> flist;
                parse_func_decl_refs(flist);
                m_curr_cmd->set_next_arg(m_ctx, flist.size(), flist.c_ptr());
                return;
            }
            case CPK_SORTED_VAR:
                NOT_IMPLEMENTED_YET();
                break;
            case CPK_SORTED_VAR_LIST:
                NOT_IMPLEMENTED_YET();
                break;
            case CPK_SEXPR:
                parse_sexpr();
                m_curr_cmd->set_next_arg(m_ctx, sexpr_stack().back());
                break;
            case CPK_INVALID:
                throw parser_exception("invalid/unexpected argument");
            default:
                throw parser_exception("unexpected argument");
            }
        }

        void parse_unknown_cmd() {
            SASSERT(curr_is_identifier());
            symbol s = curr_id();
            next();
            while (!curr_is_rparen()) {
                consume_sexpr();
            }
            m_ctx.print_unsupported(s, m_scanner.get_line(), m_scanner.get_pos());
            next();
            return;
        }

        void parse_ext_cmd(int line, int pos) {
            symbol s = curr_id();
            m_curr_cmd = m_ctx.find_cmd(s);
            if (m_curr_cmd == nullptr) {
                parse_unknown_cmd();
                return;
            }
            next();
            unsigned arity = m_curr_cmd->get_arity();
            unsigned i     = 0;
            unsigned sort_spos  = size(m_sort_stack);
            unsigned expr_spos  = size(m_expr_stack);
            unsigned sexpr_spos = size(m_sexpr_stack);
            unsigned sym_spos   = m_symbol_stack.size();
            m_curr_cmd->set_line_pos(line, pos);
            m_curr_cmd->prepare(m_ctx);
            while (true) {
                if (curr_is_rparen()) {
                    if (arity != VAR_ARITY && i < arity)
                        throw parser_exception("invalid command, argument(s) missing");
                    m_curr_cmd->execute(m_ctx);
                    next();
                    m_curr_cmd = nullptr;
                    shrink(m_sort_stack, sort_spos);
                    shrink(m_expr_stack, expr_spos);
                    shrink(m_sexpr_stack, sexpr_spos);
                    m_symbol_stack.shrink(sym_spos);
                    m_num_bindings = 0;
                    // HACK for propagating the update of parser parameters
                    if (norm_param_name(s) == "set_option") {
                        updt_params();
                    }
                    return;
                }
                else {
                    if (arity != VAR_ARITY && i == arity)
                        throw parser_exception("invalid command, too many arguments");
                    parse_next_cmd_arg();
                }
                i++;
            }
        }

        void parse_cmd() {
            SASSERT(curr_is_lparen());
            int line = m_scanner.get_line();
            int pos  = m_scanner.get_pos();
            next();
            check_identifier("invalid command, symbol expected");
            symbol s = curr_id();
            if (s == m_assert) {
                parse_assert();
                return;
            }
            if (s == m_declare_fun) {
                parse_declare_fun();
                return;
            }
            if (s == m_declare_const) {
                parse_declare_const();
                return;
            }
            if (s == m_check_sat) {
                parse_check_sat();
                return;
            }
            if (s == m_push) {
                parse_push();
                return;
            }
            if (s == m_pop) {
                parse_pop();
                return;
            }
            if (s == m_define_fun) {
                parse_define_fun();
                return;
            }
            if (s == m_define_const) {
                parse_define_const();
                return;
            }
            if (s == m_define_sort) {
                parse_define_sort();
                return;
            }
            if (s == m_declare_sort) {
                parse_declare_sort();
                return;
            }
            if (s == m_declare_datatypes) {
                parse_declare_datatypes();
                return;
            }
            if (s == m_declare_datatype) {
                parse_declare_datatype();
                return;
            }
            if (s == m_get_value) {
                parse_get_value();
                return;
            }
            if (s == m_reset) {
                parse_reset();
                return;
            }
            if (s == m_check_sat_assuming) {
                parse_check_sat_assuming();
                return;
            }
            if (s == m_define_fun_rec) {
                parse_define_fun_rec();
                return;
            }
            if (s == m_define_funs_rec) {
                parse_define_funs_rec();
                return;
            }
            if (s == m_model_add) {
                parse_model_add();
                return;
            }
            if (s == m_model_del) {
                parse_model_del();
                return;
            }
            parse_ext_cmd(line, pos);
        }

    public:
        parser(cmd_context & ctx, std::istream & is, bool interactive, params_ref const & p, char const * filename=nullptr):
            m_ctx(ctx),
            m_params(p),
            m_scanner(ctx, is, interactive),
            m_curr(scanner::NULL_TOKEN),
            m_curr_cmd(nullptr),
            m_num_bindings(0),
            m_let("let"),
            m_bang("!"),
            m_forall("forall"),
            m_exists("exists"),
            m_lambda("lambda"),
            m_as("as"),
            m_not("not"),
            m_root_obj("root-obj"),
            m_named(":named"),
            m_weight(":weight"),
            m_qid(":qid"),
            m_skid(":skolemid"),
            m_ex_act(":ex-act"),
            m_pattern(":pattern"),
            m_nopattern(":no-pattern"),
            m_lblneg(":lblneg"),
            m_lblpos(":lblpos"),
            m_assert("assert"),
            m_check_sat("check-sat"),
            m_define_fun("define-fun"),
            m_define_const("define-const"),
            m_model_add("model-add"),
            m_model_del("model-del"),
            m_declare_fun("declare-fun"),
            m_declare_const("declare-const"),
            m_define_sort("define-sort"),
            m_declare_sort("declare-sort"),
            m_declare_datatypes("declare-datatypes"),
            m_declare_datatype("declare-datatype"),
            m_par("par"),
            m_push("push"),
            m_pop("pop"),
            m_get_value("get-value"),
            m_reset("reset"),
            m_check_sat_assuming("check-sat-assuming"),
            m_define_fun_rec("define-fun-rec"),
            m_define_funs_rec("define-funs-rec"),
            m_match("match"),
            m_case("case"),
            m_underscore("_"),
            m_num_open_paren(0),
            m_current_file(filename) {
            // the following assertion does not hold if ctx was already attached to an AST manager before the parser object is created.
            // SASSERT(!m_ctx.has_manager());

            updt_params();
        }

        ~parser() {
            reset_stack();
        }

        void updt_params() {
            parser_params p(m_params);
            m_ignore_user_patterns = p.ignore_user_patterns();
            m_ignore_bad_patterns  = p.ignore_bad_patterns();
            m_display_error_for_vs = p.error_for_visual_studio();
        }

        void reset() {
            reset_stack();
            m_num_bindings    = 0;
            m_psort_stack     = nullptr;
            m_sort_stack      = nullptr;
            m_expr_stack      = nullptr;
            m_pattern_stack   = nullptr;
            m_nopattern_stack = nullptr;
            m_sexpr_stack     = nullptr;
            m_symbol_stack      .reset();
            m_param_stack       .reset();
            m_env               .reset();
            m_sort_id2param_idx .reset();
            m_dt_name2idx       .reset();

            m_bv_util           = nullptr;
            m_arith_util        = nullptr;
            m_seq_util          = nullptr;
            m_pattern_validator = nullptr;
            m_var_shifter       = nullptr;
        }

        bool operator()() {
            m_num_bindings    = 0;
            unsigned found_errors = 0;

            try {
                scan_core();
            }
            catch (scanner_exception & ex) {
                error(ex.msg());
                if (!sync_after_error())
                    return false;
                found_errors++;
            }

            while (true) {
                try {
                    m_num_open_paren = 0;
                    while (true) {
                        switch (curr()) {
                        case scanner::LEFT_PAREN:
                            parse_cmd();
                            break;
                        case scanner::EOF_TOKEN:
                            return found_errors == 0;
                        default:
                            throw parser_exception("invalid command, '(' expected");
                            break;
                        }
                    }
                }
                catch (z3_error & ex) {
                    // Can't invoke error(...) when out of memory.
                    // Reason: escaped() string builder needs memory
                    m_ctx.regular_stream() << "(error \"line " << m_scanner.get_line() << " column " << m_scanner.get_pos()
                                           << ": " << ex.msg() << "\")" << std::endl;
                    exit(ex.error_code());
                }
                catch (const stop_parser_exception &) {
                    m_scanner.stop_caching();
                    return !found_errors;
                }
                catch (parser_exception & ex) {
                    if (ex.has_pos())
                        error(ex.line(), ex.pos(), ex.msg());
                    else
                        error(ex.msg());
                }
                catch (ast_exception & ex) {
                    error(ex.msg());
                }
                catch (z3_exception & ex) {
                    error(ex.msg());
                }
                m_scanner.stop_caching();
                if (m_curr_cmd)
                    m_curr_cmd->failure_cleanup(m_ctx);
                reset();
                found_errors = true;
                if (!sync_after_error())
                    return false;
                TRACE("parser_error", tout << "after sync: " << curr() << "\n";);
                SASSERT(m_num_open_paren == 0);
            }
        }
    };
};

bool parse_smt2_commands(cmd_context & ctx, std::istream & is, bool interactive, params_ref const & ps, char const * filename) {
    smt2::parser p(ctx, is, interactive, ps, filename);
    return p();
}

