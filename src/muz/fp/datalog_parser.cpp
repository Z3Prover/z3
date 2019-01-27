
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#include "muz/fp/datalog_parser.h"
#include "util/string_buffer.h"
#include "util/str_hashtable.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "util/region.h"
#include "util/warning.h"
#include<iostream>
#include<sstream>
#include<cstdio>

using namespace datalog;

enum dtoken {
    TK_LP,
    TK_RP,
    TK_STRING,
    TK_ID,
    TK_NUM,
    TK_PERIOD,
    TK_INCLUDE,
    TK_COMMA,
    TK_COLON,
    TK_WILD,
    TK_LEFT_ARROW,
    TK_EOS,
    TK_NEWLINE,
    TK_ERROR,
    TK_NEQ,
    TK_LT,
    TK_GT,
    TK_EQ,
    TK_NEG
};    

static char const* dtoken_strings[] = { "(", ")", "<string>", "<id>", "<num>", ".", ".include", ",", ":", "_", ":-", "<eos>", "\\n", "<error>", "!=", "<", ">", "=", "!" };

class line_reader {

    static const char s_delimiter = '\n';
    static const unsigned s_expansion_step = 1024;

    FILE * m_file;
    svector<char> m_data;
    bool m_eof;
    bool m_eof_behind_buffer;
    unsigned m_next_index;
    bool m_ok;
    
    //actually by one larger than the actual size of m_data, 
    //to fit in the terminating delimiter
    unsigned m_data_size;

    void resize_data(unsigned sz) {
        m_data_size = sz;
        m_data.resize(m_data_size+1);
        m_data[m_data_size] = s_delimiter;
    }

#if 0
    void refill_buffer(unsigned start) {
        unsigned should_read = m_data_size-start;
        m_stm.read(m_data.begin()+start, should_read);
        unsigned actually_read = static_cast<unsigned>(m_stm.gcount());
        SASSERT(should_read==actually_read || m_stm.eof());
        if(m_stm.eof()) {
            m_eof_behind_buffer = true;
            resize_data(start+actually_read);
        }
    }
#else
    void refill_buffer(unsigned start) {
        unsigned should_read = m_data_size-start;
        size_t actually_read = fread(m_data.begin()+start, 1, should_read, m_file);
        if(actually_read==should_read) {
            return;
        }
        SASSERT(actually_read < should_read);
        SASSERT(feof(m_file));
        m_eof_behind_buffer = true;
        resize_data(start+static_cast<unsigned>(actually_read));
    }
#endif

public:

    line_reader(const char * fname) 
        :m_eof(false), 
         m_eof_behind_buffer(false), 
         m_next_index(0),
         m_ok(true),
         m_data_size(0) {
        m_data.resize(2*s_expansion_step);
        resize_data(0);
#if _WINDOWS
        errno_t err = fopen_s(&m_file, fname, "rb");
        m_ok = (m_file != nullptr) && (err == 0);
#else
        m_file = fopen(fname, "rb");
        m_ok = (m_file != nullptr);
#endif
    }
    ~line_reader() {
        if (m_file != nullptr){
            fclose(m_file);
        }
    }

    bool operator()() { return m_ok; }

    /**
       \brief Retrieve next line from the stream.

       This operation invalidates the line previously retrieved.

       This operation can be called only if we are not at the end of file.

       User is free to modify the content of the returned array until the terminating NULL character.
     */
    char * get_line() {
        SASSERT(!m_eof);
        unsigned start = m_next_index;
        unsigned curr = start;
        for(;;) {
            SASSERT(curr<=m_data_size);
            SASSERT(m_data[m_data_size]==s_delimiter);
            {
                const char * data_ptr = m_data.begin();
                const char * ptr = data_ptr+curr;
                while(*ptr!=s_delimiter) {
                    ptr++;
                }
                curr = static_cast<unsigned>(ptr-data_ptr);
            }
            SASSERT(m_data[curr]==s_delimiter);
            if(curr<m_data_size || m_eof_behind_buffer) {
                if(curr==m_data_size) {
                    SASSERT(m_eof_behind_buffer);
                    m_eof = true;
                }
                m_data[curr] = 0; //put in string terminator
                m_next_index = curr+1;
                return m_data.begin()+start;
            }
            if(start!=0) {
                unsigned len = curr-start;
                if(len) {
                    memmove(m_data.begin(), m_data.begin()+start, len);
                }
                start = 0;
                curr = len;
            }
            if(m_data_size-curr<s_expansion_step) {
                resize_data(m_data_size+s_expansion_step);
            }
            refill_buffer(curr);
        }
    }

    bool eof() const { return m_eof; }
};

class char_reader {
    line_reader m_line_reader;
    char const* m_line;
public:
    char_reader(char const* file):
        m_line_reader(file),
        m_line(nullptr)
    {}
   
    bool operator()() { return m_line_reader(); }

    char get() {
        if (!m_line) {
            if (m_line_reader.eof()) {
                return EOF;
            }
            m_line = m_line_reader.get_line();
        }
        if (!(m_line[0])) {
            m_line = nullptr;
            return '\n';
        }
        char result = m_line[0];
        ++m_line;
        return result;
    }

    bool eof() {
        return m_line_reader.eof();
    }
};

class reserved_symbols {
    typedef map<char const *, dtoken, str_hash_proc, str_eq_proc> str2token;
    str2token m_str2token;

public:
    reserved_symbols() {
        m_str2token.insert(":-", TK_LEFT_ARROW);
        m_str2token.insert("_",  TK_WILD);
        m_str2token.insert(".",  TK_PERIOD);
        m_str2token.insert("!=", TK_NEQ);
        m_str2token.insert("=", TK_EQ);
        m_str2token.insert("<",  TK_LT);
        m_str2token.insert(">",  TK_GT);
        m_str2token.insert(":",  TK_COLON);
        m_str2token.insert(".include", TK_INCLUDE);
        m_str2token.insert("!", TK_NEG);
    }

    dtoken string2dtoken(char const * str) {
        str2token::entry * e = m_str2token.find_core(str);
        if (e)
            return e->get_data().m_value;
        else
            return TK_ID;
    }
};


class dlexer {
    std::istream*   m_input;
    char_reader*    m_reader;
    char            m_prev_char;
    char            m_curr_char;
    int             m_line;
    int             m_pos;
    int             m_tok_pos;
    string_buffer<> m_buffer;
    reserved_symbols m_reserved_symbols;

public:
    //when parsing domains, we want '.' character to be allowed in IDs, but elsewhere 
    //we don't (because of the "y." in rules like "P(x,y):-x=y.")
    bool m_parsing_domains;

    bool eos() const {
        return m_curr_char == EOF;
    }
    
    void next() {
        m_prev_char = m_curr_char;
        if (m_reader) {
            m_curr_char = m_reader->get();
        }
        else {
            m_curr_char = m_input->get();
        }
        m_pos++;
    }
    
    void save_char(char c) {
        m_buffer << c;
    }

    void save_and_next() {
        m_buffer << m_curr_char;
        next();
    }

    dlexer():
        m_input(nullptr),
        m_reader(nullptr),
        m_prev_char(0),
        m_curr_char(0),
        m_line(1),
        m_pos(0),
        m_tok_pos(0),
        m_parsing_domains(false) {
    }

    void set_stream(std::istream* s, char_reader* r) { 
        m_input = s; 
        m_reader = r;
        next();
    }


    dtoken read_num() {
        while(isdigit(m_curr_char)) {
            save_and_next();
        }        
        return TK_NUM;
    }

    dtoken read_id() {
        while (!eos() && m_curr_char != '(' && m_curr_char != ')' && 
               m_curr_char != '#' && m_curr_char != ',' && (m_parsing_domains || m_curr_char != '.') && 
               m_curr_char != ':' && m_curr_char != '=' && !iswspace(m_curr_char) ) {
            save_and_next();
        }
        return m_reserved_symbols.string2dtoken(m_buffer.c_str());
    }
    
    // read an id of the form '|'.*'|' 
    dtoken read_bid() {
        while (!eos() && m_curr_char != '|') {
            save_and_next();
        }
        if (m_curr_char == '|') {
            next();
        }
        return m_reserved_symbols.string2dtoken(m_buffer.c_str());
    }

    dtoken read_string() { 
        m_tok_pos = m_pos; 
        next(); 
        while (m_curr_char != '"') { 
            if (m_input && m_input->eof()) {
                return TK_ERROR;
            }
            if (m_reader && m_reader->eof()) {
                return TK_ERROR;
            }
            if (m_curr_char == '\n') {
                return TK_ERROR;
            }
            save_and_next(); 
        }
        next(); 
        return TK_STRING;
    } 

    void read_comment() {
        bool line_comment = m_prev_char=='\n' || m_prev_char == 0;
        while (m_curr_char != '\n' && !eos()) {
            next();
        }
        if (line_comment && m_curr_char == '\n') {
            m_line++;
            next();
        }
    }

    bool lookahead_newline() {
        while (m_curr_char == ' ') {
            save_and_next();
        }
        if (m_curr_char == '\n') {
            next();
            m_line++;
            m_buffer.reset();
            return true;
        }
        if (m_curr_char == '#') {
            m_buffer.reset();
            m_prev_char = 0;
            read_comment();
            return true;
        }
        return false;
    }

    dtoken next_token() {
        for(;;) {
            if (eos()) {
                return TK_EOS;
            }
            
            m_buffer.reset();
            switch (m_curr_char) {
            case '#': // comment
                read_comment();
                break;
            case '\n':
                next();
                m_line++;
                return TK_NEWLINE;
            case '\\':
                // here we ignore a newline if it is preceded by a backslash.
                // We need to take care, since anywhere else backshlash is used
                // as a regular character
                next();
                save_char('\\');
                if (lookahead_newline()) {
                    break;
                }
                return read_id();
            case '(':
                m_tok_pos = m_pos;
                next();
                return TK_LP;
            case ')':
                m_tok_pos = m_pos;
                next();
                return TK_RP;               
            case ',':
                m_tok_pos = m_pos;
                next();
                return TK_COMMA; 
            case '=':
                m_tok_pos = m_pos;
                next();
                return TK_EQ; 
            case '!':
                m_tok_pos = m_pos;
                next();
                if(m_curr_char == '=') {
                    next();
                    return TK_NEQ;
                }
                return TK_NEG; 
            case ':':
                m_tok_pos = m_pos;
                next();
                if (m_curr_char == '-') {
                    next();
                    return TK_LEFT_ARROW;
                }
                return TK_COLON;
            case '\"':
                return read_string();
            case '|':
                next();
                return read_bid();
            default:
                if (iswspace(m_curr_char)) {
                    next();
                    break;
                }
                else if (iswdigit(m_curr_char)) {
                    m_tok_pos = m_pos;
                    save_and_next();
                    return read_num();
                }
                else {
                    char old = m_curr_char;
                    m_tok_pos = m_pos;
                    save_and_next();
                    if (old == '-' && iswdigit(m_curr_char)) {
                        return read_num();
                    }
                    else {
                        return read_id();
                    }
                }
            }
        }
    }

    const char * get_token_data() const {
        return m_buffer.c_str();
    }

    unsigned get_token_pos() const {
        return m_tok_pos;
    }

    unsigned get_line() const { return m_line; }

    
      
};

class dparser : public parser {
protected:
    typedef map<std::string, expr*,      std_string_hash_proc, default_eq<std::string> > str2var;
    typedef map<std::string, sort*,      std_string_hash_proc, default_eq<std::string> > str2sort;

    context&          m_context;
    ast_manager&      m_manager;

    dlexer*           m_lexer;
    region            m_region;
    dl_decl_util &    m_decl_util;
    arith_util        m_arith;

    unsigned          m_num_vars;
    str2var           m_vars;
    unsigned          m_sym_idx;
    std::string       m_path;
    str2sort          m_sort_dict;

    
    // true if an error occurred during the current call to the parse_stream
    // function
    bool              m_error;
public:
    dparser(context& ctx, ast_manager& m):
        m_context(ctx),
        m_manager(m),
        m_decl_util(ctx.get_decl_util()),
        m_arith(m),
        m_num_vars(0),
        m_sym_idx(0)
    {
    }

    bool parse_file(char const * filename) override {
        reset();
        if (filename != nullptr) {
            set_path(filename);
            char_reader reader(filename);            
            if (!reader()) {
                get_err() << "ERROR: could not open file '" << filename << "'.\n";
                return false;
            }
            return parse_stream(nullptr, &reader);
        }
        else {
            return parse_stream(&std::cin, nullptr);
        }
    }

    bool parse_string(char const * string) override {
        reset();
        std::string s(string);
        std::istringstream is(s);
        return parse_stream(&is, nullptr);
    }
    
protected:

    void reset() {
        m_num_vars = 0;
        m_sym_idx = 0;
        m_vars.reset();
        m_region.reset();
        m_path.clear();
        m_sort_dict.reset();
    }

    void set_path(char const* filename) {
        char const* div = strrchr(filename, '/');
        if (!div) {
            div = strrchr(filename,'\\');
        }
        if (div) {
            m_path.assign(filename, div - filename + 1);
        }
    }

    std::ostream& get_err() {
        return std::cerr;
    }

    bool parse_stream(std::istream* is, char_reader* r) {
        bool result = false;
        try {
            m_error=false;
            dlexer lexer;
            m_lexer = &lexer;
            m_lexer->set_stream(is, r);
            dtoken tok = m_lexer->next_token();
            tok = parse_domains(tok);
            tok = parse_decls(tok);
            result = tok == TK_EOS && m_error == false;
        }
        catch (z3_exception& ex) {
            std::cerr << ex.msg() << std::endl;
            result = false;
        }
        return result;
    }

    dtoken parse_domains(dtoken tok) {
        flet<bool> flet_parsing_domains(m_lexer->m_parsing_domains, true);
        while (tok != TK_EOS && tok != TK_ERROR) {
            switch(tok) {
            case TK_ID:
                tok = parse_domain();
                break;
            case TK_NEWLINE:
                return m_lexer->next_token();
            case TK_INCLUDE:
                tok = m_lexer->next_token();
                if (tok != TK_STRING) {
                    tok = unexpected(tok, "a string");
                    break;
                }
                tok = parse_include(m_lexer->get_token_data(), true);                
                if(tok!=TK_NEWLINE) {
                    tok = unexpected(tok, "newline expected after include statement");
                }
                else {
                    tok = m_lexer->next_token();
                }
                break;
            default:
                tok = unexpected(tok, "identifier, newline or include");
                break;
            }
        }
        return tok;
    }

    bool extract_domain_name(const char* s0, std::string & result) {
        std::string str(s0);
        size_t last_non_digit = str.find_last_not_of("0123456789");
        if(last_non_digit==std::string::npos) {
            //the domain name consists only of digits, which should not happen
            result=str;
            return false;
        }
        str.erase(last_non_digit+1);
        result=str;
        return true;
    }

    dtoken parse_domain() {
        std::string domain_name;
        if(!extract_domain_name(m_lexer->get_token_data(), domain_name)) {
            return unexpected(TK_ID, "domain name");
        }
        dtoken tok = m_lexer->next_token();
        if (tok == TK_ID && strcmp(m_lexer->get_token_data(), "int")==0) {
            register_int_sort(symbol(domain_name.c_str()));

            tok = m_lexer->next_token();
            if(tok != TK_NEWLINE) {
                return unexpected(tok, "end of line");
            }
            return tok;
        }
        if (tok != TK_NUM) {
            return unexpected(tok, "numeral or 'int'");
        }

        unsigned num = atoi(m_lexer->get_token_data());
        sort * s = register_finite_sort(symbol(domain_name.c_str()), num, context::SK_SYMBOL);

        tok = m_lexer->next_token();
        if (tok == TK_ID) {
            tok = parse_mapfile(tok, s, m_lexer->get_token_data());
        }
        if (tok == TK_NEWLINE) {
            tok = m_lexer->next_token();
        }
        return tok;
    }


    dtoken parse_decls(dtoken tok) {
        while (tok != TK_EOS && tok != TK_ERROR) {
            switch(tok) {
            case TK_ID:
                tok = parse_rule(tok);
                break;
            case TK_NEWLINE:
                tok = m_lexer->next_token();
                break;                
            case TK_INCLUDE:
                tok = m_lexer->next_token();
                if (tok != TK_STRING) {
                    tok = unexpected(tok, "a string");
                    break;
                }
                tok = parse_include(m_lexer->get_token_data(), false);                
                break;
            default:
                tok = unexpected(tok, "identifier");
                break;
            }
        }
        return tok;
    }

    dtoken unexpected(dtoken tok, char const* msg) {
#if 1
        throw default_exception(default_exception::fmt(), "%s at line %u '%s' found '%s'\n", msg, 
            m_lexer->get_line(), m_lexer->get_token_data(), dtoken_strings[tok]);

        SASSERT(false);
        return tok;
#else
        m_error = true;

        get_err() << msg << " expected at line " << m_lexer->get_line() << "\n";
        get_err() << "'" << m_lexer->get_token_data() << "' found\n";
        get_err() << "'" << dtoken_strings[tok] << "'\n";
        if (tok == TK_ERROR || tok == TK_EOS) {
            return tok;
        }
        return m_lexer->next_token();
#endif
    }

    dtoken parse_rule(dtoken tok) {
        m_num_vars = 0;
        m_vars.reset();

        switch(tok) {
        case TK_EOS:
            return tok;
        case TK_ID: {
            app_ref pred(m_manager);
            symbol s(m_lexer->get_token_data());
            tok = m_lexer->next_token();
            bool is_predicate_declaration;
            tok = parse_pred(tok, s, pred, is_predicate_declaration);
            switch (tok) {
            case TK_PERIOD:
                if(is_predicate_declaration) {
                    return unexpected(tok, "predicate declaration should not end with '.'");
                }
                add_rule(pred, 0, nullptr, nullptr);
                return m_lexer->next_token();
            case TK_LEFT_ARROW:
                return parse_body(pred);
            case TK_NEWLINE:
            case TK_EOS:
                if(!is_predicate_declaration) {
                    return unexpected(tok, "'.' expected at the end of rule");
                }
                return tok;
            default:
                return unexpected(tok, "unexpected token");
            }
        }
        default:
            return unexpected(tok, "rule expected");
        }
    }

    dtoken parse_body(app* head) {
        app_ref_vector body(m_manager);
        svector<bool> polarity_vect;
        dtoken tok = m_lexer->next_token();
        while (tok != TK_ERROR && tok != TK_EOS) {            
            if (tok == TK_PERIOD) {
                SASSERT(body.size()==polarity_vect.size());
                add_rule(head, body.size(), body.c_ptr(), polarity_vect.c_ptr());
                return m_lexer->next_token();
            }
            char const* td = m_lexer->get_token_data();
            app_ref pred(m_manager);
            bool is_neg = false;
            if (tok == TK_NEG) {
                tok = m_lexer->next_token();
                is_neg = true;
            }

            if (tok == TK_STRING || tok == TK_NUM || (tok == TK_ID && m_vars.contains(td))) {
                tok = parse_infix(tok, td, pred);
            }
            else if (tok == TK_ID) {
                symbol s(td);
                tok = m_lexer->next_token();
                bool is_declaration;
                tok = parse_pred(tok, s, pred, is_declaration);
                SASSERT(!is_declaration);
            }
            else {
                tok = unexpected(tok, "expected predicate or relation");
                return tok;
            }
            body.push_back(pred);
            polarity_vect.push_back(is_neg);

            if (tok == TK_COMMA) {
                tok = m_lexer->next_token();
            }
            else if (tok == TK_PERIOD) {
                continue;
            }
            else {
                tok = unexpected(tok, "expected comma or period");
                return tok;
            }
        }    
        return tok;
    }

    //
    // infix:
    // Sym REL Sym
    // Sym ::= String | NUM | Var
    // 
    dtoken parse_infix(dtoken tok1, char const* td, app_ref& pred) {
        symbol td1(td);
        expr_ref v1(m_manager), v2(m_manager);
        sort* s = nullptr;
        dtoken tok2 = m_lexer->next_token();
        if (tok2 != TK_NEQ && tok2 != TK_GT && tok2 != TK_LT && tok2 != TK_EQ) {
            return unexpected(tok2, "built-in infix operator");
        }
        dtoken tok3 = m_lexer->next_token();
        td = m_lexer->get_token_data();
        if (tok3 != TK_STRING && tok3 != TK_NUM && !(tok3 == TK_ID && m_vars.contains(td))) {
            return unexpected(tok3, "identifier");
        }
        symbol td2(td);

        if (tok1 == TK_ID) {
            expr* _v1 = nullptr;
            m_vars.find(td1.bare_str(), _v1);
            v1 = _v1;
        }
        if (tok3 == TK_ID) {
            expr* _v2 = nullptr;
            m_vars.find(td2.bare_str(), _v2);
            v2 = _v2;
        }
        if (!v1 && !v2) {
            return unexpected(tok3, "at least one argument should be a variable");
        }
        if (v1) {
            s = m_manager.get_sort(v1);
        }        
        else {
            s = m_manager.get_sort(v2);
        }
        if (!v1) {
            v1 = mk_const(td1, s);
        }
        if (!v2) {
            v2 = mk_const(td2, s);
        }

        switch(tok2) {
        case TK_EQ:
            pred = m_manager.mk_eq(v1,v2);
            break;
        case TK_NEQ:
            pred = m_manager.mk_not(m_manager.mk_eq(v1,v2));
            break;
        case TK_LT:
            pred = m_decl_util.mk_lt(v1, v2);
            break;
        case TK_GT:
            pred = m_decl_util.mk_lt(v2, v1);
            break;
        default:
            UNREACHABLE();
        }
        
        return m_lexer->next_token();
    }


    dtoken parse_pred(dtoken tok, symbol const& s, app_ref& pred, bool & is_predicate_declaration) {

        expr_ref_vector args(m_manager);        
        svector<symbol> arg_names;
        func_decl* f = m_context.try_get_predicate_decl(s);
        tok = parse_args(tok, f, args, arg_names);
        is_predicate_declaration = f==nullptr;
        if (f==nullptr) {
            //we're in a declaration
            unsigned arity = args.size();
            ptr_vector<sort> domain;
            for (unsigned i = 0; i < arity; ++i) {
                domain.push_back(m_manager.get_sort(args[i].get()));
            }
            f = m_manager.mk_func_decl(s, domain.size(), domain.c_ptr(), m_manager.mk_bool_sort());

            m_context.register_predicate(f, true);
        
            while (tok == TK_ID) {
                char const* pred_pragma = m_lexer->get_token_data();
                if(strcmp(pred_pragma, "printtuples")==0 || strcmp(pred_pragma, "outputtuples")==0) {
                    m_context.set_output_predicate(f);
                }
                tok = m_lexer->next_token();
            }
            m_context.set_argument_names(f, arg_names);
        }
        if(args.size() < f->get_arity()) {
            return unexpected(tok, "too few arguments passed to predicate");
        }
        SASSERT(args.size()==f->get_arity());
        //TODO: we do not need to do the mk_app if we're in a declaration
        pred = m_manager.mk_app(f, args.size(), args.c_ptr());
        return tok;
    }

    /**
       \brief Parse predicate arguments. If \c f==0, they are arguments of a predicate declaration.
       If parsing a declaration, argument names are pushed to the \c arg_names vector.
    */
    dtoken parse_args(dtoken tok, func_decl* f, expr_ref_vector& args, svector<symbol> & arg_names) {
        if (tok != TK_LP) {
            return tok;
        }
        unsigned arg_idx = 0;
        tok = m_lexer->next_token();
        while (tok != TK_EOS && tok != TK_ERROR) {
            symbol alias;
            sort* s = nullptr;

            if(!f) {
                //we're in a predicate declaration
                if(tok != TK_ID) {
                    tok = unexpected(tok, "Expecting variable in declaration");
                    return tok;
                }
                symbol var_symbol(m_lexer->get_token_data());
                tok = m_lexer->next_token();
                if (tok != TK_COLON) {
                    tok = unexpected(tok, 
                        "Expecting colon in declaration (first occurrence of a predicate must be a declaration)");
                    return tok;
                }
                tok = m_lexer->next_token();

                if (tok != TK_ID) {
                    tok = unexpected(tok, "Expecting sort after colon in declaration");
                    return tok;
                }
                std::string sort_name;
                if(!extract_domain_name(m_lexer->get_token_data(), sort_name)) {
                    return unexpected(TK_ID, "sort name");
                }
                sort* s = get_sort(sort_name.c_str());
                args.push_back(m_manager.mk_var(m_num_vars, s));
                arg_names.push_back(var_symbol);
                tok = m_lexer->next_token();
            }
            else {
                if(arg_idx>=f->get_arity()) {
                    return unexpected(tok, "too many arguments passed to predicate");
                }
                s = f->get_domain(arg_idx);

                symbol var_symbol;
                tok = parse_arg(tok, s, args);
            }


            ++arg_idx;

            if (tok == TK_RP) {
                return m_lexer->next_token();
            }
            if (tok == TK_COMMA) {
                tok = m_lexer->next_token();
            }            
        }
        return tok;
    }

    /**
       \remark \c var_symbol argument is assigned name of the variable. If the argument is not
       a variable, is remains unchanged.
    */
    dtoken parse_arg(dtoken tok, sort* s, expr_ref_vector& args) {
        switch(tok) {
        case TK_WILD: {
            args.push_back(m_manager.mk_var(m_num_vars++, s));
            break;
        }
        case TK_ID: {
            symbol data (m_lexer->get_token_data());
            if (is_var(data.bare_str())) {
                unsigned idx = 0;
                expr* v = nullptr;
                if (!m_vars.find(data.bare_str(), v)) {
                    idx = m_num_vars++;
                    v = m_manager.mk_var(idx, s);
                    m_vars.insert(data.bare_str(), v);
                }
                else if (s != m_manager.get_sort(v)) {
                    throw default_exception(default_exception::fmt(), "sort: %s expected, but got: %s\n",
                        s->get_name().bare_str(), m_manager.get_sort(v)->get_name().bare_str());
                }
                args.push_back(v);
            }
            else {
                args.push_back(mk_const(data, s));
            }
            break;
        }
        case TK_STRING: {
            char const* data = m_lexer->get_token_data();
            args.push_back(mk_const(symbol(data), s));
            break;
        }
        case TK_NUM: {
            char const* data = m_lexer->get_token_data();
            rational num(data);
            if(!num.is_uint64()) {
                return unexpected(tok, "integer expected");
            }
            uint64_t int_num = num.get_uint64();
            
            app * numeral = mk_symbol_const(int_num, s);
            args.push_back(numeral);
            break;
        }
        default:
            break;
        }
        return m_lexer->next_token();
    }

    // all IDs are variables.
    bool is_var(char const* data) {
        return true;
    }

    dtoken parse_decl(dtoken tok) {

        return tok;
    }    

    dtoken parse_include(char const* filename, bool parsing_domain) {
        IF_VERBOSE(2, verbose_stream() << "include: " << filename << "\n";);
        std::string path(m_path);
        path += filename;
        char_reader stream(path.c_str());
        if (!stream()) {
            get_err() << "ERROR: could not open file '" << path << "'.\n";
            return TK_ERROR;
        }
        dtoken tok;
        dlexer lexer;
        {
            flet<dlexer*> lexer_let(m_lexer, &lexer);
            m_lexer->set_stream(nullptr, &stream);
            tok = m_lexer->next_token();
            if(parsing_domain) {
                tok = parse_domains(tok);
            }
            tok = parse_decls(tok);
        }
        if (tok == TK_EOS) {
            tok = m_lexer->next_token();
        }
        return tok;
    }

    dtoken parse_mapfile(dtoken tok, sort * s, char const* filename) {
        std::string path(m_path);
        path += filename;
        line_reader reader(path.c_str());

        if (!reader()) {
            get_err() << "Warning: could not open file '" << path << "'.\n";
            return m_lexer->next_token();
        }

        std::string line;
        while(!reader.eof()) {
            symbol sym=symbol(reader.get_line());
            m_context.get_constant_number(s, sym); 
        }        
        return m_lexer->next_token();
    }

    bool read_line(std::istream& strm, std::string& line) {
        line.clear();
        char ch = strm.get();
        while (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') {
            ch = strm.get();
        }
        while (ch != '\n' && ch != '\r' && ch != EOF) {
            line.push_back(ch);
            ch = strm.get();
        }
        return !line.empty();
    }

    void add_rule(app* head, unsigned sz, app* const* body, const bool * is_neg) {
        rule_manager& m = m_context.get_rule_manager();

        if(sz==0 && m.is_fact(head)) {
            m_context.add_fact(head);
        }
        else {
            rule * r = m.mk(head, sz, body, is_neg);
            rule_ref rule(r, m);
            m_context.add_rule(rule);

        }
    }

    sort * register_finite_sort(symbol name, uint64_t domain_size, context::sort_kind k) {
        if(m_sort_dict.contains(name.bare_str())) {
            throw default_exception(default_exception::fmt(), "sort %s already declared", name.bare_str());
        }
        sort * s = m_decl_util.mk_sort(name, domain_size);
        m_context.register_finite_sort(s, k);
        m_sort_dict.insert(name.bare_str(), s);
        return s;
    }

    sort * register_int_sort(symbol name) {
        if(m_sort_dict.contains(name.bare_str())) {
            throw default_exception(default_exception::fmt(), "sort %s already declared", name.bare_str());
        }
        sort * s = m_arith.mk_int();
        m_sort_dict.insert(name.bare_str(), s);
        return s;
    }

    sort * get_sort(const char* str) {
        sort * res;
        if(!m_sort_dict.find(str, res)) {
            throw default_exception(default_exception::fmt(), "unknown sort \"%s\"", str);
        }
        return res;
    }

    app* mk_const(symbol const& name, sort* s) {
        app * res;
        if(m_arith.is_int(s)) {
            uint64_t val;
            if(!string_to_uint64(name.bare_str(), val)) {
                throw default_exception(default_exception::fmt(), "Invalid integer: \"%s\"", name.bare_str());
            }
            res = m_arith.mk_numeral(rational(val, rational::ui64()), s);
        }
        else {
            unsigned idx = m_context.get_constant_number(s, name);
            res = m_decl_util.mk_numeral(idx, s);
        }
        return res;
    }
    /**
       \brief Make a constant for DK_SYMBOL sort out of an integer
     */
    app* mk_symbol_const(uint64_t el, sort* s) {
        app * res;
        if(m_arith.is_int(s)) {
            res = m_arith.mk_numeral(rational(el, rational::ui64()), s);
        }
        else {
            unsigned idx = m_context.get_constant_number(s, symbol(to_string(el).c_str()));
            res = m_decl_util.mk_numeral(idx, s);
        }
        return res;
    }
    app* mk_const(uint64_t el, sort* s) {
        unsigned idx = m_context.get_constant_number(s, el);
        app * res = m_decl_util.mk_numeral(idx, s);
        return res;
    }

    table_element mk_table_const(symbol const& name, sort* s) {
        return m_context.get_constant_number(s, name);
    }
    table_element mk_table_const(uint64_t el, sort* s) {
        return m_context.get_constant_number(s, el);
    }
};

/*
  
  Program     ::== Sort* (Rule | Include | Decl)*
  Comment     ::== '#...'
  Rule        ::== Fact | InfRule
  Fact        ::== Identifier(Element*).
  InfRule     ::== Identifier(Element*) :- (Identifier(Element*))+.
  Element     ::== '_' | 'string' | integer | Identifier
 
  Sort        ::== Identifier (Number [map-file]| 'int')
  Decl        ::== Identifier(SortDecl) [Pragma] \n
  SortDecl    ::== Identifier ':' Identifier

  Pragma      ::== 'input' | 'printtuples' | 


  If sort name ends with a sequence of digits, they are ignored (so V and V1234 stand for the same sort)
  This is how BDDBDDB behaves.
*/

// -----------------------------------
//
// wpa_parser
//
// -----------------------------------

class wpa_parser_impl : public wpa_parser, dparser {
    typedef svector<uint64_t> uint64_vector;
    typedef hashtable<uint64_t, uint64_hash, default_eq<uint64_t> > uint64_set;
    typedef map<uint64_t, symbol, uint64_hash, default_eq<uint64_t> > num2sym;
    typedef map<symbol, uint64_set*, symbol_hash_proc, symbol_eq_proc> sym2nums;

    num2sym m_number_names;
    sym2nums m_sort_contents;

    sort_ref m_bool_sort;
    sort_ref m_short_sort;

    std::string m_current_file;
    unsigned m_current_line;

    bool m_use_map_names;

    uint64_set& ensure_sort_content(symbol sort_name) {
        sym2nums::entry * e = m_sort_contents.insert_if_not_there2(sort_name, nullptr);
        if(!e->get_data().m_value) {
            e->get_data().m_value = alloc(uint64_set);
        }
        return *e->get_data().m_value;
    }

public:        
    wpa_parser_impl(context & ctx) 
        : dparser(ctx, ctx.get_manager()),
          m_bool_sort(ctx.get_manager()),
          m_short_sort(ctx.get_manager()),
          m_use_map_names(ctx.use_map_names()) {
    }
    ~wpa_parser_impl() override {
        reset_dealloc_values(m_sort_contents);
    }
    void reset() {
    }

    bool parse_directory(char const * path) override {
        bool result = false;
        try {
            result = parse_directory_core(path);
        }
        catch (z3_exception& ex) {
            std::cerr << ex.msg() << std::endl;
            return false;
        }
        return result;
    }

private:

    bool parse_directory_core(char const* path) {

        IF_VERBOSE(10, verbose_stream() << "Start parsing directory " << path << "\n";);
        reset();
        string_vector map_files;
        get_file_names(path, "map", true, map_files);
        string_vector::iterator mit = map_files.begin();
        string_vector::iterator mend = map_files.end();
        for(; mit!=mend; ++mit) {
            std::string map_file_name = *mit;
            parse_map_file(map_file_name);
        }

        finish_map_files();

        string_vector rule_files;
        get_file_names(path, "rules", true, rule_files);
        string_vector::iterator rlit = rule_files.begin();
        string_vector::iterator rlend = rule_files.end();
        for(; rlit!=rlend; ++rlit) {
            parse_rules_file(*rlit);
        }

        string_vector rel_files;
        get_file_names(path, "rel", true, rel_files);
        string_vector::iterator rit = rel_files.begin();
        string_vector::iterator rend = rel_files.end();
        for(; rit!=rend; ++rit) {
            std::string rel_file_name = *rit;
            //skip relations which we do not support yet
            if(rel_file_name.find("DirectCall")!=std::string::npos ||
                  rel_file_name.find("FunctionFormals")!=std::string::npos ||
                  rel_file_name.find("IndirectCall")!=std::string::npos) {
                continue;
            }
            parse_rel_file(rel_file_name);
        }
        IF_VERBOSE(10, verbose_stream() << "Done parsing directory " << path << "\n";);
        return true;
    }

    bool inp_num_to_element(sort * s, uint64_t num, table_element & res) {
        if(s==m_bool_sort.get() || s==m_short_sort.get()) {
            res = mk_table_const(num, s);
            return true;
        }

        if(num==0) {
            if(!m_use_map_names) {
                res = mk_table_const(0, s);
            }
            else {
                res = mk_table_const(symbol("<zero element>"), s);
            }
            return true;
        }

        sym2nums::entry * e =  m_sort_contents.find_core(s->get_name());
        SASSERT(e);
        SASSERT(e->get_data().m_value);
        uint64_set & sort_content = *e->get_data().m_value;
        if(!sort_content.contains(num)) {
            warning_msg("symbol number %I64u on line %d in file %s does not belong to sort %s", 
                num, m_current_line, m_current_file.c_str(), s->get_name().bare_str());
            return false;
        }
        if(!m_use_map_names) {
            res = mk_table_const(num, s);
            return true;
        }
        else {
            symbol const_name;
            if(num==0) {
                const_name = symbol("<zero element>");
            } else if(!m_number_names.find(num, const_name)) {
                throw default_exception(default_exception::fmt(), "unknown symbol number %I64u on line %d in file %s", 
                    num, m_current_line, m_current_file.c_str());
            }
            res =  mk_table_const(const_name, s);
            return true;
        }
    }

    void parse_rules_file(const std::string & fname) {
        SASSERT(file_exists(fname));
        flet<std::string> flet_cur_file(m_current_file, fname);

        std::ifstream stm(fname.c_str());
        SASSERT(!stm.fail());

        dlexer lexer;
        m_lexer = &lexer;
        m_lexer->set_stream(&stm, nullptr);
        dtoken tok = m_lexer->next_token();
        tok = parse_decls(tok);
        m_lexer = nullptr;
    }

    bool parse_rel_line(char * full_line, uint64_vector & args) {
        SASSERT(args.empty());
        cut_off_comment(full_line);
        if(full_line[0]==0) {
            return false;
        }
        const char * ptr = full_line;

        bool last = false;
        do {
            while(*ptr==' ') { ptr++; }
            if(*ptr==0) {
                break;
            }
            uint64_t num;
            if(!read_uint64(ptr, num)) {
                throw default_exception(default_exception::fmt(), "number expected on line %d in file %s", 
                    m_current_line, m_current_file.c_str());
            }
            if(*ptr!=' ' && *ptr!=0) {
                throw default_exception(default_exception::fmt(), 
                                        "' ' expected to separate numbers on line %d in file %s, got '%s'", 
                                        m_current_line, m_current_file.c_str(), ptr);
            }
            args.push_back(num);
        } while(!last);
        return true;
    }

    void parse_rel_file(const std::string & fname) {
        SASSERT(file_exists(fname));

        IF_VERBOSE(10, verbose_stream() << "Parsing relation file " << fname << "\n";);

        flet<std::string> flet_cur_file(m_current_file, fname);
        flet<unsigned> flet_cur_line(m_current_line, 0);

        std::string predicate_name_str = get_file_name_without_extension(fname);
        symbol predicate_name(predicate_name_str.c_str());

        func_decl * pred = m_context.try_get_predicate_decl(predicate_name);
        if(!pred) {
            throw default_exception(default_exception::fmt(), "tuple file %s for undeclared predicate %s", 
                m_current_file.c_str(), predicate_name.bare_str());
        }
        unsigned pred_arity = pred->get_arity();
        sort * const * arg_sorts = pred->get_domain();

        uint64_vector args;
        table_fact fact;

        //std::ifstream stm(fname.c_str(), std::ios_base::binary);
        //SASSERT(!stm.fail());
        //line_reader rdr(stm);
        line_reader rdr(fname.c_str());
        while(!rdr.eof()) {
            m_current_line++;
            char * full_line = rdr.get_line();

            args.reset();
            if(!parse_rel_line(full_line, args)) {
                continue;
            }
            if(args.size()!=pred_arity) {
                throw default_exception(default_exception::fmt(), "invalid number of arguments on line %d in file %s", 
                    m_current_line, m_current_file.c_str());
            }

            bool fact_fail = false;
            fact.reset();
            for(unsigned i=0;i<pred_arity; i++) {
                uint64_t const_num = args[i];
                table_element c;
                if(!inp_num_to_element(arg_sorts[i], const_num, c)) {
                    fact_fail = true;
                    break;
                }
                fact.push_back(c);
            }
            if(fact_fail) {
                continue;
            }
            m_context.add_table_fact(pred, fact);
        }
    }

    void finish_map_files() {

        m_bool_sort = register_finite_sort(symbol("BOOL"), 2, context::SK_UINT64);
        m_short_sort = register_finite_sort(symbol("SHORT"), 65536, context::SK_UINT64);

        sym2nums::iterator sit = m_sort_contents.begin();
        sym2nums::iterator send = m_sort_contents.end();
        for(; sit!=send; ++sit) {
            symbol sort_name = sit->m_key;
            uint64_set & sort_content = *sit->m_value;
            //the +1 is for a zero element which happens to appear in the problem files
            uint64_t domain_size = sort_content.size()+1;
            // sort * s;
            if(!m_use_map_names) {
                /* s = */ register_finite_sort(sort_name, domain_size, context::SK_UINT64);
            }
            else {
                /* s = */ register_finite_sort(sort_name, domain_size, context::SK_SYMBOL);
            }

            /*
            uint64_set::iterator cit = sort_content.begin();
            uint64_set::iterator cend = sort_content.end();
            for(; cit!=cend; ++cit) {
                uint64_t const_num = *cit;
                inp_num_to_element(s, const_num);
            }
            */
        }
    }

    void cut_off_comment(char * line) {
        char * ptr = line;
        while(*ptr && *ptr!='#' && *ptr!='\n' && *ptr!='\r') {
            ptr++;
        }
        *ptr=0;
    }

    bool parse_map_line(char * full_line, uint64_t & num, symbol & name) {
        cut_off_comment(full_line);
        if(full_line[0]==0) {
            return false;
        }

        const char * ptr = full_line;
        if(!read_uint64(ptr, num)) {
            throw default_exception(default_exception::fmt(), 
                                    "number expected at line %d in file %s", m_current_line, m_current_file.c_str());
        }
        if(*ptr!=' ') {
            throw default_exception(default_exception::fmt(), 
                                    "' ' expected after the number at line %d in file %s", m_current_line, m_current_file.c_str());
        }
        ptr++;

        if(!m_use_map_names) {
            static symbol no_name("<names ignored>");
            name=no_name;
        }
        else {
            std::string rest_of_line(ptr);

            const char * cut_off_word = " SC_EXTERN ";
            size_t cut_off_pos = rest_of_line.find(cut_off_word);
            if(cut_off_pos!=std::string::npos) {
                rest_of_line = rest_of_line.substr(0, cut_off_pos);
            }

            cut_off_word = " _ZONE_";
            cut_off_pos = rest_of_line.find(cut_off_word);
            if(cut_off_pos!=std::string::npos) {
                rest_of_line = rest_of_line.substr(0, cut_off_pos);
            }

            const char * const ignored_suffix = "Constant ";
            const size_t ignored_suffix_len = 9;

            if(rest_of_line.size()>ignored_suffix_len && 
                    rest_of_line.substr(rest_of_line.size()-ignored_suffix_len)==ignored_suffix) {
                rest_of_line = rest_of_line.substr(0, rest_of_line.size()-ignored_suffix_len);
            }

            if(rest_of_line[rest_of_line.size()-1]==' ') {
                rest_of_line = rest_of_line.substr(0, rest_of_line.size()-1);
            }

            name = symbol(rest_of_line.c_str());
        }
        return true;
    }

    void parse_map_file(const std::string & fname) {
        SASSERT(file_exists(fname));

        IF_VERBOSE(10, verbose_stream() << "Parsing map file " << fname << "\n";);
        flet<std::string> flet_cur_file(m_current_file, fname);
        flet<unsigned> flet_cur_line(m_current_line, 0);

        std::string sort_name_str = get_file_name_without_extension(fname);
        symbol sort_name(sort_name_str.c_str());
        uint64_set & sort_elements = ensure_sort_content(sort_name);

        //std::ifstream stm(fname.c_str(), std::ios_base::binary);
        //SASSERT(!stm.fail());
        //line_reader rdr(stm);
        line_reader rdr(fname.c_str());
        while(!rdr.eof()) {
            m_current_line++;
            char * full_line = rdr.get_line();

            uint64_t num;
            symbol el_name;

            if(!parse_map_line(full_line, num, el_name)) {
                continue;
            }

            sort_elements.insert(num);
            
            if(m_use_map_names) {
                num2sym::entry * e = m_number_names.insert_if_not_there2(num, el_name);
                if(e->get_data().m_value!=el_name) {
                    warning_msg("mismatch of number names on line %d in file %s. old: \"%s\" new: \"%s\"", 
                        m_current_line, fname.c_str(), e->get_data().m_value.bare_str(), el_name.bare_str());
                }
            }
        }
    }
};

parser* parser::create(context& ctx, ast_manager& m) {
    return alloc(dparser, ctx, m);
}

wpa_parser * wpa_parser::create(context& ctx, ast_manager & ast_manager) {
    return alloc(wpa_parser_impl, ctx);
}

