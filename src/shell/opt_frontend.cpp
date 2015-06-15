
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<fstream>
#include<signal.h>
#include<time.h>
#include"opt_context.h"
#include"ast_util.h"
#include"arith_decl_plugin.h"
#include"gparams.h"
#include"timeout.h"
#include"reg_decl_plugins.h"

extern bool g_display_statistics;
static bool g_first_interrupt = true;
static opt::context* g_opt = 0;
static double g_start_time = 0;
static unsigned_vector g_handles;

class stream_buffer {
    std::istream & m_stream;
    int            m_val;
    unsigned       m_line;
public:    
    stream_buffer(std::istream & s):
        m_stream(s),
        m_line(0) {
        m_val = m_stream.get();
    }
    int  operator *() const { return m_val;}
    void operator ++() { m_val = m_stream.get(); }
    int ch() const { return m_val; }
    void next() { m_val = m_stream.get(); }
    bool eof() const { return ch() == EOF; }
    unsigned line() const { return m_line; }
    void skip_whitespace() {
        while ((ch() >= 9 && ch() <= 13) || ch() == 32) {
            if (ch() == 10) ++m_line;
            next(); 
        }
    }
    void skip_line() {
        while(true) {
            if (eof()) {
                return;
            }
            if (ch() == '\n') { 
                ++m_line;
                next();
                return; 
            }
            next();
        } 
    }

    bool parse_token(char const* token) {
        skip_whitespace();
        char const* t = token;
        while (ch() == *t) {
            next();
            ++t;
        }
        return 0 == *t;
   }

    int parse_int() {
        int     val = 0;
        bool    neg = false;
        skip_whitespace();
        
        if (ch() == '-') {
            neg = true;
            next();
        }
        else if (ch() == '+') {
            next();
        }        
        if (ch() < '0' || ch() > '9') {
            std::cerr << "(error line " << line() << " \"unexpected char: " << ((char)ch()) << "\" )\n";
            exit(3);
        }        
        while (ch() >= '0' && ch() <= '9') {
            val = val*10 + (ch() - '0');
            next();
        }
        return neg ? -val : val; 
    }
};

class wcnf {
    opt::context&  opt;
    ast_manager&   m;
    stream_buffer& in;

    app_ref read_clause(int& weight) {
        int     parsed_lit;
        int     var;    
        parsed_lit = in.parse_int();
        weight = parsed_lit;
        app_ref result(m), p(m);
        expr_ref_vector ors(m);
        while (true) { 
            parsed_lit = in.parse_int();
            if (parsed_lit == 0)
                break;
            var = abs(parsed_lit);
            p = m.mk_const(symbol(var), m.mk_bool_sort());
            if (parsed_lit < 0) p = m.mk_not(p);
            ors.push_back(p);
        }
        result = to_app(mk_or(m, ors.size(), ors.c_ptr()));
        return result;
    }
    
    void parse_spec(int& num_vars, int& num_clauses, int& max_weight) {
        in.parse_token("wcnf");
        num_vars = in.parse_int();
        num_clauses = in.parse_int();
        max_weight = in.parse_int();
    }

public:
    
    wcnf(opt::context& opt, stream_buffer& in): opt(opt), m(opt.get_manager()), in(in) {
        opt.set_clausal(true);
    }
    
    void parse() {
        int num_vars = 0, num_clauses = 0, max_weight = 0;
        while (true) {
            in.skip_whitespace();
            if (in.eof()) {
                break;
            }
            else if (*in == 'c') {
                in.skip_line();
            }
            else if (*in == 'p') {
                ++in;
                parse_spec(num_vars, num_clauses, max_weight);
            }
            else {
                int weight = 0;
                app_ref cls = read_clause(weight);
                if (weight == max_weight) {
                    opt.add_hard_constraint(cls);
                }
                else {
                    unsigned id = opt.add_soft_constraint(cls, rational(weight), symbol::null);
                    if (g_handles.empty()) {
                        g_handles.push_back(id);
                    }
                }
            }
        }
    }    
};


class opb {
    opt::context&  opt;
    ast_manager&   m;
    stream_buffer& in;
    arith_util     arith;

    app_ref parse_id() {
        bool negated = in.parse_token("~");
        if (!in.parse_token("x")) {
            std::cerr << "(error line " << in.line() << " \"unexpected char: " << ((char)in.ch()) << "\")\n";
            exit(3);
        }
        app_ref p(m);
        int id = in.parse_int();
        p = m.mk_const(symbol(id), m.mk_bool_sort());
        if (negated) p = m.mk_not(p);
        in.skip_whitespace();
        return p;
    }

    app_ref parse_ids() {
        app_ref result = parse_id();
        while (*in == '~' || *in == 'x') {            
            result = m.mk_and(result, parse_id());
        }
        return result;
    }

    rational parse_coeff_r() {
        in.skip_whitespace();
        svector<char> num;
        bool pos = true;
        if (*in == '-') pos = false, ++in;
        if (*in == '+') ++in;
        if (!pos) num.push_back('-');
        in.skip_whitespace();
        while ('0' <= *in && *in <='9') num.push_back(*in), ++in;
        num.push_back(0);
        return rational(num.c_ptr());
    }

    app_ref parse_coeff() {
        return app_ref(arith.mk_numeral(parse_coeff_r(), true), m);
    }
    
    app_ref parse_term() {        
        app_ref c = parse_coeff();
        app_ref e = parse_ids();
        return app_ref(m.mk_ite(e, c, arith.mk_numeral(rational(0), true)), m);
    }

    void parse_objective() {
        app_ref t = parse_term();
        while (!in.parse_token(";") && !in.eof()) {
            t = arith.mk_add(t, parse_term());
        }
        g_handles.push_back(opt.add_objective(t, false));
    }

    void parse_constraint() {
        app_ref t = parse_term();
        while (!in.eof()) {
            if (in.parse_token(">=")) {    
                t = arith.mk_ge(t, parse_coeff());
                in.parse_token(";");
                break;
            }
            if (in.parse_token("=")) {
                t = m.mk_eq(t, parse_coeff());
                in.parse_token(";");
                break;
            }            
            t = arith.mk_add(t, parse_term());
        }        
        opt.add_hard_constraint(t);
    }
public:
    opb(opt::context& opt, stream_buffer& in): 
        opt(opt), m(opt.get_manager()), 
        in(in), arith(m) {}

    void parse() {
        while (true) {
            in.skip_whitespace();
            if (in.eof()) {
                break;
            }
            else if (*in == '*') {
                in.skip_line();
            }
            else if (in.parse_token("min:")) {
                parse_objective();
            }
            else {
                parse_constraint();
            }
        }
    }
};



static void display_statistics() {
    if (g_display_statistics && g_opt) {
        ::statistics stats;
        g_opt->collect_statistics(stats);
        stats.display(std::cout);
        double end_time = static_cast<double>(clock());
        std::cout << "time:                " << (end_time - g_start_time)/CLOCKS_PER_SEC << " secs\n";
        for (unsigned i = 0; i < g_handles.size(); ++i) {
            expr_ref lo = g_opt->get_lower(g_handles[i]);
            expr_ref hi = g_opt->get_upper(g_handles[i]);
            if (lo == hi) {
                std::cout << "   " << lo << "\n";
            }
            else {
                std::cout << "  [" << lo << ":" << hi << "]\n";
            }
        }
    }    
}

static void on_ctrl_c(int) {
    if (g_opt && g_first_interrupt) {
        g_opt->set_cancel(true);
        g_first_interrupt = false;
    }
    else {
        signal (SIGINT, SIG_DFL);
        #pragma omp critical (g_display_stats) 
        {
            display_statistics();
        }
        raise(SIGINT);
    }
}

static void on_timeout() {
    #pragma omp critical (g_display_stats) 
    {
        display_statistics();
        exit(0);
    }
}

static unsigned parse_opt(std::istream& in, bool is_wcnf) {
    ast_manager m;
    reg_decl_plugins(m);
    opt::context opt(m);
    g_opt = &opt;
    params_ref p = gparams::get_module("opt");
    opt.updt_params(p);
    stream_buffer _in(in);
    if (is_wcnf) {
        wcnf wcnf(opt, _in);
        wcnf.parse();
    }
    else {
        opb opb(opt, _in);
        opb.parse();
    }
    try {
        lbool r = opt.optimize();
        switch (r) {
        case l_true:  std::cout << "sat\n"; break;
        case l_false: std::cout << "unsat\n"; break;
        case l_undef: std::cout << "unknown\n"; break;
        }
    }
    catch (z3_exception & ex) {
        std::cerr << ex.msg() << "\n";
    }
    #pragma omp critical (g_display_stats) 
    {
        display_statistics();
        register_on_timeout_proc(0);
        g_opt = 0;
    }    
    return 0;
}

unsigned parse_opt(char const* file_name, bool is_wcnf) {
    g_first_interrupt = true;
    g_start_time = static_cast<double>(clock());
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        return parse_opt(in, is_wcnf);
    }
    else {
        return parse_opt(std::cin, is_wcnf);
    }
}

