#include<vector>
#include<fstream>
#include<signal.h>
#include<time.h>
#include"z3++.h"
using namespace z3;

static char const* g_input_file = 0;
static bool g_display_statistics = false;
static bool g_first_interrupt = true;
static int g_timeout = 0;
static bool g_display_model = false;
static context* g_context = 0;
static optimize* g_opt = 0;
static double g_start_time = 0;
static std::vector<optimize::handle> g_handles;

class stream_buffer {
    std::istream & m_stream;
    int            m_val;
public:    
    stream_buffer(std::istream & s):
        m_stream(s) {
        m_val = m_stream.get();
    }
    int  operator *() const { return m_val;}
    void operator ++() { m_val = m_stream.get(); }
    int ch() const { return m_val; }
    void next() { m_val = m_stream.get(); }
    bool eof() const { return ch() == EOF; }
    void skip_whitespace() {
        while ((ch() >= 9 && ch() <= 13) || ch() == 32) {
            next(); 
        }
    }
    void skip_line() {
        while(true) {
            if (eof()) {
                return;
            }
            if (ch() == '\n') { 
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
            std::cerr << "(error, \"unexpected char: " << ((char)ch()) << "\")\n";
            exit(3);
        }
        
        while (ch() >= '0' && ch() <= '9') {
            val = val*10 + (ch() - '0');
            next();
        }

        return neg ? -val : val; 
    }



};

typedef stream_buffer Buffer;

class wcnf {
    context& ctx;
    optimize& opt;
    stream_buffer& in;

    z3::expr read_clause(unsigned& weight) {
        int     parsed_lit;
        int     var;    
        parsed_lit = in.parse_int();
        weight = static_cast<unsigned>(parsed_lit);
        expr result = ctx.bool_val(false);
        bool has_result = false;

        while (true) { 
            parsed_lit = in.parse_int();
            if (parsed_lit == 0)
                break;
            var = abs(parsed_lit);
            expr p = ctx.constant(ctx.int_symbol(var), ctx.bool_sort());
            if (parsed_lit < 0) p = !p;
            if (has_result) {
                result = result || p;
            }
            else {
                result = p;
                has_result = true;
            }
        }
        return result;
    }
    
    void parse_spec(int& num_vars, int& num_clauses, int& max_weight) {
        in.parse_token("wcnf");
        num_vars = in.parse_int();
        num_clauses = in.parse_int();
        max_weight = in.parse_int();
    }

public:
    
    wcnf(context& ctx, optimize& opt, stream_buffer& in): ctx(ctx), opt(opt), in(in) {}
    
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
                unsigned weight = 0;
                expr cls = read_clause(weight);
                if (weight == max_weight) {
                    opt.add(cls);
                }
                else {
                    optimize::handle h = opt.add(cls, weight);
                    if (g_handles.empty()) g_handles.push_back(h);
                }
            }
        }
    }    
};


class opb {
    context&       ctx;
    optimize&      opt;
    stream_buffer& in;

    expr parse_id() {
        bool negated = in.parse_token("~");
        if (!in.parse_token("x")) {
            std::cerr << "expecting x, got: " << ((char)(*in)) << "\n";
            exit(3);
        }
        int id = in.parse_int();
        expr p = ctx.constant(ctx.int_symbol(id), ctx.bool_sort());
        if (negated) p = !p;
        return p;
    }

    expr parse_ids() {
        expr result = parse_id();
        while (*in == '~' || *in == 'x') {            
            result = result && parse_id();
        }
        return result;
    }

    expr parse_coeff() {
        in.skip_whitespace();
        std::vector<char> num;
        bool pos = true;
        if (*in == '-') pos = false, ++in;
        if (*in == '+') ++in;
        if (!pos) num.push_back('-');
        in.skip_whitespace();
        while (*in >= '0' && *in <='9') num.push_back(*in), ++in;
        num.push_back(0);
        return ctx.int_val(&num[0]);
    }
    
    expr parse_term() {        
        expr c = parse_coeff();
        expr e = parse_ids();
        return ite(e, c, ctx.int_val(0));
    }

    void parse_objective() {
        expr t = parse_term();
        while (!in.parse_token(";") && !in.eof()) {
            t = t + parse_term();
        }
        g_handles.push_back(opt.minimize(t));
    }

    void parse_constraint() {
        expr t = parse_term();
        while (!in.eof()) {
            if (in.parse_token(">=")) {    
                expr c = parse_coeff();
                in.parse_token(";");
                t = t >= c;
                break;
            }
            if (in.parse_token("=")) {
                expr c = parse_coeff();
                in.parse_token(";");
                t = (t == c);
                break;
            }            
            t = t + parse_term();
        }        
        opt.add(t);
    }
public:
    opb(context& ctx, optimize& opt, stream_buffer& in): ctx(ctx), opt(opt), in(in) {}

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



void display_statistics() {
    if (g_display_statistics && g_opt) {
        std::cout << g_opt->statistics() << "\n";
        double end_time = static_cast<double>(clock());
        std::cout << "time:   " << (end_time - g_start_time)/CLOCKS_PER_SEC << " secs\n";
        for (size_t i = 0; i < g_handles.size(); ++i) {
            std::cout << "  [" << g_opt->lower(g_handles[i]) << ":" << g_opt->upper(g_handles[i]) << "]\n";
        }
    }    
}


void display_usage() {
    unsigned major, minor, build_number, revision_number;
    Z3_get_version(&major, &minor, &build_number, &revision_number);
    std::cout << "z3_opt [" << major << "." << minor << "." << build_number << "." << revision_number << "] (c) 2006-20**. Microsoft Corp.\n";
    std::cout << "Usage: z3_opt [options] [-file:]file\n";
    std::cout << "  -h, -?       prints this message.\n";
    std::cout << "  -st, -statistics display statistics.\n";
    std::cout << "  -t:timeout   set timeout (in second).\n";
    std::cout << "  -<param>:<value> configuration parameter and value.\n";
}


void parse_cmd_line_args(int argc, char ** argv) {
    g_input_file = 0;
    int i = 1;
    while (i < argc) {
        char* arg = argv[i];
        char * eq = 0;
        char * opt_arg = 0;
        if (arg[0] == '-' || arg[0] == '/') {
            ++arg;
            while (*arg == '-') {
                ++arg;
            }
            char * colon = strchr(arg, ':');
            if (colon) {
                opt_arg = colon + 1;
                *colon = 0;
            }
            if (!strcmp(arg,"h") || !strcmp(arg,"help") || !strcmp(arg,"?")) {
                display_usage();
                exit(0);
            }
            else if (!strcmp(arg,"st") || !strcmp(arg,"statistics")) {
                g_display_statistics = true;
            }
            else if (!strcmp(arg,"t") || !strcmp(arg,"timeout")) {
                if (!opt_arg) {
                    display_usage();
                    exit(0);
                }
                g_timeout = atoi(opt_arg);
            }
            else if (!strcmp(arg, "file")) {
                g_input_file = opt_arg;
            }
            else if (opt_arg && arg[0] != '"') {
                Z3_global_param_set(arg, opt_arg);
            }
            else {
                std::cerr << "parameter " << arg << " was not recognized\n";
                display_usage();
                exit(0);
            }
        }
        else {
            g_input_file = arg;
        }
        ++i;
    }

    if (!g_input_file) {
        display_usage();
        exit(0);
    }
}


static void on_ctrl_c(int) {
    if (g_context && g_first_interrupt) {
        Z3_interrupt(*g_context);
        g_first_interrupt = false;
    }
    else {
        signal (SIGINT, SIG_DFL);
        display_statistics();
        raise(SIGINT);
    }
}

bool ends_with(char const* filename, char const* suffix) {
    size_t l1 = strlen(filename);
    size_t l2 = strlen(suffix);
    if (l1 < l2) return false;
    filename += (l1 - l2);
    for (; *filename; ++filename, ++suffix) {
        if (*filename != *suffix) return false;
    }
    return true;
}

void main(int argc, char ** argv) {
    g_start_time = static_cast<double>(clock());
    signal(SIGINT, on_ctrl_c);

    parse_cmd_line_args(argc, argv);
    context ctx;
    optimize opt(ctx);
    g_context = &ctx;
    g_opt     = &opt;

    std::ifstream in(g_input_file);        
    if (!in.bad() && !in.fail()) {
        stream_buffer _in(in);
        if (ends_with(g_input_file, "wcnf")) {
            wcnf wcnf(ctx, opt, _in);
            wcnf.parse();
        }
        else if (ends_with(g_input_file, "opb")) {
            opb opb(ctx, opt, _in);
            opb.parse();
        }
        else {
            std::cout << "Suffix is not recognized: " << g_input_file << "\n";
            exit(3);
        }
    }
    else {
        std::cout << "Parsing file " << g_input_file << " failed\n";
    }

    check_result r = opt.check();
    std::cout << r << "\n";
    display_statistics();
    g_opt = 0;
    g_context = 0;
}
