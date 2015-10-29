
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include <string>
#include <cstring>
#include <list>
#include <vector>
#include <set>
#include <map>
#include <signal.h>
#include <time.h>
#include <iostream>
#include <fstream>
#include <limits>
#include <string.h>
#include <cstdlib>
#include "z3++.h"

struct alloc_region {
    std::list<char*> m_alloc;

    void * allocate(size_t s) {
        char * res = new char[s];
        m_alloc.push_back(res);
        return res;
    }

    ~alloc_region() {
        std::list<char*>::iterator it = m_alloc.begin(), end = m_alloc.end();
        for (; it != end; ++it) {
            delete *it;
        }
    }    
};

template<typename T>
class flet {
    T & m_ref;
    T   m_old;
public:
    flet(T& x, T const& y): m_ref(x), m_old(x) { x = y; }
    ~flet() { m_ref = m_old; }
};

struct symbol_compare {
    bool operator()(z3::symbol const& s1, z3::symbol const& s2) const {
        return s1 < s2;
    };
};


template <typename T>
struct symbol_table {
    typedef std::map<z3::symbol, T> map;
    map m_map;

    void insert(z3::symbol s, T val) {
        m_map.insert(std::pair<z3::symbol, T>(s, val));
    }

    bool find(z3::symbol const& s, T& val) { 
        typename map::iterator it = m_map.find(s);
        if (it == m_map.end()) {
            return false;
        }
        else {
            val = it->second;
            return true;
        }
    }    
};


typedef std::set<z3::symbol, symbol_compare> symbol_set;


struct named_formulas {
    std::vector<z3::expr>    m_formulas;
    std::vector<std::string> m_names;
    std::vector<std::string> m_files;
    bool                     m_has_conjecture;

    named_formulas(): m_has_conjecture(false) {}

    void push_back(z3::expr fml, char const * name, char const* file) {
        m_formulas.push_back(fml);
        m_names.push_back(name);
        m_files.push_back(file);
    }

    void set_has_conjecture() {
        m_has_conjecture = true;
    }

    bool has_conjecture() const {
        return m_has_conjecture;
    }
};

inline void * operator new(size_t s, alloc_region & r) { return r.allocate(s); }

inline void * operator new[](size_t s, alloc_region & r) { return r.allocate(s); }

inline void operator delete(void *, alloc_region & ) { /* do nothing */ }

inline void operator delete[](void *, alloc_region & ) { /* do nothing */ }

struct failure_ex {
    std::string msg;
    failure_ex(char const* m):msg(m) {}
};


extern char* tptp_lval[];
extern int yylex();

static char* strdup(alloc_region& r, char const* s) {
    size_t l = strlen(s) + 1;
    char* result = new (r) char[l];
    memcpy(result, s, l);
    return result;
}

class TreeNode {
    char const* m_symbol;
    int         m_symbol_index;
    TreeNode**  m_children;
    
public:
    TreeNode(alloc_region& r, char const* sym, 
             TreeNode* A, TreeNode* B, TreeNode* C, TreeNode* D, TreeNode* E,
             TreeNode* F, TreeNode* G, TreeNode* H, TreeNode* I, TreeNode* J):
        m_symbol(strdup(r, sym)),
        m_symbol_index(-1) {
        m_children = new (r) TreeNode*[10];
        m_children[0] = A;
        m_children[1] = B;
        m_children[2] = C;
        m_children[3] = D;
        m_children[4] = E;
        m_children[5] = F;
        m_children[6] = G;
        m_children[7] = H;
        m_children[8] = I;
        m_children[9] = J;

    }
        
    char const* symbol() const { return m_symbol; }
    TreeNode *const* children() const { return m_children; }
    TreeNode* child(unsigned i) const { return m_children[i]; }
    int index() const { return m_symbol_index; }

    void set_index(int idx) { m_symbol_index = idx; }
};

TreeNode* MkToken(alloc_region& r, char const* token, int symbolIndex) { 
    TreeNode* ss;
    char* symbol = tptp_lval[symbolIndex];
    ss = new (r) TreeNode(r, symbol, NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
    ss->set_index(symbolIndex);
    return ss; 
}


// ------------------------------------------------------
// Build Z3 formulas.

class env {
    z3::context&                  m_context;
    z3::expr_vector               m_bound;  // vector of bound constants.
    z3::sort                       m_univ;
    symbol_table<z3::func_decl>    m_decls;
    symbol_table<z3::sort>         m_defined_sorts;
    static std::vector<TreeNode*>*  m_nodes;    
    static alloc_region*                m_region;
    char const*                   m_filename;


    enum binary_connective {
        IFF,
        IMPLIES,
        IMPLIED,
        LESS_TILDE_GREATER,
        TILDE_VLINE        
    };

    void mk_error(TreeNode* f, char const* msg) {
        std::ostringstream strm;
        strm << "expected: " << msg << "\n";
        strm << "got: " << f->symbol();
        throw failure_ex(strm.str().c_str());
    }

    void mk_not_handled(TreeNode* f, char const* msg) {
        std::ostringstream strm;
        strm << "Construct " << f->symbol() << " not handled: " << msg;
        throw failure_ex(strm.str().c_str());
    }

    void mk_input(TreeNode* f, named_formulas& fmls) {
        if (!strcmp(f->symbol(),"annotated_formula")) {
            mk_annotated_formula(f->child(0), fmls);
        }
        else if (!strcmp(f->symbol(),"include")) {
            mk_include(f->child(2), f->child(3), fmls);
        }
        else {
            mk_error(f, "annotated formula or include");
        }
    }

    void mk_annotated_formula(TreeNode* f, named_formulas& fmls) {
        if (!strcmp(f->symbol(),"fof_annotated")) {
            fof_annotated(f->child(2), f->child(4), f->child(6), f->child(7), fmls);            
        }
        else if (!strcmp(f->symbol(),"tff_annotated")) {
            fof_annotated(f->child(2), f->child(4), f->child(6), f->child(7), fmls);            
        }
        else if (!strcmp(f->symbol(),"cnf_annotated")) {
            cnf_annotated(f->child(2), f->child(4), f->child(6), f->child(7), fmls);
        }
        else if (!strcmp(f->symbol(),"thf_annotated")) {
            mk_error(f, "annotated formula (not thf)");
        }
        else {
            mk_error(f, "annotated formula");
        }
    }

    void check_arity(unsigned num_args, unsigned arity) {
        if (num_args != arity) {
            throw failure_ex("arity missmatch");
        }
    }

    void mk_include(TreeNode* file_name, TreeNode* formula_selection, named_formulas& fmls) {
        char const* fn = file_name->child(0)->symbol();
        TreeNode* name_list = formula_selection->child(2);
        if (name_list && !strcmp("null",name_list->symbol())) {            
            name_list = 0;
        }
        std::string inc_name;
        bool f_exists = false;
        for (unsigned i = 1; !f_exists && i <= 3; ++i) {
            inc_name.clear();
            f_exists = mk_filename(fn, i, inc_name);
            
        }
        if (!f_exists) {
            inc_name.clear();
            f_exists = mk_env_filename(fn, inc_name);            
        }
        if (!f_exists) {
            inc_name = fn;
        }
        
        parse(inc_name.c_str(), fmls);
        while (name_list) {
            return mk_error(name_list, "name list (not handled)");
            //char const* name = name_list->child(0)->symbol();
            name_list = name_list->child(2);            
        }
    }

#define CHECK(_node_) if (0 != strcmp(_node_->symbol(),#_node_)) return mk_error(_node_,#_node_); 

    const char* get_name(TreeNode* name) {
        if (!name->child(0)) {
            mk_error(name, "node with a child");
        }
        if (!name->child(0)->child(0)) {
            return name->child(0)->symbol();
        }
        return name->child(0)->child(0)->symbol();        
    }

    z3::expr mk_forall(z3::expr_vector& bound, z3::expr body) {
        return mk_quantifier(true, bound, body);
    }

    z3::expr mk_quantifier(bool is_forall, z3::expr_vector& bound, z3::expr body) {
        Z3_app* vars = new Z3_app[bound.size()];
        for (unsigned i = 0; i < bound.size(); ++i) {
            vars[i] = (Z3_app) bound[i];
        }
        Z3_ast r = Z3_mk_quantifier_const(m_context, is_forall, 1, bound.size(), vars, 0, 0, body);
        delete[] vars;
        return z3::expr(m_context, r);
    }
    
    void cnf_annotated(TreeNode* name, TreeNode* formula_role, TreeNode* formula, TreeNode* annotations, named_formulas& fmls) {
        symbol_set st;
        get_cnf_variables(formula, st);
        symbol_set::iterator it = st.begin(), end = st.end();
        std::vector<z3::symbol>  names;
        m_bound.resize(0);
        for(; it != end; ++it) {
            names.push_back(*it);
            m_bound.push_back(m_context.constant(names.back(), m_univ));
        }
        z3::expr r(m_context);
        cnf_formula(formula, r);
        if (!m_bound.empty()) {
            r = mk_forall(m_bound, r);
        }
        char const* role = formula_role->child(0)->symbol();
        if (!strcmp(role,"conjecture")) {
            fmls.set_has_conjecture();
            r = !r;
        }
        fmls.push_back(r, get_name(name), m_filename);
        m_bound.resize(0);
    }

    void cnf_formula(TreeNode* formula, z3::expr& r) {
        std::vector<z3::expr> disj;
        if (formula->child(1)) {
            disjunction(formula->child(1), disj);
        }
        else {
            disjunction(formula->child(0), disj);
        }
        if (disj.size() > 0) {
            r = disj[0];
        }
        else {
            r = m_context.bool_val(false);
        }
        for (unsigned i = 1; i < disj.size(); ++i) {
            r = r || disj[i];
        }
    }

    void disjunction(TreeNode* d, std::vector<z3::expr>& r) {
        z3::expr lit(m_context);
        if (d->child(2)) {
            disjunction(d->child(0), r);
            literal(d->child(2), lit);
            r.push_back(lit);
        }
        else {
            literal(d->child(0), lit);
            r.push_back(lit);
        }
    }

    void literal(TreeNode* l, z3::expr& lit) {
        if (!strcmp(l->child(0)->symbol(),"~")) {
            fof_formula(l->child(1), lit);
            lit = !lit;
        }
        else {
            fof_formula(l->child(0), lit);
        }
    }

    void fof_annotated(TreeNode* name, TreeNode* formula_role, TreeNode* formula, TreeNode* annotations, named_formulas& fmls) {
        z3::expr fml(m_context);
        //CHECK(fof_formula);
        CHECK(formula_role);
        fof_formula(formula->child(0), fml);
        char const* role = formula_role->child(0)->symbol();
        if (!strcmp(role,"conjecture")) {
            fmls.set_has_conjecture();
            fmls.push_back(!fml, get_name(name), m_filename);
        }
        else if (!strcmp(role,"type")) {
        }
        else {
            fmls.push_back(fml, get_name(name), m_filename);
        }
    }

    void fof_formula(TreeNode* f, z3::expr& fml) {
        z3::expr f1(m_context);
        char const* name = f->symbol();
        if (!strcmp(name,"fof_logic_formula") ||
            !strcmp(name,"fof_binary_assoc") ||
            !strcmp(name,"fof_binary_formula") ||
            !strcmp(name,"tff_logic_formula") ||
            !strcmp(name,"tff_binary_assoc") ||
            !strcmp(name,"tff_binary_formula") ||
            !strcmp(name,"atomic_formula") ||
            !strcmp(name,"defined_atomic_formula")) {
            fof_formula(f->child(0), fml);
        }
        else if (!strcmp(name, "fof_sequent") ||
            !strcmp(name, "tff_sequent")) {
            fof_formula(f->child(0), f1);
            fof_formula(f->child(2), fml);
            fml = implies(f1, fml);
        }
        else if (!strcmp(name, "fof_binary_nonassoc") ||
            !strcmp(name, "tff_binary_nonassoc")) {
            fof_formula(f->child(0), f1);
            fof_formula(f->child(2), fml);
            //SASSERT(!strcmp("binary_connective",f->child(1)->symbol()));
            char const* conn = f->child(1)->child(0)->symbol();
            if (!strcmp(conn, "<=>")) {
                fml = (f1 == fml);
            }
            else if (!strcmp(conn, "=>")) {
                fml = implies(f1, fml);
            }
            else if (!strcmp(conn, "<=")) {
                fml = implies(fml, f1);
            }
            else if (!strcmp(conn, "<~>")) {
                fml = ! (f1 == fml);
            }
            else if (!strcmp(conn, "~|")) {
                fml = !(f1 || fml);
            }
            else if (!strcmp(conn, "~&")) {
                fml = ! (f1 && fml);
            }
            else {
                mk_error(f->child(1)->child(0), "connective");            
            }
        }
        else if (!strcmp(name,"fof_or_formula") ||
            !strcmp(name,"tff_or_formula")) {
            fof_formula(f->child(0), f1);
            fof_formula(f->child(2), fml);
            fml = f1 || fml;
        }
        else if (!strcmp(name,"fof_and_formula") ||
            !strcmp(name,"tff_and_formula")) {
            fof_formula(f->child(0), f1);
            fof_formula(f->child(2), fml);
            fml = f1 && fml;
        }
        else if (!strcmp(name,"fof_unitary_formula") ||
            !strcmp(name,"tff_unitary_formula")) {
            if (f->child(1)) {
                // parenthesis
                fof_formula(f->child(1), fml);
            }
            else {
                fof_formula(f->child(0), fml);
            }
        }
        else if (!strcmp(name,"fof_quantified_formula") ||
            !strcmp(name,"tff_quantified_formula")) {
            fof_quantified_formula(f->child(0), f->child(2), f->child(5), fml);
        }
        else if (!strcmp(name,"fof_unary_formula") ||
            !strcmp(name,"tff_unary_formula")) {
            if (!f->child(1)) {
                fof_formula(f->child(0), fml);
            }
            else {
                fof_formula(f->child(1), fml);
                char const* conn = f->child(0)->child(0)->symbol();
                if (!strcmp(conn,"~")) {
                    fml = !fml;
                }
                else {
                    mk_error(f->child(0)->child(0), "fof_unary_formula");
                }
            }
        }
        else if (!strcmp(name,"fof_let")) {
            mk_let(f->child(2), f->child(5), fml);
        }
        else if (!strcmp(name,"variable")) {
            char const* v  = f->child(0)->symbol();
            if (!find_bound(v, fml)) {
                mk_error(f->child(0), "variable");
            }
        }
        else if (!strcmp(name,"fof_conditional")) {
            z3::expr f2(m_context);
            fof_formula(f->child(2), f1);
            fof_formula(f->child(4), f2);
            fof_formula(f->child(6), fml);
            fml = ite(f1, f2, fml);
        }
        else if (!strcmp(name,"plain_atomic_formula") ||             
            !strcmp(name,"defined_plain_formula") ||
            !strcmp(name,"system_atomic_formula")) {
            z3::sort srt(m_context.bool_sort());
            term(f->child(0), srt, fml);
        }
        else if (!strcmp(name,"defined_infix_formula") ||
            !strcmp(name,"fol_infix_unary")) {
            z3::expr t1(m_context), t2(m_context);
            term(f->child(0), m_univ, t1);
            term(f->child(2), m_univ, t2);
            TreeNode* inf = f->child(1);
            while (inf && strcmp(inf->symbol(),"=") && strcmp(inf->symbol(),"!=")) {
                inf = inf->child(0);
            }
            if (!inf) {
                mk_error(f->child(1), "defined_infix_formula");
            }
            char const* conn = inf->symbol();
            if (!strcmp(conn,"=")) {
                fml = t1 == t2;
            }
            else if (!strcmp(conn,"!=")) {
                fml = ! (t1 == t2);
            }
            else {
                mk_error(inf, "defined_infix_formula");
            }
        }
        else if (!strcmp(name, "tff_typed_atom")) {
            while (!strcmp(f->child(0)->symbol(),"(")) {
                f = f->child(1);
            }
            char const* id = 0;
            z3::sort s(m_context);
            z3::sort_vector sorts(m_context);

            mk_id(f->child(0), id);
            if (is_ttype(f->child(2))) {
                s = mk_sort(id);
                m_defined_sorts.insert(symbol(id), s);
            }
            else {
                mk_mapping_sort(f->child(2), sorts, s);
                z3::func_decl fd(m_context.function(id, sorts, s));
                m_decls.insert(symbol(id), fd);
            }
        }
        else {
            mk_error(f, "fof_formula");
        }
    }

    bool is_ttype(TreeNode* t) {
        char const* name = t->symbol();
        if (!strcmp(name,"atomic_defined_word")) {
            return !strcmp("$tType", t->child(0)->symbol());
        }
        return false;
    }

    void fof_quantified_formula(TreeNode* fol_quantifier, TreeNode* vl, TreeNode* formula, z3::expr& fml) {
        unsigned l = m_bound.size();       
        mk_variable_list(vl);
        fof_formula(formula, fml);
        bool is_forall = !strcmp(fol_quantifier->child(0)->symbol(),"!");
        z3::expr_vector bound(m_context);
        for (unsigned i = l; i < m_bound.size(); ++i) {
            bound.push_back(m_bound[i]);
        }
        fml = mk_quantifier(is_forall, bound, fml);
        m_bound.resize(l);
    }

    void mk_variable_list(TreeNode* variable_list) {
        while (variable_list) {
            TreeNode* var = variable_list->child(0);
            if (!strcmp(var->symbol(),"tff_variable")) {
                var = var->child(0);
            }
            if (!strcmp(var->symbol(),"variable")) {
                char const* name = var->child(0)->symbol();
                m_bound.push_back(m_context.constant(name, m_univ));
            }
            else if (!strcmp(var->symbol(),"tff_typed_variable")) {
                z3::sort s(m_context);
                char const* name = var->child(0)->child(0)->symbol();
                mk_sort(var->child(2), s);
                m_bound.push_back(m_context.constant(name, s));
            }
            else {
                mk_error(var, "variable_list");
            }
            variable_list = variable_list->child(2);
        }
    }

    void mk_sort(TreeNode* t, z3::sort& s) {
        char const* name = t->symbol();
        if (!strcmp(name, "tff_atomic_type") ||
            !strcmp(name, "defined_type")) {
            mk_sort(t->child(0), s);
        }
        else if (!strcmp(name, "atomic_defined_word")) {
            z3::symbol sname = symbol(t->child(0)->symbol());
            z3::sort srt(m_context);
            if (!strcmp("$tType", t->child(0)->symbol())) {
                char const* id = 0;
                s = mk_sort(id);
                m_defined_sorts.insert(symbol(id), s);
            }
            else if (m_defined_sorts.find(sname, srt)) {
                s = srt;
            }
            else {
                s = mk_sort(sname);
                if (sname == symbol("$rat")) {
                    throw failure_ex("rational sorts are not handled\n");
                }                
                mk_error(t, sname.str().c_str());
            }
        }
        else if (!strcmp(name,"atomic_word")) {
            name = t->child(0)->symbol();
            z3::symbol symname = symbol(name);
            s = mk_sort(symname);
        }
        else {
            mk_error(t, "sort");
        }
    }

    void mk_mapping_sort(TreeNode* t, z3::sort_vector& domain, z3::sort& s) {
        char const* name = t->symbol();
        //char const* id = 0;
        if (!strcmp(name,"tff_top_level_type")) {
            mk_mapping_sort(t->child(0), domain, s);
        }
        else if (!strcmp(name,"tff_atomic_type")) {
            mk_sort(t->child(0), s);
        }            
        else if (!strcmp(name,"tff_mapping_type")) {
            TreeNode* t1 = t->child(0);
            if (t1->child(1)) {
                mk_xprod_sort(t1->child(1), domain);
            }
            else {
                mk_sort(t1->child(0), s);
                domain.push_back(s);
            }
            mk_sort(t->child(2), s);
        }
        else {
            mk_error(t, "mapping sort");
        }
    }

    void  mk_xprod_sort(TreeNode* t, z3::sort_vector& sorts) {        
        char const* name = t->symbol();
        z3::sort s1(m_context), s2(m_context);
        if (!strcmp(name, "tff_atomic_type")) {
            mk_sort(t->child(0), s1);
            sorts.push_back(s1);
        }
        else if (!strcmp(name, "tff_xprod_type")) {
            name = t->child(0)->symbol();
            if (!strcmp(name, "tff_atomic_type") ||
                !strcmp(name, "tff_xprod_type")) {
                mk_xprod_sort(t->child(0), sorts);
                mk_xprod_sort(t->child(2), sorts);
            }
            else if (t->child(1)) {
                mk_xprod_sort(t->child(1), sorts);
            }
            else {
                mk_error(t, "xprod sort");
            }
        }
        else {
            mk_error(t, "xprod sort");
        }
    }

    void term(TreeNode* t, z3::sort const& s, z3::expr& r) {
        char const* name = t->symbol();
        if (!strcmp(name, "defined_plain_term") ||
            !strcmp(name, "system_term") ||
            !strcmp(name, "plain_term")) {
            if (!t->child(1)) {
                term(t->child(0), s, r);
            }
            else {
                apply_term(t->child(0), t->child(2), s, r);
            }
        }
        else if (!strcmp(name, "constant") ||
            !strcmp(name, "functor") ||
            !strcmp(name, "defined_plain_formula") ||
            !strcmp(name, "defined_functor") ||
            !strcmp(name, "defined_constant") ||
            !strcmp(name, "system_constant") ||
            !strcmp(name, "defined_atomic_term") ||
            !strcmp(name, "system_functor") ||
            !strcmp(name, "function_term") ||
            !strcmp(name, "term") ||
            !strcmp(name, "defined_term")) {
            term(t->child(0), s, r);
        }


        else if (!strcmp(name, "defined_atom")) {
            char const* name0 = t->child(0)->symbol();
            if (!strcmp(name0,"number")) {
                name0 = t->child(0)->child(0)->symbol();
                char const* per = strchr(name0, '.');
                bool is_real = 0 != per;
                bool is_rat  = 0 != strchr(name0, '/');
                bool is_int  = !is_real && !is_rat;
                if (is_int) {
                    r = m_context.int_val(name0);
                }
                else {
                    r = m_context.real_val(name0);
                }
            }
            else if (!strcmp(name0, "distinct_object")) {
                throw failure_ex("distinct object not handled");
            }
            else {
                mk_error(t->child(0), "number or distinct object");
            }
        }
        else if (!strcmp(name, "atomic_defined_word")) {
            char const* ch = t->child(0)->symbol();
            z3::symbol s = symbol(ch);
            z3::func_decl fd(m_context);
            if (!strcmp(ch, "$true")) {
                r = m_context.bool_val(true);
            }
            else if (!strcmp(ch, "$false")) {
                r = m_context.bool_val(false);
            }
            else if (m_decls.find(s, fd)) {
                r = fd(0,0);
            }
            else {
                mk_error(t->child(0), "atomic_defined_word");
            }
        }
        else if (!strcmp(name, "atomic_word")) {
            z3::func_decl f(m_context);
            z3::symbol sym = symbol(t->child(0)->symbol());
            if (m_decls.find(sym, f)) {
                r = f(0,0);
            }
            else {
                r = m_context.constant(sym, s);
            }
        }
        else if (!strcmp(name, "variable")) {
            char const* v = t->child(0)->symbol();
            if (!find_bound(v, r)) {
                mk_error(t->child(0), "variable not bound");
            }
        }
        else {
            mk_error(t, "term not recognized");
        }
    }

    void apply_term(TreeNode* f, TreeNode* args, z3::sort const& s, z3::expr& r) {
        z3::expr_vector terms(m_context);
        z3::sort_vector sorts(m_context);
        mk_args(args, terms);
        for (unsigned i = 0; i < terms.size(); ++i) {
            sorts.push_back(terms[i].get_sort());
        }
        if (!strcmp(f->symbol(),"functor") ||
            !strcmp(f->symbol(),"system_functor") ||
            !strcmp(f->symbol(),"defined_functor")) {
            f = f->child(0);
        }
        bool atomic_word = !strcmp(f->symbol(),"atomic_word");
        if (atomic_word ||
            !strcmp(f->symbol(),"atomic_defined_word") ||
            !strcmp(f->symbol(),"atomic_system_word")) {
            char const* ch = f->child(0)->symbol();
            z3::symbol fn = symbol(ch);   
            z3::func_decl fun(m_context);
            z3::context& ctx = r.ctx();
            if (!strcmp(ch,"$less")) {
                check_arity(terms.size(), 2);
                r = terms[0] < terms[1]; 
            }
            else if (!strcmp(ch,"$lesseq")) {
                check_arity(terms.size(), 2);
                r = terms[0] <= terms[1];
            }
            else if (!strcmp(ch,"$greater")) {
                check_arity(terms.size(), 2);
                r = terms[0] > terms[1];
            }
            else if (!strcmp(ch,"$greatereq")) {
                check_arity(terms.size(), 2);
                r = terms[0] >= terms[1];
            }
            else if (!strcmp(ch,"$uminus")) {
                check_arity(terms.size(), 1);
                r = -terms[0];
            }
            else if (!strcmp(ch,"$sum")) {
                check_arity(terms.size(), 2);
                r = terms[0] + terms[1];
            }
            else if (!strcmp(ch,"$plus")) {
                check_arity(terms.size(), 2);
                r = terms[0] + terms[1];
            }
            else if (!strcmp(ch,"$difference")) {
                check_arity(terms.size(), 2);
                r = terms[0] - terms[1];
            }
            else if (!strcmp(ch,"$product")) {
                check_arity(terms.size(), 2);
                r = terms[0] * terms[1];
            }
            else if (!strcmp(ch,"$quotient")) {
                check_arity(terms.size(), 2);
                r = terms[0] / terms[1];
            }
            else if (!strcmp(ch,"$quotient_e")) {
                check_arity(terms.size(), 2);
                r = terms[0] / terms[1];
            }
            else if (!strcmp(ch,"$distinct")) {
                if (terms.size() == 2) {
                    r = terms[0] != terms[1];
                }
                else {
                    r = distinct(terms);
                }
            }
            else if (!strcmp(ch,"$floor") || !strcmp(ch,"$to_int")) {
                check_arity(terms.size(), 1);
                r = to_real(to_int(terms[0]));
            }
            else if (!strcmp(ch,"$to_real")) {
                check_arity(terms.size(), 1);
                r = to_real(terms[0]);
            }
            else if (!strcmp(ch,"$is_int")) {
                check_arity(terms.size(), 1);
                r = z3::expr(ctx, Z3_mk_is_int(ctx, terms[0]));
            }            
            else if (!strcmp(ch,"$true")) {
                r = ctx.bool_val(true);
            }
            else if (!strcmp(ch,"$false")) {
                r = ctx.bool_val(false);
            }
            // ceiling(x) = -floor(-x)
            else if (!strcmp(ch,"$ceiling")) {
                check_arity(terms.size(), 1);
                r = ceiling(terms[0]);
            }
            // truncate - The nearest integral value with magnitude not greater than the absolute value of the argument. 
            // if x >= 0 floor(x) else ceiling(x)
            else if (!strcmp(ch,"$truncate")) {
                check_arity(terms.size(), 1);    
                r = truncate(terms[0]);
            }
            //  The nearest integral number to the argument. When the argument 
            // is halfway between two integral numbers, the nearest even integral number to the argument.  
            else if (!strcmp(ch,"$round")) {
                check_arity(terms.size(), 1); 
                z3::expr t = terms[0];
                z3::expr i = to_int(t);
                z3::expr i2 = i + ctx.real_val(1,2);
                r = ite(t > i2, i + 1, ite(t == i2, ite(is_even(i), i, i+1), i));
            }
            // $quotient_e(N,D) - the Euclidean quotient, which has a non-negative remainder. 
            // If D is positive then $quotient_e(N,D) is the floor (in the type of N and D) of 
            // the real division N/D, and if D is negative then $quotient_e(N,D) is the ceiling of N/D.

            // $quotient_t(N,D) - the truncation of the real division N/D. 
            else if (!strcmp(ch,"$quotient_t")) {
                check_arity(terms.size(), 2); 
                r = truncate(terms[0] / terms[1]);
            }
            // $quotient_f(N,D) - the floor of the real division N/D. 
            else if (!strcmp(ch,"$quotient_f")) {
                check_arity(terms.size(), 2); 
                r = to_real(to_int(terms[0] / terms[1]));
            }
            // For t in {$int,$rat, $real}, x in {e, t,f}, $quotient_x and $remainder_x are related by
            // ! [N:t,D:t] : $sum($product($quotient_x(N,D),D),$remainder_x(N,D)) = N 
            // For zero divisors the result is not specified. 
            else if (!strcmp(ch,"$remainder_t")) {
                mk_not_handled(f, ch);
            }
            else if (!strcmp(ch,"$remainder_e")) {
                check_arity(terms.size(), 2); 
                r = z3::expr(ctx, Z3_mk_mod(ctx, terms[0], terms[1]));
            }
            else if (!strcmp(ch,"$remainder_r")) {
                mk_not_handled(f, ch);
            }
            else if (!strcmp(ch,"$to_rat") ||
                     !strcmp(ch,"$is_rat")) {
                mk_not_handled(f, ch);
            }
            else if (m_decls.find(fn, fun)) {
                r = fun(terms);
            }
            else if (true) {
                z3::func_decl func(m_context);
                func = m_context.function(fn, sorts, s);
                r = func(terms);
            }
            else {
                mk_error(f->child(0), "atomic, defined or system word");
            }      
            return;
        }
        mk_error(f, "function");
    }

    z3::expr to_int(z3::expr e) {
        return z3::expr(e.ctx(), Z3_mk_real2int(e.ctx(), e));
    }

    z3::expr to_real(z3::expr e) {
        return z3::expr(e.ctx(), Z3_mk_int2real(e.ctx(), e));
    }

    z3::expr ceiling(z3::expr e) {
        return -to_real(to_int(-e));
    }

    z3::expr is_even(z3::expr e) {
        z3::context& ctx = e.ctx();
        z3::expr two = ctx.int_val(2);
        z3::expr m = z3::expr(ctx, Z3_mk_mod(ctx, e, two));
        return m == 0;
    }

    z3::expr truncate(z3::expr e) {
        return ite(e >= 0, to_int(e), ceiling(e));
    }

    bool check_app(z3::func_decl& f, unsigned num, z3::expr const* args) {
        if (f.arity() == num) {
            for (unsigned i = 0; i < num; ++i) {
                if (!eq(args[i].get_sort(), f.domain(i))) {
                    return false;
                }
            }
            return true;
        }
        else {
            return true;
        }
    }

    void mk_args(TreeNode* args, z3::expr_vector& result) {
        z3::expr t(m_context);
        while (args) {
            term(args->child(0), m_univ, t);
            result.push_back(t);
            args = args->child(2);
        }
    }


    bool find_bound(char const* v, z3::expr& b) {
        for (unsigned l = m_bound.size(); l > 0; ) {
            --l;
            if (v == m_bound[l].decl().name().str()) {
                b = m_bound[l];
                return true;
            }
        }
        return false;
    }

    void mk_id(TreeNode* f, char const*& sym) {
        char const* name = f->symbol();
        if (!strcmp(name, "tff_untyped_atom") ||
            !strcmp(name, "functor") ||
            !strcmp(name, "system_functor")) {
             mk_id(f->child(0), sym);
        }
        else if (!strcmp(name, "atomic_word") ||
            !strcmp(name, "atomic_system_word")) {
            sym = f->child(0)->symbol();
        }
        else {
            mk_error(f, "atom");
        }
    }

    void mk_let(TreeNode* let_vars, TreeNode* f, z3::expr& fml) {        
        mk_error(f, "let construct is not handled");
    }

    FILE* open_file(char const* filename) {
        FILE* fp = 0;
#ifdef _WINDOWS
        if (0 > fopen_s(&fp, filename, "r") || fp == 0) {
            fp = 0;
        }
#else
        fp = fopen(filename, "r");
#endif
        return fp;
    }

    bool is_sep(char s) {
        return s == '/' || s == '\\';
    }

    void add_separator(const char* rel_name, std::string& inc_name) {
        size_t sz = inc_name.size();
        if (sz == 0) return;
        if (sz > 0 && is_sep(inc_name[sz-1])) return;
        if (is_sep(rel_name[0])) return;
        inc_name += "/";
    }

    void append_rel_name(const char * rel_name, std::string& inc_name) {
        if (rel_name[0] == '\'') {
            add_separator(rel_name+1, inc_name);
            inc_name.append(rel_name+1);
            inc_name.resize(inc_name.size()-1);
        }
        else {
            add_separator(rel_name, inc_name);
            inc_name.append(rel_name);
        }
    }

    bool mk_filename(const char *rel_name, unsigned num_sep, std::string& inc_name) {
        unsigned sep1 = 0, sep2 = 0, sep3 = 0;
        size_t len = strlen(m_filename);
        for (unsigned i = 0; i < len; ++i) {
            if (is_sep(m_filename[i])) {
                sep3 = sep2;
                sep2 = sep1;
                sep1 = i;
            }
        }
        if ((num_sep == 3) && sep3 > 0) {
            inc_name.append(m_filename,sep3+1);
        }
        if ((num_sep == 2) && sep2 > 0) {
            inc_name.append(m_filename,sep2+1);
        }
        if ((num_sep == 1) && sep1 > 0) {
            inc_name.append(m_filename,sep1+1);
        }
        append_rel_name(rel_name, inc_name);
        return file_exists(inc_name.c_str());        
    }

    bool file_exists(char const* filename) {
        FILE* fp = open_file(filename);
        if (!fp) {
            return false;
        }
        fclose(fp);
        return true;
    }

    bool mk_env_filename(const char* rel_name, std::string& inc_name) {
#ifdef _WINDOWS
        char buffer[1024];
        size_t sz;
        errno_t err = getenv_s( 
            &sz,
            buffer,
            "$TPTP");
        if (err != 0) {
            return false;
        }        
#else
        char const* buffer = getenv("$TPTP");
        if (!buffer) {
            return false;
        }
#endif
        inc_name = buffer;
        append_rel_name(rel_name, inc_name);
        return file_exists(inc_name.c_str());
    }

    void get_cnf_variables(TreeNode* t, symbol_set& symbols) {
        std::vector<TreeNode*> todo;
        todo.push_back(t);
        while (!todo.empty()) {
            t = todo.back();
            todo.pop_back();
            if (!t) continue;
            if (!strcmp(t->symbol(),"variable")) {
                z3::symbol sym = symbol(t->child(0)->symbol());
                symbols.insert(sym);
            }
            else {
                for (unsigned i = 0; i < 10; ++i) {
                    todo.push_back(t->child(i));
                }                
            }            
        }
    }

    z3::symbol symbol(char const* s) {
        return m_context.str_symbol(s);
    }

    z3::sort mk_sort(char const* s) {
        return m_context.uninterpreted_sort(s);
    }

    z3::sort mk_sort(z3::symbol& s) {
        return m_context.uninterpreted_sort(s);
    }
    
public:
    env(z3::context& ctx):
        m_context(ctx),
        m_bound(ctx),
        m_univ(mk_sort("$i")),
        m_filename(0) {
        m_nodes = 0;
        m_region = new alloc_region();
        m_defined_sorts.insert(symbol("$i"),    m_univ);
        m_defined_sorts.insert(symbol("$o"),    m_context.bool_sort());
        m_defined_sorts.insert(symbol("$real"), m_context.real_sort());
        m_defined_sorts.insert(symbol("$int"),  m_context.int_sort());

    }

    ~env() {
        delete m_region;
        m_region = 0;        
    }
    void parse(const char* filename, named_formulas& fmls);
    static void register_node(TreeNode* t) { m_nodes->push_back(t); }
    static alloc_region& r() { return *m_region; }
};    

std::vector<TreeNode*>* env::m_nodes = 0;
alloc_region* env::m_region = 0;

#  define P_USERPROC
#  define P_ACT(ss) if(verbose)printf("%7d %s\n",yylineno,ss);
#  define P_BUILD(sym,A,B,C,D,E,F,G,H,I,J) new (env::r()) TreeNode(env::r(), sym,A,B,C,D,E,F,G,H,I,J)
#  define P_TOKEN(tok,symbolIndex) MkToken(env::r(), tok,symbolIndex)
#  define P_PRINT(ss) env::register_node(ss) 


// ------------------------------------------------------
// created by YACC.
#include "tptp5.tab.c"

extern FILE* yyin;

    
void env::parse(const char* filename, named_formulas& fmls) {
    std::vector<TreeNode*> nodes;
    flet<char const*> fn(m_filename, filename);
    flet<std::vector<TreeNode*>*> fnds(m_nodes, &nodes);

    FILE* fp = open_file(filename);
    if (!fp) {
        std::stringstream strm;
        strm << "Could not open file " << filename << "\n";
        throw failure_ex(strm.str().c_str());
    }
    yyin = fp;
    int result = yyparse();
    fclose(fp);

    if (result != 0) {
        throw failure_ex("could not parse input");
    }

    for (unsigned i = 0; i < nodes.size(); ++i) {
        TreeNode* cl = nodes[i];
        if (cl) {
            mk_input(cl, fmls);
        }
    }

}

class pp_tptp {
    z3::context& ctx;
    std::vector<std::string>   names;
    std::vector<z3::sort>      sorts;
    std::vector<z3::func_decl> funs;
    std::vector<z3::expr>      todo;
    std::set<unsigned>         seen_ids;
    unsigned                   m_formula_id;
    unsigned                   m_node_number;
    std::map<unsigned, unsigned>            m_proof_ids;
    std::map<unsigned, std::set<unsigned> > m_proof_hypotheses;
    std::map<unsigned, unsigned>            m_axiom_ids;
    named_formulas*                         m_named_formulas;

public:
    pp_tptp(z3::context& ctx): ctx(ctx), m_formula_id(0) {}


    void display_func_decl(std::ostream& out, z3::func_decl& f) {
        std::string name = lower_case_fun(f.name());
        out << "tff(" << name << "_type, type, (\n   " << name << ": ";
        unsigned na = f.arity();
        switch(na) {
        case 0:
            break;
        case 1: {
            z3::sort s(f.domain(0));
            display_sort(out, s);
            out << " > ";
            break;
        }
        default:
            out << "( ";
            for (unsigned j = 0; j < na; ++j) {
                z3::sort s(f.domain(j));
                display_sort(out, s);
                if (j + 1 < na) {
                    out << " * ";
                }
            }
            out << " ) > ";
        }
        z3::sort srt(f.range());
        display_sort(out, srt);
        out << ")).\n";
    }

    void display_axiom(std::ostream& out, z3::expr e) {
        out << "tff(formula" << (++m_formula_id) << ", axiom,\n    ";
        display(out, e);
        out << ").\n";
    }

    void display(std::ostream& out, z3::expr e) {
        if (e.is_numeral()) {
            __int64 num, den;
            if (Z3_get_numeral_small(ctx, e, &num, &den)) {
                if (num < 0 && den == 1 && num != std::numeric_limits<__int64>::min()) {
                    out << "-" << (-num);
                    return;
                }
            }
            // potential incompatibility: prints negative numbers with a space.
            out << e;
        }
        else if (e.is_var()) {
            unsigned idx = Z3_get_index_value(ctx, e);
            out << names[names.size()-1-idx];
        }
        else if (e.is_app()) {
            switch(e.decl().decl_kind()) {
            case Z3_OP_TRUE:
                out << "$true";
                break;
            case Z3_OP_FALSE:
                out << "$false";
                break;
            case Z3_OP_AND:
                display_infix(out, "&", e);
                break;
            case Z3_OP_OR:
                display_infix(out, "|", e);
                break;
            case Z3_OP_IMPLIES:
                display_infix(out, "=>", e);
                break;
            case Z3_OP_NOT:
                out << "(~";
                display(out, e.arg(0));
                out << ")";
                break;
            case Z3_OP_EQ:
                if (e.arg(0).is_bool()) {
                    display_infix(out, "<=>", e);
                }
                else {
                    display_infix(out, "=", e);
                }
                break;
            case Z3_OP_IFF:
                display_infix(out, "<=>", e);
                break;
            case Z3_OP_XOR:
                display_infix(out, "<~>", e);
                break;
            case Z3_OP_MUL:  
                display_binary(out, "$product", e);
                break;               
            case Z3_OP_ADD:
                display_binary(out, "$sum", e);
                break;     
            case Z3_OP_SUB:
                display_prefix(out, "$difference", e); 
                break;     
            case Z3_OP_LE:
                display_prefix(out, "$lesseq", e);
                break;     
            case Z3_OP_GE:
                display_prefix(out, "$greatereq", e);
                break;     
            case Z3_OP_LT:
                display_prefix(out, "$less", e);
                break;     
            case Z3_OP_GT:
                display_prefix(out, "$greater", e);
                break;     
            case Z3_OP_UMINUS:
                display_prefix(out, "$uminus", e);
                break;            
            case Z3_OP_DIV:
                display_prefix(out, "$quotient", e);
                break;
            case Z3_OP_IS_INT:
                display_prefix(out, "$is_int", e);
                break;
            case Z3_OP_TO_REAL:
                display_prefix(out, "$to_real", e);
                break;
            case Z3_OP_TO_INT:
                display_prefix(out, "$to_int", e);
                break;
            case Z3_OP_IDIV:
                display_prefix(out, "$quotient_e", e);
                break;
            case Z3_OP_MOD:
                display_prefix(out, "$remainder_e", e);
                break;                
            case Z3_OP_ITE:
                display_prefix(out, e.is_bool()?"ite_f":"ite_t", e);
                break;
            case Z3_OP_DISTINCT:
                display_prefix(out, "$distinct", e);
                break;
            case Z3_OP_REM:
                throw failure_ex("rem is not handled");
                break;
            case Z3_OP_OEQ:
                display_prefix(out, "$oeq", e);
                break;
            default:
                display_app(out, e);
                break;
            }
        }
        else if (e.is_quantifier()) {
            Z3_bool is_forall = Z3_is_quantifier_forall(ctx, e);
            unsigned nb = Z3_get_quantifier_num_bound(ctx, e);

            out << (is_forall?"!":"?") << "[";
            for (unsigned i = 0; i < nb; ++i) {
                Z3_symbol n = Z3_get_quantifier_bound_name(ctx, e, i);
                names.push_back(upper_case_var(z3::symbol(ctx, n)));
                z3::sort srt(ctx, Z3_get_quantifier_bound_sort(ctx, e, i));
                out << names.back() << ": ";
                display_sort(out, srt);
                if (i + 1 < nb) {
                    out << ", ";
                }
            }
            out << "] : ";
            display(out, e.body());
            for (unsigned i = 0; i < nb; ++i) {
                names.pop_back();
            }
        }
    }

    void display_app(std::ostream& out, z3::expr e) {
        if (e.is_const()) {
            out << e;
            return;
        }
        out << lower_case_fun(e.decl().name()) << "(";
        unsigned n = e.num_args();
        for(unsigned i = 0; i < n; ++i) {
            display(out, e.arg(i));
            if (i + 1 < n) {
                out << ", ";
            }
        }
        out << ")";
    }

    void display_sort(std::ostream& out, z3::sort const& s) {
        if (s.is_int()) {
            out << "$int";
        }
        else if (s.is_real()) {
            out << "$real";
        }
        else if (s.is_bool()) {
            out << "$o";
        }
        else {
            out << s;
        }
    }

    void display_infix(std::ostream& out, char const* conn, z3::expr& e) {
        out << "(";
        unsigned sz = e.num_args();
        for (unsigned i = 0; i < sz; ++i) {
            display(out, e.arg(i));
            if (i + 1 < sz) {
                out << " " << conn << " ";
            }
        }
        out << ")";
    }

    void display_prefix(std::ostream& out, char const* conn, z3::expr& e) {
        out << conn << "(";
        unsigned sz = e.num_args();
        for (unsigned i = 0; i < sz; ++i) {
            display(out, e.arg(i));
            if (i + 1 < sz) {
                out << ", ";
            }
        }
        out << ")";
    }

    void display_binary(std::ostream& out, char const* conn, z3::expr& e) {
        out << conn << "(";
        unsigned sz = e.num_args();
        unsigned np = 1;
        for (unsigned i = 0; i < sz; ++i) {
            display(out, e.arg(i));
            if (i + 1 < sz) {
                out << ", ";
            }
            if (i + 2 < sz) {
                out << conn << "(";
                ++np;
            }
        }
        for (unsigned i = 0; i < np; ++i) {
            out << ")";
        }
    }

    void collect_axiom_ids(named_formulas& axioms) {
        m_named_formulas = &axioms;
        m_axiom_ids.clear();
        for (unsigned i = 0; i < axioms.m_formulas.size(); ++i) {
            z3::expr& e = axioms.m_formulas[i];
            unsigned id = Z3_get_ast_id(ctx, e);
            m_axiom_ids.insert(std::make_pair(id, i));
        }
    }

    void display_proof(std::ostream& out, named_formulas& fmls, z3::solver& solver) {
        m_node_number = 0;
        m_proof_ids.clear();
        m_proof_hypotheses.clear();        
        z3::expr proof = solver.proof();
        collect_axiom_ids(fmls);
        collect_decls(proof);
        collect_hypotheses(proof);
        display_sort_decls(out);
        display_func_decls(out);
        display_proof_rec(out, proof);
    }

    /**
       \brief collect hypotheses for each proof node.
     */
    void collect_hypotheses(z3::expr& proof) {
        Z3_sort proof_sort = proof.get_sort();
        size_t todo_size = todo.size();
        todo.push_back(proof);
        while (todo_size != todo.size()) {
            z3::expr p = todo.back();
            unsigned id = Z3_get_ast_id(ctx, p);
            if (m_proof_hypotheses.find(id) != m_proof_hypotheses.end()) {
                todo.pop_back();
                continue;
            }
            bool all_visited = true;
            for (unsigned i = 0; i < p.num_args(); ++i) {
                z3::expr arg = p.arg(i);
                if (arg.get_sort() == proof_sort) {
                    if (m_proof_hypotheses.find(Z3_get_ast_id(ctx,arg)) == m_proof_hypotheses.end()) {
                        all_visited = false;
                        todo.push_back(arg);
                    }
                }
            }
            if (!all_visited) {
                continue;
            }
            todo.pop_back();
            std::set<unsigned> hyps;
            if (p.decl().decl_kind() == Z3_OP_PR_LEMMA) {
                // we assume here that all hypotheses get consumed in lemmas.
            }
            else {
                for (unsigned i = 0; i < p.num_args(); ++i) {
                    z3::expr arg = p.arg(i);
                    if (arg.get_sort() == proof_sort) {
                        unsigned arg_id = Z3_get_ast_id(ctx,arg);
                        std::set<unsigned> const& arg_hyps = m_proof_hypotheses.find(arg_id)->second;
                        std::set<unsigned>::iterator it = arg_hyps.begin(), end = arg_hyps.end();
                        for (; it != end; ++it) {
                            hyps.insert(*it);
                        }
                    }
                }
            }
            m_proof_hypotheses.insert(std::make_pair(id, hyps));
        }
        
    }

    unsigned display_proof_rec(std::ostream& out, z3::expr proof) {
        Z3_sort proof_sort = proof.get_sort();
        size_t todo_size = todo.size();
        todo.push_back(proof);
        while (todo_size != todo.size()) {
            z3::expr p = todo.back();
            unsigned id = Z3_get_ast_id(ctx, p);
            if (m_proof_ids.find(id) != m_proof_ids.end()) {
                todo.pop_back();
                continue;
            }

            switch (p.decl().decl_kind()) {
            case Z3_OP_PR_MODUS_PONENS_OEQ: {
                unsigned hyp = display_proof_rec(out, p.arg(0));                
                unsigned num = display_proof_hyp(out, hyp, p.arg(1));
                m_proof_ids.insert(std::make_pair(id, num));
                todo.pop_back();
                continue;
            }
            default:
                break;
            }
            bool all_visited = true;
            for (unsigned i = 0; i < p.num_args(); ++i) {
                z3::expr arg = p.arg(i);
                if (arg.get_sort() == proof_sort) {
                    if (m_proof_ids.find(Z3_get_ast_id(ctx,arg)) == m_proof_ids.end()) {
                        all_visited = false;
                        todo.push_back(arg);
                    }
                }
            }
            if (!all_visited) {
                continue;
            }
            todo.pop_back();
            unsigned num = ++m_node_number;
            m_proof_ids.insert(std::make_pair(id, num));
            
            switch (p.decl().decl_kind()) {
            case Z3_OP_PR_ASSERTED: {
                std::string formula_name;
                std::string formula_file;
                unsigned id = Z3_get_ast_id(ctx, p.arg(0));
                std::map<unsigned, unsigned>::iterator it = m_axiom_ids.find(id);
                if (it != m_axiom_ids.end()) {                    
                    formula_name = m_named_formulas->m_names[it->second];
                    formula_file = m_named_formulas->m_files[it->second];
                }
                else {
                    std::ostringstream str;
                    str << "axiom_" << id;
                    formula_name = str.str();
                    formula_file = "unknown";
                }
                out << "tff(" << m_node_number << ",axiom,(";
                display(out, get_proof_formula(p));
                out << "), file('" << formula_file << "','";
                out << formula_name << "')).\n";
                break;               
            } 
            case Z3_OP_PR_UNDEF:
                throw failure_ex("undef rule not handled");
            case Z3_OP_PR_TRUE:
                display_inference(out, "true", "thm", p);
                break;                 
            case Z3_OP_PR_GOAL:
                display_inference(out, "goal", "thm", p);
                break;                 
            case Z3_OP_PR_MODUS_PONENS: 
                display_inference(out, "modus_ponens", "thm", p);
                break;
            case Z3_OP_PR_REFLEXIVITY: 
                display_inference(out, "reflexivity", "thm", p);
                break;
            case Z3_OP_PR_SYMMETRY: 
                display_inference(out, "symmetry", "thm", p);
                break;
            case Z3_OP_PR_TRANSITIVITY: 
            case Z3_OP_PR_TRANSITIVITY_STAR: 
                display_inference(out, "transitivity", "thm", p);
                break;
            case Z3_OP_PR_MONOTONICITY: 
                display_inference(out, "monotonicity", "thm", p);
                break;
            case Z3_OP_PR_QUANT_INTRO:
                display_inference(out, "quant_intro", "thm", p);
                break;                
            case Z3_OP_PR_DISTRIBUTIVITY: 
                display_inference(out, "distributivity", "thm", p);
                break;
            case Z3_OP_PR_AND_ELIM: 
                display_inference(out, "and_elim", "thm", p);
                break;
            case Z3_OP_PR_NOT_OR_ELIM: 
                display_inference(out, "or_elim", "thm", p);
                break;
            case Z3_OP_PR_REWRITE:                 
            case Z3_OP_PR_REWRITE_STAR: 
                display_inference(out, "rewrite", "thm", p);
                break;
            case Z3_OP_PR_PULL_QUANT: 
            case Z3_OP_PR_PULL_QUANT_STAR: 
                display_inference(out, "pull_quant", "thm", p);
                break;
            case Z3_OP_PR_PUSH_QUANT: 
                display_inference(out, "push_quant", "thm", p);
                break;
            case Z3_OP_PR_ELIM_UNUSED_VARS: 
                display_inference(out, "elim_unused_vars", "thm", p);
                break;
            case Z3_OP_PR_DER: 
                display_inference(out, "destructive_equality_resolution", "thm", p);
                break;                
            case Z3_OP_PR_QUANT_INST:
                display_inference(out, "quant_inst", "thm", p);
                break;
            case Z3_OP_PR_HYPOTHESIS: 
                out << "tff(" << m_node_number << ",assumption,(";
                display(out, get_proof_formula(p));
                out << "), introduced(assumption)).\n";
                break;                
            case Z3_OP_PR_LEMMA: {
                out << "tff(" << m_node_number << ",plain,(";
                display(out, get_proof_formula(p));
                out << "), inference(lemma,lemma(discharge,";
                unsigned parent_id = Z3_get_ast_id(ctx, p.arg(0));
                std::set<unsigned> const& hyps = m_proof_hypotheses.find(parent_id)->second;
                print_hypotheses(out, hyps);
                out << "))).\n";
                break;                
            }     
            case Z3_OP_PR_UNIT_RESOLUTION:                                 
                display_inference(out, "unit_resolution", "thm", p);
                break;                
            case Z3_OP_PR_IFF_TRUE: 
                display_inference(out, "iff_true", "thm", p); 
                break;
            case Z3_OP_PR_IFF_FALSE: 
                display_inference(out, "iff_false", "thm", p); 
                break;
            case Z3_OP_PR_COMMUTATIVITY: 
                display_inference(out, "commutativity", "thm", p); 
                break;                
            case Z3_OP_PR_DEF_AXIOM:
                display_inference(out, "tautology", "thm", p); 
                break;                
            case Z3_OP_PR_DEF_INTRO: 
                display_inference(out, "def_intro", "sab", p); 
                break;
            case Z3_OP_PR_APPLY_DEF: 
                display_inference(out, "apply_def", "sab", p); 
                break;
            case Z3_OP_PR_IFF_OEQ: 
                display_inference(out, "iff_oeq", "sab", p); 
                break;
            case Z3_OP_PR_NNF_POS:
                display_inference(out, "nnf_pos", "sab", p); 
                break;
            case Z3_OP_PR_NNF_NEG: 
                display_inference(out, "nnf_neg", "sab", p); 
                break;
            case Z3_OP_PR_NNF_STAR: 
                display_inference(out, "nnf", "sab", p); 
                break;
            case Z3_OP_PR_CNF_STAR: 
                display_inference(out, "cnf", "sab", p); 
                break;
            case Z3_OP_PR_SKOLEMIZE:
                display_inference(out, "skolemize", "sab", p); 
                break;                
            case Z3_OP_PR_MODUS_PONENS_OEQ: 
                display_inference(out, "modus_ponens_sab", "sab", p); 
                break;                
            case Z3_OP_PR_TH_LEMMA: 
                display_inference(out, "theory_lemma", "thm", p); 
                break;
            case Z3_OP_PR_HYPER_RESOLVE:
                display_inference(out, "hyper_resolve", "thm", p); 
                break;
            default:
                out << "TBD: " << m_node_number << "\n" << p << "\n";
                throw failure_ex("rule not handled");
            }
        }
        return m_proof_ids.find(Z3_get_ast_id(ctx, proof))->second;
    }

    unsigned display_proof_hyp(std::ostream& out, unsigned hyp, z3::expr p) {
        z3::expr fml = p.arg(p.num_args()-1);
        z3::expr conclusion = fml.arg(1);        
        switch (p.decl().decl_kind()) {
        case Z3_OP_PR_REFLEXIVITY: 
            return display_hyp_inference(out, "reflexivity", "sab", conclusion, hyp);
        case Z3_OP_PR_IFF_OEQ: {
            unsigned hyp2 = display_proof_rec(out, p.arg(0));
            return display_hyp_inference(out, "modus_ponens", "thm", conclusion, hyp, hyp2);
        }
        case Z3_OP_PR_NNF_POS:
        case Z3_OP_PR_NNF_STAR: 
            return display_hyp_inference(out, "nnf", "sab", conclusion, hyp);
        case Z3_OP_PR_CNF_STAR: 
            return display_hyp_inference(out, "cnf", "sab", conclusion, hyp);
        case Z3_OP_PR_SKOLEMIZE:
            return display_hyp_inference(out, "skolemize", "sab", conclusion, hyp);
        case Z3_OP_PR_TRANSITIVITY:
        case Z3_OP_PR_TRANSITIVITY_STAR: {
            unsigned na = p.num_args();
            for (unsigned i = 0; i + 1 < na; ++i) {
                if (p.arg(i).num_args() != 2) {
                    // cop-out: Z3 produces transitivity proofs that are not a chain of equivalences/equi-sats.
                    // the generated proof is (most likely) not going to be checkable.
                    continue;
                }
                z3::expr conclusion = p.arg(i).arg(1);
                hyp = display_hyp_inference(out, "transitivity", "sab", conclusion, hyp);
            }
            return hyp;
        }
        case Z3_OP_PR_MONOTONICITY: 
            throw failure_ex("monotonicity rule is not handled");            
        default: 
            unsigned hyp2 = 0;
            if (p.num_args() == 2) {
                hyp2 = display_proof_rec(out, p.arg(0));
            }
            if (p.num_args() > 2) {
                std::cout << "unexpected number of arguments: " << p << "\n";
                throw failure_ex("unexpected number of arguments");
            }
            
            return display_hyp_inference(out, p.decl().name().str().c_str(), "sab", conclusion, hyp, hyp2);
        }
        return 0;
    }


    void display_inference(std::ostream& out, char const* name, char const* status, z3::expr p) {
        unsigned id = Z3_get_ast_id(ctx, p);
        std::set<unsigned> const& hyps = m_proof_hypotheses.find(id)->second;
        out << "tff(" << m_node_number << ",plain,\n    (";
        display(out, get_proof_formula(p));
        out << "),\n    inference(" << name << ",[status(" << status << ")";
        if (!hyps.empty()) {
            out << ", assumptions(";
            print_hypotheses(out, hyps);
            out << ")";
        }
        out << "],";
        display_hypotheses(out, p);
        out << ")).\n";
    }

    void print_hypotheses(std::ostream& out, std::set<unsigned> const& hyps) {
        std::set<unsigned>::iterator it = hyps.begin(), end = hyps.end();
        bool first = true;
        out << "[";
        for (; it != end; ++it) {
            if (!first) {
                out << ", ";
            }
            first = false;
            out << m_proof_ids.find(*it)->second;
        }
        out << "]";
    }

    unsigned display_hyp_inference(std::ostream& out, char const* name, char const* status, z3::expr conclusion, unsigned hyp1, unsigned hyp2 = 0) {
        ++m_node_number;
        out << "tff(" << m_node_number << ",plain,(\n    ";
        display(out, conclusion);
        out << "),\n    inference(" << name << ",[status(" << status << ")],";
        out << "[" << hyp1;
        if (hyp2) {
            out << ", " << hyp2;
        }
        out << "])).\n";
        return m_node_number;
    }



    void get_free_vars(z3::expr const& e, std::vector<z3::sort>& vars) {
        std::set<unsigned> seen;
        size_t sz = todo.size();
        todo.push_back(e);
        while (todo.size() != sz) {
            z3::expr e = todo.back();
            todo.pop_back();
            unsigned id = Z3_get_ast_id(e.ctx(), e);
            if (seen.find(id) != seen.end()) {
                continue;
            }
            seen.insert(id);
            if (e.is_var()) {
                unsigned idx = Z3_get_index_value(ctx, e);
                while (idx >= vars.size()) {
                    vars.push_back(e.get_sort());
                }
                vars[idx] = e.get_sort();
            }
            else if (e.is_app()) {
                unsigned sz = e.num_args();
                for (unsigned i = 0; i < sz; ++i) {
                    todo.push_back(e.arg(i));
                }
            }
            else {
                // e is a quantifier
                std::vector<z3::sort> fv;
                get_free_vars(e.body(), fv);
                unsigned nb = Z3_get_quantifier_num_bound(e.ctx(), e);
                for (unsigned i = nb; i < fv.size(); ++i) {
                    if (vars.size() <= i - nb) {
                        vars.push_back(fv[i]);
                    }
                }
            }
        }        
    }

    z3::expr get_proof_formula(z3::expr proof) {
        // unsigned na = proof.num_args();
        z3::expr result = proof.arg(proof.num_args()-1);
        std::vector<z3::sort> vars;
        get_free_vars(result, vars);
        if (vars.empty()) {
            return result;
        }
        Z3_sort* sorts = new Z3_sort[vars.size()];
        Z3_symbol* names = new Z3_symbol[vars.size()];
        for (unsigned i = 0; i < vars.size(); ++i) {
            std::ostringstream str;
            str << "X" << (i+1);
            sorts[vars.size()-i-1] = vars[i];
            names[vars.size()-i-1] = Z3_mk_string_symbol(ctx, str.str().c_str());
        }
        result = z3::expr(ctx, Z3_mk_forall(ctx, 1, 0, 0, static_cast<unsigned>(vars.size()), sorts, names, result));
        delete[] sorts;
        delete[] names;
        return result;
    }

    void display_hypotheses(std::ostream& out, z3::expr p) {
        unsigned na = p.num_args();
        out << "[";
        for (unsigned i = 0; i + 1 < na; ++i) {
            out << m_proof_ids.find(Z3_get_ast_id(p.ctx(), p.arg(i)))->second;
            if (i + 2 < na) {
                out << ", ";
            }
        }
        out << "]";
    }

    void display_sort_decls(std::ostream& out) {
        for (unsigned i = 0; i < sorts.size(); ++i) {
            display_sort_decl(out, sorts[i]);
        }
    }
    
    void display_sort_decl(std::ostream& out, z3::sort& s) {
        out << "tff(" << s << "_type, type, (" << s << ": $tType)).\n";
    }


    void display_func_decls(std::ostream& out) {
        for (size_t i = 0; i < funs.size(); ++i) {
            display_func_decl(out, funs[i]);
        }
    }

    bool contains_id(unsigned id) const {
        return seen_ids.find(id) != seen_ids.end();
    }

    void collect_decls(z3::expr e) {
        todo.push_back(e);
        while (!todo.empty()) {
            z3::expr e = todo.back();
            todo.pop_back();
            unsigned id = Z3_get_ast_id(ctx, e);
            if (contains_id(id)) {
                continue;
            }
            seen_ids.insert(id);
            if (e.is_app()) {
                collect_fun(e.decl());
                unsigned sz = e.num_args();
                for (unsigned i = 0; i < sz; ++i) {
                    todo.push_back(e.arg(i));
                }
            }
            else if (e.is_quantifier()) {
                unsigned nb = Z3_get_quantifier_num_bound(e.ctx(), e);
                for (unsigned i = 0; i < nb; ++i) {
                    z3::sort srt(ctx, Z3_get_quantifier_bound_sort(e.ctx(), e, i));
                    collect_sort(srt);
                }
                todo.push_back(e.body());
            }
            else if (e.is_var()) {
                collect_sort(e.get_sort());
            }
        }
    }

    void collect_sort(z3::sort s) {
        unsigned id = Z3_get_sort_id(ctx, s);
        if (s.sort_kind() == Z3_UNINTERPRETED_SORT && 
            contains_id(id)) {
            seen_ids.insert(id);
            sorts.push_back(s);
        }
    }

    void collect_fun(z3::func_decl f) {
        unsigned id = Z3_get_func_decl_id(ctx, f);
        if (contains_id(id)) {
            return;
        }
        seen_ids.insert(id);
        if (f.decl_kind() == Z3_OP_UNINTERPRETED) {
            funs.push_back(f);
        }
        for (unsigned i = 0; i < f.arity(); ++i) {
            collect_sort(f.domain(i));
        }
        collect_sort(f.range());
    }    

    std::string upper_case_var(z3::symbol const& sym) {
        std::string result = sanitize(sym);
        char ch = result[0];
        if ('A' <= ch && ch <= 'Z') {
            return result;
        }
        return "X" + result;
    }

    std::string lower_case_fun(z3::symbol const& sym) {
        std::string result = sanitize(sym);
        char ch = result[0];
        if ('a' <= ch && ch <= 'z') {
            return result;
        }
        else {
            return "tptp_fun_" + result;
        }
    }

    std::string sanitize(z3::symbol const& sym) {
        std::ostringstream str;
        if (sym.kind() == Z3_INT_SYMBOL) {
            str << sym;
            return str.str();
        }
        std::string s = sym.str();
        size_t sz = s.size();
        for (size_t i = 0; i < sz; ++i) {
            char ch = s[i];
            if ('a' <= ch && ch <= 'z') {
                str << ch;
            }
            else if ('A' <= ch && ch <= 'Z') {
                str << ch;
            }
            else if ('0' <= ch && ch <= '9') {
                str << ch;
            }
            else if ('_' == ch) {
                str << ch;
            }
            else {
                str << "_";
            }
        }
        return str.str();
    }
};

static char* g_input_file = 0;
static bool g_display_smt2 = false;
static bool g_generate_model = false;
static bool g_generate_proof = false;
static bool g_generate_core = false;
static bool g_display_statistics = false;
static bool g_first_interrupt = true;
static bool g_smt2status = false;
static bool g_check_status = false;
static int g_timeout = 0;
static double g_start_time = 0;
static z3::solver*   g_solver = 0;
static z3::context*  g_context = 0;
static std::ostream* g_out = &std::cout;



static void display_usage() {
    unsigned major, minor, build_number, revision_number;
    Z3_get_version(&major, &minor, &build_number, &revision_number);
    std::cout << "Z3tptp [" << major << "." << minor << "." << build_number << "." << revision_number << "] (c) 2006-20**. Microsoft Corp.\n";
    std::cout << "Usage: tptp [options] [-file:]file\n";
    std::cout << "  -h, -?       prints this message.\n";
    std::cout << "  -smt2        print SMT-LIB2 benchmark.\n";
    std::cout << "  -m, -model   generate model.\n";
    std::cout << "  -p, -proof   generate proof.\n";
    std::cout << "  -c, -core    generate unsat core of named formulas.\n";
    std::cout << "  -st, -statistics display statistics.\n";
    std::cout << "  -t:timeout   set timeout (in second).\n";
    std::cout << "  -smt2status  display status in smt2 format instead of SZS.\n";
    std::cout << "  -check_status check the status produced by Z3 against annotation in benchmark.\n";
    std::cout << "  -<param>:<value> configuration parameter and value.\n";
    std::cout << "  -o:<output-file> file to place output in.\n";
}


static void display_statistics() {
    if (g_solver && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        double end_time = static_cast<double>(clock());
        z3::stats stats = g_solver->statistics();
        std::cout << stats << "\n";
        std::cout << "time:   " << (end_time - g_start_time)/CLOCKS_PER_SEC << " secs\n";
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

bool parse_token(char const*& line, char const* token) {
    char const* result = line;
    while (result[0] == ' ') ++result;
    while (token[0] && result[0] == token[0]) {
        ++token;
        ++result;
    }
    if (!token[0]) {
        line = result;
        return true;
    }
    else {
        return false;
    }
}

bool parse_is_sat_line(char const* line, bool& is_sat) {
    if (!parse_token(line, "%")) return false;
    if (!parse_token(line, "Status")) return false;
    if (!parse_token(line, ":")) return false;
    
    if (parse_token(line, "Unsatisfiable")) {
        is_sat = false;
        return true;
    }
    if (parse_token(line, "Theorem")) {
        is_sat = false;
        return true;
    }
    if (parse_token(line, "Theorem")) {
        is_sat = false;
        return true;
    }
    if (parse_token(line, "CounterSatisfiable")) {
        is_sat = true;
        return true;
    }
    if (parse_token(line, "Satisfiable")) {
        is_sat = true;
        return true;
    }
    return false;
}    

bool parse_is_sat(char const* filename, bool& is_sat) {
    std::ifstream is(filename);
    if (is.bad() || is.fail()) {
        std::stringstream strm;
        strm << "Could not open file " << filename << "\n";
        throw failure_ex(strm.str().c_str());
    }
    
    for (unsigned i = 0; !is.eof() && i < 200; ++i) {
        std::string line;
        std::getline(is, line);
        if (parse_is_sat_line(line.c_str(), is_sat)) {
            return true;
        }
    }
    return false;
}


void parse_cmd_line_args(int argc, char ** argv) {
    g_input_file = 0;
    g_display_smt2 = false;
    int i = 1;
    while (i < argc) {
        char* arg = argv[i];
        //char * eq = 0;
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
            if (!strcmp(arg,"p") || !strcmp(arg,"proof")) {
                g_generate_proof = true;
            }
            else if (!strcmp(arg,"m") || !strcmp(arg,"model")) {
                g_generate_model = true;
            }
            else if (!strcmp(arg,"c") || !strcmp(arg,"core")) {
                g_generate_core = true;
            }
            else if (!strcmp(arg,"st") || !strcmp(arg,"statistics")) {
                g_display_statistics = true;
            }
            else if (!strcmp(arg,"check_status")) {
                g_check_status = true;
            }
            else if (!strcmp(arg,"t") || !strcmp(arg,"timeout")) {
                if (!opt_arg) {
                    display_usage();
                    exit(0);
                }
                g_timeout = atoi(opt_arg);
            }
            else if (!strcmp(arg,"smt2status")) {
                g_smt2status = true;
            }
            else if (!strcmp(arg,"o")) {
                if (opt_arg) {
                    g_out = new std::ofstream(opt_arg);
                    if (g_out->bad() || g_out->fail()) {
                        std::cout << "Could not open file of output: " << opt_arg << "\n";
                        exit(0);
                    }
                }
                else {
                    display_usage();
                    exit(0);
                }
            }
            else if (!strcmp(arg,"smt2")) {
                g_display_smt2 = true;

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

static bool is_smt2_file(char const* filename) {
    size_t len = strlen(filename);
    return (len > 4 && !strcmp(filename + len - 5,".smt2"));    
}

static void check_error(z3::context& ctx) {
    Z3_error_code e = Z3_get_error_code(ctx);
    if (e != Z3_OK) {
        std::cout << Z3_get_error_msg_ex(ctx, e) << "\n";
        exit(1);
    }
}

static void display_tptp(std::ostream& out) {
    // run SMT2 parser, pretty print TFA format.
    z3::context ctx;
    Z3_ast _fml = Z3_parse_smtlib2_file(ctx, g_input_file, 0, 0, 0, 0, 0, 0);
    check_error(ctx);
    z3::expr fml(ctx, _fml);

    pp_tptp pp(ctx);
    pp.collect_decls(fml);
    pp.display_sort_decls(out);
    pp.display_func_decls(out);

    if (fml.decl().decl_kind() == Z3_OP_AND) {
        for (unsigned i = 0; i < fml.num_args(); ++i) {
            pp.display_axiom(out, fml.arg(i));
        }
    }
    else {
        pp.display_axiom(out, fml);
    }
}

static void display_proof(z3::context& ctx, named_formulas& fmls, z3::solver& solver) {
    pp_tptp pp(ctx);    
    pp.display_proof(std::cout, fmls, solver);
}

static void display_model(z3::context& ctx, z3::model model) {
    unsigned nc = model.num_consts();
    unsigned nf = model.num_funcs();
    z3::expr_vector fmls(ctx);
    for (unsigned i = 0; i < nc; ++i) {
        z3::func_decl f = model.get_const_decl(i);
        z3::expr e = model.get_const_interp(f);
        fmls.push_back(f() == e);
    }

    for (unsigned i = 0; i < nf; ++i) {
        z3::func_decl f = model.get_func_decl(i);
        z3::func_interp fi = model.get_func_interp(f);
        unsigned arity = f.arity();
        z3::expr_vector args(ctx);
        for (unsigned j = 0; j < arity; ++j) {
            std::ostringstream str;
            str << "X" << j;
            z3::symbol sym(ctx, Z3_mk_string_symbol(ctx, str.str().c_str()));
            args.push_back(ctx.constant(sym, f.domain(j)));
        }
        unsigned ne = fi.num_entries();
        Z3_ast* conds = new Z3_ast[arity];
        Z3_ast* conds_match = new Z3_ast[ne];
        z3::expr_vector conds_matchv(ctx);
        z3::expr els = fi.else_value();
        unsigned num_cases = 0;
        for (unsigned k = 0; k < ne; ++k) {
            z3::func_entry e = fi.entry(k);
            z3::expr_vector condv(ctx), args_e(ctx);
            if (((Z3_ast)els) && (Z3_get_ast_id(ctx, els) == Z3_get_ast_id(ctx, e.value()))) {
                continue;
            }
            for (unsigned j = 0; j < arity; ++j) {
                args_e.push_back(e.arg(j));
                condv.push_back(e.arg(j) == args[j]);
                conds[j] = condv.back();
            }
            z3::expr cond(ctx, Z3_mk_and(ctx, arity, conds));
            conds_matchv.push_back(cond);
            conds_match[num_cases] = cond;
            fmls.push_back(f(args_e) == e.value());
            ++num_cases;
        }
        if (els) {
            els = f(args) == els;
            switch (num_cases) {
            case 0: els = forall(args, els); break;
            case 1: els = forall(args, implies(!z3::expr(ctx, conds_match[0]), els)); break;
            default: els = forall(args, implies(!z3::expr(ctx, Z3_mk_or(ctx, num_cases, conds_match)), els)); break;
            }
            fmls.push_back(els);
        }
        delete[] conds;
        delete[] conds_match;
    }

    pp_tptp pp(ctx);
    for (unsigned i = 0; i < fmls.size(); ++i) {
        pp.collect_decls(fmls[i]);
    }
    pp.display_sort_decls(std::cout);
    pp.display_func_decls(std::cout);
    for (unsigned i = 0; i < fmls.size(); ++i) {
        pp.display_axiom(std::cout, fmls[i]);
    }   
}

static void display_smt2(std::ostream& out) {
    z3::config config;
    z3::context ctx(config);
    named_formulas fmls;
    env env(ctx);
    try {
        env.parse(g_input_file, fmls);
    }
    catch (failure_ex& ex) {
        std::cerr << ex.msg << "\n";
        return;
    }

    size_t num_assumptions = fmls.m_formulas.size();

    Z3_ast* assumptions = new Z3_ast[num_assumptions];
    for (size_t i = 0; i < num_assumptions; ++i) {
        assumptions[i] = fmls.m_formulas[i];
    }
    Z3_string s = 
        Z3_benchmark_to_smtlib_string(
            ctx, 
            "Benchmark generated from TPTP", // comment
            0,         // no logic is set
            "unknown", // no status annotation
            "",        // attributes
            static_cast<unsigned>(num_assumptions), 
            assumptions, 
            ctx.bool_val(true));

    out << s << "\n";
    delete[] assumptions;
}

static void prove_tptp() {
    z3::config config;
    if (g_generate_proof) {
        config.set("proof", true);
        z3::set_param("proof", true);
    }    
    z3::context ctx(config);
    z3::solver solver(ctx);
    g_solver  = &solver;
    g_context = &ctx;
    if (g_timeout) {
        // TBD overflow check
        z3::set_param("timeout", g_timeout*1000);
        z3::params params(ctx);
        params.set("timeout", static_cast<unsigned>(g_timeout*1000));
        solver.set(params);
    }
    

    named_formulas fmls;
    env env(ctx);
    try {
        env.parse(g_input_file, fmls);
    }
    catch (failure_ex& ex) {
        std::cerr << ex.msg << "\n";
        std::cout << "SZS status GaveUp\n";
        return;
    }

    size_t num_assumptions = fmls.m_formulas.size();

    z3::check_result result;

    if (g_generate_core) {
        z3::expr_vector assumptions(ctx);
        
        for (size_t i = 0; i < num_assumptions; ++i) {
            z3::expr pred = ctx.constant(fmls.m_names[i].c_str(), ctx.bool_sort());
            z3::expr def = fmls.m_formulas[i] == pred;
            solver.add(def);
            assumptions.push_back(pred);
        }
        result = solver.check(assumptions);
    }
    else {
        for (unsigned i = 0; i < num_assumptions; ++i) {
            solver.add(fmls.m_formulas[i]);
        }        
        result = solver.check();
    }

    switch(result) {
    case z3::unsat:
        if (g_smt2status) {
            std::cout << result << "\n";
        }
        else if (fmls.has_conjecture()) {
            std::cout << "SZS status Theorem\n";
        }
        else {
            std::cout << "SZS status Unsatisfiable\n";
        }
        if (g_generate_proof) {
            try {
                display_proof(ctx, fmls, solver);
            }
            catch (failure_ex& ex) {
                std::cerr << "Proof display could not be completed: " << ex.msg << "\n";
            }
        }
        if (g_generate_core) {
            z3::expr_vector core = solver.unsat_core();
            std::cout << "SZS core ";
            for (unsigned i = 0; i < core.size(); ++i) {
                std::cout << core[i] << " ";
            }
            std::cout << "\n";
        }
        break;
    case z3::sat:
        if (g_smt2status) {
            std::cout << result << "\n";
        }
        else if (fmls.has_conjecture()) {
            std::cout << "SZS status CounterSatisfiable\n";            
        }
        else {
            std::cout << "SZS status Satisfiable\n";
        }
        if (g_generate_model) {
            display_model(ctx, solver.get_model());
        }
        break;
    case z3::unknown:
        if (g_smt2status) {
            std::cout << result << "\n";
        }
        else if (!g_first_interrupt) {
            std::cout << "SZS status Interrupted\n";
        }
        else {
            std::cout << "SZS status GaveUp\n";
            std::string reason = solver.reason_unknown();
            std::cout << "SZS reason " << reason << "\n";
        }
        break;
    }    
    bool is_sat = true;
    if (g_check_status && 
        result != z3::unknown &&
        parse_is_sat(g_input_file, is_sat)) {
        if (is_sat && result == z3::unsat) {
            std::cout << "BUG!! expected result is Satisfiable, returned result is Unsat\n";
        }
        if (!is_sat && result == z3::sat) {
            std::cout << "BUG!! expected result is Unsatisfiable, returned result is Satisfiable\n";
        }
    }
    display_statistics();
}

int main(int argc, char** argv) {

    //std::ostream* out = &std::cout;
    g_start_time = static_cast<double>(clock());
    signal(SIGINT, on_ctrl_c);

    parse_cmd_line_args(argc, argv);
    
    if (is_smt2_file(g_input_file)) {
        display_tptp(*g_out);
    }
    else if (g_display_smt2) {
        display_smt2(*g_out);
    }
    else {
        prove_tptp();
    }
    return 0;
}

