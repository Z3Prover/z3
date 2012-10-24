/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    symmetry_reduce.cpp

Abstract:

    Add symmetry breaking predicates to goals.

Author:

    Nikolaj (nbjorner) 2011-05-31

Notes:

    This is a straight-forward and literal
    adaption of the algorithms proposed for veriT.

--*/
#include"tactical.h"
#include"for_each_expr.h"
#include"map.h"
#include"expr_replacer.h"
#include"rewriter_def.h"
#include"ast_pp.h"

class symmetry_reduce_tactic : public tactic {
    class imp;
    imp *  m_imp;
public:
    symmetry_reduce_tactic(ast_manager & m);

    virtual tactic * translate(ast_manager & m) {
        return alloc(symmetry_reduce_tactic, m);
    }
    
    virtual ~symmetry_reduce_tactic();
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core);
    virtual void cleanup();
};

class ac_rewriter {
    ast_manager& m_manager;
public:
    ac_rewriter(ast_manager& m): m_manager(m) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        if ((f->is_associative() && f->is_commutative()) ||
            m_manager.is_distinct(f)) {
            ptr_buffer<expr> buffer;
            buffer.append(num_args, args);
            std::sort(buffer.begin(), buffer.end(), ast_lt_proc());
            bool change = false;
            for (unsigned i = 0; !change && i < num_args; ++i) {
                change = (args[i] != buffer[i]);
            }
            if (change) {
                result = m().mk_app(f, num_args, buffer.begin());
                return BR_DONE;
            }
        }
        else if (f->is_commutative() && num_args == 2 && args[0]->get_id() > args[1]->get_id()) {
            expr* args2[2] = { args[1], args[0] };
            result = m().mk_app(f, num_args, args2);
            return BR_DONE;
        }
        return BR_FAILED;
    }

    void mk_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_app_core(f, num_args, args, result) == BR_FAILED)
            result = m().mk_app(f, num_args, args);
    }
private:
    ast_manager& m() const { return m_manager; }
};


struct ac_rewriter_cfg : public default_rewriter_cfg {
    ac_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        return m_r.mk_app_core(f, num, args, result);
    }
    ac_rewriter_cfg(ast_manager & m):m_r(m) {}
};

class ac_rewriter_star : public rewriter_tpl<ac_rewriter_cfg> {
    ac_rewriter_cfg m_cfg;
public:
    ac_rewriter_star(ast_manager & m):
        rewriter_tpl<ac_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m) {}
};

template class rewriter_tpl<ac_rewriter_cfg>;

class symmetry_reduce_tactic::imp {
    typedef ptr_vector<app>     permutation;
    typedef vector<permutation> permutations;
    typedef ptr_vector<app>     term_set;
    typedef obj_map<app, unsigned> app_map;
    typedef u_map<ptr_vector<app> > inv_app_map;
    ast_manager&                m_manager;
    ac_rewriter_star            m_rewriter;
    scoped_ptr<expr_replacer>   m_replace;
    
    ast_manager& m() const { return m_manager; }
public:
    imp(ast_manager& m) : m_manager(m), m_rewriter(m) {
        m_replace = mk_default_expr_replacer(m);
    }

    ~imp() {}

    void operator()(goal & g) {
        if (g.inconsistent())
            return;
        tactic_report report("symmetry-reduce", g);
        vector<ptr_vector<app> > P;    
        expr_ref fml(m());
        to_formula(g, fml);
        app_map occs;
        compute_occurrences(fml, occs);
        find_candidate_permutations(fml, occs, P);
        if (P.empty()) {
            return;
        }
        term_set T, cts;        
        unsigned num_sym_break_preds = 0;
        for (unsigned i = 0; i < P.size(); ++i) {
            term_set& consts = P[i];
            if (invariant_by_permutations(fml, consts)) {
                cts.reset();
                select_terms(fml, consts, T);
                while (!T.empty() && cts.size() < consts.size()) {
                    app* t = select_most_promising_term(fml, T, cts, consts, occs);
                    T.erase(t);                    
                    compute_used_in(t, cts, consts);
                    app* c = select_const(consts, cts);
                    if (!c) break;
                    cts.push_back(c);
                    expr* mem = mk_member(t, cts);
                    g.assert_expr(mem); 
                    num_sym_break_preds++;
                    TRACE("symmetry_reduce", tout << "member predicate: " << mk_pp(mem, m()) << "\n";);
                    fml = m().mk_and(fml.get(), mem);
                    normalize(fml);
                }
            }
        }
        report_tactic_progress(":num-symmetry-breaking ", num_sym_break_preds);
    }

private:
    void to_formula(goal const & g, expr_ref& fml) {
        ptr_vector<expr> conjs;
        for (unsigned i = 0; i < g.size(); ++i) {
            conjs.push_back(g.form(i));
        }
        fml = m().mk_and(conjs.size(), conjs.c_ptr());
        normalize(fml);
    }

    // find candidate permutations
    void find_candidate_permutations(expr* fml, app_map const& occs, permutations& P) {
        app_map coloring;
        app_map depth;
        inv_app_map inv_color;
        unsigned num_occs;
        compute_sort_colors(fml, coloring);
        compute_max_depth(fml, depth);
        merge_colors(occs, coloring);        
        merge_colors(depth, coloring);     
        // compute_siblings(fml, coloring);
        compute_inv_app(coloring, inv_color);
        
        inv_app_map::iterator it = inv_color.begin(), end = inv_color.end();
        for (; it != end; ++it) {
            if (it->m_value.size() < 2) {
                continue;
            }
            VERIFY(occs.find(it->m_value[0], num_occs));
            if (num_occs < 2) {
                continue;
            }
            bool is_const = true;
            for (unsigned j = 0; is_const && j < it->m_value.size(); ++j) {
                is_const = it->m_value[j]->get_num_args() == 0;
            }
            if (!is_const) {
                continue;
            }
            P.push_back(it->m_value);
            TRACE("symmetry_reduce",
                for (unsigned i = 0; i < it->m_value.size(); ++i) {
                    tout << mk_pp(it->m_value[i], m()) << " ";
                }
            tout << "\n";);
        }
    }

    //
    // refine coloring by taking most specific generalization.
    // a |-> c1, b |-> c2 <c1,c2> |-> c
    // 
    struct u_pair {
        unsigned m_first;
        unsigned m_second;
        u_pair(unsigned f, unsigned s) : m_first(f), m_second(s) {}
        u_pair(): m_first(0), m_second(0) {}

        struct hash {
            unsigned operator()(u_pair const& p) const {
                return mk_mix(p.m_first, p.m_second, 23);
            }
        };
        struct eq {
            bool operator()(u_pair const& p, u_pair const& q) const {
                return p.m_first == q.m_first && p.m_second == q.m_second;
            }
        };
    };
    typedef map<u_pair, unsigned, u_pair::hash, u_pair::eq> pair_map;
    bool merge_colors(app_map const& colors1, app_map& colors2) {
        pair_map recolor;
        unsigned num_colors = 0, v1, v2, w, old_max = 0;
        app_map::iterator it = colors2.begin(), end = colors2.end();
        for (; it != end; ++it) {
            app* a = it->m_key;
            v1 = it->m_value;
            VERIFY(colors1.find(a, v2));
            if (recolor.find(u_pair(v1, v2), w)) {
                it->m_value = w;
            }
            else {
                it->m_value = num_colors;
                recolor.insert(u_pair(v1, v2), num_colors++);
            }
            if (v1 > old_max) old_max = v1;
        }
        return num_colors > old_max + 1;
    }

    class sort_colors {
        ast_manager& m_manager;
        app_map& m_app2sortid;
        obj_map<sort,unsigned>  m_sort2id;
        unsigned m_max_id;

    public:
        sort_colors(ast_manager& m, app_map& app2sort): 
          m_manager(m), m_app2sortid(app2sort), m_max_id(0) {}

        void operator()(app* n) {
            sort* s = m_manager.get_sort(n);
            unsigned id;
            if (!m_sort2id.find(s, id)) {
                id = m_max_id++;
                m_sort2id.insert(s, id);
            }
            m_app2sortid.insert(n, id);
        }
        void operator()(quantifier * n) {}
        void operator()(var * n) {}
    };

    void compute_sort_colors(expr* fml, app_map& app2sortId) {
        app2sortId.reset();
        sort_colors sc(m(), app2sortId);
        for_each_expr(sc, fml);
    }

    void compute_inv_app(app_map const& map, inv_app_map& inv_map) {
        app_map::iterator it = map.begin(), end = map.end();
        for (; it != end; ++it) {
            app* t = it->m_key;
            unsigned n = it->m_value;
            if (is_uninterpreted(t)) {
                inv_app_map::entry* e = inv_map.insert_if_not_there2(n, ptr_vector<app>());
                e->get_data().m_value.push_back(t);
            }
        }
    }
    bool is_uninterpreted(app* t) const {
        return t->get_family_id() == null_family_id;
    }

    // compute maximal depth of terms.
    void compute_max_depth(expr* e, app_map& depth) {
        ptr_vector<expr> todo;
        unsigned_vector  depths;
        unsigned d, d1;
        todo.push_back(e);
        depths.push_back(0);
        while (!todo.empty()) {
            e = todo.back();
            d = depths.back();
            todo.pop_back();
            depths.pop_back();
            if (is_var(e)) {
                // nothing
            }
            else if (is_quantifier(e)) {
                todo.push_back(to_quantifier(e)->get_expr());
                depths.push_back(d+1);
            }
            else if (is_app(e)) {
                app* a = to_app(e);
                if (depth.find(a, d1) && d <= d1) {
                    continue;
                }
                depth.insert(a, d);                
                ++d;
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    todo.push_back(a->get_arg(i));
                    depths.push_back(d);
                }
            }
            else {
                UNREACHABLE();
            }

        }
    }

    // color nodes according to the function symbols they appear in
    typedef obj_hashtable<func_decl> fun_set;
    typedef obj_map<app, fun_set*> app_parents;

    class parents {
        app_parents m_use_funs;        
    public:
        parents() {}

        app_parents const& get_parents() { return m_use_funs; }

        void operator()(app* n) {
            func_decl* f;
            unsigned sz = n->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                expr* e = n->get_arg(i);
                if (is_app(e)) {
                    app_parents::obj_map_entry* entry = m_use_funs.insert_if_not_there2(to_app(e), 0);
                    if (!entry->get_data().m_value) entry->get_data().m_value = alloc(fun_set);
                    entry->get_data().m_value->insert(f); 
                }
            }
        }
        void operator()(quantifier *n) {}
        void operator()(var* n) {}
    };
    void compute_parents(expr* e, app_map& parents) {
    }

    typedef hashtable<unsigned, u_hash, u_eq> uint_set;
    typedef obj_map<app, uint_set*> app_siblings;;

    class siblings {
        app_map const& m_colors;
        app_siblings m_sibs;
    public:
        siblings(app_map const& colors): m_colors(colors) {}

        app_siblings const& get() { return m_sibs; }
        void operator()(app* n) {
            unsigned sz = n->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                expr* e = n->get_arg(i);
                if (!is_app(e)) continue;
                app_siblings::obj_map_entry* entry = m_sibs.insert_if_not_there2(to_app(e), 0);
                if (!entry->get_data().get_value()) entry->get_data().m_value = alloc(uint_set);
                for (unsigned j = 0; j < sz; ++j) {
                    expr* f = n->get_arg(j);
                    if (is_app(f) && i != j) {
                        unsigned c1 = 0;
                        m_colors.find(to_app(f), c1);
                        entry->get_data().m_value->insert(c1);
                    }
                }
            }
        }
        void operator()(quantifier *n) {}
        void operator()(var* n) {}        
    };
    // refine coloring by taking colors of siblings into account.
    bool compute_siblings_rec(expr* e, app_map& colors) {
        siblings sibs(colors);
        app_map colors1;
        for_each_expr(sibs, e);
        app_siblings const& s = sibs.get();
        app_siblings::iterator it = s.begin(), end = s.end();
        for (; it != end; ++it) {
            app* a = it->m_key;
            uint_set* set = it->m_value;
            uint_set::iterator it2 = set->begin(), end2 = set->end();
            unsigned c = 0;
            for(; it2 != end2; ++it2) {
                c += 1 + *it2;
            }
            colors1.insert(a, c);
            dealloc(set);
        }
        if (is_app(e)) {
            colors1.insert(to_app(e), 0);
        }
        return merge_colors(colors1, colors);
    }
    void compute_siblings(expr* fml, app_map& colors) {
        while(compute_siblings_rec(fml, colors));
    }

    // check if assertion set is invariant under the current permutation
    bool invariant_by_permutations(expr* fml, permutation& p) {

        SASSERT(p.size() >= 2);
        bool result = check_swap(fml, p[0], p[1]) && check_cycle(fml, p);
        TRACE("symmetry_reduce", 
              if (result) {
                  tout << "Symmetric: ";
              }
              else {
                  tout << "Not symmetric: ";
              }
              for (unsigned i = 0; i < p.size(); ++i) {
                  tout << mk_pp(p[i], m()) << " ";
              }
              tout << "\n";);
        return result;
    }

    bool check_swap(expr* fml, app* t1, app* t2) {
        expr_substitution sub(m());
        sub.insert(t1, t2);
        sub.insert(t2, t1);
        m_replace->set_substitution(&sub);
        return check_substitution(fml);
    }

    bool check_cycle(expr* fml, permutation& p) {
        expr_substitution sub(m());
        for (unsigned i = 0; i + 1 < p.size(); ++i) {
            sub.insert(p[i], p[i+1]);
        }
        sub.insert(p[p.size()-1], p[0]);
        m_replace->set_substitution(&sub);
        return check_substitution(fml);
    }

    bool check_substitution(expr* t) {
        expr_ref r(m());
        (*m_replace)(t, r);
        normalize(r);
        return t == r.get();
    }

    void normalize(expr_ref& r) {
        proof_ref pr(m());
        expr_ref  result(m());
        m_rewriter(r.get(), result, pr);
        r = result;
    }

    // select terms that are range restricted by set p.
    void select_terms(expr* fml, term_set const& p, term_set& T) {
        T.reset();
        ptr_vector<expr> todo;
        todo.push_back(fml);
        app* t = 0;
        while (!todo.empty()) {
            fml = todo.back();
            todo.pop_back();
            if (m().is_and(fml)) {
                todo.append(to_app(fml)->get_num_args(), to_app(fml)->get_args());               
            }
            else if (is_range_restriction(fml, p, t)) {
                T.push_back(t);
            }
        }
    }
    bool is_range_restriction(expr* form, term_set const& C, app*& t) {
        if (!m().is_or(form)) return false;
        unsigned sz = to_app(form)->get_num_args();
        t = 0;
        for (unsigned i = 0; i < sz; ++i) {
            expr* e = to_app(form)->get_arg(i);
            expr* e1, *e2;
            if (!m().is_eq(e, e1, e2)) return false;
            if (!is_app(e1) || !is_app(e2)) return false;
            app* a1 = to_app(e1), *a2 = to_app(e2);
            if (C.contains(a1) && (t == 0 || t == a2)) {
                t = a2;
            }
            else if (C.contains(a2) && (t == 0 || t == a1)) {
                t = a1;
            }
            else {
                return false;
            }
        }
        return t != 0;
    }


    // select the most promising term among T.
    // terms with the largest number of occurrences have higher weight.
    // terms that have fewest terms among C as subterms are preferred.
    
    class num_occurrences {
        app_map& m_occs;
    public:
        num_occurrences(app_map& occs): m_occs(occs) {}
        void operator()(app* n) {
            app_map::obj_map_entry* e;
            m_occs.insert_if_not_there2(n, 0);
            unsigned sz = n->get_num_args();
            for (unsigned i = 0; i < sz; ++i) {
                expr* arg = n->get_arg(i);
                if (is_app(arg)) {
                    e = m_occs.insert_if_not_there2(to_app(arg), 0);
                    e->get_data().m_value++;
                }
            }
        }
        void operator()(quantifier * n) {}
        void operator()(var * n) {}
    };
    void compute_occurrences(expr* fml, app_map& occs) {
        occs.reset();
        num_occurrences num_occ(occs);
        for_each_expr(num_occ, fml);
    }

    app* select_most_promising_term(
        expr* fml, term_set const& T, 
        term_set& cts, term_set const& consts, app_map const& occs) {
        SASSERT(!T.empty());
        app* t = T[0];
        unsigned weight, weight1;
        VERIFY(occs.find(t, weight));
        unsigned cts_delta = compute_cts_delta(t, cts, consts);
        TRACE("symmetry_reduce", tout << mk_pp(t, m()) << " " << weight << " " << cts_delta << "\n";);
        for (unsigned i = 1; i < T.size(); ++i) {
            app* t1 = T[i];
            VERIFY(occs.find(t1, weight1));
            if (weight1 < weight && t->get_num_args() <= t1->get_num_args()) {
                continue;
            }
            unsigned cts_delta1 = compute_cts_delta(t1, cts, consts);
            TRACE("symmetry_reduce", tout << mk_pp(t1, m()) << " " << weight1 << " " << cts_delta1 << "\n";);
            if ((t->get_num_args() == t1->get_num_args() && (weight1 > weight || cts_delta1 < cts_delta)) || 
                t->get_num_args() > t1->get_num_args()) {
                 cts_delta = cts_delta1;
                 weight = weight1;
                 t = t1;
            }
        }        
        return t;
    }

    // add to cts subterms of t that are members of consts.
    class member_of {
        term_set const& m_S;
        term_set&       m_r;
    public:
        member_of(term_set const& S, term_set& r) : m_S(S), m_r(r) {}
        void operator()(app* n) {
            if (m_S.contains(n) && !m_r.contains(n)) {
                m_r.push_back(n);
            }
        }
        void operator()(quantifier * n) {}
        void operator()(var * n) {}
    };
    void compute_used_in(app* t, term_set& cts, term_set const& consts) {
        member_of mem(consts, cts);
        for_each_expr(mem, t);
        TRACE("symmetry_reduce",
              tout << "Term: " << mk_pp(t, m()) << "\n";
              tout << "Support set: ";
              for (unsigned i = 0; i < consts.size(); ++i) {
                  tout << mk_pp(consts[i], m()) << " ";
              }
              tout << "\n";
              tout << "Constants: ";
              for (unsigned i = 0; i < cts.size(); ++i) {
                  tout << mk_pp(cts[i], m()) << " ";
              }
              tout << "\n";
              );
    }

    unsigned compute_cts_delta(app* t, term_set& cts, term_set const& consts) {
        unsigned cts_size = cts.size();
        if (cts_size == consts.size()) {
            return 0;
        }
        compute_used_in(t, cts, consts);
        unsigned cts_delta = cts.size() - cts_size;
        cts.resize(cts_size);
        return cts_delta;
    }

    // select element in A not in B
    app* select_const(term_set const& A, term_set const& B) {
        unsigned j;
        for (j = 0; j < A.size() && B.contains(A[j]); ++j);
        return (j == A.size())?0:A[j];
    }

    app* mk_member(app* t, term_set const& C) {
        expr_ref_vector eqs(m());
        for (unsigned i = 0; i < C.size(); ++i) {
            eqs.push_back(m().mk_eq(t, C[i]));
        }
        return m().mk_or(eqs.size(), eqs.c_ptr());
    }
};

symmetry_reduce_tactic::symmetry_reduce_tactic(ast_manager & m) {
    m_imp = alloc(imp, m);
}

symmetry_reduce_tactic::~symmetry_reduce_tactic() {
    dealloc(m_imp);
}
    
void symmetry_reduce_tactic::operator()(goal_ref const & g, 
                                        goal_ref_buffer & result, 
                                        model_converter_ref & mc, 
                                        proof_converter_ref & pc,
                                        expr_dependency_ref & core) {
    fail_if_proof_generation("symmetry_reduce", g);
    fail_if_unsat_core_generation("symmetry_reduce", g);
    mc = 0; pc = 0; core = 0; result.reset();
    (*m_imp)(*(g.get()));
    g->inc_depth();
    result.push_back(g.get());
}

void symmetry_reduce_tactic::cleanup() {
    // no-op.
}

tactic * mk_symmetry_reduce_tactic(ast_manager & m, params_ref const & p) {
    return alloc(symmetry_reduce_tactic, m);
}
