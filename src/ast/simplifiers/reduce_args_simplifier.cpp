/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    reduce_args_simplifier.cpp

Abstract:

    Reduce the number of arguments in function applications.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/

#include "util/map.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_util.h"
#include "ast/has_free_vars.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/simplifiers/dependent_expr_state.h"

/**
   \brief Reduce the number of arguments in function applications.

   Example, suppose we have a function f with 2 arguments. 
   There are 1000 applications of this function, but the first argument is always "a", "b" or "c".
   Thus, we replace the f(t1, t2)
   with 
      f_a(t2)   if   t1 = a
      f_b(t2)   if   t2 = b
      f_c(t2)   if   t2 = c

   Since f_a, f_b, f_c are new symbols, satisfiability is preserved.
   
   This transformation is very similar in spirit to the Ackermman's reduction. 

   This transformation should work in the following way:

   1- Create a mapping decl2arg_map from declarations to tuples of booleans, an entry [f -> (true, false, true)]
       means that f is a declaration with 3 arguments where the first and third arguments are always values.
   2- Traverse the formula and populate the mapping. 
        For each function application f(t1, ..., tn) do
          a) Create a boolean tuple (is_value(t1), ..., is_value(tn)) and do
             the logical-and with the tuple that is already in the mapping. If there is no such tuple
             in the mapping, we just add a new entry.

   If all entries are false-tuples, then there is nothing to be done. The transformation is not applicable.

   Now, we create a mapping decl2new_decl from (decl, val_1, ..., val_n) to decls. Note that, n may be different for each entry,
   but it is the same for the same declaration.
   For example, suppose we have [f -> (true, false, true)] in decl2arg_map, and applications f(1, a, 2), f(1, b, 2), f(1, b, 3), f(2, b, 3), f(2, c, 3) in the formula.
   Then, decl2arg_map would contain
        (f, 1, 2) -> f_1_2
        (f, 1, 3) -> f_1_3
        (f, 2, 3) -> f_2_3
   where f_1_2, f_1_3 and f_2_3 are new function symbols.
   Using the new map, we can replace the occurrences of f.
*/

class reduce_args_simplifier : public dependent_expr_simplifier {
    bv_util                  m_bv;
    
    static bool is_var_plus_offset(ast_manager& m, bv_util& bv, expr* e, expr*& base) {
        expr *lhs, *rhs;
        if (bv.is_bv_add(e, lhs, rhs) && bv.is_numeral(lhs)) 
            base = rhs;
        else
            base = e;        
        return !has_free_vars(base);
    }

    static bool may_be_unique(ast_manager& m, bv_util& bv, expr* e, expr*& base) {
        base = nullptr;
        return m.is_unique_value(e) || is_var_plus_offset(m, bv, e, base);
    }

    static bool may_be_unique(ast_manager& m, bv_util& bv, expr* e) {
        expr* base;
        return may_be_unique(m, bv, e, base);
    }
    
    struct find_non_candidates_proc {
        ast_manager &              m;
        bv_util &                  m_bv;
        obj_hashtable<func_decl> & m_non_candidates;
        
        find_non_candidates_proc(ast_manager & m, bv_util & bv, obj_hashtable<func_decl> & non_candidates):
            m(m),
            m_bv(bv),
            m_non_candidates(non_candidates) {
        }
        
        void operator()(var * n) {}
        
        void operator()(quantifier *n) {}
        
        void operator()(app * n) {
            if (!is_uninterp(n))
                return;
            func_decl * d;
            if (n->get_num_args() == 0)
                return; // ignore constants
            d = n->get_decl();
            if (m_non_candidates.contains(d))
                return; // it is already in the set.
            for (expr* arg : *n)
                if (may_be_unique(m, m_bv, arg))
                    return;
            m_non_candidates.insert(d);
        }
    };

    /**
       \brief Populate the table non_candidates with function declarations \c f
       such that there is a function application (f t1 ... tn) where t1 ... tn are not values.
    */
    void find_non_candidates(obj_hashtable<func_decl> & non_candidates) {
        non_candidates.reset();
        find_non_candidates_proc proc(m, m_bv, non_candidates);
        expr_fast_mark1 visited;
        for (auto i : indices())
            quick_for_each_expr(proc, visited, m_fmls[i].fml());

        TRACE("reduce_args", tout << "non_candidates:\n"; for (func_decl* d : non_candidates) tout << d->get_name() << "\n";);
    }

    struct populate_decl2args_proc {
        reduce_args_simplifier&           m_owner;
        ast_manager &                     m;
        bv_util &                         m_bv;
        obj_hashtable<func_decl> &        m_non_candidates;
        obj_map<func_decl, bit_vector> &  m_decl2args;    
        obj_map<func_decl, svector<expr*> > m_decl2base; // for args = base + offset

        populate_decl2args_proc(reduce_args_simplifier& o, ast_manager & m, bv_util & bv, obj_hashtable<func_decl> & nc, obj_map<func_decl, bit_vector> & d):
            m_owner(o), m(m), m_bv(bv), m_non_candidates(nc), m_decl2args(d) {}
        
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app * n) {
            if (n->get_num_args() == 0)
                return; // ignore constants
            func_decl * d = n->get_decl();
            if (d->get_family_id() != null_family_id)
                return; // ignore interpreted symbols
            if (m_non_candidates.contains(d))
                return; // declaration is not a candidate
            if (m_owner.m_fmls.frozen(d))
                return;
            
            unsigned j = n->get_num_args();
            obj_map<func_decl, bit_vector>::iterator it = m_decl2args.find_iterator(d);
            expr* base;
            if (it == m_decl2args.end()) {
                m_decl2args.insert(d, bit_vector());
                svector<expr*>& bases = m_decl2base.insert_if_not_there(d, svector<expr*>());
                bases.resize(j);
                it = m_decl2args.find_iterator(d);
                SASSERT(it != m_decl2args.end());
                it->m_value.reserve(j);
                while (j > 0) {
                    --j;
                    it->m_value.set(j, may_be_unique(m, m_bv, n->get_arg(j), base));
                    bases[j] = base;
                }
            } else {
                svector<expr*>& bases = m_decl2base[d];
                SASSERT(j == it->m_value.size());                        
                while (j > 0) {
                    --j;
                    it->m_value.set(j, it->m_value.get(j) && may_be_unique(m, m_bv, n->get_arg(j), base) && bases[j] == base);
                }
            }
        }
    };

    void populate_decl2args(obj_hashtable<func_decl> & non_candidates, 
                            obj_map<func_decl, bit_vector> & decl2args) {
        expr_fast_mark1 visited;
        decl2args.reset();
        populate_decl2args_proc proc(*this, m, m_bv, non_candidates, decl2args);
        for (auto i : indices()) 
            quick_for_each_expr(proc, visited, m_fmls[i].fml());
        
        // Remove all cases where the simplification is not applicable.
        ptr_buffer<func_decl> bad_decls;
        for (auto const& [k, v] : decl2args) 
            if (all_of(v, [&](auto b) { return !b;}))
                bad_decls.push_back(k);                        
    
        for (func_decl* a : bad_decls)
            decl2args.erase(a);

        TRACE("reduce_args", tout << "decl2args:" << std::endl;
              for (auto const& [k, v] : decl2args) {
                  tout << k->get_name() << ": ";
                  for (unsigned i = 0; i < v.size(); ++i)
                      tout << (v.get(i) ? "1" : "0");
                  tout << std::endl;
              });
    }

    struct arg2func_hash_proc {
        bit_vector const & m_bv;
        
        arg2func_hash_proc(bit_vector const & bv):m_bv(bv) {}
        unsigned operator()(app const * n) const {
            // compute the hash-code using only the arguments where m_bv is true.
            unsigned a = 0x9e3779b9;
            unsigned num_args = n->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                if (!m_bv.get(i)) 
                    continue; // ignore argument
                a = hash_u_u(a, n->get_arg(i)->get_id());
            }
            return a;
        }
    };
     
    struct arg2func_eq_proc {
        bit_vector const & m_bv;
     
        arg2func_eq_proc(bit_vector const & bv):m_bv(bv) {}
        bool operator()(app const * n1, app const * n2) const {
            // compare only the arguments where m_bv is true
            SASSERT(n1->get_num_args() == n2->get_num_args());
            unsigned num_args = n1->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                if (!m_bv.get(i)) 
                    continue; // ignore argument
                if (n1->get_arg(i) != n2->get_arg(i))
                    return false;
            }
            return true;
        }
    };

    typedef map<app *, func_decl *, arg2func_hash_proc, arg2func_eq_proc> arg2func;
    typedef obj_map<func_decl, arg2func *> decl2arg2func_map;

    struct reduce_args_ctx { 
        ast_manager &           m;
        decl2arg2func_map       m_decl2arg2funcs;

        reduce_args_ctx(ast_manager & m): m(m) {
        }
        
        ~reduce_args_ctx() {
            for (auto const& [_, map] : m_decl2arg2funcs) {
                for (auto const& [k, v] : *map) {
                    m.dec_ref(k);
                    m.dec_ref(v);
                }
                dealloc(map);
            }
        }
    };
    
    struct reduce_args_rw_cfg : public default_rewriter_cfg {
        ast_manager &                    m;
        reduce_args_simplifier&          m_owner;
        obj_map<func_decl, bit_vector> & m_decl2args;
        decl2arg2func_map &              m_decl2arg2funcs;
        
        reduce_args_rw_cfg(reduce_args_simplifier& owner, obj_map<func_decl, bit_vector> & decl2args, decl2arg2func_map & decl2arg2funcs):
            m(owner.m),
            m_owner(owner),
            m_decl2args(decl2args),
            m_decl2arg2funcs(decl2arg2funcs) {
        }
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = nullptr;
            if (f->get_arity() == 0)
                return BR_FAILED; // ignore constants
            if (f->get_family_id() != null_family_id)
                return BR_FAILED; // ignore interpreted symbols
            obj_map<func_decl, bit_vector>::iterator it = m_decl2args.find_iterator(f);
            if (it == m_decl2args.end())
                return BR_FAILED;

            bit_vector & bv = it->m_value;
            arg2func *& map = m_decl2arg2funcs.insert_if_not_there(f, 0);
            if (!map) {
                map = alloc(arg2func, arg2func_hash_proc(bv), arg2func_eq_proc(bv));
            }

            app_ref tmp(m.mk_app(f, num, args), m);
            func_decl *& new_f = map->insert_if_not_there(tmp, nullptr);
            if (!new_f) {
                // create fresh symbol
                ptr_buffer<sort> domain;
                unsigned arity = f->get_arity();
                for (unsigned i = 0; i < arity; ++i) {
                    if (!bv.get(i))
                        domain.push_back(f->get_domain(i));
                }
                new_f = m.mk_fresh_func_decl(f->get_name(), symbol::null, domain.size(), domain.data(), f->get_range());
                m.inc_ref(tmp);
                m.inc_ref(new_f);
            }

            ptr_buffer<expr> new_args;
            for (unsigned i = 0; i < num; i++) {
                if (!bv.get(i))
                    new_args.push_back(args[i]);
            }
            result = m.mk_app(new_f, new_args.size(), new_args.data());
            return BR_DONE;
        }
    };

    struct reduce_args_rw : rewriter_tpl<reduce_args_rw_cfg> {
        reduce_args_rw_cfg m_cfg;
    public:
        reduce_args_rw(reduce_args_simplifier & owner, obj_map<func_decl, bit_vector> & decl2args, decl2arg2func_map & decl2arg2funcs):
            rewriter_tpl<reduce_args_rw_cfg>(owner.m, false, m_cfg),
            m_cfg(owner, decl2args, decl2arg2funcs) {
        }
    };

    void mk_mc(obj_map<func_decl, bit_vector> & decl2args, decl2arg2func_map & decl2arg2funcs, vector<dependent_expr> const& removed) {
        ptr_buffer<expr> new_args;
        var_ref_vector   new_vars(m);
        ptr_buffer<expr> new_eqs;
        for (auto const& [f, map] : decl2arg2funcs)
            for (auto const& [t, new_def] : *map)
                m_fmls.model_trail().hide(new_def);
               
        vector<std::tuple<func_decl_ref, expr_ref, expr_dependency_ref>> defs;
        for (auto const& [f, map] : decl2arg2funcs) {
            expr * def     = nullptr;
            SASSERT(decl2args.contains(f));
            bit_vector & bv = decl2args.find(f);
            new_vars.reset();
            new_args.reset();
            for (unsigned i = 0; i < f->get_arity(); i++) {
                new_vars.push_back(m.mk_var(i, f->get_domain(i)));
                if (!bv.get(i))
                    new_args.push_back(new_vars.back());
            }
            for (auto const& [t, new_def] : *map) {
                SASSERT(new_def->get_arity() == new_args.size());
                app * new_t = m.mk_app(new_def, new_args);
                if (def == nullptr) {
                    def = new_t;
                }
                else {
                    new_eqs.reset();
                    for (unsigned i = 0; i < f->get_arity(); i++) 
                        if (bv.get(i))
                            new_eqs.push_back(m.mk_eq(new_vars.get(i), t->get_arg(i)));                    
                    SASSERT(new_eqs.size() > 0);
                    expr * cond = mk_and(m, new_eqs);
                    def = m.mk_ite(cond, new_t, def);
                }
            }
            SASSERT(def);
            expr_dependency* dep = nullptr;
            defs.push_back({ func_decl_ref(f,m), expr_ref(def, m), expr_dependency_ref(dep, m) });                 
        }        
        m_fmls.model_trail().push(defs, removed);
    }

    unsigned m_num_decls = 0;

public:
    reduce_args_simplifier(ast_manager& m, dependent_expr_state& st, params_ref const& p) :
        dependent_expr_simplifier(m, st),
        m_bv(m)
    {}

    char const* name() const override { return "reduce-args"; }

    void collect_statistics(statistics& st) const override {
        st.update("reduced-funcs", m_num_decls);
    }

    void reset_statistics() override {
        m_num_decls = 0;
    }

    void reduce() override {
        m_fmls.freeze_suffix();
        
        obj_hashtable<func_decl> non_candidates;
        obj_map<func_decl, bit_vector> decl2args;
        find_non_candidates(non_candidates);
        populate_decl2args(non_candidates, decl2args);

        if (decl2args.empty())
            return;

        m_num_decls += decl2args.size();

        reduce_args_ctx ctx(m);
        reduce_args_rw rw(*this, decl2args, ctx.m_decl2arg2funcs);
        vector<dependent_expr> removed;
        // if not global scope then what?
        // cannot just use in incremental mode.
        for (auto i : indices()) {
            auto [f, p, d] = m_fmls[i]();
            if (p)
                continue;
            expr_ref new_f(m);
            rw(f, new_f);
            if (f != new_f) {
                removed.push_back(m_fmls[i]);
                m_fmls.update(i, dependent_expr(m, new_f, p, d));
            }
        }
        mk_mc(decl2args, ctx.m_decl2arg2funcs, removed);
    }

};

dependent_expr_simplifier* mk_reduce_args_simplifier(ast_manager & m, dependent_expr_state& st, params_ref const & p) {
    return alloc(reduce_args_simplifier, m, st, p);
}

