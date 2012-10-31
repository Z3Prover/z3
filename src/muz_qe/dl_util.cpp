/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_util.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-20.

Revision History:

--*/

#include <sstream>
#include <sys/types.h>
#include <sys/stat.h>
#ifdef _WINDOWS
#include <windows.h>
#endif
#include"ast_pp.h"
#include"bool_rewriter.h"
#include"dl_context.h"
#include"dl_rule.h"
#include"for_each_expr.h"
#include"dl_util.h"

namespace datalog {

    void universal_delete(relation_base* ptr) {
        ptr->deallocate();
    }

    void universal_delete(table_base* ptr) {
        ptr->deallocate();
    }

    void flatten_and(expr_ref_vector& result) {
        ast_manager& m = result.get_manager();
        expr* e1, *e2, *e3;
        for (unsigned i = 0; i < result.size(); ++i) {
            if (m.is_and(result[i].get())) {
                app* a = to_app(result[i].get());
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(a->get_arg(j));
                }
                result[i] = result.back();
                result.pop_back();
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_not(e1, e2)) {
                result[i] = e2;
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_or(e1)) {
                app* a = to_app(e1);
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(m.mk_not(a->get_arg(j)));
                }
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_not(result[i].get(), e1) && m.is_implies(e1,e2,e3)) {
                result.push_back(e2);
                result[i] = m.mk_not(e3);
                --i;
            }
            else if (m.is_true(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_false(e1))) {
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_false(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_true(e1))) {
                result.reset();
                result.push_back(m.mk_false());
                return;
            }
        }
    }

    void flatten_and(expr* fml, expr_ref_vector& result) {
        SASSERT(result.get_manager().is_bool(fml));
        result.push_back(fml);        
        flatten_and(result);
    }

    void flatten_or(expr_ref_vector& result) {
        ast_manager& m = result.get_manager();
        expr* e1, *e2, *e3;
        for (unsigned i = 0; i < result.size(); ++i) {
            if (m.is_or(result[i].get())) {
                app* a = to_app(result[i].get());
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(a->get_arg(j));
                }
                result[i] = result.back();
                result.pop_back();
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_not(e1, e2)) {
                result[i] = e2;
                --i;
            }
            else if (m.is_not(result[i].get(), e1) && m.is_and(e1)) {
                app* a = to_app(e1);
                unsigned num_args = a->get_num_args();
                for (unsigned j = 0; j < num_args; ++j) {
                    result.push_back(m.mk_not(a->get_arg(j)));
                }
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_implies(result[i].get(),e2,e3)) {
                result.push_back(e3);
                result[i] = m.mk_not(e2);
                --i;
            }
            else if (m.is_false(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_true(e1))) {
                result[i] = result.back();
                result.pop_back();
                --i;                
            }
            else if (m.is_true(result[i].get()) ||
                     (m.is_not(result[i].get(), e1) &&
                      m.is_false(e1))) {
                result.reset();
                result.push_back(m.mk_true());
                return;
            }
        }        
    }


    void flatten_or(expr* fml, expr_ref_vector& result) {
        SASSERT(result.get_manager().is_bool(fml));
        result.push_back(fml);        
        flatten_or(result);
    }

    bool push_toplevel_junction_negation_inside(expr_ref& e)
    {
        ast_manager& m = e.get_manager();
        bool_rewriter brwr(m);

        expr * arg;
        if(!m.is_not(e, arg)) { return false; }
        bool is_and = m.is_and(arg);
        if(!is_and && !m.is_or(arg)) { return false; }

        //now we know we have formula we need to transform
        app * junction = to_app(arg);
        expr_ref_vector neg_j_args(m);
        unsigned num_args = junction->get_num_args();
        for(unsigned i=0; i<num_args; ++i) {
            expr_ref neg_j_arg(m);
            brwr.mk_not(junction->get_arg(i), neg_j_arg);
            neg_j_args.push_back(neg_j_arg);
        }
        if(is_and) {
            brwr.mk_or(neg_j_args.size(), neg_j_args.c_ptr(), e);
        }
        else {
            brwr.mk_and(neg_j_args.size(), neg_j_args.c_ptr(), e);
        }
        return true;
    }


    bool contains_var(expr * trm, unsigned var_idx) {
        ptr_vector<sort> vars;
        ::get_free_vars(trm, vars);
        return var_idx < vars.size() && vars[var_idx] != 0;
    }


    void collect_vars(ast_manager & m, expr * e, var_idx_set & result) {
        ptr_vector<sort> vars;
        ::get_free_vars(e, vars);
        unsigned sz = vars.size();
        for(unsigned i=0; i<sz; ++i) {
            if(vars[i]) { result.insert(i); }
        }
    }
    
    void collect_tail_vars(ast_manager & m, rule * r, var_idx_set & result) {
        unsigned n = r->get_tail_size();
        for(unsigned i=0;i<n;i++) {
            collect_vars(m, r->get_tail(i), result);
        }
    }

    void get_free_tail_vars(rule * r, ptr_vector<sort>& sorts) {
        unsigned n = r->get_tail_size();
        for(unsigned i=0;i<n;i++) {
            get_free_vars(r->get_tail(i), sorts);
        }
    }

    void get_free_vars(rule * r, ptr_vector<sort>& sorts) {
        get_free_vars(r->get_head(), sorts);
        get_free_tail_vars(r, sorts);
    }

    unsigned count_variable_arguments(app * pred)
    {
        SASSERT(is_uninterp(pred));
        unsigned res = 0;
        unsigned n = pred->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * arg = pred->get_arg(i);
            if (is_var(arg)) {
                res++;
            }
        }
        return res;
    }

    void collect_non_local_vars(ast_manager & m, rule const * r, app * t, var_idx_set & result) {
        collect_vars(m, r->get_head(), result);
        unsigned sz = r->get_tail_size();
        for (unsigned i = 0; i < sz; i++) {
            app * curr = r->get_tail(i);
            if (curr != t)
                collect_vars(m, curr, result);
        }
    }

    void collect_non_local_vars(ast_manager & m, rule const * r, app * t_1, app * t_2, var_idx_set & result) {
        collect_vars(m, r->get_head(), result);
        unsigned sz = r->get_tail_size();
        for (unsigned i = 0; i < sz; i++) {
            app * curr = r->get_tail(i);
            if (curr != t_1 && curr != t_2)
                collect_vars(m, curr, result);
        }
    }

    void mk_new_rule_tail(ast_manager & m, app * pred, var_idx_set const & non_local_vars, unsigned & next_idx, varidx2var_map & varidx2var, 
                          sort_ref_buffer & new_rule_domain, expr_ref_buffer & new_rule_args, app_ref & new_pred) {
        expr_ref_buffer new_args(m);
        unsigned n  = pred->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * arg = pred->get_arg(i);
            if (m.is_value(arg)) {
                new_args.push_back(arg);
            }
            else {
                SASSERT(is_var(arg));
                int vidx      = to_var(arg)->get_idx();
                var * new_var = 0;
                if (!varidx2var.find(vidx, new_var)) {
                    new_var = m.mk_var(next_idx, to_var(arg)->get_sort());
                    next_idx++;
                    varidx2var.insert(vidx, new_var);
                    if (non_local_vars.contains(vidx)) {
                        // other predicates used this variable... so it should be in the domain of the filter
                        new_rule_domain.push_back(to_var(arg)->get_sort());
                        new_rule_args.push_back(new_var);
                    }
                }
                SASSERT(new_var != 0);
                new_args.push_back(new_var);
            }
        }
        new_pred = m.mk_app(pred->get_decl(), new_args.size(), new_args.c_ptr());
    }

    void apply_subst(expr_ref_vector& tgt, expr_ref_vector const& sub) {
        ast_manager& m = tgt.get_manager();
        var_subst vs(m, false);
        expr_ref tmp(m);
        for (unsigned i = 0; i < tgt.size(); ++i) {
            if (tgt[i].get()) {
                vs(tgt[i].get(), sub.size(), sub.c_ptr(), tmp);
                tgt[i] = tmp;
            }
            else {
                tgt[i] = sub[i];
            }
        }
        for (unsigned i = tgt.size(); i < sub.size(); ++i) {
            tgt.push_back(sub[i]);
        }
    }


    void output_predicate(context & ctx, app * f, std::ostream & out)
    {
        func_decl * pred_decl = f->get_decl();
        unsigned arity = f->get_num_args();

        out << pred_decl->get_name() << '(';

        for (unsigned i = 0; i < arity; i++) {
            expr * arg = f->get_arg(i);
            if (i != 0) {
                out << ',';
            }
            if (is_var(arg)) {
                out << "#" << to_var(arg)->get_idx();
            }
            else {
                out << mk_pp(arg, ctx.get_manager());
            }
        }
        out << ")";
    }

    void display_predicate(context & ctx, app * f, std::ostream & out)
    {
        output_predicate(ctx, f, out);
        out << "\n";
    }

    void display_fact(context & ctx, app * f, std::ostream & out)
    {
        func_decl * pred_decl = f->get_decl();
        unsigned arity = f->get_num_args();

        out << "\t(";

        for(unsigned i = 0; i < arity; i++) {
            if (i != 0) {
                out << ',';
            }

            expr * arg = f->get_arg(i);
            uint64 sym_num;
            SASSERT(is_app(arg));
            VERIFY( ctx.get_decl_util().is_numeral_ext(to_app(arg), sym_num) );
            relation_sort sort = pred_decl->get_domain(i);            
            out << ctx.get_argument_name(pred_decl, i) << '=';
            ctx.print_constant_name(sort, sym_num, out);
            out << '(' << sym_num << ')';
        }
        out << ")\n";
    }

    void idx_set_union(idx_set & tgt, const idx_set & src) {
        idx_set::iterator vit = src.begin();
        idx_set::iterator vend = src.end();
        for(;vit!=vend;++vit) {
            tgt.insert(*vit);
        }
    }


    bool variable_intersection::values_match(const expr * v1, const expr * v2)
    {
        //return !m_manager.are_distinct(v1, v2);
        return v1==v2;
    }

    bool variable_intersection::args_match(const app * f1, const app * f2)
    {
        unsigned n=size();
        for (unsigned i = 0; i < n; i++) {
            unsigned f1_index, f2_index;
            get(i, f1_index, f2_index);
            if (!values_match(f1->get_arg(f1_index),f2->get_arg(f2_index))) {
                return false;
            }
        }
        return true;
    }

    bool variable_intersection::args_self_match(const app * f)
    {
        if(!args_match(f,f)) {
            return false;
        }

        unsigned n = m_const_indexes.size();
        for(unsigned i=0; i<n; i++) {
            unsigned f_index = m_const_indexes[i];
            if(!values_match(f->get_arg(f_index), m_consts[i].get())) {
                return false;
            }
        }
        return true;
    }

    void variable_intersection::populate_self(const app * a)
    {
        SASSERT(is_uninterp(a));

        //TODO: optimize quadratic complexity
        //TODO: optimize number of checks when variable occurs multiple times
        unsigned arity = a->get_num_args();
        for(unsigned i1=0; i1<arity; i1++) {
            expr * e1=a->get_arg(i1);
            if(is_var(e1)) {
                var* v1=to_var(e1);
                for(unsigned i2=i1+1; i2<arity; i2++) {
                    expr * e2=a->get_arg(i2);
                    if(!is_var(e2)) {
                        continue;
                    }
                    var* v2=to_var(e2);
                    if(v1->get_idx()==v2->get_idx()) {
                        add_pair(i1, i2);
                    }
                }
            }
            else {
                SASSERT(is_app(e1));
                app * c1 = to_app(e1);
                SASSERT(c1->get_num_args()==0); //c1 must be a constant

                m_const_indexes.push_back(i1);
                m_consts.push_back(c1);

                SASSERT(m_const_indexes.size()==m_consts.size());
            }
        }
    }

    void counter::update(unsigned el, int delta) {
        int & counter = get(el);
        SASSERT(!m_stay_non_negative || counter>=0);
        SASSERT(!m_stay_non_negative || static_cast<int>(counter)>=-delta);
        counter += delta;
    }

    int & counter::get(unsigned el) {
        return m_data.insert_if_not_there2(el, 0)->get_data().m_value;
    }

    counter & counter::count(unsigned sz, const unsigned * els, int delta) {
        for(unsigned i=0; i<sz; i++) {
            update(els[i], delta);
        }
        return *this;
    }

    unsigned counter::get_positive_count() const {
        unsigned cnt = 0;
        iterator eit = begin();
        iterator eend = end();
        for(; eit!=eend; ++eit) {
            if( eit->m_value>0 ) { 
                cnt++;
            }
        }
        return cnt;
    }

    void counter::collect_positive(idx_set & acc) const {
        iterator eit = begin();
        iterator eend = end();
        for(; eit!=eend; ++eit) {
            if(eit->m_value>0) { acc.insert(eit->m_key); }
        }
    }

    bool counter::get_max_positive(unsigned & res) const {
        bool found = false;
        iterator eit = begin();
        iterator eend = end();
        for(; eit!=eend; ++eit) {
            if( eit->m_value>0 && (!found || eit->m_key>res) ) { 
                found = true;
                res = eit->m_key;
            }
        }
        return found;
    }

    unsigned counter::get_max_positive() const {
        unsigned max_pos;
        VERIFY(get_max_positive(max_pos));
        return max_pos;
    }

    int counter::get_max_counter_value() const {
        int res = 0;
        iterator eit = begin();
        iterator eend = end();
        for (; eit!=eend; ++eit) {
            if( eit->m_value>res ) { 
                res = eit->m_value;
            }
        }
        return res;
    }

    void var_counter::count_vars(ast_manager & m, const app * pred, int coef) {
        unsigned n = pred->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            m_sorts.reset();
            ::get_free_vars(pred->get_arg(i), m_sorts);
            for (unsigned j = 0; j < m_sorts.size(); ++j) {
                if (m_sorts[j]) {
                    update(j, coef);
                }
            }
        }
    }

    void var_counter::count_vars(ast_manager & m, const rule * r, int coef) {
        count_vars(m, r->get_head(), 1);
        unsigned n = r->get_tail_size();
        for (unsigned i = 0; i < n; i++) {
            count_vars(m, r->get_tail(i), coef);
        }
    }

    unsigned var_counter::get_max_var(bool& has_var) {
        has_var = false;
        unsigned max_var = 0;
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            unsigned scope = m_scopes.back();
            m_todo.pop_back();
            m_scopes.pop_back();
            if (m_visited.is_marked(e)) {
                continue;
            }
            m_visited.mark(e, true);
            switch(e->get_kind()) {
            case AST_QUANTIFIER: {
                quantifier* q = to_quantifier(e);
                m_todo.push_back(q->get_expr());
                m_scopes.push_back(scope + q->get_num_decls());
                break;                 
            }
            case AST_VAR: {
                if (to_var(e)->get_idx() >= scope + max_var) {
                    has_var = true;
                    max_var = to_var(e)->get_idx() - scope;
                }
                break;
            }
            case AST_APP: {
                app* a = to_app(e);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    m_todo.push_back(a->get_arg(i));
                    m_scopes.push_back(scope);                    
                }
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
        m_visited.reset();
        return max_var;
    }

    unsigned var_counter::get_max_var(const rule & r) {
        m_todo.push_back(r.get_head());
        m_scopes.push_back(0);
        unsigned n = r.get_tail_size();
        bool has_var = false;
        for (unsigned i = 0; i < n; i++) {
            m_todo.push_back(r.get_tail(i));
            m_scopes.push_back(0);
        }
        return get_max_var(has_var);
    }

    unsigned var_counter::get_max_var(expr* e) {
        bool has_var = false;
        m_todo.push_back(e);
        m_scopes.push_back(0);
        return get_max_var(has_var);
    }

    unsigned var_counter::get_next_var(expr* e) {
        bool has_var = false;
        m_todo.push_back(e);
        m_scopes.push_back(0);
        unsigned mv = get_max_var(has_var);
        if (has_var) mv++;
        return mv;
    }

    void del_rule(horn_subsume_model_converter* mc, rule& r) {
        if (mc) {
            ast_manager& m = mc->get_manager();
            expr_ref_vector body(m);
            for (unsigned i = 0; i < r.get_tail_size(); ++i) {
                if (r.is_neg_tail(i)) {
                    body.push_back(m.mk_not(r.get_tail(i)));
                }
                else {
                    body.push_back(r.get_tail(i));
                }
            }
            TRACE("dl_dr", 
                  tout << r.get_decl()->get_name() << "\n";
                  for (unsigned i = 0; i < body.size(); ++i) {
                      tout << mk_pp(body[i].get(), m) << "\n";
                  });
                      
            mc->insert(r.get_head(), body.size(), body.c_ptr());
        }
    }

    void resolve_rule(replace_proof_converter* pc, rule const& r1, rule const& r2, unsigned idx, 
                      expr_ref_vector const& s1, expr_ref_vector const& s2, rule const& res) {
        if (!pc) return;
        ast_manager& m = s1.get_manager();
        dl_decl_util util(m);
        expr_ref fml1(m), fml2(m), fml3(m);
        r1.to_formula(fml1);
        r2.to_formula(fml2);
        res.to_formula(fml3);
        vector<expr_ref_vector> substs;
        svector<std::pair<unsigned, unsigned> > positions;
        substs.push_back(s1);
        substs.push_back(s2);

        scoped_coarse_proof _sc(m);
        proof_ref pr(m);
        proof_ref_vector premises(m);
        premises.push_back(m.mk_asserted(fml1));
        premises.push_back(m.mk_asserted(fml2));
        positions.push_back(std::make_pair(idx+1, 0));

        TRACE("dl", 
              tout << premises[0]->get_id() << " " << mk_pp(premises[0].get(), m) << "\n";
              for (unsigned i = 0; i < s1.size(); ++i) {
                  tout << mk_pp(s1[i], m) << " ";
              }
              tout << "\n";
              tout << premises[1]->get_id() << " " << mk_pp(premises[1].get(), m) << "\n";
              for (unsigned i = 0; i < s2.size(); ++i) {
                  tout << mk_pp(s2[i], m) << " ";
              }
              tout << "\n";
              ); 

        pr = m.mk_hyper_resolve(2, premises.c_ptr(), fml3, positions, substs);
        pc->insert(pr);
    }

    class skip_model_converter : public model_converter {
    public:
        skip_model_converter() {}
 
        virtual model_converter * translate(ast_translation & translator) { 
            return alloc(skip_model_converter);
        }

    };

    model_converter* mk_skip_model_converter() { return alloc(skip_model_converter); }

    class skip_proof_converter : public proof_converter {
        virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
            SASSERT(num_source == 1);
            result = source[0];
        }

        virtual proof_converter * translate(ast_translation & translator) {
            return alloc(skip_proof_converter);
        }

    };

    proof_converter* mk_skip_proof_converter() { return alloc(skip_proof_converter); }


    unsigned get_max_var(const rule & r, ast_manager & m) {
        var_counter ctr;
        return ctr.get_max_var(r);
    }

    void reverse_renaming(ast_manager & m, const expr_ref_vector & src, expr_ref_vector & tgt) {
        SASSERT(tgt.empty());
        unsigned src_sz = src.size();
        unsigned src_ofs = src_sz-1;

        unsigned max_var_idx = 0;
        for(unsigned i=0; i<src_sz; i++) {
            if(!src[i]) {
                continue;
            }
            SASSERT(is_var(src[i]));
            unsigned var_idx = to_var(src[i])->get_idx();
            if(var_idx>max_var_idx) {
                max_var_idx=var_idx;
            }
        }

        unsigned tgt_sz = max_var_idx+1;
        unsigned tgt_ofs = tgt_sz-1;
        tgt.resize(tgt_sz, 0);
        for(unsigned i=0; i<src_sz; i++) {
            expr * e = src[src_ofs-i];
            if(!e) {
                continue;
            }
            var * v = to_var(e);
            unsigned var_idx = v->get_idx();
            tgt[tgt_ofs-var_idx] = m.mk_var(i, v->get_sort());
        }
    }

    void get_renaming_args(const unsigned_vector & map, const relation_signature & orig_sig, 
            expr_ref_vector & renaming_arg) {
        ast_manager & m = renaming_arg.get_manager();
        unsigned sz = map.size();
        unsigned ofs = sz-1;
        renaming_arg.resize(sz, static_cast<expr *>(0));
        for(unsigned i=0; i<sz; i++) {
            if(map[i]!=UINT_MAX) {
                renaming_arg.set(ofs-i, m.mk_var(map[i], orig_sig[i]));
            }
        }
    }

    void print_renaming(const expr_ref_vector & cont, std::ostream & out) {
        unsigned len = cont.size();
        out << "(";
        for(int i=len-1; i>=0; i--) {
            out << (len-1-i) <<"->";
            if(cont.get(i)==0) {
                out << "{none}";
            }
            else {
                out << to_var(cont.get(i))->get_idx();
            }
            if(i!=0) { out << ","; }
        }
        out << ")\n";
    }

    void cycle_from_permutation(unsigned_vector & permutation, unsigned_vector & cycle) {
        try_remove_cycle_from_permutation(permutation, cycle);
        DEBUG_CODE(
            //here we assert that there is at most one cycle in the permutation
            unsigned_vector aux;
            SASSERT(!try_remove_cycle_from_permutation(permutation, aux));
            );
    }

    bool try_remove_cycle_from_permutation(unsigned_vector & permutation, unsigned_vector & cycle) {
        SASSERT(cycle.empty());
        DEBUG_CODE(
            counter ctr;
            ctr.count(permutation);
            SASSERT(permutation.empty() || ctr.get_max_positive()==permutation.size()-1);
            SASSERT(permutation.empty() || ctr.get_positive_count()==permutation.size());
            );
        unsigned sz = permutation.size();
        for(unsigned i=0; i<sz; i++) {
            if(i==permutation[i]) {
                continue;
            }
            unsigned prev_i = i;
            for(;;) {
                cycle.push_back(prev_i);
                unsigned next_i = permutation[prev_i];
                permutation[prev_i] = prev_i;
                if(next_i==i) {
                    break;
                }
                prev_i = next_i;
            }
            return true;
        }
        return false;
    }

    void collect_sub_permutation(const unsigned_vector & permutation, const unsigned_vector & translation,
            unsigned_vector & res, bool & identity) {
        SASSERT(res.empty());
        identity = true;
        unsigned sz = permutation.size();
        for(unsigned new_i=0; new_i<sz; new_i++) {
            unsigned idx = permutation[new_i];
            bool is_selected = translation[idx]!=UINT_MAX;
            if(is_selected) {
                unsigned sel_idx = translation[idx];
                if(!res.empty() && sel_idx!=res.back()+1) {
                    identity = false;
                }
                res.push_back(sel_idx);
            }
        }
    }

    void collect_and_transform(const unsigned_vector & src, const unsigned_vector & translation, 
            unsigned_vector & res) {
        unsigned n = src.size();
        for(unsigned i=0; i<n; i++) {
            unsigned translated = translation[src[i]];
            if(translated!=UINT_MAX) {
                res.push_back(translated);
            }
        }
    }


    void transform_set(const unsigned_vector & map, const idx_set & src, idx_set & result) {
        idx_set::iterator it = src.begin();
        idx_set::iterator end = src.end();
        for(; it!=end; ++it) {
            result.insert(map[*it]);
        }
    }

    void add_sequence(unsigned start, unsigned count, unsigned_vector & v) {
        unsigned after_last = start+count;
        for(unsigned i=start; i<after_last; i++) {
            v.push_back(i);
        }
    }

    void dealloc_ptr_vector_content(ptr_vector<relation_base> & v) {
        ptr_vector<relation_base>::iterator it = v.begin();
        ptr_vector<relation_base>::iterator end = v.end();
        for(; it!=end; ++it) {
            (*it)->deallocate();
        }
    }


    // -----------------------------------
    //
    // misc helper functions (not datalog related)
    //
    // -----------------------------------

    void get_file_names(std::string directory, std::string extension, bool traverse_subdirs, 
            string_vector & res) {

        if(directory[directory.size()-1]!='\\' && directory[directory.size()-1]!='/') {
#ifdef _WINDOWS
            directory+='\\';
#else
            directory+='/';
#endif
        }

#ifdef _WINDOWS
        WIN32_FIND_DATAA findFileData;
        HANDLE hFind;
        std::string filePattern = directory+"*."+extension;

        hFind = FindFirstFileA(filePattern.c_str(), &findFileData);
        if (hFind != INVALID_HANDLE_VALUE) {
            do {
                char const* name = findFileData.cFileName;
                size_t len = strlen(name);
                if (len > extension.size() && extension == std::string(name+len-extension.size())) {
                    res.push_back(directory+std::string(name));
                }
            } while(FindNextFileA(hFind, &findFileData));
            FindClose(hFind);
        } 


        if(traverse_subdirs) {
            std::string subdirPattern = directory+"*.*";
            hFind = FindFirstFileA(subdirPattern.c_str(), &findFileData);
            if (hFind != INVALID_HANDLE_VALUE) {
                do {
                    if(findFileData.cFileName[0]=='.') {
                        continue;
                    }
                    get_file_names(directory+findFileData.cFileName, extension, traverse_subdirs, res);
                } while(FindNextFileA(hFind, &findFileData));
                FindClose(hFind);
            }
        }

#else
        NOT_IMPLEMENTED_YET();
#endif
    }

    bool file_exists(std::string name) {
        struct stat st;
        if(stat(name.c_str(),&st) == 0) {
            return true;
        }
        return false;
    }

    bool is_directory(std::string name) {
        if(!file_exists(name)) {
            return false;
        }
        struct stat status;
        stat(name.c_str(), &status);
        return (status.st_mode&S_IFDIR)!=0;
    }

    std::string get_file_name_without_extension(std::string name) {
        size_t slash_index = name.find_last_of("\\/");
        size_t dot_index = name.rfind(".");
        size_t ofs = (slash_index==std::string::npos) ? 0 : slash_index+1;
        size_t count = (dot_index!=std::string::npos && dot_index>ofs) ? 
            (dot_index-ofs) : std::string::npos;
        return name.substr(ofs, count);
    }

    bool string_to_uint64(const char * s, uint64 & res) {
#if _WINDOWS
        int converted = sscanf_s(s, "%I64u", &res);
#else
        int converted = sscanf(s, "%llu", &res);
#endif
        if(converted==0) {
            return false;
        }
        SASSERT(converted==1);
        return true;
    }

    bool read_uint64(const char * & s, uint64 & res) {
        static const uint64 max_but_one_digit = ULLONG_MAX/10;
        static const uint64 max_but_one_digit_safe = (ULLONG_MAX-9)/10;

        if(*s<'0' || *s>'9') {
            return false;
        }
        res=*s-'0';
        s++;
        while(*s>='0' && *s<='9') {
            if(res>max_but_one_digit_safe) {
                if(res>max_but_one_digit) {
                    return false; //overflow
                }
                res*=10;
                char digit = *s-'0';
                if(static_cast<int>(ULLONG_MAX-res)-digit<0) {
                    return false; //overflow
                }
                res+=digit;
            }
            else {
                res*=10;
                res+=*s-'0';
                s++;
            }
        }
        return true;
    }

    std::string to_string(uint64 num) {
        std::stringstream stm;
        stm<<num;
        return stm.str();
    }
};

