/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qe_lite.cpp

Abstract:

    Light weight partial quantifier-elimination procedure

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-17

Revision History:

 - TBD: integrate Fourier Motzkin elimination
        integrate Gaussean elimination

--*/
#include "qe_lite.h"
#include "expr_abstract.h"
#include "used_vars.h"
#include"occurs.h"
#include"for_each_expr.h"
#include"rewriter_def.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"ast_smt2_pp.h"
#include"tactical.h"
#include"bool_rewriter.h"
#include"var_subst.h"

class der2 {
    ast_manager &   m;
    var_subst       m_subst;
    expr_ref_buffer m_new_exprs;
    
    ptr_vector<expr> m_map;
    int_vector       m_pos2var;
    ptr_vector<var>  m_inx2var;
    unsigned_vector  m_order;
    expr_ref_vector  m_subst_map;
    expr_ref_buffer  m_new_args;

    /**
       \brief Return true if e can be viewed as a variable disequality. 
       Store the variable id in v and the definition in t.
       For example:

          if e is (not (= (VAR 1) T)), then v assigned to 1, and t to T.
          if e is (iff (VAR 2) T), then v is assigned to 2, and t to (not T).
              (not T) is used because this formula is equivalent to (not (iff (VAR 2) (not T))),
              and can be viewed as a disequality.
    */
    bool is_var_diseq(expr * e, unsigned num_decls, var *& v, expr_ref & t);

    /**
       \brief Return true if e can be viewed as a variable equality.
    */
    bool is_var_eq(expr * e, unsigned num_decls, var *& v, expr_ref & t);

    bool is_var_def(bool check_eq, expr* e, unsigned num_decls, var*& v, expr_ref& t);

    void get_elimination_order();
    void create_substitution(unsigned sz);
    void apply_substitution(quantifier * q, expr_ref & r);
    void reduce_quantifier1(quantifier * q, expr_ref & r, proof_ref & pr);
    void elim_unused_vars(expr_ref& r, proof_ref &pr);

public:
    der2(ast_manager & m):m(m),m_subst(m),m_new_exprs(m),m_subst_map(m),m_new_args(m) {}
    void operator()(quantifier * q, expr_ref & r, proof_ref & pr);
    void reduce_quantifier(quantifier * q, expr_ref & r, proof_ref & pr);
    ast_manager& get_manager() const { return m; }
};

static bool is_var(expr * e, unsigned num_decls) {
    return is_var(e) && to_var(e)->get_idx() < num_decls;
}

static bool is_neg_var(ast_manager & m, expr * e, unsigned num_decls) {
    expr* e1;
    return m.is_not(e, e1) && is_var(e1, num_decls);
}

bool der2::is_var_def(bool check_eq, expr* e, unsigned num_decls, var*& v, expr_ref& t) {
    if (check_eq) {
        return is_var_eq(e, num_decls, v, t);
    }
    else {
        return is_var_diseq(e, num_decls, v, t);
    }    
}

bool der2::is_var_eq(expr * e, unsigned num_decls, var * & v, expr_ref & t) {
    expr* lhs, *rhs;
    
    // (= VAR t), (iff VAR t), (iff (not VAR) t), (iff t (not VAR)) cases    
    if (m.is_eq(e, lhs, rhs) || m.is_iff(e, lhs, rhs)) {
        // (iff (not VAR) t) (iff t (not VAR)) cases
        if (!is_var(lhs, num_decls) && !is_var(rhs, num_decls) && m.is_bool(lhs)) {
            if (!is_neg_var(m, lhs, num_decls)) {
                std::swap(lhs, rhs);
            }
            if (!is_neg_var(m, lhs, num_decls)) {
                return false;
            }
            v = to_var(lhs);
            t = m.mk_not(rhs);
            m_new_exprs.push_back(t);
            TRACE("der", tout << mk_pp(e, m) << "\n";);
            return true;
        }
        if (!is_var(lhs, num_decls))
            std::swap(lhs, rhs);
        if (!is_var(lhs, num_decls))
            return false;
        v = to_var(lhs);
        t = rhs;
        TRACE("der", tout << mk_pp(e, m) << "\n";);
        return true;
    }

    // (ite cond (= VAR t) (= VAR t2)) case
    expr* cond, *e2, *e3;
    if (m.is_ite(e, cond, e2, e3)) {
        if (is_var_eq(e2, num_decls, v, t)) {
            expr_ref t2(m);
            var* v2;
            if (is_var_eq(e3, num_decls, v2, t2) && v2 == v) {
                t = m.mk_ite(cond, t, t2);
                m_new_exprs.push_back(t);
                return true;
            }
        }
        return false;
    }

    // VAR = true case
    if (is_var(e, num_decls)) {
        t = m.mk_true();
        v = to_var(e);
        TRACE("der", tout << mk_pp(e, m) << "\n";);
        return true;
    }

    // VAR = false case
    if (is_neg_var(m, e, num_decls)) {
        t = m.mk_false();
        v = to_var(to_app(e)->get_arg(0));
        TRACE("der", tout << mk_pp(e, m) << "\n";);
        return true;
    }

    return false;
}

/**
   \brief Return true if \c e is of the form (not (= VAR t)) or (not (iff VAR t)) or 
                                (iff VAR t) or (iff (not VAR) t) or (VAR IDX) or (not (VAR IDX)).
   The last case can be viewed 
*/
bool der2::is_var_diseq(expr * e, unsigned num_decls, var * & v, expr_ref & t) {
    expr* e1;
    if (m.is_not(e, e1)) {
        return is_var_eq(e, num_decls, v, t);
    }
    else if (is_var_eq(e, num_decls, v, t) && m.is_bool(v)) { 
        bool_rewriter(m).mk_not(t, t);
        m_new_exprs.push_back(t);
        return true;
    }
    else {
        return false;
    }
}

void der2::elim_unused_vars(expr_ref& r, proof_ref& pr) {
    if (is_quantifier(r)) {
        quantifier * q = to_quantifier(r);
        ::elim_unused_vars(m, q, r);
        if (m.proofs_enabled()) {
            proof * p1 = m.mk_elim_unused_vars(q, r);
            pr = m.mk_transitivity(pr, p1);
        }
    }
}

/**
   Reduce the set of definitions in quantifier.
   Then eliminate variables that have become unused
*/
void der2::operator()(quantifier * q, expr_ref & r, proof_ref & pr) {
    TRACE("der", tout << mk_pp(q, m) << "\n";);    
    pr = 0;
    r  = q;
    reduce_quantifier(q, r, pr);    
    if (r != q) {
        elim_unused_vars(r, pr);
    }
}

void der2::reduce_quantifier(quantifier * q, expr_ref & r, proof_ref & pr) {   
    r = q;
    // Keep applying reduce_quantifier1 until r doesn't change anymore
    do {
        proof_ref curr_pr(m);
        q  = to_quantifier(r);
        reduce_quantifier1(q, r, curr_pr);
        if (m.proofs_enabled()) {
            pr = m.mk_transitivity(pr, curr_pr);
        }
    } while (q != r && is_quantifier(r));

    m_new_exprs.reset();
}

void der2::reduce_quantifier1(quantifier * q, expr_ref & r, proof_ref & pr) {    
    expr * e = q->get_expr();
    unsigned num_decls = q->get_num_decls();
    var * v = 0;
    expr_ref t(m);    
    unsigned num_args = 1;
    expr* const* args = &e;
    if ((q->is_forall() && m.is_or(e)) ||
        (q->is_exists() && m.is_and(e))) {
        num_args = to_app(e)->get_num_args();
        args     = to_app(e)->get_args();
    }

    unsigned def_count = 0;
    unsigned largest_vinx = 0;
    
    m_map.reset();
    m_pos2var.reset();
    m_inx2var.reset();    
    m_pos2var.reserve(num_args, -1);
    
    // Find all definitions
    for (unsigned i = 0; i < num_args; i++) {
        if (is_var_def(q->is_exists(), args[i], num_decls, v, t)) {
            unsigned idx = v->get_idx();
            if(m_map.get(idx, 0) == 0) {
                m_map.reserve(idx + 1, 0);
                m_inx2var.reserve(idx + 1, 0);                
                m_map[idx] = t;
                m_inx2var[idx] = v;
                m_pos2var[i] = idx;
                def_count++;
                largest_vinx = std::max(idx, largest_vinx); 
            }
        }
    }
    
    if (def_count > 0) {
        get_elimination_order();
        SASSERT(m_order.size() <= def_count); // some might be missing because of cycles
        
        if (!m_order.empty()) {            
            create_substitution(largest_vinx + 1);
            apply_substitution(q, r);
        }
        else {
            r = q;
        }
    }
    else {
        TRACE("der_bug", tout << "Did not find any diseq\n" << mk_pp(q, m) << "\n";);
        r = q;
    }
 
    if (m.proofs_enabled()) {
        pr = r == q ? 0 : m.mk_der(q, r);
    }    
}

static void der_sort_vars(ptr_vector<var> & vars, ptr_vector<expr> & definitions, unsigned_vector & order) {
    order.reset();
    
    // eliminate self loops, and definitions containing quantifiers.
    bool found = false;
    for (unsigned i = 0; i < definitions.size(); i++) {
        var * v  = vars[i];
        expr * t = definitions[i];
        if (t == 0 || has_quantifiers(t) || occurs(v, t))
            definitions[i] = 0;
        else
            found = true; // found at least one candidate
    }
    
    if (!found)
        return;

    typedef std::pair<expr *, unsigned> frame;
    svector<frame> todo;

    expr_fast_mark1 visiting;
    expr_fast_mark2 done;

    unsigned vidx, num;

    for (unsigned i = 0; i < definitions.size(); i++) {
        if (definitions[i] == 0)
            continue;
        var * v = vars[i];
        SASSERT(v->get_idx() == i);
        SASSERT(todo.empty());
        todo.push_back(frame(v, 0));
        while (!todo.empty()) {
        start:
            frame & fr = todo.back();
            expr * t   = fr.first;
            if (t->get_ref_count() > 1 && done.is_marked(t)) {
                todo.pop_back();
                continue;
            }
            switch (t->get_kind()) {
            case AST_VAR:
                vidx = to_var(t)->get_idx();
                if (fr.second == 0) {
                    CTRACE("der_bug", vidx >= definitions.size(), tout << "vidx: " << vidx << "\n";);
                    // Remark: The size of definitions may be smaller than the number of variables occuring in the quantified formula.
                    if (definitions.get(vidx, 0) != 0) {
                        if (visiting.is_marked(t)) {
                            // cycle detected: remove t
                            visiting.reset_mark(t);
                            definitions[vidx] = 0;
                        }
                        else {
                            visiting.mark(t);
                            fr.second = 1;
                            todo.push_back(frame(definitions[vidx], 0));
                            goto start;
                        }
                    }
                }
                else {
                    SASSERT(fr.second == 1);
                    if (definitions.get(vidx, 0) != 0) {
                        visiting.reset_mark(t);
                        order.push_back(vidx);
                    }
                    else {
                        // var was removed from the list of candidate vars to elim cycle
                        // do nothing
                    }
                }
                if (t->get_ref_count() > 1)
                    done.mark(t);
                todo.pop_back();
                break;
            case AST_QUANTIFIER:
                UNREACHABLE();
                todo.pop_back();
                break;
            case AST_APP:
                num = to_app(t)->get_num_args();
                while (fr.second < num) {
                    expr * arg = to_app(t)->get_arg(fr.second);
                    fr.second++;
                    if (arg->get_ref_count() > 1 && done.is_marked(arg))
                        continue;
                    todo.push_back(frame(arg, 0));
                    goto start;
                }
                if (t->get_ref_count() > 1)
                    done.mark(t);
                todo.pop_back();
                break;
            default:
                UNREACHABLE();
                todo.pop_back();
                break;
            }
        }
    }
}

void der2::get_elimination_order() {
    m_order.reset();

    TRACE("top_sort",
        tout << "DEFINITIONS: " << std::endl;
        for(unsigned i = 0; i < m_map.size(); i++)
            if(m_map[i]) tout << "VAR " << i << " = " << mk_pp(m_map[i], m) << std::endl;
      );

    // der2::top_sort ts(m);
    der_sort_vars(m_inx2var, m_map, m_order);

    TRACE("der", 
            tout << "Elimination m_order:" << std::endl;
            for(unsigned i=0; i<m_order.size(); i++)
            {
                if (i != 0) tout << ",";
                tout << m_order[i];
            }
            tout << std::endl;            
          );
}

void der2::create_substitution(unsigned sz) {
    m_subst_map.reset();
    m_subst_map.resize(sz, 0);

    for(unsigned i = 0; i < m_order.size(); i++) {
        expr_ref cur(m_map[m_order[i]], m);

        // do all the previous substitutions before inserting
        expr_ref r(m);
        m_subst(cur, m_subst_map.size(), m_subst_map.c_ptr(), r);

        unsigned inx = sz - m_order[i]- 1;
        SASSERT(m_subst_map[inx]==0);
        m_subst_map[inx] = r;
    }
}

void der2::apply_substitution(quantifier * q, expr_ref & r) {
    expr * e = q->get_expr();
    unsigned num_args=to_app(e)->get_num_args(); 
    bool_rewriter rw(m);
    
    // get a new expression
    m_new_args.reset();
    for(unsigned i = 0; i < num_args; i++) {
        int x = m_pos2var[i];
        if (x != -1 && m_map[x] != 0) 
            continue; // this is a disequality with definition (vanishes)
                
        m_new_args.push_back(to_app(e)->get_arg(i));
    }

    expr_ref t(m);
    if (q->is_forall()) {
        rw.mk_or(m_new_args.size(), m_new_args.c_ptr(), t);
    }
    else {
        rw.mk_and(m_new_args.size(), m_new_args.c_ptr(), t);
    }
    expr_ref new_e(m);    
    m_subst(t, m_subst_map.size(), m_subst_map.c_ptr(), new_e);
    
    // don't forget to update the quantifier patterns
    expr_ref_buffer  new_patterns(m);
    expr_ref_buffer  new_no_patterns(m);
    for (unsigned j = 0; j < q->get_num_patterns(); j++) {
        expr_ref new_pat(m);
        m_subst(q->get_pattern(j), m_subst_map.size(), m_subst_map.c_ptr(), new_pat);
        new_patterns.push_back(new_pat);
    }

    for (unsigned j = 0; j < q->get_num_no_patterns(); j++) {
        expr_ref new_nopat(m);
        m_subst(q->get_no_pattern(j), m_subst_map.size(), m_subst_map.c_ptr(), new_nopat);
        new_no_patterns.push_back(new_nopat);
    }

    r = m.update_quantifier(q, new_patterns.size(), new_patterns.c_ptr(), 
                            new_no_patterns.size(), new_no_patterns.c_ptr(), new_e);
}





class qe_lite::impl {
    ast_manager& m;
    der2         m_der;

public:
    impl(ast_manager& m): m(m), m_der(m) {}
    
    void operator()(app_ref_vector& vars, expr_ref& fml) {
        expr_ref tmp(fml);
        quantifier_ref q(m);
        proof_ref pr(m);     
        symbol qe_lite("QE");
        expr_abstract(m, 0, vars.size(), (expr*const*)vars.c_ptr(), fml, tmp);
        ptr_vector<sort> sorts;
        svector<symbol> names;
        for (unsigned i = 0; i < vars.size(); ++i) {
            sorts.push_back(m.get_sort(vars[i].get()));
            names.push_back(vars[i]->get_decl()->get_name());
        }
        q = m.mk_exists(vars.size(), sorts.c_ptr(), names.c_ptr(), tmp, 1, qe_lite);
        m_der.reduce_quantifier(q, tmp, pr);
        // assumes m_der just updates the quantifier and does not change things more.
        if (is_exists(tmp) && to_quantifier(tmp)->get_qid() == qe_lite) {
            used_vars used;
            tmp = to_quantifier(tmp)->get_expr();
            used.process(tmp);
            var_subst vs(m, true);
            vs(tmp, vars.size(), (expr*const*)vars.c_ptr(), fml);
            // collect set of variables that were used.
            unsigned j = 0;
            for (unsigned i = 0; i < vars.size(); ++i) {
                if (used.contains(vars.size()-i-1)) {
                    vars[j] = vars[i];
                    ++j;
                }
            }
            vars.resize(j);            
        }        
        else {
            fml = tmp;
        }
    }

    void operator()(expr_ref& fml, proof_ref& pr) {
        // TODO apply der everywhere as a rewriting rule.
        // TODO add cancel method.
        if (is_quantifier(fml)) {
            m_der(to_quantifier(fml), fml, pr);
        }
    }

};

qe_lite::qe_lite(ast_manager& m) {
    m_impl = alloc(impl, m);
}

qe_lite::~qe_lite() {
    dealloc(m_impl);
}

void qe_lite::operator()(app_ref_vector& vars, expr_ref& fml) {
    (*m_impl)(vars, fml);
}

void qe_lite::operator()(expr_ref& fml, proof_ref& pr) {
    (*m_impl)(fml, pr);
}
