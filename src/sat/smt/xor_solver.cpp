/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    xor_solver.h

Abstract:

    XOR solver.
    Interface outline.

--*/

#include "sat/smt/xor_matrix_finder.h"
#include "sat/smt/xor_solver.h"
#include "sat/sat_simplifier_params.hpp"
#include "sat/sat_xor_finder.h"

namespace xr {
    
    solver::solver(euf::solver& ctx) :
        solver(ctx.get_manager(), ctx.get_manager().mk_family_id("xor")) {
        m_ctx = &ctx;
    }

    solver::solver(ast_manager& m, euf::theory_id id) : euf::th_solver(m, symbol("xor"), id) { }
    
    solver::~solver() {
        /*for (justification* j : m_justifications) {
            j->deallocate(m_allocator);
        }*/
        clear_gauss_matrices(true);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        // and relevant copy internal state
        return alloc(solver, ctx);
    }
    
    void solver::add_every_combination_xor(const sat::literal_vector& lits, const bool attach) {
        unsigned at = 0, num = 0;
        sat::literal_vector xorlits;
        m_tmp_xor_clash_vars.clear();
        sat::literal lastlit_added = sat::null_literal;
        while (at != lits.size()) {
            xorlits.clear();
            for (unsigned last_at = at; at < last_at + s().get_config().m_xor_gauss_var_per_cut && at < lits.size(); at++) {
                xorlits.push_back(lits[at]);
            }
    
            //Connect to old cut
            if (lastlit_added != sat::null_literal) {
                xorlits.push_back(lastlit_added);
            } else if (at < lits.size()) {
                xorlits.push_back(lits[at]);
                at++;
            }
    
            if (at + 1 == lits.size()) {
                xorlits.push_back(lits[at]);
                at++;
            }
    
            //New lit to connect to next cut
            if (at != lits.size()) {
                const sat::bool_var new_var = m_solver->mk_var();
                m_tmp_xor_clash_vars.push_back(new_var);
                const sat::literal to_add = sat::literal(new_var, false);
                xorlits.push_back(to_add);
                lastlit_added = to_add;
            }
    
            // TODO: Implement the following function. Unfortunately, it is needed (every xor constraint is also present as an ordinary CNF; e.g., if there is only a single xor constraint no GJ elimination will be performed)
            // add_xor_clause_inter_cleaned_cut(xorlits, attach);
            if (s().inconsistent())
                break;
    
            num++;
        }
    }
    
    void solver::add_xor_clause(const sat::literal_vector& lits, bool rhs, const bool attach) {
        // TODO: make overload in which "lits" ==> svector<sat::bool_var>; however, first implement missing function "add_xor_clause_inter_cleaned_cut"
        if (s().inconsistent())
            return;
        TRACE("xor", tout << "adding xor: " << lits << " rhs: " << rhs << "\n");
        SASSERT(!attach || m_prop_queue_head == m_prop_queue.size());
        SASSERT(s().at_search_lvl());
    
        sat::literal_vector ps(lits);
        for (sat::literal& lit: ps) {
            if (lit.sign()) {
                rhs ^= true;
                lit.neg();
            }
        }
        clean_xor_no_prop(ps, rhs);
    
        if (ps.size() >= (0x01UL << 28)) 
            throw default_exception("xor clause too long");
    
        if (ps.empty()) {
            if (rhs)
                m_solver->set_conflict();
            return;
        }
    
        if (rhs)
            ps[0].neg();
    
        //add_every_combination_xor(ps, attach); TODO: Blasts xors; ignored for now
        if (ps.size() > 2) {
            m_xor_clauses_updated = true;
            m_xorclauses.push_back(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
            m_xorclauses_orig.push_back(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
        }
        else {
            // TODO: This completely ignore xors of size <= 2. The case of 2 has to be treated with more care
            add_simple_xor_constraint(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
        }
    }

    void solver::asserted(sat::literal l) {        
        TRACE("xor", tout << "asserted: " << l << "\n";);
        force_push();
        m_prop_queue.push_back(l);
    }

    bool solver::unit_propagate() {
        if (m_prop_queue_head == m_prop_queue.size())
            return false;
        force_push();
        m_ctx->push(value_trail<unsigned>(m_prop_queue_head));
        for (; m_prop_queue_head < m_prop_queue.size() && !s().inconsistent(); ++m_prop_queue_head) {
            sat::literal const p = m_prop_queue[m_prop_queue_head];
            sat::justification conflict = gauss_jordan_elim(p, m_num_scopes);
            if (conflict.is_none()) {
                m_prop_queue_head = m_prop_queue.size();
                s().set_conflict(conflict);
            }
        }
        return true;
    }
    
    sat::justification solver::gauss_jordan_elim(const sat::literal p, const unsigned currLevel) {
        if (m_gmatrices.empty()) 
            return sat::justification(-1);
        for (unsigned i = 0; i < m_gqueuedata.size(); i++) {
            if (m_gqueuedata[i].disabled || !m_gmatrices[i]->is_initialized()) continue;
            m_gqueuedata[i].reset();
            m_gmatrices[i]->update_cols_vals_set();
        }
        
        bool confl_in_gauss = false;
        SASSERT(m_gwatches.size() > p.var());
        svector<gauss_watched>& ws = m_gwatches[p.var()];
        unsigned i = 0, j = 0;
        const unsigned end = ws.size();
        
        for (; i < end; i++) {
            const unsigned matrix_num = ws[i].matrix_num; 
            const unsigned row_n = ws[i].row_n; 
            if (m_gqueuedata[matrix_num].disabled || !m_gmatrices[matrix_num]->is_initialized())
                continue; //remove watch and continue
        
            m_gqueuedata[matrix_num].new_resp_var = UINT_MAX;
            m_gqueuedata[matrix_num].new_resp_row = UINT_MAX;
            m_gqueuedata[matrix_num].do_eliminate = false;
            m_gqueuedata[matrix_num].currLevel = currLevel;
        
            if (m_gmatrices[matrix_num]->find_truths(ws, i, j, p.var(), row_n, m_gqueuedata[matrix_num])) {
                continue;
            } 
            else {
                confl_in_gauss = true;
                i++;
                break;
            }
        }
        
        for (; i < end; i++) 
            ws[j++] = ws[i];
        ws.shrink((unsigned)(i - j));
        
        for (unsigned g = 0; g < m_gqueuedata.size(); g++) {
            if (m_gqueuedata[g].disabled || !m_gmatrices[g]->is_initialized())
                continue;
        
            if (m_gqueuedata[g].do_eliminate) {
                m_gmatrices[g]->eliminate_col(p.var(), m_gqueuedata[g]);
                confl_in_gauss |= (m_gqueuedata[g].status == gauss_res::confl);
            }
        }
        
        for (gauss_data& gqd: m_gqueuedata) {
            if (gqd.disabled) continue;
        
            //There was a conflict but this is not that matrix.
            //Just skip.
            if (confl_in_gauss && gqd.status != gauss_res::confl) 
                continue;
        
            switch (gqd.status) {
                case gauss_res::confl:
                    gqd.num_conflicts++;
                    return gqd.conflict;
        
                case gauss_res::prop:
                    gqd.num_props++;
                    break;
        
                case gauss_res::none:
                    //nothing
                    break;
        
                default:
                    UNREACHABLE();
            }
        }
        return sat::justification(-1);
    }
    
    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx,
                                 sat::literal_vector & r, bool probing) {
        
    }
    
    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }
    
    // TODO: we should separate this parts from the euf_solver. Other non-euf theories might need it as well
    // Similar: Attaching "theory_var"s in non-euf/enode cases  
    void solver::force_push() {
        for (; m_num_scopes > 0; --m_num_scopes) 
            push_core();        
    }
    
    void solver::push_core() {
        m_prop_queue_lim.push_back(m_prop_queue.size());
        //m_justifications_lim.push_back(m_justifications.size());
    }
    
    void solver::pop_core(unsigned num_scopes) {
        SASSERT(m_num_scopes == 0);
        unsigned old_sz = m_prop_queue_lim.size() - num_scopes;
        m_prop_queue.shrink(m_prop_queue_lim[old_sz]);
        m_prop_queue_lim.shrink(old_sz);
        
        /*old_sz = m_justifications_lim.size() - num_scopes;
        unsigned lim = m_justifications_lim[old_sz];
        for (unsigned i = m_justifications.size(); i > lim; i--) {
            m_justifications[i - 1].destroy(m_allocator);
        }
        m_justifications_lim.shrink(old_sz);
        m_justifications.shrink(old_sz);*/
    }
    
    void solver::push() {
        m_num_scopes++; 
    }
    
    void solver::pop(unsigned n) {
        unsigned k = std::min(m_num_scopes, n);
        m_num_scopes -= k;
        n -= k;
        if (n > 0)
            pop_core(n);
    }

    // inprocessing
    // pre_simplify: decompile all xor constraints to allow other in-processing.
    // simplify: recompile clauses to xor constraints
    // literals that get added to xor constraints are tagged with the theory.
    void solver::pre_simplify() {
        
    }

    void solver::simplify() {
        
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }

    // simplify xors by triggering (unit)propagation until nothing changes anymore
    bool solver::clean_xor_clauses(vector<xor_clause>& xors) {     
        SASSERT(!inconsistent());
        
        unsigned last_trail = UINT_MAX;
        while (last_trail != s().trail_size() && !inconsistent()) {
            last_trail = s().trail_size();
            unsigned j = 0;
            for (xor_clause& x : xors) {
                if (inconsistent()) {
                    xors[j++] = x;
                    continue;
                }
        
                const bool keep = clean_one_xor(x);
                if (keep) {
                    SASSERT(x.size() > 2);
                    xors[j++] = x;
                } 
                else {
                    for (const bool_var& v : x.m_clash_vars)
                        m_removed_xorclauses_clash_vars.insert(v);                                        
                }
            }
            xors.shrink(j);
            if (inconsistent()) 
                break;
            s().propagate(false);
        }
        
        return !inconsistent();
    }
    
    // Adds xor constraints of size 0, 1 and 2. In case the constraint is larger the function returns true
    bool solver::add_simple_xor_constraint(const xor_clause& constraint) {
        SASSERT(!inconsistent());
        switch (constraint.size()) {
            case 0:
                if (constraint.m_rhs)
                    s().set_conflict();
                return false;
            case 1: {
                s().assign_scoped(sat::literal(constraint[0], !constraint.m_rhs));
                s().propagate(false);
                return false;
            }
            case 2: {
                /*literal_vector vec(constraint.size());
                for (const auto& v : constraint.m_vars)
                    vec.push_back(literal(v));
                add_xor_clause(vec, constraint.m_rhs, true);*/

                /*m_ctx->e_internalize(m_ctx->bool_var2expr(constraint[0]));
                m_ctx->e_internalize(m_ctx->bool_var2expr(constraint[1]));
                expr* e = m_ctx->mk_eq(m_ctx->bool_var2enode(constraint[0]), m_ctx->bool_var2enode(constraint[1]));
                literal l = m_ctx->expr2literal(e);
                if (constraint.m_rhs)
                    l.neg();
                s().add_clause(l, sat::status::th(false, get_id()));*/
                literal l1(constraint[0]);
                literal l2(constraint[1]);
                if (constraint.m_rhs) { // not equal
                    s().add_clause(l1, l2, sat::status::th(false, get_id()));
                    s().add_clause(~l1, ~l2, sat::status::th(false, get_id()));
                }
                else { // equal
                    s().add_clause(l1, ~l2, sat::status::th(false, get_id()));
                    s().add_clause(~l1, l2, sat::status::th(false, get_id()));
                }
                return false;
            }
            default:
                return true;
        }
    }
    
    // throw away all assigned clash-variables and simplify xor-clause with respect to current assignment
    // may add conflict or propagate
    bool solver::clean_one_xor(xor_clause& x) {
    
        unsigned j = 0;
        for (const bool_var & v : x.m_clash_vars)
            if (s().value(v) == l_undef)
                x.m_clash_vars[j++] = v;
        
        x.m_clash_vars.shrink(j);
    
        j = 0;
        for (const bool_var& v : x) {
            if (s().value(v) != l_undef)
                x.m_rhs  ^= s().value(v) == l_true;
            else
                x[j++] = v;
        }
        x.shrink(j);
        return add_simple_xor_constraint(x);
    }
    
    // reset all data-structures. Resets m_xorclauses from m_xorclauses_orig
    bool solver::clear_gauss_matrices(const bool destruct) {
        // TODO: Include; ignored for now. Maybe we can ignore the detached clauses
        /*if (!destruct) {
            if (!fully_undo_xor_detach()) 
                return false;
        }*/
        m_xor_clauses_updated = true;

        for (EGaussian* g: m_gmatrices) 
            g->move_back_xor_clauses();
        for (EGaussian* g: m_gmatrices) 
            dealloc(g);
        for (auto& w: m_gwatches) 
            w.clear();

        m_gmatrices.clear();
        m_gqueuedata.clear();

        m_xorclauses.clear(); // we rely on xorclauses_orig now
        m_xorclauses_unused.clear();

        if (!destruct)
            for (const auto& x: m_xorclauses_orig)
                m_xorclauses.push_back(x);

        return !s().inconsistent();
    }
    
    bool solver::find_and_init_all_matrices() {
        if (!m_xor_clauses_updated/* && (!m_detached_xor_clauses || !assump_contains_xor_clash())*/)
            return true;
        
        bool can_detach;
        if (!clear_gauss_matrices(false)) 
            return false;
        
        xor_matrix_finder mfinder(*this);
        mfinder.find_matrices(can_detach);
        if (s().inconsistent()) return false;
        if (!init_all_matrices()) return false;
        
        /* TODO: Make this work (ignored for now)
        bool ret_no_irred_nonxor_contains_clash_vars;
        if (can_detach &&
            s().get_config().m_xor_gauss_detach_reattach &&
            !s().get_config().autodisable &&
            (ret_no_irred_nonxor_contains_clash_vars = no_irred_nonxor_contains_clash_vars())) {
            detach_xor_clauses(mfinder.clash_vars_unused);
            unset_clash_decision_vars(xorclauses);
            rebuildOrderHeap();
        }*/
        m_xor_clauses_updated = false;
        return true;
    }
    
    bool solver::init_all_matrices() {
        SASSERT(!s().inconsistent());
        SASSERT(s().at_search_lvl());
        SASSERT(m_gmatrices.size() == m_gqueuedata.size());
        
        for (unsigned i = 0; i < m_gmatrices.size(); i++) {
            auto& g = m_gmatrices[i];
            bool created = false;
            if (!g->full_init(created)) 
                return false;
            SASSERT(!s().inconsistent());
    
            if (!created) {
                m_gqueuedata[i].disabled = true;
                memory::deallocate(g);
                g = nullptr;
            }
        }
    
        unsigned j = 0;
        bool modified = false;
        for (unsigned i = 0; i < m_gqueuedata.size(); i++) {
            if (m_gmatrices[i] == nullptr) {
                modified = true;
                continue;
            }
            if (!modified) {
                j++;
                continue;
            }
            m_gmatrices[j] = m_gmatrices[i];
            m_gmatrices[j]->update_matrix_no(j);
            m_gqueuedata[j] = m_gqueuedata[i];
            
            for (unsigned var = 0; var < s().num_vars(); var++) 
                for (gauss_watched& k : m_gwatches[var]) 
                    if (k.matrix_num == i)
                        k.matrix_num = j;
            j++;
        }
        m_gqueuedata.shrink(j);
        m_gmatrices.shrink(j);
        
        return !s().inconsistent();
    }
    
    bool solver::xor_has_interesting_var(const xor_clause& x) {
        return std::any_of(x.begin(), x.end(), [&](bool_var v) { return s().num_visited(v) > 1; });
    }
    
    // moves all non-detached (as those are anyway relevant) xor clauses which variables occur in no other xor clause to unused 
    void solver::move_xors_without_connecting_vars_to_unused() {
        if (m_xorclauses.empty()) 
            return;
    
        vector<xor_clause> cleaned;
        s().init_visited(2);
        
        for (const xor_clause& x: m_xorclauses) 
            for (bool_var v : x) 
                s().inc_visited(v);
    
        //has at least 1 var with occur of 2
        for (const xor_clause& x: m_xorclauses) {
            bool has_connecting_var = x.m_detached || xor_has_interesting_var(x);
            TRACE("xor", tout << "XOR " << (has_connecting_var ? "" : "has no") << "connecting var : " << x << ")\n");

            if (has_connecting_var)                 
                cleaned.push_back(x);
            else 
                m_xorclauses_unused.push_back(x);
        }
        
        m_xorclauses = cleaned;
    }

    // As the name suggests: Checks if there are (syntactically) equivalent xors and removes all these duplicates
    void solver::clean_equivalent_xors(vector<xor_clause>& txors){
        if (!txors.empty()) {
            for (xor_clause& x: txors) 
                std::sort(x.begin(), x.end());            
            std::sort(txors.begin(), txors.end());
    
            m_visited.init_visited(s().num_vars());
            
            unsigned sz = 1;
            unsigned j = 0;
            for (unsigned i = 1; i < txors.size(); i++) {
                xor_clause& jd = txors[j];
                xor_clause& id = txors[i];
                if (jd.m_vars == id.m_vars && jd.m_rhs == id.m_rhs) {
                    jd.merge_clash(id, m_visited, s().num_vars());
                    jd.m_detached |= id.m_detached;
                } 
                else {
                    j++;
                    txors[j] = txors[i];
                    sz++;
                }
            }
            txors.resize(sz);
        }
    }
    
    sat::justification solver::mk_justification(const int level, const unsigned int matrix_no, const unsigned int row_i) {
        void* mem = m_ctx->get_region().allocate(justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) justification(matrix_no, row_i);
        return sat::justification::mk_ext_justification(level, constraint->to_index()); 
    }
    
    // sort xors, eliminate duplicates, and eliminate negations by flipping rhs
    void solver::clean_xor_no_prop(sat::literal_vector & ps, bool & rhs) {
        std::sort(ps.begin(), ps.end());
        sat::literal p_last = sat::null_literal;
        unsigned j = 0;
        for (auto p : ps) {
            SASSERT(!p.sign());
            if (p.var() == p_last.var()) {                
                // added, but easily removed
                j--;
                p_last = sat::null_literal;
                // Flip rhs if necessary
                if (s().value(p) != l_undef) 
                    rhs ^= s().value(p) == l_true;                
            } 
            else if (s().value(p) == l_undef) 
                // Add and remember as last one to have been added
                ps[j++] = p_last = p;            
            else 
                // modify rhs instead of adding
                rhs ^= s().value(p) == l_true;
        }
        ps.shrink(j);
    }
    
    bool solver::xor_together_xors(vector<xor_clause>& xors) {
        
        if (xors.empty())
            return !s().inconsistent();
        
        if (m_occ_cnt.size() != s().num_vars()) {
            m_occ_cnt.clear();
            m_occ_cnt.resize(s().num_vars(), 0);
        }
    
        TRACE("xor",
            tout << "XOR-ing together XORs. Starting with: " << "\n";
            for (const auto& x : xors)
                tout << "XOR before xor-ing together: " << x << "\n";);
        
        SASSERT(!s().inconsistent());
        SASSERT(s().at_search_lvl());
        const size_t origsize = xors.size();
    
        SASSERT(m_occurrences.empty());

        vector<unsigned_vector> occurs;
        occurs.reserve(s().num_vars());
    
        // Link in xors into watchlist
        for (unsigned i = 0; i < xors.size(); i++) {
            const xor_clause& x = xors[i];
            for (bool_var v: x) {
                if (m_occ_cnt[v] == 0) 
                    m_occurrences.push_back(v);
                m_occ_cnt[v]++;
                occurs[v].push_back(i);
            }
        }
    
        s().init_visited();

        // We can only eliminate variables that are non-external and not used in clauses.
        // Don't XOR together over variables that are external
        for (unsigned i = 0; i < s().num_vars(); i++)
            if (s().is_external(i))
                s().mark_visited(i);

        // Don't XOR together over variables that are in irredundant clauses
        // learned clauses are redundant.
        for (unsigned i = 0; i < 2 * s().num_vars(); i++) 
            for (const auto& w: s().get_wlist(i)) 
                if (w.is_binary_clause() && !w.is_learned())
                    s().mark_visited(w.get_literal().var());
    
        for (const auto& cl: s().clauses()) 
            if (!cl->is_learned())
                for (literal l: *cl)
                    s().mark_visited(l.var());
    
        // until fixedpoint
        bool changed = true;
        while (changed) {
            changed = false;
            m_interesting.clear();
            for (bool_var v : m_occurrences)
                if (m_occ_cnt[v] == 2 && !s().is_visited(v))
                    m_interesting.push_back(v);
    
            while (!m_interesting.empty()) {
    
                // Pop and check if it can be XOR-ed together
                const unsigned v = m_interesting.back();
                m_interesting.pop_back();
                if (m_occ_cnt[v] != 2)
                    continue;

                unsigned indexes[2];
                unsigned at = 0;
                unsigned_vector& ws = occurs[v];
                for (unsigned i : ws) 
                    if (!xors[i].empty()) 
                        indexes[at++] = i;
                SASSERT(at == 2);
                
                
                xor_clause& x0 = xors[indexes[0]];
                xor_clause& x1 = xors[indexes[1]];
                unsigned clash_var;
                unsigned clash_num = xor_two(&x0, &x1, clash_var);
    
                // If they are equivalent
                if (x0.size() == x1.size()
                    && x0.m_rhs == x1.m_rhs
                    && clash_num == x0.size()) {
                    
                    TRACE("xor", tout 
                        << "x1: " << x0 << " -- at idx: " << indexes[0] 
                        << "and  x2: " << x1 << " -- at idx: " << indexes[1] 
                        << "are equivalent.\n");
    
                    // Update clash values & detached values
                    x1.merge_clash(x0, m_visited, s().num_vars());
                    x1.m_detached |= x0.m_detached;
    
                    TRACE("xor", tout << "after merge: " << x1 <<  " -- at idx: " << indexes[1] << "\n";);

                    x0 = xor_clause();
                    
                    for (unsigned v2: x1) {
                        SASSERT(m_occ_cnt[v2] >= 2);
                        m_occ_cnt[v2]--;
                        if (m_occ_cnt[v2] == 2 && !s().is_visited(v2))
                            m_interesting.push_back(v2);                        
                    }
                }
                else if (clash_num > 1 || x0.m_detached || x1.m_detached) {
                    // keep x0, x1 in watch-list                    
                }
                else {
                    m_occ_cnt[v] -= 2;
                    SASSERT(m_occ_cnt[v] == 0);
    
                    xor_clause x_new(m_tmp_vars_xor_two, x0.m_rhs ^ x1.m_rhs, clash_var);
                    x_new.merge_clash(x0, m_visited, s().num_vars());
                    x_new.merge_clash(x1, m_visited, s().num_vars());
    
                    TRACE("xor", tout 
                        << "x1: " << x0 << " -- at idx: " << indexes[0] << "\n" 
                        << "x2: " << x1 << " -- at idx: " << indexes[1] << "\n"
                        << "clashed on var: " << clash_var+1 << "\n"
                        << "final: " << x_new <<  " -- at idx: " << xors.size() << "\n";);

                    // NSB - m_occ_cnt is not being updated on variables?
                    changed = true;
                    x0 = xor_clause();
                    x1 = xor_clause();
                    xors.push_back(x_new);
                    for (bool_var v2 : x_new) {
                        occurs[v2].push_back(xors.size()-1);
                        SASSERT(m_occ_cnt[v2] >= 1);
                        if (m_occ_cnt[v2] == 2 && !s().is_visited(v2)) 
                            m_interesting.push_back(v2);                        
                    }
                }
            }
        }

        for (auto v : m_occurrences)
            m_occ_cnt[v] = 0;

        m_occurrences.reset();
    
        clean_xors_from_empty(xors);
    
        return !s().inconsistent();
    }
    
    
    
    // Removes all xor clauses that do not contain any variables 
    // (and have rhs = false; i.e., are trivially satisfied) and move them to unused
    void solver::clean_xors_from_empty(vector<xor_clause>& thisxors) {
        unsigned j = 0;
        for (xor_clause& x : thisxors) {
            if (x.is_true()) {
                if (!x.m_clash_vars.empty()) 
                    m_xorclauses_unused.push_back(x);
            }
            else
                thisxors[j++] = x;
        }
        thisxors.shrink(j);
    }
    
    // Merge two xor clauses; the resulting clause is in m_tmp_vars_xor_two and the variable where it was glued is in clash_var
    // returns 0 if no common variable was found, 1 if there was exactly one and 2 if there are more
    // only 1 is successful
    unsigned solver::xor_two(xor_clause const* x1_p, xor_clause const* x2_p, bool_var& clash_var) {
        m_tmp_vars_xor_two.clear();
        if (x1_p->size() > x2_p->size())
            std::swap(x1_p, x2_p);
        
        const xor_clause& x1 = *x1_p;
        const xor_clause& x2 = *x2_p;
    
        m_visited.init_visited(s().num_vars(), 2);
        
        unsigned clash_num = 0;
        for (bool_var v : x1) {
            SASSERT(!m_visited.is_visited(v));
            m_visited.inc_visited(v);
        }
    
        bool_var i_x2;
        bool early_abort = false;
        for (i_x2 = 0; i_x2 < x2.size(); i_x2++) {
            bool_var v = x2[i_x2];
            SASSERT(m_visited.num_visited(v) < 2);
            if (!m_visited.is_visited(v)) {
                m_tmp_vars_xor_two.push_back(v);
            } 
            else {
                clash_var = v;
                if (clash_num > 0 && clash_num != i_x2) {
                    //early abort, it's never gonna be good
                    clash_num++;
                    early_abort = true;
                    break;
                }
                clash_num++;
            }
            
            m_visited.inc_visited(v, 2);
        }
    
        if (!early_abort) 
            for (bool_var v: x1) 
                if (m_visited.num_visited(v) < 2) 
                    m_tmp_vars_xor_two.push_back(v);
    
        return clash_num;
    }
    
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const  {
        return out;
    }
    
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }
}

