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
    
            // TODO: Implement the following function. Unfortunately, it is needed
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
    
        add_every_combination_xor(ps, attach);
        if (ps.size() > 2) {
            m_xor_clauses_updated = true;
            m_xorclauses.push_back(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
            m_xorclauses_orig.push_back(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
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
        gauss_watched* i = ws.begin();
        gauss_watched* j = i;
        const gauss_watched* end = ws.end();
        
        for (; i != end; i++) {
            if (m_gqueuedata[i->matrix_num].disabled || !m_gmatrices[i->matrix_num]->is_initialized())
                continue; //remove watch and continue
        
            m_gqueuedata[i->matrix_num].new_resp_var = UINT_MAX;
            m_gqueuedata[i->matrix_num].new_resp_row = UINT_MAX;
            m_gqueuedata[i->matrix_num].do_eliminate = false;
            m_gqueuedata[i->matrix_num].currLevel = currLevel;
        
            if (m_gmatrices[i->matrix_num]->find_truths(i, j, p.var(), i->row_n, m_gqueuedata[i->matrix_num])) {
                continue;
            } else {
                confl_in_gauss = true;
                i++;
                break;
            }
        }
        
        for (; i != end; i++) 
            *j++ = *i;
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
        for (; m_num_scopes > 0; --m_num_scopes) {
            push_core();
        }
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
                    for (const auto& v : x.m_clash_vars) {
                        m_removed_xorclauses_clash_vars.insert(v);                    
                    }
                }
            }
            xors.shrink(j);
            if (inconsistent()) break;
            s().propagate(false);
        }
        
        return !inconsistent();
    }
    
    
    bool solver::clean_one_xor(xor_clause& x) {
    
        unsigned j = 0;
        for (auto const& v : x.m_clash_vars)
            if (s().value(v) == l_undef)
                x.m_clash_vars[j++] = v;
        
        x.m_clash_vars.shrink(j);
    
        j = 0;
        for (auto const& v : x) {
            if (s().value(v) != l_undef)
                x.m_rhs  ^= s().value(v) == l_true;
            else
                x[j++] = v;
        }
        x.shrink(j);
        SASSERT(!inconsistent());
        switch (x.size()) {
            case 0:
                if (x.m_rhs)
                    s().set_conflict();
                /*TODO: Implement
                if (inconsistent()) {
                    SASSERT(m_solver.unsat_cl_ID == 0);
                    m_solver.unsat_cl_ID = solver->clauseID;
                }*/
                return false;
            case 1: {
                s().assign_scoped(sat::literal(x[0], !x.m_rhs));
                s().propagate(false);
                return false;
            }
            case 2: {
                sat::literal_vector vec(x.size());
                for (const auto& v : x.m_vars)
                    vec.push_back(sat::literal(v));
                add_xor_clause(vec, x.m_rhs, true);
                return false;
            }
            default:
                return true;
        }
    }
    
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
            
            for (unsigned var = 0; var < s().num_vars(); var++) {
                for (gauss_watched& k : m_gwatches[var]) {
                    if (k.matrix_num == i)
                        k.matrix_num = j;
                }
            }
            j++;
        }
        m_gqueuedata.shrink(j);
        m_gmatrices.shrink(j);
        
        return !s().inconsistent();
    }
    
    bool solver::xor_has_interesting_var(const xor_clause& x) {
        return std::any_of(x.begin(), x.end(), [&](bool_var v) { return s().num_visited(v) > 1; });
    }
    
    void solver::move_xors_without_connecting_vars_to_unused() {
        if (m_xorclauses.empty()) 
            return;
    
        vector<xor_clause> cleaned;
        s().init_visited(2);
        
        for(const xor_clause& x: m_xorclauses) {
            for (unsigned v : x) {
                s().inc_visited(v);
            }
        }
    
        //has at least 1 var with occur of 2
        for(const xor_clause& x: m_xorclauses) {
            if (xor_has_interesting_var(x) || x.m_detached) {
                TRACE("xor", tout << "XOR has connecting var: " << x << "\n";);
                cleaned.push_back(x);
            } else {
                TRACE("xor", tout << "XOR has no connecting var: " << x << "\n";);
                m_xorclauses_unused.push_back(x);
            }
        }
        
        m_xorclauses = cleaned;
    }
    
    void solver::clean_equivalent_xors(vector<xor_clause>& txors){
        if (!txors.empty()) {
            size_t orig_size = txors.size();
            for (xor_clause& x: txors) {
                std::sort(x.begin(), x.end());
            }
            std::sort(txors.begin(), txors.end());
    
            unsigned sz = 1;
            unsigned j = 0;
            for (unsigned i = 1; i < txors.size(); i++) {
                auto& jd = txors[j];
                auto& id = txors[i];
                if (jd.m_vars == id.m_vars && jd.m_rhs == id.m_rhs) {
                    jd.merge_clash(id, m_visited);
                    jd.m_detached |= id.m_detached;
                } else {
                    j++;
                    j = i;
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
    
    void solver::clean_xor_no_prop(sat::literal_vector & ps, bool & rhs) {
        std::sort(ps.begin(), ps.end());
        sat::literal p = sat::null_literal;
        unsigned i = 0, j = 0;
        for (; i != ps.size(); i++) {
            SASSERT(!ps[i].sign());
            if (ps[i].var() == p.var()) {
                //added, but easily removed
                j--;
                p = sat::null_literal;
                //Flip rhs if necessary
                if (s().value(ps[i]) != l_undef) {
                    rhs ^= s().value(ps[i]) == l_true;
                }
            } else if (s().value(ps[i]) == l_undef) {
                //Add and remember as last one to have been added
                ps[j++] = p = ps[i];
            } else {
                //modify rhs instead of adding
                rhs ^= s().value(ps[i]) == l_true;
            }
        }
        ps.resize(ps.size() - (i - j));
    }
    
    bool solver::xor_together_xors(vector<xor_clause>& xors) {
        
        if (xors.empty())
            return !s().inconsistent();
        
        if (m_occ_cnt.size() != s().num_vars()) {
            m_occ_cnt.clear();
            m_occ_cnt.resize(s().num_vars(), 0);
        }
    
        TRACE_CODE( 
            TRACE("xor", tout << "XOR-ing together XORs. Starting with: " << "\n";);
            for (const auto& x: xors) {
                TRACE("xor", tout << "XOR before xor-ing together: " << x << "\n";);
            };
        );
        
        SASSERT(!s().inconsistent());
        SASSERT(s().at_search_lvl());
        const size_t origsize = xors.size();
    
        unsigned xored = 0;
        SASSERT(m_occurrences.empty());
    #if 0
        //Link in xors into watchlist
        for (unsigned i = 0; i < xors.size(); i++) {
            const xor_clause& x = xors[i];
            for (bool_var v: x) {
                if (m_occ_cnt[v] == 0) {
                    m_occurrences.push_back(v);
                }
                m_occ_cnt[v]++;
    
                sat::literal l(v, false);
                SASSERT(s()->watches.size() > l.toInt());
                m_watches[l].push(Watched(i, WatchType::watch_idx_t));
                m_watches.smudge(l);
            }
        }
    
        //Don't XOR together over variables that are in regular clauses
        s().init_visited();
        
        for (unsigned i = 0; i < 2 * s().num_vars(); i++) {
            const auto& ws = s().get_wlist(i);
            for (const auto& w: ws) {
                if (w.is_binary_clause()/* TODO: Does redundancy information exist in Z3? Can we use learned instead of "!w.red()"?*/ && !w.is_learned()) {
                    sat::bool_var v = w.get_literal().var();
                    s().mark_visited(v);
                }
            }
        }
    
        for (const auto& cl: s().clauses()) {
            /* TODO: Do we need this? Are the xors still in the clause set?
            if (cl->red() || cl->used_in_xor()) {
                continue;
            }*/
            // TODO: maybe again instead
            if (cl->is_learned())
                continue;
            for (literal l: *cl)
                s().mark_visited(l.var());
        }
    
        //until fixedpoint
        bool changed = true;
        while (changed) {
            changed = false;
            m_interesting.clear();
            for (const unsigned l : m_occurrences) {
                if (m_occ_cnt[l] == 2 && !s().is_visited(l)) {
                    m_interesting.push_back(l);
                }
            }
    
            while (!m_interesting.empty()) {
    
                //Pop and check if it can be XOR-ed together
                const unsigned v = m_interesting.back();
                m_interesting.resize(m_interesting.size()-1);
                if (m_occ_cnt[v] != 2)
                    continue;
    
                unsigned indexes[2];
                unsigned at = 0;
                size_t i2 = 0;
                //SASSERT(watches.size() > literal(v, false).index());
                vector<sat::watched> ws = s().get_wlist(literal(v, false));
    
                //Remove the 2 indexes from the watchlist
                for (unsigned i = 0; i < ws.size(); i++) {
                    const sat::watched& w = ws[i];
                    if (!w.isIdx()) {
                        ws[i2++] = ws[i];
                    } else if (!xors[w.get_idx()].empty()) {
                        SASSERT(at < 2);
                        indexes[at] = w.get_idx();
                        at++;
                    }
                }
                SASSERT(at == 2);
                ws.resize(i2);
    
                xor_clause& x0 = xors[indexes[0]];
                xor_clause& x1 = xors[indexes[1]];
                unsigned clash_var;
                unsigned clash_num = xor_two(&x0, &x1, clash_var);
    
                //If they are equivalent
                if (x0.size() == x1.size()
                    && x0.m_rhs == x1.m_rhs
                    && clash_num == x0.size()
                ) {
                    TRACE("xor", tout 
                    << "x1: " << x0 << " -- at idx: " << indexes[0] 
                    << "and  x2: " << x1 << " -- at idx: " << indexes[1] 
                    << "are equivalent.\n");
    
                    //Update clash values & detached values
                    x1.merge_clash(x0, m_visited);
                    x1.m_detached |= x0.m_detached;
    
                    TRACE("xor", tout << "after merge: " << x1 <<  " -- at idx: " << indexes[1] << "\n";);
    
                    x0 = xor_clause();
    
                    //Re-attach the other, remove the occur of the one we deleted
                    s().m_watches[Lit(v, false)].push(Watched(indexes[1], WatchType::watch_idx_t));
    
                    for (unsigned v2: x1) {
                        sat::literal l(v2, false);
                        SASSERT(m_occ_cnt[l.var()] >= 2);
                        m_occ_cnt[l.var()]--;
                        if (m_occ_cnt[l.var()] == 2 && !s().is_visited(l.var())) {
                            m_interesting.push_back(l.var());
                        }
                    }
                } else if (clash_num > 1 || x0.m_detached || x1.m_detached) {
                    //add back to ws, can't do much
                    ws.push(Watched(indexes[0], WatchType::watch_idx_t));
                    ws.push(Watched(indexes[1], WatchType::watch_idx_t));
                    continue;
                } else {
                    m_occ_cnt[v] -= 2;
                    SASSERT(m_occ_cnt[v] == 0);
    
                    xor_clause x_new(m_tmp_vars_xor_two, x0.m_rhs ^ x1.m_rhs, clash_var);
                    x_new.merge_clash(x0, m_visited);
                    x_new.merge_clash(x1, m_visited);
    
                    TRACE("xor", tout 
                    << "x1: " << x0 << " -- at idx: " << indexes[0] << "\n" 
                    << "x2: " << x1 << " -- at idx: " << indexes[1] << "\n"
                    << "clashed on var: " << clash_var+1 << "\n"
                    << "final: " << x_new <<  " -- at idx: " << xors.size() << "\n";);
    
                    changed = true;
                    xors.push_back(x_new);
                    for(uint32_t v2: x_new) {
                        sat::literal l(v2, false);
                        s().watches[l].push(Watched(xors.size()-1, WatchType::watch_idx_t));
                        SASSERT(m_occ_cnt[l.var()] >= 1);
                        if (m_occ_cnt[l.var()] == 2 && !s().is_visited(l.var())) {
                            m_interesting.push_back(l.var());
                        }
                    }
                    xors[indexes[0]] = xor_clause();
                    xors[indexes[1]] = xor_clause();
                    xored++;
                }
            }
        }
    
        //Clear
        for (const bool_var l : m_occurrences) { 
            m_occ_cnt[l] = 0;
        }
        m_occurrences.clear();
    
        clean_occur_from_idx_types_only_smudged();
        clean_xors_from_empty(xors);
        #endif
    
        return !s().inconsistent();
    }
    
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const  {
        return out;
    }
    
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }
}

