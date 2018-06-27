/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    ast_pattern_match.cpp

Abstract:

    Search for opportune pattern matching utilities.

Author:

    Nikolaj Bjorner (nbjorner) 2007-04-10
    Leonardo (leonardo)

Notes:

    instead of the brute force enumeration of permutations
    we can add an instruction 'gate' which copies the ast
    into a register and creates another register with the same 
    term. Matching against a 'gate' is a noop, apart from clearing
    the ast in the register. Then on backtracking we know how many
    terms were matched from the permutation. It does not make sense
    to enumerate all combinations of terms that were not considered, so
    skip these.

    Also, compilation should re-order terms to fail fast.

--*/

#include "ast/ast.h"
#include "ast/pattern/expr_pattern_match.h"
#include "ast/for_each_ast.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"

expr_pattern_match::expr_pattern_match(ast_manager & manager):
    m_manager(manager), m_precompiled(manager) {        
}

expr_pattern_match::~expr_pattern_match() {
}

bool 
expr_pattern_match::match_quantifier(quantifier* qf, app_ref_vector& patterns, unsigned& weight) {
    if (m_regs.empty()) {
        // HACK: the code crashes if database is empty.
        return false; 
    }
    m_regs[0] = qf->get_expr();
    for (unsigned i = 0; i < m_precompiled.size(); ++i) {
        quantifier* qf2 = m_precompiled[i].get();
        if (qf2->get_kind() != qf->get_kind() || is_lambda(qf)) {
            continue;
        }
        if (qf2->get_num_decls() != qf->get_num_decls()) {
            continue;
        }
        subst s;
        if (match(qf->get_expr(), m_first_instrs[i], s)) {
            for (unsigned j = 0; j < qf2->get_num_patterns(); ++j) {
                app* p = static_cast<app*>(qf2->get_pattern(j));
                expr_ref p_result(m_manager);
                instantiate(p, qf->get_num_decls(), s, p_result);
                patterns.push_back(to_app(p_result.get()));
            }
            weight = qf2->get_weight();
            return true;            
        }
    }
    return false;
}

void
expr_pattern_match::instantiate(expr* a, unsigned num_bound, subst& s, expr_ref& result) {
    bound b;
    for (unsigned i = 0; i < num_bound; ++i) {
        b.insert(m_bound_dom[i], m_bound_rng[i]);
    }
    
    inst_proc proc(m_manager, s, b, m_regs);
    for_each_ast(proc, a);
    expr* v = nullptr;
    proc.m_memoize.find(a, v);
    SASSERT(v);
    result = v;
}



void
expr_pattern_match::compile(expr* q) 
{
    SASSERT(q->get_kind() == AST_QUANTIFIER);
    quantifier* qf = to_quantifier(q);
    unsigned ip = m_instrs.size();
    m_first_instrs.push_back(ip);
    m_precompiled.push_back(qf);

    instr instr(BACKTRACK);
    unsigned_vector regs;
    ptr_vector<expr> pats;
    unsigned max_reg = 1;
    subst s;
    pats.push_back(qf->get_expr());
    regs.push_back(0);
    unsigned num_bound = 0;
    obj_map<var, unsigned> bound;
        
    while (!pats.empty()) {

        unsigned reg = regs.back();
        expr* pat     = pats.back();
        regs.pop_back();
        pats.pop_back();

        instr.m_pat  = pat;
        instr.m_next = m_instrs.size()+1;
        instr.m_reg  = reg;
        instr.m_offset = max_reg;

        switch(pat->get_kind()) {
        case AST_VAR: {
            var* b = to_var(pat);
            if (bound.find(b, instr.m_num_bound)) {
                instr.m_kind = CHECK_BOUND;
            }
            else {
                instr.m_kind = SET_BOUND;
                instr.m_num_bound = num_bound;
                bound.insert(b, num_bound);
                ++num_bound;
            }            
            break;
        }        
        case AST_APP: {
            unsigned r = 0;
            app* app = to_app(pat);
            func_decl* d  = app->get_decl();
                        
            for (unsigned i = 0; i < app->get_num_args(); ++i) {
                regs.push_back(max_reg);
                pats.push_back(app->get_arg(i));
                ++max_reg;
            }

            if (is_var(d)) {
                if (s.find(d, r)) {
                    instr.m_kind = CHECK_VAR;
                    instr.m_other_reg = r;
                }
                else {
                    instr.m_kind = SET_VAR;
                    s.insert(d, reg);
                }        
            }
            else {
                if (d->is_associative() && d->is_commutative()) {
                    instr.m_kind = BIND_AC;
                }
                else if (d->is_commutative()) {
                    SASSERT(app->get_num_args() == 2);
                    instr.m_kind = BIND_C;
                }
                else {
                    instr.m_kind = BIND;           
                }
            }
            break;
        }
        default:
            instr.m_kind = CHECK_TERM;
            break;
        }
        m_instrs.push_back(instr);
    }

    if (m_regs.size() <= max_reg) {
        m_regs.resize(max_reg+1);
    }
    if (m_bound_dom.size() <= num_bound) {
        m_bound_dom.resize(num_bound+1);
        m_bound_rng.resize(num_bound+1);
    }
    
    instr.m_kind = YIELD;
    m_instrs.push_back(instr);
}


bool 
expr_pattern_match::match(expr* a, unsigned init, subst& s) 
{    
    svector<instr> bstack;
    instr pc = m_instrs[init];
    
    while (true) {
        bool ok = false;
        switch(pc.m_kind) {
        case YIELD:
            // substitution s contains registers with matching declarations.
            return true;
        case CHECK_TERM:
            ok = (pc.m_pat == m_regs[pc.m_reg]);
            break;
        case SET_VAR: 
        case CHECK_VAR: {
            app* app1 = to_app(pc.m_pat);
            a   = m_regs[pc.m_reg];
            if (a->get_kind() != AST_APP) {
                break;
            }
            app* app2 = to_app(a);
            if (app1->get_num_args() != app2->get_num_args()) {
                break;
            }
            if (pc.m_kind == CHECK_VAR && 
                to_app(m_regs[pc.m_reg])->get_decl() != 
                to_app(m_regs[pc.m_other_reg])->get_decl()) {
                break;
            }
            for (unsigned i = 0; i < app2->get_num_args(); ++i) {
                m_regs[pc.m_offset + i] = app2->get_arg(i);
            }
            if (pc.m_kind == SET_VAR) {
                s.insert(app1->get_decl(), pc.m_reg);
            }
            ok = true;
            break;
        }
        case SET_BOUND: {
            a = m_regs[pc.m_reg];
            if (a->get_kind() != AST_VAR) {
                break;
            }
            ok = true;
            var* var_a = to_var(a);
            var* var_p = to_var(pc.m_pat);
            // check that the mapping of bound variables remains a bijection.
            for (unsigned i = 0; ok && i < pc.m_num_bound; ++i) {
                ok = (a != m_bound_rng[i]);
            }
            if (!ok) {
                break;
            }
            m_bound_dom[pc.m_num_bound] = var_p;
            m_bound_rng[pc.m_num_bound] = var_a;
            break;
        }
        case CHECK_BOUND:
            TRACE("expr_pattern_match", 
                  tout 
                  << "check bound " 
                  << pc.m_num_bound << " " << pc.m_reg;
                  );
            ok = m_bound_rng[pc.m_num_bound] == m_regs[pc.m_reg];
            break;            
        case BIND:
        case BIND_AC:
        case BIND_C: {
            TRACE("expr_pattern_match", display(tout, pc);
                  tout << mk_pp(m_regs[pc.m_reg],m_manager) << "\n";);
            app* app1 = to_app(pc.m_pat);
            a   = m_regs[pc.m_reg];
            if (a->get_kind() != AST_APP) {
                break;
            }
            app* app2 = to_app(a);
            if (app1->get_num_args() != app2->get_num_args()) {
                break;
            }
            if (!match_decl(app1->get_decl(), app2->get_decl())) {
                break;
            }
            switch(pc.m_kind) {
            case BIND:
                for (unsigned i = 0; i < app2->get_num_args(); ++i) {
                    m_regs[pc.m_offset + i] = app2->get_arg(i);
                }
                ok = true;
                break; // process the next instruction.
            case BIND_AC:
                // push CHOOSE_AC on the backtracking stack.
                bstack.push_back(instr(CHOOSE_AC, pc.m_offset, pc.m_next, app2, 1));
                break;
            case BIND_C:
                // push CHOOSE_C on the backtracking stack.
                ok = true;
                m_regs[pc.m_offset]   = app2->get_arg(0);
                m_regs[pc.m_offset+1] = app2->get_arg(1);
                bstack.push_back(instr(CHOOSE_C, pc.m_offset, pc.m_next, app2, 2));
                break;
            default:
                break;
            }
            break;
        }
        case CHOOSE_C:
            ok = true;
            SASSERT (pc.m_count == 2);
            m_regs[pc.m_offset+1] = pc.m_app->get_arg(0);
            m_regs[pc.m_offset]   = pc.m_app->get_arg(1);
            break;
        case CHOOSE_AC: {
            ok = true;
            app* app2 = pc.m_app;
            for (unsigned i = 0; i < app2->get_num_args(); ++i) {
                m_regs[pc.m_offset + i] = app2->get_arg(i);
            }
            // generate the k'th permutation.
            unsigned k = pc.m_count;
            unsigned fac = 1;
            unsigned num_args = pc.m_app->get_num_args();
            for (unsigned j = 2; j <= num_args; ++j) {
                fac *= (j-1);
                SASSERT(((k /fac) % j) + 1 <= j);
                std::swap(m_regs[pc.m_offset + j - 1], m_regs[pc.m_offset + j - ((k / fac) % j) - 1]);
            }  
            if (k < fac*num_args) {
                bstack.push_back(instr(CHOOSE_AC, pc.m_offset, pc.m_next, app2, k+1));
            }
            break;
        }
        case BACKTRACK:
            if (bstack.empty()) {
                return false;
            }
            pc = bstack.back();
            bstack.pop_back();
            continue; // with the loop.
        }

        if (ok) {
            pc = m_instrs[pc.m_next];
        }
        else {
            TRACE("expr_pattern_match", tout << "backtrack\n";);
            pc = m_instrs[0];
        }
    }
}


bool
expr_pattern_match::match_decl(func_decl const * pat, func_decl const * d) const {
    if (pat == d) {
        return true;
    }
    if (pat->get_arity() != d->get_arity()) {
        return false;
    }
    // match families
    if (pat->get_family_id() == null_family_id) {
        return false;
    }
    if (d->get_family_id() != pat->get_family_id()) {
        return false;
    }
    if (d->get_decl_kind() != pat->get_decl_kind()) {
        return false;
    }
    if (d->get_num_parameters() != pat->get_num_parameters()) {
        return false;
    }
    for (unsigned i = 0; i < d->get_num_parameters(); ++i) {
        if (!(d->get_parameter(i) == pat->get_parameter(i))) {
            return false;
        }
    }
    return true;
}

bool 
expr_pattern_match::is_var(func_decl* d) {
    const char* s = d->get_name().bare_str();
    return s && *s == '?';
}

void 
expr_pattern_match::initialize(char const * spec_string) {
    if (!m_instrs.empty()) {
        return;
    }
    m_instrs.push_back(instr(BACKTRACK));

    std::istringstream is(spec_string);
    cmd_context      ctx(true, &m_manager);	
    bool ps = ctx.print_success_enabled();
    ctx.set_print_success(false);
    VERIFY(parse_smt2_commands(ctx, is));
    ctx.set_print_success(ps);

    ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
    ptr_vector<expr>::const_iterator end = ctx.end_assertions();
    for (; it != end; ++it) {
        compile(*it);
    }
    TRACE("expr_pattern_match", display(tout); );
}

void 
expr_pattern_match::display(std::ostream& out) const {
    for (unsigned i = 0; i < m_instrs.size(); ++i) {
        display(out, m_instrs[i]);
    }
}

void
expr_pattern_match::display(std::ostream& out, instr const& pc) const {
    switch(pc.m_kind) {
    case BACKTRACK:
        out << "backtrack\n";
        break;
    case BIND:
        out << "bind       ";
        out << mk_pp(to_app(pc.m_pat)->get_decl(), m_manager) << " ";
        out << mk_pp(pc.m_pat, m_manager) << "\n";
        out << "next:      " << pc.m_next << "\n";
        out << "offset:    " << pc.m_offset << "\n";
        out << "reg:       " << pc.m_reg << "\n";
        break;
    case BIND_AC:
        out << "bind_ac    ";
        out << mk_pp(to_app(pc.m_pat)->get_decl(), m_manager) << " ";
        out << mk_pp(pc.m_pat, m_manager) << "\n";
        out << "next:      " << pc.m_next << "\n";
        out << "offset:    " << pc.m_offset << "\n";
        out << "reg:       " << pc.m_reg << "\n";
        break;
    case BIND_C:
        out << "bind_c     ";
        out << mk_pp(to_app(pc.m_pat)->get_decl(), m_manager) << " ";
        out << mk_pp(pc.m_pat, m_manager) << "\n";
        out << "next:      " << pc.m_next << "\n";
        out << "offset:    " << pc.m_offset << "\n";
        out << "reg:       " << pc.m_reg << "\n";
        break;
    case CHOOSE_AC:
        out << "choose_ac\n";
        out << "next:      " << pc.m_next  << "\n";
        out << "count:     " << pc.m_count << "\n";
        break;
    case CHOOSE_C:
        out << "choose_c\n";
        out << "next:      " << pc.m_next << "\n";
        //out << "reg:       " << pc.m_reg << "\n";
        break;
    case CHECK_VAR:
        out << "check_var  ";
        out << mk_pp(pc.m_pat, m_manager) << "\n";
        out << "next:      " << pc.m_next << "\n";
        out << "reg:       " << pc.m_reg << "\n";
        out << "other_reg: " << pc.m_other_reg << "\n";
        break;
    case CHECK_TERM:
        out << "check      ";
        out << mk_pp(pc.m_pat, m_manager) << "\n";
        out << "next:      " << pc.m_next << "\n";
        out << "reg:       " << pc.m_reg << "\n";
        break;
    case YIELD:
        out << "yield\n";
        break;
    case SET_VAR:
        out << "set_var    ";
        out << mk_pp(pc.m_pat, m_manager) << "\n";
        out << "next:      " << pc.m_next << "\n";
        break;
    default:
        break;
    } }


// TBD: fix type overloading.
// TBD: bound number of permutations.
// TBD: forward pruning checks.
